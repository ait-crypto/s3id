use ark_ff::{UniformRand, Zero};
use groth_sahai::{prover::Provable, verifier::Verifiable, AbstractCrs};
use rand::thread_rng;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use thiserror::Error;

use crate::{
    atact::{self, AtACTError, Token},
    bls381_helpers::{
        gs::{CProof, CRS, PPE},
        hash_with_domain_separation, multi_pairing, Gt, Scalar, G1G2,
    },
    pedersen::{
        self, get_parameters, Commitment, MultiBasePublicParameters, Opening, ProofMultiIndex,
    },
    tsw::Signature,
};

pub struct PublicParameters {
    atact_pp: atact::PublicParameters,
    pedersen_pp: MultiBasePublicParameters,
    big_l: usize,
    crs: CRS,
}

#[derive(Debug, Error, PartialEq)]
pub enum S3IDError {
    #[error("AtACT error: {0}")]
    AtACT(#[from] AtACTError),
    #[error("Pedersen commitment error: {0}")]
    Pedersen(#[from] pedersen::Error),
    #[error("Invalid attributes")]
    InvalidAttributes,
    #[error("Invalid credential")]
    InvalidCredential,
}

pub struct Issuer {
    sk: atact::Issuer,
    // FIXME: The use of T_dedup to check for duplicate tokens is not
    // implemented. Checking it would make benchmarking harder. Performance-wise
    // it does not make a significant difference.
    _t_dedup: (),
}

impl From<atact::Issuer> for Issuer {
    fn from(value: atact::Issuer) -> Self {
        Self {
            sk: value,
            _t_dedup: (),
        }
    }
}

pub fn setup(
    num_issuers: usize,
    t: usize,
    n: usize,
    tprime: usize,
    big_l: usize,
) -> Result<(PublicParameters, Vec<Issuer>), S3IDError> {
    let (atact_pp, issuers) = atact::setup(num_issuers, n, t, tprime, big_l + 1)?;
    let pedersen_pp = MultiBasePublicParameters::new(big_l);
    let crs = CRS::generate_crs(&mut thread_rng());

    Ok((
        PublicParameters {
            atact_pp,
            pedersen_pp,
            big_l,
            crs,
        },
        issuers.into_iter().map(Into::into).collect(),
    ))
}

pub struct UserPublicParameters {
    // FIXME: token is only used for the deduplication check which is currently
    // not implemented as it would complicat benchmarking
    _token: Token,
    cm_k: Commitment,
}

fn prf_base(msg: &[u8]) -> G1G2 {
    hash_with_domain_separation(msg, b"PRF")
}

pub struct UserSecretKey {
    k: Scalar,
    cm_k_opening: Opening,
}

impl UserSecretKey {
    // Evaluate PRF and return base point (`H(m)`) and the result (`H(m)^k`)
    fn prf(&self, msg: &[u8]) -> (G1G2, G1G2) {
        let prf_base = prf_base(msg);
        (prf_base.clone(), prf_base * self.k)
    }
}

pub fn dedup(
    pp: &PublicParameters,
    attribute: &Scalar,
    issuers: &[Issuer],
) -> Result<(UserPublicParameters, UserSecretKey), S3IDError> {
    // 7.a
    let (strg, cm) = atact::register(attribute, &pp.atact_pp)?;
    let (blind_request, rand) = atact::token_request(&strg, &cm, &pp.atact_pp)?;

    // 7.b
    let blind_tokens = issuers
        .par_iter()
        .map(|issuer| atact::tissue(&blind_request, &issuer.sk, &pp.atact_pp))
        .collect::<Result<Vec<_>, _>>()?;

    // 7.c
    let token = atact::aggregate_unblind(&blind_tokens, &rand, &pp.atact_pp);
    // 7.d
    let token_proof = atact::prove(&token, &rand, &pp.atact_pp);

    let bold_k = Scalar::rand(&mut thread_rng());
    let (cm_k, cm_k_opening) = Commitment::commit(&bold_k);

    // 7.f
    atact::verify(&token, &token_proof, &blind_request, &pp.atact_pp)?;
    // todo: check token in T_Dedup

    Ok((
        UserPublicParameters {
            _token: token,
            cm_k,
        },
        UserSecretKey {
            k: bold_k,
            cm_k_opening,
        },
    ))
}

pub fn microcred(
    attributes: &[Scalar],
    pp_u: &UserPublicParameters,
    prv_u: &UserSecretKey,
    issuers: &[Issuer],
    pp: &PublicParameters,
) -> Result<Vec<Signature>, S3IDError> {
    if attributes.len() != pp.big_l {
        return Err(S3IDError::InvalidAttributes);
    }

    // first produce attributes with their indices to enable parallel iteration
    // `attributes.iter().enumerate().par_bridge()` is not stable!
    let indexed_attributes: Vec<_> = attributes.iter().enumerate().collect();

    indexed_attributes
        .par_iter()
        .map(|(idx, attribute)| -> Result<Signature, S3IDError> {
            // 10.a
            let (cm_i, op_i) = Commitment::index_commit(&prv_u.k, *idx, attribute, &pp.pedersen_pp);
            // 10.b
            let pi_i = pp_u.cm_k.proof_index_commit(
                &prv_u.k,
                &prv_u.cm_k_opening,
                &cm_i,
                &prv_u.k,
                *idx,
                attribute,
                &op_i,
                &pp.pedersen_pp,
            );

            let signatures = issuers
                .par_iter()
                .map(|issuer| -> Result<Signature, S3IDError> {
                    // 10.f
                    pp_u.cm_k
                        .verify_proof_index_commit(&cm_i, *idx, &pi_i, &pp.pedersen_pp)?;

                    // TODO: T_Dedup check

                    // 10.g
                    // NOTE: sign with basis u_i, hence idx + 1
                    Ok(issuer.sk.as_ref().sign_pedersen_commitment(
                        &cm_i,
                        idx + 1,
                        &pp.atact_pp.tsw_pp,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?;
            // 10.h
            let sigma_i =
                Signature::from_shares(&signatures[..pp.atact_pp.t], &pp.atact_pp.lagrange_t);
            // sanity check
            // NOTE: signed with basis u_i, hence idx + 1
            debug_assert!(pp
                .atact_pp
                .pk
                .verify_pedersen_commitment(&cm_i, idx + 1, &sigma_i, &pp.atact_pp.tsw_pp)
                .is_ok());
            // 10.i
            Ok(&sigma_i + &(&pp.atact_pp.pk * -*op_i.as_ref()))
        })
        .collect::<Result<Vec<_>, _>>()
}

pub struct Credential {
    tau: Commitment,
    prf: G1G2,
}

pub struct Proof {
    pi: ProofMultiIndex,
    gs_pi_1: CProof,
}

fn setup_ppe(target: Gt) -> PPE {
    let pp2 = get_parameters();

    let a_consts = vec![pp2.g.0.into()];
    let b_consts = vec![pp2.g.1.into()];
    let gamma = vec![vec![Scalar::zero()]];

    PPE {
        a_consts,
        b_consts,
        gamma,
        target,
    }
}

pub fn appcred(
    attributes: &[Scalar],
    signatures: &[Signature],
    prv_u: &UserSecretKey,
    msg: &[u8],
    attribute_subset: &[Scalar],
    pp: &PublicParameters,
) -> Result<(Credential, Proof), S3IDError> {
    let mut rng = thread_rng();

    let q: Vec<_> = attribute_subset
        .iter()
        .map(|attribute| {
            attributes
                .iter()
                .position(|a| *a == *attribute)
                .ok_or(S3IDError::InvalidAttributes)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let (tau, tau_opening) = Commitment::multi_index_commit(
        &prv_u.k,
        q.iter().map(|idx| (*idx, attributes[*idx])),
        &pp.pedersen_pp,
    );

    let (prf_base, prf) = prv_u.prf(msg);

    let zeta = q.iter().map(|idx| &signatures[*idx]).sum::<Signature>()
        + (&pp.atact_pp.pk * tau_opening.r);

    let pp2 = get_parameters();

    let g1_1_vars = vec![zeta.0 .0.into()];
    let g2_2_vars = vec![zeta.0 .1.into()];

    let target = multi_pairing(&[(&zeta.0, &pp2.g), (&pp2.g, &zeta.0)]);

    // this is limitation of the GS implementation, we can only do one equation
    // where both variables in G1 and G2 are used; hence we prove the product of
    // these two equations to understand the performance characteristics
    let equ_1 = setup_ppe(target);
    let gs_pi_1 = equ_1.commit_and_prove(&g1_1_vars, &g2_2_vars, &pp.crs, &mut rng);

    let pi = tau.proof_multi_index_commit(
        &prv_u.k,
        q.iter().map(|idx| (*idx, attributes[*idx])),
        &tau_opening,
        &prf_base,
        &prf,
        Some(&gs_pi_1),
        &pp.pedersen_pp,
    );

    Ok((Credential { tau, prf }, Proof { pi, gs_pi_1 }))
}

pub fn verifycred(
    cred: &Credential,
    pi: &Proof,
    msg: &[u8],
    pp: &PublicParameters,
) -> Result<(), S3IDError> {
    cred.tau.verify_proof_multi_index_commit(
        &prf_base(msg),
        &cred.prf,
        Some(&pi.gs_pi_1),
        &pi.pi,
        &pp.pedersen_pp,
    )?;

    let h: G1G2 = pi
        .pi
        .s_i
        .iter()
        .map(|(idx, _)| {
            // NOTE: signed with basis u_i, hence idx + 1
            &pp.atact_pp.tsw_pp[*idx + 1]
        })
        .sum();
    let pk = &pp.atact_pp.pk;
    let tau = &cred.tau;
    let check = h + &tau.0;

    let target = multi_pairing(&[(&check, &pk.0), (&pk.0, &check)]);

    let equ_1 = setup_ppe(target);
    if equ_1.verify(&pi.gs_pi_1, &pp.crs) {
        Ok(())
    } else {
        Err(S3IDError::InvalidCredential)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use ark_ff::UniformRand;

    #[test]
    fn basic() {
        let mut rng = thread_rng();

        let num_issuers = 10;
        let t = num_issuers / 2 + 1;
        let n = 32;
        let tprime = n / 2 + 1;
        let big_l = 10;

        let attribute = Scalar::rand(&mut rng);
        let attributes: Vec<_> = (0..big_l).map(|_| Scalar::rand(&mut rng)).collect();
        let msg = b"some message";

        let (pp, issuers) = setup(num_issuers, t, n, tprime, big_l).expect("setup failed");
        let (pp_u, prv_u) = dedup(&pp, &attribute, &issuers).expect("dedup failed");

        let signatures =
            microcred(&attributes, &pp_u, &prv_u, &issuers, &pp).expect("microred failed");

        for selector in [2, 3, 4] {
            let attributes_subset: Vec<_> = (0..big_l)
                .filter_map(|idx| {
                    if idx % selector == 0 {
                        Some(attributes[idx])
                    } else {
                        None
                    }
                })
                .collect();

            let (cred, pi) = appcred(
                &attributes,
                &signatures,
                &prv_u,
                msg,
                &attributes_subset,
                &pp,
            )
            .expect("appcred failed");

            assert_eq!(verifycred(&cred, &pi, msg, &pp), Ok(()));
            assert!(verifycred(&cred, &pi, b"some other message", &pp).is_err());
        }
    }

    #[test]
    fn parameters_for_benches() {
        const NUM_ISSUERS: [usize; 3] = [4, 16, 64];
        const N: [usize; 3] = [30, 40, 128];
        const BIG_L: usize = 16;

        for num_issuers in NUM_ISSUERS {
            for n in N {
                let t = num_issuers / 2 + 1;
                let tprime = n / 2 + 1;

                assert!(
                    setup(num_issuers, t, n, tprime, BIG_L).is_ok(),
                    "issuers {}, t {}, n {}, t' {}",
                    num_issuers,
                    t,
                    n,
                    tprime
                );
            }
        }
    }
}
