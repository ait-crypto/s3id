use ark_ff::{UniformRand, Zero};
use groth_sahai::{prover::Provable, verifier::Verifiable, AbstractCrs, Matrix};
use rand::thread_rng;
use rayon::iter::{IntoParallelRefIterator, ParallelBridge, ParallelIterator};
use thiserror::Error;

use crate::{
    atact::{self, AtACTError, Token},
    bls381_helpers::{
        gs::{CProof, CRS, PPE},
        hash_with_domain_separation, pairing, Scalar, G1G2,
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
    #[error("Pedersen commitment erro: {0}")]
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
    // it makes not significant difference.
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
    _token: Token,
    cm_k: Commitment,
    // idx
}

pub struct UserSecretKey {
    k: Scalar,
    // TODO: fix in paper
    cm_k_opening: Opening,
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

    attributes
        .iter()
        .enumerate()
        .par_bridge()
        .map(|(idx, attribute)| -> Result<Signature, S3IDError> {
            // 10.a
            let (cm_i, op_i) = Commitment::index_commit(&prv_u.k, idx, attribute, &pp.pedersen_pp);
            // 10.b
            let pi_i = pp_u.cm_k.proof_index_commit(
                &prv_u.k,
                &prv_u.cm_k_opening,
                &cm_i,
                &prv_u.k,
                idx,
                attribute,
                &op_i,
                &pp.pedersen_pp,
            );

            let signatures = issuers
                .par_iter()
                .map(|issuer| -> Result<Signature, S3IDError> {
                    // 10.f
                    pp_u.cm_k
                        .verify_proof_index_commit(&cm_i, idx, &pi_i, &pp.pedersen_pp)?;

                    // TODO: T_Dedup check

                    // 10.g
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
    // gs_pi_2: CProof,
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

    let prf_base = hash_with_domain_separation(msg, b"PRF");
    let prf = prf_base.clone() * prv_u.k;

    let zeta = q.iter().map(|idx| &signatures[*idx]).sum::<Signature>()
        + (&pp.atact_pp.pk * tau_opening.r);

    let pi = tau.proof_multi_index_commit(
        &prv_u.k,
        q.iter().map(|idx| (*idx, attributes[*idx])),
        &tau_opening,
        &prf_base,
        &prf,
        &pp.pedersen_pp,
    );

    // equation:
    // e(zeta, g) = t
    // e(g, zeta) = t

    let pp2 = get_parameters();

    let g1_1_vars = vec![zeta.0 .0.into()];
    let g2_2_vars = vec![zeta.0 .1.into()];

    let g1_2_consts = vec![pp2.g.0.into()];
    let g2_1_consts = vec![pp2.g.1.into()];

    let gamma: Matrix<_> = vec![vec![Scalar::zero()]];

    let target_1 = pairing(&zeta.0, &pp2.g);
    let target_2 = pairing(&pp2.g, &zeta.0);

    let equ_1 = PPE {
        a_consts: g1_2_consts,
        b_consts: g2_1_consts,
        gamma: gamma.clone(),
        target: target_1 * target_2,
    };
    let gs_pi_1 = equ_1.commit_and_prove(&g1_1_vars, &g2_2_vars, &pp.crs, &mut rng);
    // assert!(equ.verify(&proof, &crs));

    Ok((
        Credential { tau, prf },
        Proof {
            pi,
            gs_pi_1,
            // gs_pi_2,
        },
    ))
}

pub fn verifycred(
    cred: &Credential,
    pi: &Proof,
    msg: &[u8],
    pp: &PublicParameters,
) -> Result<(), S3IDError> {
    cred.tau.verify_proof_multi_index_commit(
        &hash_with_domain_separation(msg, b"PRF"),
        &cred.prf,
        &pi.pi,
        &pp.pedersen_pp,
    )?;

    let h: G1G2 = pi
        .pi
        .s_i
        .iter()
        .map(|(idx, _)| &pp.atact_pp.tsw_pp[*idx + 1])
        .sum();
    let pk = &pp.atact_pp.pk;
    let tau = &cred.tau;
    let pp2 = get_parameters();
    let check = h + &tau.0;

    let g1_2_consts = vec![pp2.g.0.into()];
    let g2_1_consts = vec![pp2.g.1.into()];

    let gamma: Matrix<_> = vec![vec![Scalar::zero()]];

    let target_1 = pairing(&check, &pk.0);
    let target_2 = pairing(&pk.0, &check);

    let equ_1 = PPE {
        a_consts: g1_2_consts,
        b_consts: g2_1_consts,
        gamma,
        target: target_1 * target_2,
    };
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
        let attributes_subset: Vec<_> = (0..big_l)
            .filter_map(|idx| {
                if idx % 2 == 0 {
                    Some(attributes[idx])
                } else {
                    None
                }
            })
            .collect();

        let msg = b"some message";

        let (pp, issuers) = setup(num_issuers, t, n, tprime, big_l).expect("setup failed");
        let (pp_u, prv_u) = dedup(&pp, &attribute, &issuers).expect("dedup failed");

        let signatures =
            microcred(&attributes, &pp_u, &prv_u, &issuers, &pp).expect("microred failed");
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
    }
}
