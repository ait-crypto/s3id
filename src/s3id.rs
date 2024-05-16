use bls12_381::{G1Projective, G2Projective, Scalar};
use group::ff::Field;
use rand::thread_rng;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use thiserror::Error;

use crate::{
    atact::{self, AtACTError, Token},
    bls381_helpers::{hash_usize_1, hash_usize_2, pairing},
    pedersen::{
        self, get_g, get_ghat, Commitment, MultiBasePublicParameters, Opening, ProofMultiIndex,
    },
    tsw::Signature,
};

pub struct PublicParameters {
    atact_pp: atact::PublicParameters,
    pedersen_pp: MultiBasePublicParameters,
    big_l: usize,
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
    _t_dedup: Vec<usize>, // FIXME
}

impl From<atact::Issuer> for Issuer {
    fn from(value: atact::Issuer) -> Self {
        Self {
            sk: value,
            _t_dedup: Default::default(),
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
    let (atact_pp, issuers) = atact::setup(num_issuers, n, t, tprime)?;
    let pedersen_pp = MultiBasePublicParameters::new(big_l);

    Ok((
        PublicParameters {
            atact_pp,
            pedersen_pp,
            big_l,
        },
        issuers.into_iter().map(|issuer| issuer.into()).collect(),
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
    let mut blind_tokens = Vec::with_capacity(issuers.len());
    for issuer in issuers {
        let token = atact::tissue(&blind_request, &issuer.sk, &pp.atact_pp)?;
        blind_tokens.push(token);
    }

    // 7.c
    let token = atact::aggregate_unblind(&blind_tokens, &rand, &pp.atact_pp);
    // 7.d
    let token_proof = atact::prove(&token, &rand, &pp.atact_pp);

    let bold_k = Scalar::random(thread_rng());
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

    let mut sis = Vec::with_capacity(attributes.len());
    for (idx, attribute) in attributes.iter().enumerate() {
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
            .map(|issuer| -> Result<Signature, pedersen::Error> {
                // 10.f
                pp_u.cm_k
                    .verify_proof_index_commit(&cm_i, idx, &pi_i, &pp.pedersen_pp)?;

                // TODO: T_Dedup check

                // 10.g
                Ok(issuer.sk.as_ref().sign_pedersen_commitment(&cm_i, idx))
            })
            .collect::<Result<Vec<_>, _>>()?;
        // 10.h
        let sigma_i = Signature::from_shares(&signatures[..pp.atact_pp.t], &pp.atact_pp.lagrange_t);
        // sanity check
        debug_assert!(pp
            .atact_pp
            .pk
            .verify_pedersen_commitment(&cm_i, idx, &sigma_i)
            .is_ok());
        // 10.i
        sis.push(&sigma_i + &(&pp.atact_pp.pk * -*op_i.as_ref()));
    }

    Ok(sis)
}

pub struct Credential {
    zeta: Signature,
    tau: Commitment,
}

pub type Proof = ProofMultiIndex;

pub fn appcred(
    attributes: &[Scalar],
    signatures: &[Signature],
    prv_u: &UserSecretKey,
    _msg: &[u8],
    attribute_subset: &[Scalar],
    pp: &PublicParameters,
) -> Result<(Credential, ProofMultiIndex), S3IDError> {
    let q: Vec<_> = attribute_subset
        .iter()
        .map(|attribute| {
            attributes
                .iter()
                .position(|a| *a == *attribute)
                .ok_or(S3IDError::InvalidAttributes)
        })
        .collect::<Result<Vec<_>, _>>()?;
    debug_assert_eq!(q, [0, 2, 4, 6, 8]);

    let (tau, tau_opening) = Commitment::multi_index_commit(
        &prv_u.k,
        q.iter().map(|idx| (*idx, attributes[*idx])),
        &pp.pedersen_pp,
    );
    let zeta = q.iter().map(|idx| &signatures[*idx]).sum::<Signature>()
        + (&pp.atact_pp.pk * tau_opening.as_ref());

    let pi = tau.proof_multi_index_commit(
        &prv_u.k,
        q.iter().map(|idx| (*idx, attributes[*idx])),
        &tau_opening,
        &pp.pedersen_pp,
    );

    Ok((Credential { zeta, tau }, pi))
}

pub fn verifycred(
    cred: &Credential,
    pi: &Proof,
    _msg: &[u8],
    pp: &PublicParameters,
) -> Result<(), S3IDError> {
    cred.tau
        .verify_proof_multi_index_commit(pi, &pp.pedersen_pp)?;

    let (h_1, h_2) = pi.s_i.iter().fold(
        (G1Projective::identity(), G2Projective::identity()),
        |(h_1, h_2), (idx, _)| (h_1 + hash_usize_1(*idx), h_2 + hash_usize_2(*idx)),
    );

    let pk = &pp.atact_pp.pk;
    let zeta = &cred.zeta;
    let tau = &cred.tau;
    if pairing(zeta.sigma_1, get_ghat()) != pairing(h_1 + tau.cm_1, pk.pk_2)
        || pairing(get_g(), zeta.sigma_2) != pairing(pk.pk_1, h_2 + tau.cm_2)
    {
        Err(S3IDError::InvalidCredential)
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic() {
        let num_issuers = 10;
        let t = num_issuers / 2 + 1;
        let n = 64;
        let tprime = n / 2 + 1;
        let big_l = 10;

        let attribute = Scalar::random(thread_rng());
        let attributes: Vec<_> = (0..big_l).map(|_| Scalar::random(thread_rng())).collect();
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
