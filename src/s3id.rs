use bls12_381::Scalar;
use group::ff::Field;
use rand::thread_rng;
use thiserror::Error;

use crate::{
    atact::{self, AtACTError, Token},
    pedersen::{self, Commitment, MultiBasePublicParameters, Opening},
    tsw::Signature,
};

pub struct PublicParameters {
    atact_pp: atact::PublicParameters,
    pedersen_pp: MultiBasePublicParameters,
    big_l: usize,
}

#[derive(Debug, Error)]
pub enum S3IDError {
    #[error("AtACT error: {0}")]
    AtACT(#[from] AtACTError),
    #[error("Pedersen commitment erro: {0}")]
    Pedersen(#[from] pedersen::Error),
    #[error("Invalid attributes")]
    InvalidAttributes,
}

pub struct Issuer {
    sk: atact::Issuer,
    t_dedup: Vec<usize>, // FIXME
}

impl From<atact::Issuer> for Issuer {
    fn from(value: atact::Issuer) -> Self {
        Self {
            sk: value,
            t_dedup: Vec::new(),
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
    token: Token,
    cm_k: Commitment,
    // idx
}

pub struct UserSecretKey {
    attribute: Scalar,
    k: Scalar,
    // TODO: fix in paper
    cm_k_opening: Opening,
}

pub fn dedup(
    pp: &PublicParameters,
    attribute: &Scalar,
    issuers: &[Issuer],
) -> Result<(UserPublicParameters, UserSecretKey), AtACTError> {
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
        UserPublicParameters { token, cm_k },
        UserSecretKey {
            attribute: *attribute,
            k: bold_k,
            cm_k_opening,
        },
    ))
}

pub fn microcred(
    attributes: &[Scalar],
    pp_u: UserPublicParameters,
    prv_u: UserSecretKey,
    issuers: &[Issuer],
    pp: &PublicParameters,
) -> Result<Vec<Signature>, S3IDError> {
    if attributes.len() != pp.big_l {
        return Err(S3IDError::InvalidAttributes);
    }

    let mut sis = Vec::with_capacity(attributes.len());
    for (idx, attribute) in attributes.iter().enumerate() {
        let (cm_i, op_i) = Commitment::index_commit(&prv_u.k, idx, attribute, &pp.pedersen_pp);
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

        let mut signatures = vec![];
        for issuer in issuers {
            pp_u.cm_k
                .verify_proof_index_commit(&cm_i, idx, &pi_i, &pp.pedersen_pp)?;

            // TODO: T_Dedup chcekc

            let sigma_ij = issuer.sk.as_ref().sign_pedersen_commitment(&cm_i, idx);
            signatures.push(sigma_ij);
        }

        let sigma_i = Signature::from_shares(&signatures[..pp.atact_pp.t], &pp.atact_pp.lagrange_t);
        sis.push(&sigma_i + &(&pp.atact_pp.pk * *prv_u.cm_k_opening.as_ref()));
    }

    Ok(sis)
}

pub fn appcred(
    attributes: &[Scalar],
    signatures: &[Signature],
    prv_u: UserSecretKey,
    msg: &[u8],
    attribute_subset: &[Scalar],
) -> Result<(), S3IDError> {
    let q: Vec<_> = attribute_subset
        .iter()
        .map(|attribute| {
            attributes
                .iter()
                .position(|a| *a == *attribute)
                .ok_or(S3IDError::InvalidAttributes)
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(())
}
