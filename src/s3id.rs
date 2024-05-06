use bls12_381::Scalar;
use group::ff::Field;
use rand::thread_rng;
use thiserror::Error;

use crate::{
    atact::{self, AtACTError, Token},
    pedersen::{self, Commitment, MultiBasePublicParameters},
};

pub struct PublicParameters {
    atact_pp: atact::PublicParameters,
    pedersen_pp: MultiBasePublicParameters,
}

#[derive(Debug, Error)]
pub enum S3IDError {
    #[error("AtACT error: {0}")]
    AtACT(#[from] AtACTError),
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
    attributes: &[Scalar],
) -> Result<(PublicParameters, Vec<Issuer>), S3IDError> {
    let (atact_pp, issuers) = atact::setup(num_issuers, n, t, tprime, attributes)?;
    let pedersen_pp = MultiBasePublicParameters::new(attributes.len());

    Ok((
        PublicParameters {
            atact_pp,
            pedersen_pp,
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
    let (cm_k, _o_k) = Commitment::commit(&bold_k);

    // 7.f
    atact::verify(&token, &token_proof, &blind_request, &pp.atact_pp)?;
    // todo: check token in T_Dedup

    Ok((
        UserPublicParameters { token, cm_k },
        UserSecretKey {
            attribute: *attribute,
            k: bold_k,
        },
    ))
}

pub fn microcred(
    attributes: &[Scalar],
    pp_u: UserPublicParameters,
    prv_u: UserSecretKey,
    issuers: &[Issuer],
) -> Result<(), S3IDError> {
    Ok(())
}
