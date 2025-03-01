use std::cmp::max;

use ark_ff::{Field, UniformRand, Zero};
use ark_serialize::CanonicalSerialize;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use thiserror::Error;

use crate::{
    bls381_helpers::{Scalar, multi_pairing},
    lagrange::Lagrange,
    pedersen::{Commitment, Proof2PK},
    tsw::{self, PublicKey, SecretKey, Signature},
};

const UNIQUE_ATTRIBUTE_INDEX: usize = 0;

pub struct Issuer {
    sk: SecretKey,
}

impl AsRef<SecretKey> for Issuer {
    fn as_ref(&self) -> &SecretKey {
        &self.sk
    }
}

pub struct PublicParameters {
    pub pk: PublicKey,
    pub n: usize,
    pub t: usize,
    pub tprime: usize,
    pub lagrange_n: Lagrange,
    pub lagrange_t: Lagrange,
    lagrange_tprime: Lagrange,
    pub tsw_pp: tsw::PublicParameters,
}

pub fn setup(
    num_issuers: usize,
    n: usize,
    t: usize,
    tprime: usize,
    l: usize,
) -> Result<(PublicParameters, Vec<Issuer>), AtACTError> {
    if tprime < 2 || tprime >= n || t < 2 || t >= num_issuers {
        return Err(AtACTError::InvalidParameters);
    }

    let sk = SecretKey::new();
    let pk = sk.to_public_key();
    let scalars: Vec<_> = (1..=max(n, t) as u64).map(Scalar::from).collect();

    let pp = PublicParameters {
        pk,
        n,
        t,
        tprime,
        lagrange_n: Lagrange::new(&scalars[..n]),
        lagrange_t: Lagrange::new(&scalars[..t]),
        lagrange_tprime: Lagrange::new(&scalars[..tprime]),
        tsw_pp: tsw::PublicParameters::new(l + 1),
    };

    Ok((
        pp,
        sk.into_shares(num_issuers, t)
            .into_iter()
            .map(|sk| Issuer { sk })
            .collect(),
    ))
}

#[derive(Clone)]
pub struct StRG {
    a: Scalar,
    r: Scalar,
}

pub fn register(a: &Scalar, _pp: &PublicParameters) -> Result<(StRG, Commitment), AtACTError> {
    // Step 7
    let (cm, opening) = Commitment::commit(a);

    Ok((
        StRG {
            a: *a,
            r: opening.r,
        },
        cm,
    ))
}

pub struct BlindRequest {
    cm: Commitment,
    cm_ks: Vec<Commitment>,
    bold_cm_k: Commitment,
}

pub struct Rand {
    strg: StRG,
    r_ks: Vec<PublicKey>,
    bold_k: Scalar,
    bold_rk: Scalar,
}

pub fn token_request(
    strg: &StRG,
    commitment: &Commitment,
    pp: &PublicParameters,
) -> Result<(BlindRequest, Rand), AtACTError> {
    let mut rng = rand::thread_rng();

    // Step 8
    let mut rks = vec![];
    let mut coms = vec![];
    for _ in 0..(pp.tprime - 1) {
        let ak = Scalar::rand(&mut rng);
        let (cm_k, o_k) = Commitment::commit(&ak);
        coms.push(cm_k);
        rks.push(&pp.pk * o_k.r);
    }

    // Step 9
    let pk_r = &pp.pk * strg.r;

    let base_points: Vec<_> = (1..=pp.tprime as u64).map(Scalar::from).collect();
    let mut lagrange = Lagrange::new(&base_points);

    for k in pp.tprime..=pp.n {
        if k != pp.tprime {
            lagrange.update_point(pp.tprime - 1, Scalar::from(k as u64));
        }
        let lk_i = lagrange
            .eval_j_0(pp.tprime - 1)
            .inverse()
            .ok_or(AtACTError::UnknownError)?;

        let base_com = commitment
            - &coms
                .iter()
                .take(pp.tprime - 1)
                .enumerate()
                .map(|(j, comj)| comj * lagrange.eval_j_0(j))
                .sum::<Commitment>();
        let base_pk = &pk_r
            - &rks
                .iter()
                .take(pp.tprime - 1)
                .enumerate()
                .map(|(j, rj)| rj * lagrange.eval_j_0(j))
                .sum::<PublicKey>();

        coms.push(base_com * lk_i);
        rks.push(base_pk * lk_i);
    }

    // Step 10
    let bold_k = Scalar::rand(&mut rng);
    let (bold_cm_k, bold_cm_opening) = Commitment::commit(&bold_k);

    Ok((
        BlindRequest {
            cm: commitment.clone(),
            cm_ks: coms,
            bold_cm_k,
        },
        Rand {
            strg: strg.clone(),
            r_ks: rks,
            bold_k,
            bold_rk: bold_cm_opening.r,
        },
    ))
}

pub struct BlindToken {
    sigma: Signature,
}

pub fn tissue(
    blind_request: &BlindRequest,
    prv_j: &Issuer,
    pp: &PublicParameters,
) -> Result<Vec<BlindToken>, AtACTError> {
    let check_cm = pp.lagrange_n.eval_0(blind_request.cm_ks.as_ref());

    if check_cm != blind_request.cm {
        return Err(AtACTError::InvalidCommitment);
    }

    Ok(blind_request
        .cm_ks
        .iter()
        .map(|commitment| BlindToken {
            sigma: prv_j.sk.sign_pedersen_commitment(
                commitment,
                UNIQUE_ATTRIBUTE_INDEX,
                &pp.tsw_pp,
            ),
        })
        .collect())
}

pub struct Token {
    s: Signature,
    sks: Vec<Signature>,
}

impl Token {
    pub fn hash_prime(&self, pp: &PublicParameters) -> Vec<usize> {
        let mut buffer = Vec::new();
        self.s.0.serialize_uncompressed(&mut buffer).unwrap();
        let mut hasher = sha3::Shake256::default();
        hasher.update(&buffer);
        let mut reader = hasher.finalize_xof();
        debug_assert!(pp.n < 256);

        let mask = pp.n.next_power_of_two() - 1;
        let mut ret = vec![];
        while ret.len() < pp.tprime - 1 {
            let mut buffer = [0u8; 1];
            reader.read(&mut buffer);
            let value = (u8::from_le_bytes(buffer) as usize) & mask;
            if value < pp.n && !ret.contains(&value) {
                ret.push(value);
            }
        }
        ret
    }
}

pub fn aggregate_unblind(
    blind_tokens: &Vec<Vec<BlindToken>>,
    rand: &Rand,
    pp: &PublicParameters,
) -> Token {
    #[cfg(debug_assertions)]
    {
        for blind_token in blind_tokens {
            assert_eq!(blind_token.len(), pp.n);
        }
    }
    debug_assert_eq!(rand.r_ks.len(), pp.n);

    let sks: Vec<_> = (0..pp.n)
        .into_par_iter()
        .map(|k| {
            let sigs: Vec<_> = blind_tokens
                .iter()
                .map(|token| &token[k].sigma)
                .take(pp.t)
                .cloned()
                .collect();
            Signature::from_shares(&sigs, &pp.lagrange_t) - &rand.r_ks[k]
        })
        .collect();

    Token {
        s: pp.lagrange_n.eval_0(&sks),
        sks,
    }
}

pub struct TokenProof {
    ss: Vec<Signature>,
    pk_prime: PublicKey,
    rs: Vec<PublicKey>,
    pi_zk: Proof2PK,
}

pub fn prove(token: &Token, rand: &Rand, pp: &PublicParameters) -> TokenProof {
    let c = token.hash_prime(pp);
    debug_assert_eq!(c.len(), pp.tprime - 1);

    let ss = token
        .sks
        .iter()
        .map(|signature| signature * rand.bold_k)
        .collect();
    let pk_prime = &pp.pk * rand.bold_k;
    debug_assert!(pk_prime.is_valid());

    let rs = c.iter().map(|k| &rand.r_ks[*k] * rand.bold_k).collect();

    let (cm, o) = Commitment::commit_with_randomness(&rand.strg.a, &rand.strg.r);
    let (bold_cm, bold_o) = Commitment::commit_with_randomness(&rand.bold_k, &rand.bold_rk);

    let pi_zk = cm.proof_2_pk(
        &rand.strg.a,
        &o,
        &bold_cm,
        &rand.bold_k,
        &bold_o,
        &pp.pk.0,
        &pk_prime.0,
    );

    TokenProof {
        ss,
        pk_prime,
        rs,
        pi_zk,
    }
}

pub fn verify(
    token: &Token,
    token_proof: &TokenProof,
    blind_request: &BlindRequest,
    pp: &PublicParameters,
) -> Result<(), AtACTError> {
    let c = token.hash_prime(pp);
    debug_assert_eq!(c.len(), pp.tprime - 1);

    let pk_prime = &token_proof.pk_prime;

    if blind_request
        .cm
        .verify_proof_2_pk(
            &blind_request.bold_cm_k,
            &pp.pk.0,
            &token_proof.pk_prime.0,
            &token_proof.pi_zk,
        )
        .is_err()
    {
        return Err(AtACTError::InvalidZKProof);
    }

    let sk_prod: Signature = (0..pp.tprime)
        .map(|k| &token_proof.ss[k] * pp.lagrange_tprime.eval_j_0(k))
        .sum();
    let sk_prod = -sk_prod.0;
    if !multi_pairing(&[(&token.s.0, &token_proof.pk_prime.0), (&sk_prod, &pp.pk.0)]).is_zero()
        || !multi_pairing(&[(&token_proof.pk_prime.0, &token.s.0), (&pp.pk.0, &sk_prod)]).is_zero()
    {
        return Err(AtACTError::InvalidToken);
    }

    let mut base_points: Vec<_> = c.iter().map(|k| Scalar::from(*k as u64 + 1)).collect();
    base_points.push(Scalar::from(u64::MAX));
    let mut lagrange = Lagrange::new(&base_points);

    for k in 0..pp.n {
        if let Some(k_index) = c.iter().position(|v| k == *v) {
            // 29.e
            let rk_prime = &token_proof.rs[k_index];
            let sk_prime = &token_proof.ss[k];

            let sigma = sk_prime + rk_prime;
            if pk_prime
                .verify_pedersen_commitment(
                    &blind_request.cm_ks[k],
                    UNIQUE_ATTRIBUTE_INDEX,
                    &sigma,
                    &pp.tsw_pp,
                )
                .is_err()
            {
                return Err(AtACTError::InvalidSignature(k));
            }
        } else {
            lagrange.update_point(pp.tprime - 1, Scalar::from(k as u64 + 1));

            let cm_base: Commitment = c
                .iter()
                .enumerate()
                .map(|(j, k)| &blind_request.cm_ks[*k] * lagrange.eval_j_0(j))
                .sum();

            // 29.d
            if &blind_request.cm_ks[k] * lagrange.eval_j_0(pp.tprime - 1) + &cm_base
                != blind_request.cm
            {
                return Err(AtACTError::InvalidCommitmentProof(k));
            }
        }
    }

    Ok(())
}

#[derive(Error, Debug, PartialEq, Clone)]
pub enum AtACTError {
    #[error("Invalid parameters.")]
    InvalidParameters,
    #[error("Commitment check failed.")]
    InvalidCommitment,
    #[error("Challenges do not match.")]
    InvalidChallenge,
    #[error("Invalid attribute.")]
    InvalidAttribute,
    #[error("Invalid commitment in proof.")]
    InvalidCommitmentProof(usize),
    #[error("Invalid signature.")]
    InvalidSignature(usize),
    #[error("Invalid token.")]
    InvalidToken,
    #[error("Invalid ZK proof.")]
    InvalidZKProof,
    #[error("Invalid token proof: {0:?}")]
    InvalidProof(Vec<AtACTError>),
    #[error("Unknown error")]
    UnknownError,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic() {
        const NUM_ISSUERS: usize = 8;
        const N: usize = 8;
        const T: usize = N / 2;
        const TPRIME: usize = N / 2;
        const NUM_ATTRIBUTES: usize = 12;

        let mut rng = rand::thread_rng();
        let attributes: Vec<_> = (0..NUM_ATTRIBUTES)
            .map(|_| Scalar::rand(&mut rng))
            .collect();

        let (pp, issuers) = setup(NUM_ISSUERS, N, T, TPRIME, 1).expect("setup failed");

        for a in attributes {
            let (strg, cm) = register(&a, &pp).expect("register failed");
            let (blind_request, rand) =
                token_request(&strg, &cm, &pp).expect("token request failed");
            let mut blind_tokens = vec![];
            for issuer in &issuers {
                let blind_token = tissue(&blind_request, issuer, &pp).expect("tissue failed");
                assert_eq!(blind_token.len(), pp.n);
                blind_tokens.push(blind_token);
            }

            let token = aggregate_unblind(&blind_tokens, &rand, &pp);
            let token_proof = prove(&token, &rand, &pp);
            assert_eq!(verify(&token, &token_proof, &blind_request, &pp), Ok(()));
        }
    }

    #[test]
    fn parameters_for_benches() {
        const NUM_ISSUERS: [usize; 3] = [4, 16, 64];
        const N: [usize; 3] = [30, 40, 128];

        for num_issuers in NUM_ISSUERS {
            for n in N {
                let t = num_issuers / 2 + 1;
                let tprime = n / 2 + 1;

                assert!(
                    setup(num_issuers, n, t, tprime, 1).is_ok(),
                    "issuers {num_issuers}, t {t}, n {n}, t' {tprime}"
                );
            }
        }
    }
}
