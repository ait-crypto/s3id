use bls12_381::Scalar;
use group::ff::Field;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use thiserror::Error;

use crate::{
    bls381_helpers::{pairing, SerdeWrapper},
    lagrange::Lagrange,
    pedersen::{Commitment, Proof2PK},
    tsw::{PublicKey, SecretKey, Signature},
};

pub struct Issuer {
    sk: SecretKey,
}

pub struct PublicParameters {
    pk: PublicKey,
    n: usize,
    t: usize,
    tprime: usize,
    attributes: Vec<Scalar>,
    lagrange_n: Lagrange,
    lagrange_t: Lagrange,
    lagrange_tprime: Lagrange,
}

pub fn setup(
    num_issuers: usize,
    n: usize,
    t: usize,
    tprime: usize,
    attributes: &[Scalar],
) -> Result<(PublicParameters, Vec<Issuer>), AtACTError> {
    if tprime < 2 || tprime >= n || t < 2 || t >= num_issuers {
        return Err(AtACTError::InvalidParameters);
    }

    let sk = SecretKey::new();
    let pk = sk.to_public_key();

    let pp = PublicParameters {
        pk,
        n,
        t,
        tprime,
        attributes: attributes.into(),
        lagrange_n: Lagrange::new(
            (1..=n)
                .map(|i| Scalar::from(i as u64))
                .collect::<Vec<_>>()
                .as_ref(),
        ),
        lagrange_t: Lagrange::new(
            (1..=t)
                .map(|i| Scalar::from(i as u64))
                .collect::<Vec<_>>()
                .as_ref(),
        ),
        lagrange_tprime: Lagrange::new(
            (1..=tprime)
                .map(|i| Scalar::from(i as u64))
                .collect::<Vec<_>>()
                .as_ref(),
        ),
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
    attribute_index: usize,
    r: Scalar,
}

pub fn register(a: &Scalar, pp: &PublicParameters) -> Result<(StRG, Commitment), AtACTError> {
    let attribute_index = pp
        .attributes
        .iter()
        .position(|attribute| *a == *attribute)
        .ok_or(AtACTError::InvalidAttribute)?;

    // Step 7
    let (cm, opening) = Commitment::commit(a);

    Ok((
        StRG {
            a: *a,
            attribute_index,
            r: *opening.as_ref(),
        },
        cm,
    ))
}

pub struct BlindRequest {
    cm: Commitment,
    cm_ks: Vec<Commitment>,
    bold_cm_k: Commitment,
    attribute_index: usize,
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
        let ak = Scalar::random(&mut rng);
        let (cm_k, o_k) = Commitment::commit(&ak);
        coms.push(cm_k);
        rks.push(&pp.pk * *o_k.as_ref());
    }

    // Step 9
    let pk_r = &pp.pk * strg.r;

    let mut base_points: Vec<_> = (1..=pp.tprime - 1)
        .map(|i| Scalar::from(i as u64))
        .collect();
    base_points.push(Scalar::from(pp.tprime as u64));
    let mut lagrange = Lagrange::new(&base_points);

    for k in pp.tprime..=pp.n {
        if k != pp.tprime {
            lagrange.update_point(pp.tprime - 1, Scalar::from(k as u64));
        }
        // SAFETY: this is always non-0
        let lk_i = lagrange.eval_j_0(pp.tprime - 1).invert().unwrap();

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
    let bold_k = Scalar::random(&mut rng);
    let (bold_cm_k, bold_cm_opening) = Commitment::commit(&bold_k);

    Ok((
        BlindRequest {
            cm: commitment.clone(),
            cm_ks: coms,
            attribute_index: strg.attribute_index,
            bold_cm_k,
        },
        Rand {
            strg: strg.clone(),
            r_ks: rks,
            bold_k,
            bold_rk: *bold_cm_opening.as_ref(),
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
            sigma: prv_j
                .sk
                .sign_pedersen_commitment(commitment, blind_request.attribute_index),
        })
        .collect())
}

pub struct Token {
    s: Signature,
    sks: Vec<Signature>,
}

impl Token {
    pub fn hash_prime(&self, pp: &PublicParameters) -> Vec<usize> {
        let mut hasher = sha3::Shake256::default();
        hasher.update(&self.s.sigma_1.as_serde_bytes());
        hasher.update(&self.s.sigma_2.as_serde_bytes());
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
        (&pp.pk.pk_1, &pp.pk.pk_2),
        (&pk_prime.pk_1, &pk_prime.pk_2),
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
    let mut errs = vec![];

    if blind_request
        .cm
        .verify_proof_2_pk(
            &blind_request.bold_cm_k,
            &pp.pk.pk_1,
            &pp.pk.pk_2,
            &token_proof.pk_prime.pk_1,
            &token_proof.pk_prime.pk_2,
            &token_proof.pi_zk,
        )
        .is_err()
    {
        errs.push(AtACTError::InvalidZKProof);
    }

    let sk_prod: Signature = (0..pp.tprime)
        .map(|k| &token_proof.ss[k] * pp.lagrange_tprime.eval_j_0(k))
        .sum();
    if pairing(token.s.sigma_1, token_proof.pk_prime.pk_2) != pairing(sk_prod.sigma_1, pp.pk.pk_2) {
        errs.push(AtACTError::InvalidToken);
    }
    if pairing(token_proof.pk_prime.pk_1, token.s.sigma_2) != pairing(pp.pk.pk_1, sk_prod.sigma_2) {
        errs.push(AtACTError::InvalidToken);
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
                    blind_request.attribute_index,
                    &sigma,
                )
                .is_err()
            {
                errs.push(AtACTError::InvalidSignature(k));
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
                errs.push(AtACTError::InvalidCommitmentProof(k));
            }
        }
    }

    if errs.is_empty() {
        Ok(())
    } else {
        Err(AtACTError::InvalidProof(errs))
    }
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
            .map(|_| Scalar::random(&mut rng))
            .collect();

        let (pp, issuers) = setup(NUM_ISSUERS, N, T, TPRIME, &attributes).expect("setup failed");

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
        const NUM_ATTRIBUTES: usize = 10;

        let attributes: Vec<_> = (0..NUM_ATTRIBUTES)
            .map(|x| Scalar::from(x as u64))
            .collect();

        for num_issuers in NUM_ISSUERS {
            for n in N {
                let t = num_issuers / 2 + 1;
                let tprime = n / 2 + 1;

                assert!(
                    setup(num_issuers, n, t, tprime, &attributes).is_ok(),
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
