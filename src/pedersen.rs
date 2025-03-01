use std::{
    iter::Sum,
    ops::{Add, Index, Mul, Sub},
    sync::OnceLock,
};

use ark_ff::{Field, UniformRand};
use ark_serialize::CanonicalSerialize;
use rand::{RngCore, SeedableRng};
// use sha3::{Digest, Sha3_512 as Hasher};
use sha2::{Digest, Sha256 as Hasher, digest::consts::U32};
use thiserror::Error;

use crate::bls381_helpers::{G1G2, Scalar, gs::CProof, hash_with_domain_separation};

pub struct PublicParameters {
    pub g: G1G2,
    pub u: G1G2,
}

impl PublicParameters {
    fn new() -> Self {
        Self {
            g: hash_with_domain_separation(b"g", b"Pedersen-PP"),
            u: hash_with_domain_separation(b"u", b"Pedersen-PP"),
        }
    }
}

pub fn get_parameters() -> &'static PublicParameters {
    static INSTANCE: OnceLock<PublicParameters> = OnceLock::new();
    INSTANCE.get_or_init(PublicParameters::new)
}

#[derive(Error, Debug, PartialEq, Eq, Clone)]
pub enum Error {
    #[error("Invalid opening for commitment.")]
    InvalidOpening,
    #[error("Invalid proof for commitment.")]
    InvalidProof,
}

pub struct MultiBasePublicParameters {
    us: Vec<G1G2>,
}

impl MultiBasePublicParameters {
    pub fn new(l: usize) -> Self {
        Self {
            us: (0..l)
                .map(|idx| {
                    hash_with_domain_separation(&(idx as u64).to_le_bytes(), b"Multi-Pedersen-PP")
                })
                .collect(),
        }
    }
}

impl Index<usize> for MultiBasePublicParameters {
    type Output = G1G2;

    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        &self.us[index]
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Commitment(pub(crate) G1G2);

pub struct Opening {
    pub(crate) r: Scalar,
}

pub struct Proof {
    t: G1G2,
    s_1: Scalar,
    s_2: Scalar,
}

pub struct ProofIndexCommit {
    t: G1G2,
    s_1: Scalar,
    s_2: Scalar,
    s_3: Scalar,
}

pub struct Proof2PK {
    pi_1: Proof,
    pi_2: Proof,
    t3: G1G2,
}

pub struct ProofMultiBase {
    pi_1: Proof,
    pi_2: ProofIndexCommit,
}

pub struct ProofMultiIndex {
    t: G1G2,
    s_1: Scalar,
    s_2: Scalar,
    pub(crate) s_i: Vec<(usize, Scalar)>,
    t_prf: G1G2,
    s_prf: Scalar,
}

#[inline]
fn hash_g1g2<D>(hasher: &mut D, g12: &G1G2)
where
    D: Digest,
{
    let mut storage = Vec::new();
    g12.serialize_uncompressed(&mut storage).unwrap();
    hasher.update(storage);
}

#[inline]
fn hash_commitment<D>(hasher: &mut D, commitment: &Commitment)
where
    D: Digest,
{
    hash_g1g2(hasher, &commitment.0);
}

#[inline]
fn hash_base<D>(hasher: &mut D)
where
    D: Digest,
{
    let pp = get_parameters();

    hash_g1g2(hasher, &pp.g);
    hash_g1g2(hasher, &pp.u);
}

fn hash_gs<D>(hasher: &mut D, proof: &CProof)
where
    D: Digest,
{
    let mut storage = Vec::new();
    proof.xcoms.coms.iter().for_each(|com| {
        com.serialize_uncompressed(&mut storage).unwrap();
        hasher.update(&storage);
        storage.clear();
    });
    proof.ycoms.coms.iter().for_each(|com| {
        com.serialize_uncompressed(&mut storage).unwrap();
        hasher.update(&storage);
        storage.clear();
    });
    proof.equ_proofs.iter().for_each(|prf| {
        prf.pi.iter().for_each(|com| {
            com.serialize_uncompressed(&mut storage).unwrap();
            hasher.update(&storage);
            storage.clear();
        });
        prf.theta.iter().for_each(|com| {
            com.serialize_uncompressed(&mut storage).unwrap();
            hasher.update(&storage);
            storage.clear();
        });
    });
}

#[inline]
fn hash_extract_scalar<D>(hasher: D) -> Scalar
where
    D: Digest<OutputSize = U32>,
{
    // FIXME!
    let digest = hasher.finalize();

    let mut rng = rand_chacha::ChaCha20Rng::from_seed(digest.into());
    loop {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        if let Some(scalar) = Scalar::from_random_bytes(&bytes) {
            return scalar;
        }
    }
}

fn hash_context() -> Hasher {
    static INSTANCE: OnceLock<Hasher> = OnceLock::new();
    INSTANCE
        .get_or_init(|| {
            let mut hasher = Hasher::new();
            hasher.update(b"hash-pedersen-proof");
            hash_base(&mut hasher);
            hasher
        })
        .clone()
}

fn hash_pedersen_proof(commitment: &Commitment, t: &G1G2) -> Scalar {
    let mut hasher = hash_context();
    hash_commitment(&mut hasher, commitment);
    hash_g1g2(&mut hasher, t);
    hash_extract_scalar(hasher)
}

impl Commitment {
    pub fn commit(message: &Scalar) -> (Self, Opening) {
        Self::commit_with_randomness(message, &Scalar::rand(&mut rand::thread_rng()))
    }

    pub fn commit_with_randomness(message: &Scalar, r: &Scalar) -> (Self, Opening) {
        let pp = get_parameters();
        (Self(&pp.g * *r + &pp.u * *message), Opening { r: *r })
    }

    pub fn verify(&self, message: &Scalar, opening: &Opening) -> Result<(), Error> {
        let pp = get_parameters();
        if &pp.g * opening.r + &pp.u * *message == self.0 {
            Ok(())
        } else {
            Err(Error::InvalidOpening)
        }
    }

    pub fn proof(&self, message: &Scalar, opening: &Opening) -> Proof {
        let mut rng = rand::thread_rng();
        let pp = get_parameters();

        let r_1 = Scalar::rand(&mut rng);
        let r_2 = Scalar::rand(&mut rng);
        let t = &pp.g * r_1 + &pp.u * r_2;

        let c = hash_pedersen_proof(self, &t);
        let s_1 = r_1 + opening.r * c;
        let s_2 = r_2 + *message * c;

        Proof { t, s_1, s_2 }
    }

    fn verify_proof_with_challenge(&self, c: &Scalar, proof: &Proof) -> Result<(), Error> {
        let pp = get_parameters();
        if &pp.g * proof.s_1 + &pp.u * proof.s_2 != &self.0 * *c + &proof.t {
            return Err(Error::InvalidProof);
        }
        Ok(())
    }

    pub fn verify_proof(&self, proof: &Proof) -> Result<(), Error> {
        let c = hash_pedersen_proof(self, &proof.t);
        self.verify_proof_with_challenge(&c, proof)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn proof_2_pk(
        &self,
        message: &Scalar,
        opening: &Opening,
        commitment_2: &Self,
        message_2: &Scalar,
        opening_2: &Opening,
        base: &G1G2,
        pk: &G1G2,
    ) -> Proof2PK {
        let pp = get_parameters();
        let mut rng = rand::thread_rng();

        let r1_1 = Scalar::rand(&mut rng);
        let r1_2 = Scalar::rand(&mut rng);
        let t1 = &pp.g * r1_1 + &pp.u * r1_2;

        let r2_1 = Scalar::rand(&mut rng);
        let r2_2 = Scalar::rand(&mut rng);
        let t2 = &pp.g * r2_1 + &pp.u * r2_2;

        let t3 = base * r2_2;

        let mut hasher = hash_context();
        hash_g1g2(&mut hasher, base);
        hash_commitment(&mut hasher, self);
        hash_commitment(&mut hasher, commitment_2);
        hash_g1g2(&mut hasher, pk);
        hash_g1g2(&mut hasher, &t1);
        hash_g1g2(&mut hasher, &t2);
        hash_g1g2(&mut hasher, &t3);
        let c = hash_extract_scalar(hasher);

        let s1_1 = r1_1 + opening.r * c;
        let s1_2 = r1_2 + *message * c;
        let s2_1 = r2_1 + opening_2.r * c;
        let s2_2 = r2_2 + *message_2 * c;

        Proof2PK {
            pi_1: Proof {
                t: t1,
                s_1: s1_1,
                s_2: s1_2,
            },
            pi_2: Proof {
                t: t2,
                s_1: s2_1,
                s_2: s2_2,
            },
            t3,
        }
    }

    pub fn verify_proof_2_pk(
        &self,
        commitment_2: &Self,
        base: &G1G2,
        pk: &G1G2,
        proof: &Proof2PK,
    ) -> Result<(), Error> {
        let mut hasher = hash_context();
        hash_g1g2(&mut hasher, base);
        hash_commitment(&mut hasher, self);
        hash_commitment(&mut hasher, commitment_2);
        hash_g1g2(&mut hasher, pk);
        hash_g1g2(&mut hasher, &proof.pi_1.t);
        hash_g1g2(&mut hasher, &proof.pi_2.t);
        hash_g1g2(&mut hasher, &proof.t3);
        let c = hash_extract_scalar(hasher);

        self.verify_proof_with_challenge(&c, &proof.pi_1)?;
        commitment_2.verify_proof_with_challenge(&c, &proof.pi_2)?;

        if base * proof.pi_2.s_2 == pk * c + &proof.t3 {
            Ok(())
        } else {
            Err(Error::InvalidProof)
        }
    }

    pub fn index_commit(
        value_0: &Scalar,
        idx: usize,
        value_i: &Scalar,
        multi_pp: &MultiBasePublicParameters,
    ) -> (Self, Opening) {
        debug_assert!(idx < multi_pp.us.len());

        let r = Scalar::rand(&mut rand::thread_rng());
        let pp = get_parameters();
        (
            Self(&pp.g * r + &pp.u * *value_0 + &multi_pp[idx] * *value_i),
            Opening { r },
        )
    }

    pub fn verify_index_commit(
        &self,
        value_0: &Scalar,
        idx: usize,
        value_i: &Scalar,
        opening: &Opening,
        multi_pp: &MultiBasePublicParameters,
    ) -> Result<(), Error> {
        debug_assert!(idx < multi_pp.us.len());

        let pp = get_parameters();
        if self.0 == &pp.g * opening.r + &pp.u * *value_0 + &multi_pp[idx] * *value_i {
            Ok(())
        } else {
            Err(Error::InvalidOpening)
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn proof_index_commit(
        &self,
        message: &Scalar,
        opening: &Opening,
        commitment_2: &Self,
        value_0: &Scalar,
        idx: usize,
        value_i: &Scalar,
        opening_2: &Opening,
        multi_pp: &MultiBasePublicParameters,
    ) -> ProofMultiBase {
        let pp = get_parameters();
        let mut rng = rand::thread_rng();

        let r1_1 = Scalar::rand(&mut rng);
        let r1_2 = Scalar::rand(&mut rng);
        let t1 = &pp.g * r1_1 + &pp.u * r1_2;

        let r2_1 = Scalar::rand(&mut rng);
        let r2_2 = Scalar::rand(&mut rng);
        let r2_3 = Scalar::rand(&mut rng);
        let t2 = &pp.g * r2_1 + &pp.u * r2_2 + &multi_pp[idx] * r2_3;

        let mut hasher = hash_context();
        hash_g1g2(&mut hasher, &multi_pp[idx]);
        hash_commitment(&mut hasher, self);
        hash_commitment(&mut hasher, commitment_2);
        hash_g1g2(&mut hasher, &t1);
        hash_g1g2(&mut hasher, &t2);
        let c = hash_extract_scalar(hasher);

        let s1_1 = r1_1 + opening.r * c;
        let s1_2 = r1_2 + *message * c;
        let s2_1 = r2_1 + opening_2.r * c;
        let s2_2 = r2_2 + *value_0 * c;
        let s2_3 = r2_3 + *value_i * c;

        ProofMultiBase {
            pi_1: Proof {
                t: t1,
                s_1: s1_1,
                s_2: s1_2,
            },
            pi_2: ProofIndexCommit {
                t: t2,
                s_1: s2_1,
                s_2: s2_2,
                s_3: s2_3,
            },
        }
    }

    pub fn verify_proof_index_commit(
        &self,
        commitment_2: &Self,
        idx: usize,
        proof: &ProofMultiBase,
        multi_pp: &MultiBasePublicParameters,
    ) -> Result<(), Error> {
        let pp = get_parameters();
        let mut hasher = hash_context();
        hash_g1g2(&mut hasher, &multi_pp[idx]);
        hash_commitment(&mut hasher, self);
        hash_commitment(&mut hasher, commitment_2);
        hash_g1g2(&mut hasher, &proof.pi_1.t);
        hash_g1g2(&mut hasher, &proof.pi_2.t);
        let c = hash_extract_scalar(hasher);

        self.verify_proof_with_challenge(&c, &proof.pi_1)?;

        if &pp.g * proof.pi_2.s_1 + &pp.u * proof.pi_2.s_2 + &multi_pp[idx] * proof.pi_2.s_3
            == &commitment_2.0 * c + &proof.pi_2.t
        {
            Ok(())
        } else {
            Err(Error::InvalidProof)
        }
    }

    pub fn multi_index_commit<I>(
        value_0: &Scalar,
        iter: I,
        multi_pp: &MultiBasePublicParameters,
    ) -> (Self, Opening)
    where
        I: Iterator<Item = (usize, Scalar)> + ExactSizeIterator,
    {
        let len = Scalar::from(iter.len() as u64);
        let pp = get_parameters();
        let r = Scalar::rand(&mut rand::thread_rng());
        let cm = iter.fold(
            &pp.g * r + &pp.u * (*value_0 * len),
            |cm, (idx, value_i)| {
                debug_assert!(idx < multi_pp.us.len());
                cm + &multi_pp[idx] * value_i
            },
        );

        (Self(cm), Opening { r })
    }

    pub fn verify_multi_index_commit<I>(
        &self,
        value_0: &Scalar,
        iter: I,
        opening: &Opening,
        multi_pp: &MultiBasePublicParameters,
    ) -> Result<(), Error>
    where
        I: Iterator<Item = (usize, Scalar)> + ExactSizeIterator,
    {
        let len = Scalar::from(iter.len() as u64);
        let pp = get_parameters();
        let cm = iter.fold(
            &pp.g * opening.r + &pp.u * (*value_0 * len),
            |cm, (idx, value_i)| {
                debug_assert!(idx < multi_pp.us.len());
                cm + &multi_pp[idx] * value_i
            },
        );

        if self.0 == cm {
            Ok(())
        } else {
            Err(Error::InvalidOpening)
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn proof_multi_index_commit<I>(
        &self,
        value_0: &Scalar,
        iter: I,
        opening: &Opening,
        prf_base: &G1G2,
        prf: &G1G2,
        gs_proof: Option<&CProof>,
        multi_pp: &MultiBasePublicParameters,
    ) -> ProofMultiIndex
    where
        I: Iterator<Item = (usize, Scalar)> + ExactSizeIterator,
    {
        let len = Scalar::from(iter.len() as u64);

        let pp = get_parameters();
        let randoms_and_values = Vec::with_capacity(iter.len());
        let mut rng = rand::thread_rng();
        let r1 = Scalar::rand(&mut rng);
        let r2 = Scalar::rand(&mut rng);
        let r_prf = Scalar::rand(&mut rng);
        let mut hasher = hash_context();

        let t_prf = prf_base * r_prf;

        let (t, randoms_and_values) = iter.fold(
            (&pp.g * r1 + &pp.u * (r2 * len), randoms_and_values),
            |(t, mut randoms_and_values), (idx, value_i)| {
                let random = Scalar::rand(&mut rng);
                randoms_and_values.push((idx, random, value_i));
                hash_g1g2(&mut hasher, &multi_pp[idx]);
                (t + &multi_pp[idx] * random, randoms_and_values)
            },
        );
        hash_g1g2(&mut hasher, prf_base);
        hash_commitment(&mut hasher, self);
        hash_g1g2(&mut hasher, prf);
        hash_g1g2(&mut hasher, &t);
        hash_g1g2(&mut hasher, &t_prf);
        if let Some(gs) = gs_proof {
            hash_gs(&mut hasher, gs);
        }
        let c = hash_extract_scalar(hasher);

        let s_1 = r1 + opening.r * c;
        let s_2 = r2 + *value_0 * c;
        let s_prf = r_prf + *value_0 * c;

        ProofMultiIndex {
            t,
            s_1,
            s_2,
            s_i: randoms_and_values
                .into_iter()
                .map(|(idx, r_i, value_i)| (idx, r_i + value_i * c))
                .collect(),
            t_prf,
            s_prf,
        }
    }

    pub fn verify_proof_multi_index_commit(
        &self,
        pk: &G1G2,
        pk_prime: &G1G2,
        gs_proof: Option<&CProof>,
        proof: &ProofMultiIndex,
        multi_pp: &MultiBasePublicParameters,
    ) -> Result<(), Error> {
        let len = Scalar::from(proof.s_i.len() as u64);

        let mut hasher = hash_context();
        let pp = get_parameters();

        let check_1 = proof.s_i.iter().fold(
            &pp.g * proof.s_1 + &pp.u * (proof.s_2 * len),
            |c, (idx, s_i)| {
                hash_g1g2(&mut hasher, &multi_pp[*idx]);
                c + &multi_pp[*idx] * *s_i
            },
        );

        hash_g1g2(&mut hasher, pk);
        hash_commitment(&mut hasher, self);
        hash_g1g2(&mut hasher, pk_prime);
        hash_g1g2(&mut hasher, &proof.t);
        hash_g1g2(&mut hasher, &proof.t_prf);
        if let Some(gs) = gs_proof {
            hash_gs(&mut hasher, gs);
        }
        let c = hash_extract_scalar(hasher);

        if check_1 == &self.0 * c + &proof.t && pk * proof.s_prf == pk_prime * c + &proof.t_prf {
            Ok(())
        } else {
            Err(Error::InvalidProof)
        }
    }
}

impl Sub for &Commitment {
    type Output = Commitment;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Commitment(&self.0 - &rhs.0)
    }
}

impl Sub<&Self> for Commitment {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: &Self) -> Self::Output {
        Self(&self.0 - &rhs.0)
    }
}

impl Add for &Commitment {
    type Output = Commitment;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Commitment(&self.0 + &rhs.0)
    }
}

impl Add<&Self> for Commitment {
    type Output = Self;

    fn add(self, rhs: &Self) -> Self::Output {
        Self(self.0 + &rhs.0)
    }
}

impl Sum for Commitment {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self(iter.map(|cm| cm.0).sum())
    }
}

impl<'a> Sum<&'a Self> for Commitment {
    #[inline]
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        Self(iter.map(|cm| &cm.0).sum())
    }
}

impl Mul<Scalar> for Commitment {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Scalar) -> Self::Output {
        Self(self.0 * rhs)
    }
}

impl Mul<Scalar> for &Commitment {
    type Output = Commitment;

    #[inline]
    fn mul(self, rhs: Scalar) -> Self::Output {
        Commitment(&self.0 * rhs)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn pedersen() {
        let msg = Scalar::rand(&mut rand::thread_rng());
        let (cm, o) = Commitment::commit(&msg);
        assert!(cm.verify(&msg, &o).is_ok());
    }

    #[test]
    fn pedersen_proof() {
        let msg = Scalar::rand(&mut rand::thread_rng());
        let (cm, o) = Commitment::commit(&msg);
        assert!(cm.verify(&msg, &o).is_ok());

        let proof = cm.proof(&msg, &o);
        assert!(cm.verify_proof(&proof).is_ok());
    }

    #[test]
    fn pedersen_proof_2_pk() {
        let mut rng = rand::thread_rng();
        let pp = get_parameters();
        let msg_1 = Scalar::rand(&mut rng);
        let (cm_1, o_1) = Commitment::commit(&msg_1);
        assert!(cm_1.verify(&msg_1, &o_1).is_ok());
        let msg_2 = Scalar::rand(&mut rng);
        let (cm_2, o_2) = Commitment::commit(&msg_2);
        assert!(cm_2.verify(&msg_2, &o_2).is_ok());

        let o_3 = msg_2;
        let pk = &pp.g * o_3;

        let proof = cm_1.proof_2_pk(&msg_1, &o_1, &cm_2, &msg_2, &o_2, &pp.g, &pk);
        assert!(cm_1.verify_proof_2_pk(&cm_2, &pp.g, &pk, &proof).is_ok());
    }

    #[test]
    fn multi_pedersen() {
        let mut rng = rand::thread_rng();
        let l = 10;
        let pp = MultiBasePublicParameters::new(l);

        let value_0 = Scalar::rand(&mut rng);
        for idx in 0..l {
            let value_i = Scalar::rand(&mut rng);
            let (cm, o) = Commitment::index_commit(&value_0, idx, &value_i, &pp);
            assert!(
                cm.verify_index_commit(&value_0, idx, &value_i, &o, &pp)
                    .is_ok()
            );
        }
    }

    #[test]
    fn multi_pedersen_proof() {
        let mut rng = rand::thread_rng();
        let msg = Scalar::rand(&mut rng);
        let (commitment, opening) = Commitment::commit(&msg);

        let l = 10;
        let pp = MultiBasePublicParameters::new(l);

        let value_0 = Scalar::rand(&mut rng);
        for idx in 0..l {
            let value_i = Scalar::rand(&mut rng);
            let (cm, o) = Commitment::index_commit(&value_0, idx, &value_i, &pp);
            assert!(
                cm.verify_index_commit(&value_0, idx, &value_i, &o, &pp)
                    .is_ok()
            );

            let proof = commitment
                .proof_index_commit(&msg, &opening, &cm, &value_0, idx, &value_i, &o, &pp);
            assert!(
                commitment
                    .verify_proof_index_commit(&cm, idx, &proof, &pp)
                    .is_ok()
            );
        }
    }

    #[test]
    fn multi_index_pedersen() {
        let mut rng = rand::thread_rng();
        let l = 10;
        let pp = MultiBasePublicParameters::new(l);

        let value_0 = Scalar::rand(&mut rng);
        let values = [
            (2usize, Scalar::rand(&mut rng)),
            (7usize, Scalar::rand(&mut rng)),
        ];
        let (cm, o) = Commitment::multi_index_commit(&value_0, values.iter().copied(), &pp);
        assert!(
            cm.verify_multi_index_commit(&value_0, values.iter().copied(), &o, &pp)
                .is_ok()
        );
    }

    #[test]
    fn multi_index_pedersen_proof() {
        let mut rng = rand::thread_rng();
        let l = 10;
        let pp = MultiBasePublicParameters::new(l);

        let value_0 = Scalar::rand(&mut rng);
        let values = [
            (2usize, Scalar::rand(&mut rng)),
            (7usize, Scalar::rand(&mut rng)),
        ];
        let (cm, o) = Commitment::multi_index_commit(&value_0, values.iter().copied(), &pp);
        assert!(
            cm.verify_multi_index_commit(&value_0, values.iter().copied(), &o, &pp)
                .is_ok()
        );

        let prf_base = hash_with_domain_separation(b"msg", b"prf");
        let prf = prf_base.clone() * value_0;

        let proof = cm.proof_multi_index_commit(
            &value_0,
            values.iter().copied(),
            &o,
            &prf_base,
            &prf,
            None,
            &pp,
        );
        assert!(
            cm.verify_proof_multi_index_commit(&prf_base, &prf, None, &proof, &pp)
                .is_ok()
        );
    }
}
