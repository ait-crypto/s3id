use std::{
    iter::Sum,
    ops::{Add, Mul, Sub},
    sync::OnceLock,
};

use bls12_381::{G1Projective, G2Projective, Scalar};
use group::ff::Field;
// use sha3::{Digest, Sha3_512 as Hasher};
use sha2::{Digest, Sha512 as Hasher};
use thiserror::Error;

use crate::bls381_helpers::{
    hash_with_domain_separation_1, hash_with_domain_separation_2, ByteConverter,
};

pub struct PublicParameters {
    pub g: G1Projective,
    pub u: G1Projective,
    pub ghat: G2Projective,
    pub uhat: G2Projective,
}

impl PublicParameters {
    fn new() -> Self {
        Self {
            g: hash_with_domain_separation_1(b"g", b"Pedersen-PP"),
            ghat: hash_with_domain_separation_2(b"g", b"Pedersen-PP"),
            u: hash_with_domain_separation_1(b"u", b"Pedersen-PP"),
            uhat: hash_with_domain_separation_2(b"u", b"Pedersen-PP"),
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
    us: Vec<G1Projective>,
    uhats: Vec<G2Projective>,
}

impl MultiBasePublicParameters {
    pub fn new(l: usize) -> Self {
        let us = (0..l).map(|idx| {
            hash_with_domain_separation_1(&(idx as u64).to_le_bytes(), b"Multi-Pedersen-PP")
        });
        let uhats = (0..l).map(|idx| {
            hash_with_domain_separation_2(&(idx as u64).to_le_bytes(), b"Multi-Pedersen-PP")
        });

        Self {
            us: us.collect(),
            uhats: uhats.collect(),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Commitment {
    pub(crate) cm_1: G1Projective,
    pub(crate) cm_2: G2Projective,
}

pub struct Opening {
    r: Scalar,
}

impl From<&Scalar> for Opening {
    fn from(value: &Scalar) -> Self {
        Self { r: *value }
    }
}

impl From<Scalar> for Opening {
    fn from(r: Scalar) -> Self {
        Self { r }
    }
}

impl AsRef<Scalar> for Opening {
    fn as_ref(&self) -> &Scalar {
        &self.r
    }
}

pub struct Proof {
    t_1: G1Projective,
    t_2: G2Projective,
    s_1: Scalar,
    s_2: Scalar,
}

pub struct ProofIndexCommit {
    t_1: G1Projective,
    t_2: G2Projective,
    s_1: Scalar,
    s_2: Scalar,
    s_3: Scalar,
}

pub struct Proof2PK {
    pi_1: Proof,
    pi_2: Proof,
    t3_1: G1Projective,
    t3_2: G2Projective,
}

pub struct ProofMultiBase {
    pi_1: Proof,
    pi_2: ProofIndexCommit,
}

pub struct ProofMultiIndex {
    t_1: G1Projective,
    t_2: G2Projective,
    s_1: Scalar,
    s_2: Scalar,
    pub s_i: Vec<(usize, Scalar)>,
}

#[inline]
fn hash_g1<D>(hasher: &mut D, g1: &G1Projective)
where
    D: Digest,
{
    hasher.update(g1.as_serde_bytes());
}

#[inline]
fn hash_g2<D>(hasher: &mut D, g2: &G2Projective)
where
    D: Digest,
{
    hasher.update(g2.as_serde_bytes());
}

#[inline]
fn hash_commitment<D>(hasher: &mut D, commitment: &Commitment)
where
    D: Digest,
{
    hash_g1(hasher, &commitment.cm_1);
    hash_g2(hasher, &commitment.cm_2);
}

#[inline]
fn hash_base<D>(hasher: &mut D)
where
    D: Digest,
{
    let pp = get_parameters();

    hash_g1(hasher, &pp.g);
    hash_g1(hasher, &pp.u);
    hash_g2(hasher, &pp.ghat);
    hash_g2(hasher, &pp.uhat);
}

#[inline]
fn hash_extract_scalar<D>(hasher: D) -> Scalar
where
    D: Digest,
{
    let digest = hasher.finalize();
    Scalar::from_bytes_wide(&digest.as_slice().try_into().unwrap())
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

fn hash_pedersen_proof(commitment: &Commitment, t_1: &G1Projective, t_2: &G2Projective) -> Scalar {
    let mut hasher = hash_context();
    hash_commitment(&mut hasher, commitment);
    hash_g1(&mut hasher, t_1);
    hash_g2(&mut hasher, t_2);
    hash_extract_scalar(hasher)
}

impl Commitment {
    pub fn commit(message: &Scalar) -> (Commitment, Opening) {
        Self::commit_with_randomness(message, &Scalar::random(rand::thread_rng()))
    }

    pub fn commit_with_randomness(message: &Scalar, r: &Scalar) -> (Commitment, Opening) {
        let pp = get_parameters();
        (
            Commitment {
                cm_1: pp.g * r + pp.u * message,
                cm_2: pp.ghat * r + pp.uhat * message,
            },
            Opening { r: *r },
        )
    }

    pub fn verify(&self, message: &Scalar, opening: &Opening) -> Result<(), Error> {
        let pp = get_parameters();
        match (
            pp.g * opening.r + pp.u * message == self.cm_1,
            pp.ghat * opening.r + pp.uhat * message == self.cm_2,
        ) {
            (true, true) => Ok(()),
            _ => Err(Error::InvalidOpening),
        }
    }

    pub fn proof(&self, message: &Scalar, opening: &Opening) -> Proof {
        let mut rng = rand::thread_rng();
        let pp = get_parameters();

        let r_1 = Scalar::random(&mut rng);
        let r_2 = Scalar::random(&mut rng);
        let t_1 = pp.g * r_1 + pp.u * r_2;
        let t_2 = pp.ghat * r_1 + pp.uhat * r_2;

        let c = hash_pedersen_proof(self, &t_1, &t_2);
        let s_1 = r_1 + opening.r * c;
        let s_2 = r_2 + message * c;

        Proof { t_1, t_2, s_1, s_2 }
    }

    fn verify_proof_with_challenge(&self, c: &Scalar, proof: &Proof) -> Result<(), Error> {
        let pp = get_parameters();
        if pp.g * proof.s_1 + pp.u * proof.s_2 != proof.t_1 + self.cm_1 * c {
            return Err(Error::InvalidProof);
        }
        if pp.ghat * proof.s_1 + pp.uhat * proof.s_2 != proof.t_2 + self.cm_2 * c {
            return Err(Error::InvalidProof);
        }
        Ok(())
    }

    pub fn verify_proof(&self, proof: &Proof) -> Result<(), Error> {
        let c = hash_pedersen_proof(self, &proof.t_1, &proof.t_2);
        self.verify_proof_with_challenge(&c, proof)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn proof_2_pk(
        &self,
        message: &Scalar,
        opening: &Opening,
        commitment_2: &Commitment,
        message_2: &Scalar,
        opening_2: &Opening,
        (base_1, base_2): (&G1Projective, &G2Projective),
        (pk_1, pk_2): (&G1Projective, &G2Projective),
    ) -> Proof2PK {
        let pp = get_parameters();
        let mut rng = rand::thread_rng();

        let r1_1 = Scalar::random(&mut rng);
        let r1_2 = Scalar::random(&mut rng);
        let t1_1 = pp.g * r1_1 + pp.u * r1_2;
        let t1_2 = pp.ghat * r1_1 + pp.uhat * r1_2;

        let r2_1 = Scalar::random(&mut rng);
        let r2_2 = Scalar::random(&mut rng);
        let t2_1 = pp.g * r2_1 + pp.u * r2_2;
        let t2_2 = pp.ghat * r2_1 + pp.uhat * r2_2;

        let t3_1 = base_1 * r2_2;
        let t3_2 = base_2 * r2_2;

        let mut hasher = hash_context();
        hash_g1(&mut hasher, base_1);
        hash_g2(&mut hasher, base_2);
        hash_commitment(&mut hasher, self);
        hash_commitment(&mut hasher, commitment_2);
        hash_g1(&mut hasher, pk_1);
        hash_g2(&mut hasher, pk_2);
        hash_g1(&mut hasher, &t1_1);
        hash_g2(&mut hasher, &t1_2);
        hash_g1(&mut hasher, &t2_1);
        hash_g2(&mut hasher, &t2_2);
        hash_g1(&mut hasher, &t3_1);
        hash_g2(&mut hasher, &t3_2);
        let c = hash_extract_scalar(hasher);

        let s1_1 = r1_1 + opening.r * c;
        let s1_2 = r1_2 + message * c;
        let s2_1 = r2_1 + opening_2.r * c;
        let s2_2 = r2_2 + message_2 * c;

        Proof2PK {
            pi_1: Proof {
                t_1: t1_1,
                t_2: t1_2,
                s_1: s1_1,
                s_2: s1_2,
            },
            pi_2: Proof {
                t_1: t2_1,
                t_2: t2_2,
                s_1: s2_1,
                s_2: s2_2,
            },
            t3_1,
            t3_2,
        }
    }

    pub fn verify_proof_2_pk(
        &self,
        commitment_2: &Commitment,
        base_1: &G1Projective,
        base_2: &G2Projective,
        pk_1: &G1Projective,
        pk_2: &G2Projective,
        proof: &Proof2PK,
    ) -> Result<(), Error> {
        let mut hasher = hash_context();
        hash_g1(&mut hasher, base_1);
        hash_g2(&mut hasher, base_2);
        hash_commitment(&mut hasher, self);
        hash_commitment(&mut hasher, commitment_2);
        hash_g1(&mut hasher, pk_1);
        hash_g2(&mut hasher, pk_2);
        hash_g1(&mut hasher, &proof.pi_1.t_1);
        hash_g2(&mut hasher, &proof.pi_1.t_2);
        hash_g1(&mut hasher, &proof.pi_2.t_1);
        hash_g2(&mut hasher, &proof.pi_2.t_2);
        hash_g1(&mut hasher, &proof.t3_1);
        hash_g2(&mut hasher, &proof.t3_2);
        let c = hash_extract_scalar(hasher);

        self.verify_proof_with_challenge(&c, &proof.pi_1)?;
        commitment_2.verify_proof_with_challenge(&c, &proof.pi_2)?;

        if base_1 * proof.pi_2.s_2 != proof.t3_1 + pk_1 * c
            || base_2 * proof.pi_2.s_2 != proof.t3_2 + pk_2 * c
        {
            Err(Error::InvalidProof)
        } else {
            Ok(())
        }
    }

    pub fn index_commit(
        value_0: &Scalar,
        idx: usize,
        value_i: &Scalar,
        multi_pp: &MultiBasePublicParameters,
    ) -> (Commitment, Opening) {
        debug_assert!(idx < multi_pp.us.len());

        let r = Scalar::random(rand::thread_rng());
        let pp = get_parameters();
        (
            Commitment {
                cm_1: pp.g * r + pp.u * value_0 + multi_pp.us[idx] * value_i,
                cm_2: pp.ghat * r + pp.uhat * value_0 + multi_pp.uhats[idx] * value_i,
            },
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
        match (
            self.cm_1 == pp.g * opening.r + pp.u * value_0 + multi_pp.us[idx] * value_i,
            self.cm_2 == pp.ghat * opening.r + pp.uhat * value_0 + multi_pp.uhats[idx] * value_i,
        ) {
            (true, true) => Ok(()),
            _ => Err(Error::InvalidOpening),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn proof_index_commit(
        &self,
        message: &Scalar,
        opening: &Opening,
        commitment_2: &Commitment,
        value_0: &Scalar,
        idx: usize,
        value_i: &Scalar,
        opening_2: &Opening,
        multi_pp: &MultiBasePublicParameters,
    ) -> ProofMultiBase {
        let pp = get_parameters();
        let mut rng = rand::thread_rng();

        let r1_1 = Scalar::random(&mut rng);
        let r1_2 = Scalar::random(&mut rng);
        let t1_1 = pp.g * r1_1 + pp.u * r1_2;
        let t1_2 = pp.ghat * r1_1 + pp.uhat * r1_2;

        let r2_1 = Scalar::random(&mut rng);
        let r2_2 = Scalar::random(&mut rng);
        let r2_3 = Scalar::random(&mut rng);
        let t2_1 = pp.g * r2_1 + pp.u * r2_2 + multi_pp.us[idx] * r2_3;
        let t2_2 = pp.ghat * r2_1 + pp.uhat * r2_2 + multi_pp.uhats[idx] * r2_3;

        let mut hasher = hash_context();
        hash_g1(&mut hasher, &multi_pp.us[idx]);
        hash_g2(&mut hasher, &multi_pp.uhats[idx]);
        hash_commitment(&mut hasher, self);
        hash_commitment(&mut hasher, commitment_2);
        hash_g1(&mut hasher, &t1_1);
        hash_g2(&mut hasher, &t1_2);
        hash_g1(&mut hasher, &t2_1);
        hash_g2(&mut hasher, &t2_2);
        let c = hash_extract_scalar(hasher);

        let s1_1 = r1_1 + opening.r * c;
        let s1_2 = r1_2 + message * c;
        let s2_1 = r2_1 + opening_2.r * c;
        let s2_2 = r2_2 + value_0 * c;
        let s2_3 = r2_3 + value_i * c;

        ProofMultiBase {
            pi_1: Proof {
                t_1: t1_1,
                t_2: t1_2,
                s_1: s1_1,
                s_2: s1_2,
            },
            pi_2: ProofIndexCommit {
                t_1: t2_1,
                t_2: t2_2,
                s_1: s2_1,
                s_2: s2_2,
                s_3: s2_3,
            },
        }
    }

    pub fn verify_proof_index_commit(
        &self,
        commitment_2: &Commitment,
        idx: usize,
        proof: &ProofMultiBase,
        multi_pp: &MultiBasePublicParameters,
    ) -> Result<(), Error> {
        let pp = get_parameters();
        let mut hasher = hash_context();
        hash_g1(&mut hasher, &multi_pp.us[idx]);
        hash_g2(&mut hasher, &multi_pp.uhats[idx]);
        hash_commitment(&mut hasher, self);
        hash_commitment(&mut hasher, commitment_2);
        hash_g1(&mut hasher, &proof.pi_1.t_1);
        hash_g2(&mut hasher, &proof.pi_1.t_2);
        hash_g1(&mut hasher, &proof.pi_2.t_1);
        hash_g2(&mut hasher, &proof.pi_2.t_2);
        let c = hash_extract_scalar(hasher);

        self.verify_proof_with_challenge(&c, &proof.pi_1)?;

        if pp.g * proof.pi_2.s_1 + pp.u * proof.pi_2.s_2 + multi_pp.us[idx] * proof.pi_2.s_3
            != proof.pi_2.t_1 + commitment_2.cm_1 * c
            || pp.ghat * proof.pi_2.s_1
                + pp.uhat * proof.pi_2.s_2
                + multi_pp.uhats[idx] * proof.pi_2.s_3
                != proof.pi_2.t_2 + commitment_2.cm_2 * c
        {
            Err(Error::InvalidProof)
        } else {
            Ok(())
        }
    }

    pub fn multi_index_commit<I>(
        value_0: &Scalar,
        iter: I,
        multi_pp: &MultiBasePublicParameters,
    ) -> (Commitment, Opening)
    where
        I: Iterator<Item = (usize, Scalar)>,
    {
        let pp = get_parameters();
        let r = Scalar::random(rand::thread_rng());
        let (cm_1, cm_2) = iter.fold(
            (pp.g * r + pp.u * value_0, pp.ghat * r + pp.uhat * value_0),
            |(cm_1, cm_2), (idx, value_i)| {
                debug_assert!(idx < multi_pp.us.len());
                (
                    cm_1 + multi_pp.us[idx] * value_i,
                    cm_2 + multi_pp.uhats[idx] * value_i,
                )
            },
        );

        (Commitment { cm_1, cm_2 }, Opening { r })
    }

    pub fn verify_multi_index_commit<I>(
        &self,
        value_0: &Scalar,
        iter: I,
        opening: &Opening,
        multi_pp: &MultiBasePublicParameters,
    ) -> Result<(), Error>
    where
        I: Iterator<Item = (usize, Scalar)>,
    {
        let pp = get_parameters();
        let (cm_1, cm_2) = iter.fold(
            (
                pp.g * opening.r + pp.u * value_0,
                pp.ghat * opening.r + pp.uhat * value_0,
            ),
            |(cm_1, cm_2), (idx, value_i)| {
                debug_assert!(idx < multi_pp.us.len());
                (
                    cm_1 + multi_pp.us[idx] * value_i,
                    cm_2 + multi_pp.uhats[idx] * value_i,
                )
            },
        );

        match (self.cm_1 == cm_1, self.cm_2 == cm_2) {
            (true, true) => Ok(()),
            _ => Err(Error::InvalidOpening),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn proof_multi_index_commit<I>(
        &self,
        value_0: &Scalar,
        iter: I,
        opening: &Opening,
        multi_pp: &MultiBasePublicParameters,
    ) -> ProofMultiIndex
    where
        I: Iterator<Item = (usize, Scalar)> + ExactSizeIterator,
    {
        let pp = get_parameters();
        let randoms_and_values = Vec::with_capacity(iter.len());
        let mut rng = rand::thread_rng();
        let r1 = Scalar::random(&mut rng);
        let r2 = Scalar::random(&mut rng);
        let mut hasher = hash_context();

        let (t_1, t_2, randoms_and_values) = iter.fold(
            (
                pp.g * r1 + pp.u * r2,
                pp.ghat * r1 + pp.uhat * r2,
                randoms_and_values,
            ),
            |(t1, t2, mut randoms_and_values), (idx, value_i)| {
                let random = Scalar::random(&mut rng);
                randoms_and_values.push((idx, random, value_i));
                hash_g1(&mut hasher, &multi_pp.us[idx]);
                hash_g2(&mut hasher, &multi_pp.uhats[idx]);
                (
                    t1 + multi_pp.us[idx] * random,
                    t2 + multi_pp.uhats[idx] * random,
                    randoms_and_values,
                )
            },
        );

        hash_commitment(&mut hasher, self);
        hash_g1(&mut hasher, &t_1);
        hash_g2(&mut hasher, &t_2);
        let c = hash_extract_scalar(hasher);

        let s_1 = r1 + opening.r * c;
        let s_2 = r2 + value_0 * c;

        ProofMultiIndex {
            t_1,
            t_2,
            s_1,
            s_2,
            s_i: randoms_and_values
                .into_iter()
                .map(|(idx, r_i, value_i)| (idx, r_i + value_i * c))
                .collect(),
        }
    }

    pub fn verify_proof_multi_index_commit(
        &self,
        proof: &ProofMultiIndex,
        multi_pp: &MultiBasePublicParameters,
    ) -> Result<(), Error> {
        let mut hasher = hash_context();
        let pp = get_parameters();

        let (c_1, c_2) = proof.s_i.iter().fold(
            (
                pp.g * proof.s_1 + pp.u * proof.s_2,
                pp.ghat * proof.s_1 + pp.uhat * proof.s_2,
            ),
            |(c_1, c_2), (idx, s_i)| {
                hash_g1(&mut hasher, &multi_pp.us[*idx]);
                hash_g2(&mut hasher, &multi_pp.uhats[*idx]);

                (
                    c_1 + multi_pp.us[*idx] * s_i,
                    c_2 + multi_pp.uhats[*idx] * s_i,
                )
            },
        );

        hash_commitment(&mut hasher, self);
        hash_g1(&mut hasher, &proof.t_1);
        hash_g2(&mut hasher, &proof.t_2);
        let c = hash_extract_scalar(hasher);

        if c_1 != proof.t_1 + self.cm_1 * c || c_2 != proof.t_2 + self.cm_2 * c {
            Err(Error::InvalidProof)
        } else {
            Ok(())
        }
    }
}

impl Sub for &Commitment {
    type Output = Commitment;

    fn sub(self, rhs: Self) -> Self::Output {
        Commitment {
            cm_1: self.cm_1 - rhs.cm_1,
            cm_2: self.cm_2 - rhs.cm_2,
        }
    }
}

impl Sub<&Commitment> for Commitment {
    type Output = Commitment;

    fn sub(self, rhs: &Commitment) -> Self::Output {
        Commitment {
            cm_1: self.cm_1 - rhs.cm_1,
            cm_2: self.cm_2 - rhs.cm_2,
        }
    }
}

impl Add for &Commitment {
    type Output = Commitment;

    fn add(self, rhs: Self) -> Self::Output {
        Commitment {
            cm_1: self.cm_1 + rhs.cm_1,
            cm_2: self.cm_2 + rhs.cm_2,
        }
    }
}

impl Add<&Commitment> for Commitment {
    type Output = Commitment;

    fn add(self, rhs: &Commitment) -> Self::Output {
        Commitment {
            cm_1: self.cm_1 + rhs.cm_1,
            cm_2: self.cm_2 + rhs.cm_2,
        }
    }
}

impl Sum for Commitment {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let (cm_1, cm_2) = iter.fold(
            (G1Projective::identity(), G2Projective::identity()),
            |(cm_1, cm_2), cm| (cm_1 + cm.cm_1, cm_2 + cm.cm_2),
        );

        Commitment { cm_1, cm_2 }
    }
}

impl<'a> Sum<&'a Commitment> for Commitment {
    fn sum<I: Iterator<Item = &'a Commitment>>(iter: I) -> Self {
        let (cm_1, cm_2) = iter.fold(
            (G1Projective::identity(), G2Projective::identity()),
            |(cm_1, cm_2), cm| (cm_1 + cm.cm_1, cm_2 + cm.cm_2),
        );

        Commitment { cm_1, cm_2 }
    }
}

impl Mul<Scalar> for Commitment {
    type Output = Commitment;

    fn mul(self, rhs: Scalar) -> Self::Output {
        Commitment {
            cm_1: self.cm_1 * rhs,
            cm_2: self.cm_2 * rhs,
        }
    }
}

impl Mul<Scalar> for &Commitment {
    type Output = Commitment;

    fn mul(self, rhs: Scalar) -> Self::Output {
        Commitment {
            cm_1: self.cm_1 * rhs,
            cm_2: self.cm_2 * rhs,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn pedersen() {
        let msg = Scalar::random(rand::thread_rng());
        let (cm, o) = Commitment::commit(&msg);
        assert!(cm.verify(&msg, &o).is_ok());
    }

    #[test]
    fn pedersen_proof() {
        let msg = Scalar::random(rand::thread_rng());
        let (cm, o) = Commitment::commit(&msg);
        assert!(cm.verify(&msg, &o).is_ok());

        let proof = cm.proof(&msg, &o);
        assert!(cm.verify_proof(&proof).is_ok());
    }

    #[test]
    fn pedersen_proof_2_pk() {
        let pp = get_parameters();
        let msg_1 = Scalar::random(rand::thread_rng());
        let (cm_1, o_1) = Commitment::commit(&msg_1);
        assert!(cm_1.verify(&msg_1, &o_1).is_ok());
        let msg_2 = Scalar::random(rand::thread_rng());
        let (cm_2, o_2) = Commitment::commit(&msg_2);
        assert!(cm_2.verify(&msg_2, &o_2).is_ok());

        let o_3 = msg_2;
        let (pk_1, pk_2) = (pp.g * o_3, pp.ghat * o_3);

        let proof = cm_1.proof_2_pk(
            &msg_1,
            &o_1,
            &cm_2,
            &msg_2,
            &o_2,
            (&pp.g, &pp.ghat),
            (&pk_1, &pk_2),
        );
        assert!(cm_1
            .verify_proof_2_pk(&cm_2, &pp.g, &pp.ghat, &pk_1, &pk_2, &proof)
            .is_ok());
    }

    #[test]
    fn multi_pedersen() {
        let l = 10;
        let pp = MultiBasePublicParameters::new(l);

        let value_0 = Scalar::random(rand::thread_rng());
        for idx in 0..l {
            let value_i = Scalar::random(rand::thread_rng());
            let (cm, o) = Commitment::index_commit(&value_0, idx, &value_i, &pp);
            assert!(cm
                .verify_index_commit(&value_0, idx, &value_i, &o, &pp)
                .is_ok());
        }
    }

    #[test]
    fn multi_pedersen_proof() {
        let msg = Scalar::random(rand::thread_rng());
        let (commitment, opening) = Commitment::commit(&msg);

        let l = 10;
        let pp = MultiBasePublicParameters::new(l);

        let value_0 = Scalar::random(rand::thread_rng());
        for idx in 0..l {
            let value_i = Scalar::random(rand::thread_rng());
            let (cm, o) = Commitment::index_commit(&value_0, idx, &value_i, &pp);
            assert!(cm
                .verify_index_commit(&value_0, idx, &value_i, &o, &pp)
                .is_ok());

            let proof = commitment
                .proof_index_commit(&msg, &opening, &cm, &value_0, idx, &value_i, &o, &pp);
            assert!(commitment
                .verify_proof_index_commit(&cm, idx, &proof, &pp)
                .is_ok())
        }
    }

    #[test]
    fn multi_index_pedersen() {
        let l = 10;
        let pp = MultiBasePublicParameters::new(l);

        let value_0 = Scalar::random(rand::thread_rng());
        let values = [
            (2usize, Scalar::random(rand::thread_rng())),
            (7usize, Scalar::random(rand::thread_rng())),
        ];
        let (cm, o) = Commitment::multi_index_commit(&value_0, values.iter().copied(), &pp);
        assert!(cm
            .verify_multi_index_commit(&value_0, values.iter().copied(), &o, &pp)
            .is_ok());
    }

    #[test]
    fn multi_index_pedersen_proof() {
        let l = 10;
        let pp = MultiBasePublicParameters::new(l);

        let value_0 = Scalar::random(rand::thread_rng());
        let values = [
            (2usize, Scalar::random(rand::thread_rng())),
            (7usize, Scalar::random(rand::thread_rng())),
        ];
        let (cm, o) = Commitment::multi_index_commit(&value_0, values.iter().copied(), &pp);
        assert!(cm
            .verify_multi_index_commit(&value_0, values.iter().copied(), &o, &pp)
            .is_ok());

        let proof = cm.proof_multi_index_commit(&value_0, values.iter().copied(), &o, &pp);
        assert!(cm.verify_proof_multi_index_commit(&proof, &pp).is_ok());
    }
}
