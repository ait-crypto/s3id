use std::{
    iter::Sum,
    ops::{Add, Mul, Neg, Sub},
};

use ark_bls12_381::Bls12_381;
use ark_ec::PairingEngine;
use ark_ff::{UniformRand, Zero};
use rand::{RngCore, SeedableRng};
use sha2::Digest;

pub type G1Affine = <Bls12_381 as PairingEngine>::G1Affine;
pub type G1Projective = <Bls12_381 as PairingEngine>::G1Projective;
pub type G2Affine = <Bls12_381 as PairingEngine>::G2Affine;
pub type G2Projective = <Bls12_381 as PairingEngine>::G2Projective;
pub type Gt = <Bls12_381 as PairingEngine>::Fqk;
pub type Scalar = <Bls12_381 as PairingEngine>::Fr;

#[inline]
fn hash_with_domain_separation_1(msg: &[u8], domain_separator: &[u8]) -> G1Projective {
    let mut digest = sha2::Sha256::new();
    digest.update(domain_separator);
    digest.update(msg);

    let mut rng = rand_chacha::ChaCha20Rng::from_seed(digest.finalize().into());
    G1Projective::rand(&mut rng)
}

#[inline]
fn hash_with_domain_separation_2(msg: &[u8], domain_separator: &[u8]) -> G2Projective {
    let mut digest = sha2::Sha256::new();
    digest.update(domain_separator);
    digest.update(msg);

    let mut rng = rand_chacha::ChaCha20Rng::from_seed(digest.finalize().into());
    G2Projective::rand(&mut rng)
}

#[inline]
pub fn hash_with_domain_separation(msg: &[u8], domain_separator: &[u8]) -> G1G2 {
    G1G2(
        hash_with_domain_separation_1(msg, domain_separator),
        hash_with_domain_separation_2(msg, domain_separator),
    )
}

#[inline]
pub fn hash_usize(size: usize) -> G1G2 {
    let bytes = (size as u64).to_le_bytes();
    hash_with_domain_separation(&bytes, b"hash-usize")
}

#[inline]
pub fn pairing(lhs: &G1G2, rhs: &G1G2) -> Gt {
    Bls12_381::pairing(lhs.0, rhs.1)
}

#[inline]
pub fn pairing_product(elements: &[(&G1G2, &G1G2)]) -> Gt {
    type G1Prepared = <Bls12_381 as PairingEngine>::G1Prepared;
    type G2Prepared = <Bls12_381 as PairingEngine>::G2Prepared;

    Bls12_381::product_of_pairings(
        elements
            .iter()
            .map(|(lhs, rhs)| {
                (
                    G1Prepared::from(G1Affine::from(lhs.0)),
                    G2Prepared::from(G2Affine::from(rhs.1)),
                )
            })
            .collect::<Vec<_>>()
            .iter(),
    )
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct G1G2(pub G1Projective, pub G2Projective);

impl G1G2 {
    pub fn random(mut rng: impl RngCore) -> Self {
        Self(G1Projective::rand(&mut rng), G2Projective::rand(&mut rng))
    }
}

impl Add for G1G2 {
    type Output = G1G2;

    fn add(self, rhs: G1G2) -> Self::Output {
        G1G2(self.0 + rhs.0, self.1 + rhs.1)
    }
}

impl Add<&G1G2> for G1G2 {
    type Output = G1G2;

    fn add(self, rhs: &G1G2) -> Self::Output {
        G1G2(self.0 + rhs.0, self.1 + rhs.1)
    }
}

impl Add for &G1G2 {
    type Output = G1G2;

    fn add(self, rhs: &G1G2) -> Self::Output {
        G1G2(self.0 + rhs.0, self.1 + rhs.1)
    }
}

impl Add<G1G2> for &G1G2 {
    type Output = G1G2;

    #[inline(always)]
    fn add(self, rhs: G1G2) -> Self::Output {
        rhs + self
    }
}

impl Neg for G1G2 {
    type Output = G1G2;

    fn neg(self) -> Self::Output {
        Self(-self.0, -self.1)
    }
}

impl Neg for &G1G2 {
    type Output = G1G2;

    fn neg(self) -> Self::Output {
        G1G2(-self.0, -self.1)
    }
}

impl Sub for G1G2 {
    type Output = G1G2;

    fn sub(self, rhs: G1G2) -> Self::Output {
        G1G2(self.0 - rhs.0, self.1 - rhs.1)
    }
}

impl Sub<&G1G2> for G1G2 {
    type Output = G1G2;

    fn sub(self, rhs: &G1G2) -> Self::Output {
        G1G2(self.0 - rhs.0, self.1 - rhs.1)
    }
}

impl Sub<&G1G2> for &G1G2 {
    type Output = G1G2;

    fn sub(self, rhs: &G1G2) -> Self::Output {
        G1G2(self.0 - rhs.0, self.1 - rhs.1)
    }
}

impl<'a> Sum<&'a G1G2> for G1G2 {
    fn sum<I: Iterator<Item = &'a G1G2>>(iter: I) -> Self {
        let (g_1, g_2) = iter.fold(
            (G1Projective::zero(), G2Projective::zero()),
            |(acc_1, acc_2), g1g2| (acc_1 + g1g2.0, acc_2 + g1g2.1),
        );
        G1G2(g_1, g_2)
    }
}

impl Sum<G1G2> for G1G2 {
    fn sum<I: Iterator<Item = G1G2>>(iter: I) -> Self {
        let (g_1, g_2) = iter.fold(
            (G1Projective::zero(), G2Projective::zero()),
            |(acc_1, acc_2), g1g2| (acc_1 + g1g2.0, acc_2 + g1g2.1),
        );
        G1G2(g_1, g_2)
    }
}

impl Mul<Scalar> for G1G2 {
    type Output = G1G2;

    fn mul(mut self, rhs: Scalar) -> Self::Output {
        self.0 *= rhs;
        self.1 *= rhs;
        self
    }
}

/*/
impl Mul<&Scalar> for G1G2 {
    type Output = G1G2;

    fn mul(mut self, rhs: &Scalar) -> Self::Output {
        self.0 *= *rhs;
        self.1 *= *rhs;
        self
    }
}
*/

impl Mul<Scalar> for &G1G2 {
    type Output = G1G2;

    fn mul(self, rhs: Scalar) -> Self::Output {
        let mut ret = self.clone();
        ret.0 *= rhs;
        ret.1 *= rhs;
        ret
    }
}

/*
impl Mul<&Scalar> for &G1G2 {
    type Output = G1G2;

    fn mul(self, rhs: &Scalar) -> Self::Output {
        let mut ret = self.clone();
        ret.0 *= *rhs;
        ret.1 *= *rhs;
        ret
    }
}
*/

/*
impl From<G1G2> for G1Affine {
    fn from(value: G1G2) -> Self {
        value.0.into()
    }
}

impl From<&G1G2> for G1Affine {
    fn from(value: &G1G2) -> Self {
        value.0.into()
    }
}

impl From<G1G2> for G2Affine {
    fn from(value: G1G2) -> Self {
        value.1.into()
    }
}

impl From<&G1G2> for G2Affine {
    fn from(value: &G1G2) -> Self {
        value.1.into()
    }
}
 */

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn pp() {
        let mut rng = rand::thread_rng();
        let lhs1 = G1G2(G1Projective::rand(&mut rng), G2Projective::rand(&mut rng));
        let lhs2 = G1G2(G1Projective::rand(&mut rng), G2Projective::rand(&mut rng));
        let rhs1 = G1G2(G1Projective::rand(&mut rng), G2Projective::rand(&mut rng));
        let rhs2 = G1G2(G1Projective::rand(&mut rng), G2Projective::rand(&mut rng));

        let check = pairing(&lhs1, &rhs1) * pairing(&lhs2, &rhs2);
        let pp = pairing_product(&[(&lhs1, &rhs1), (&lhs2, &rhs2)]);
        assert_eq!(check, pp);

        let check = pairing(&lhs1, &rhs1) / pairing(&lhs2, &rhs2);
        let pp = pairing_product(&[(&lhs1, &rhs1), (&-lhs2, &rhs2)]);
        assert_eq!(check, pp);
    }
}

pub mod gs {
    use ark_bls12_381::Bls12_381;

    #[allow(clippy::upper_case_acronyms)]
    pub type CRS = groth_sahai::CRS<Bls12_381>;
    #[allow(clippy::upper_case_acronyms)]
    pub type PPE = groth_sahai::statement::PPE<Bls12_381>;
    pub type CProof = groth_sahai::prover::CProof<Bls12_381>;
}
