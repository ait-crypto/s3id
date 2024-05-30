use std::{
    iter::Sum,
    ops::{Add, Mul, Neg, Sub},
};

use bls12_381::hash_to_curve::{ExpandMsgXmd, HashToCurve};
pub use bls12_381::{G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective, Gt, Scalar};
pub use group::{ff::Field, Group};
use rand::RngCore;

pub trait ByteConverter<const SIZE: usize>: Sized {
    type Error;

    fn as_serde_bytes(&self) -> [u8; SIZE];
    fn from_serde_bytes(bytes: &[u8; SIZE]) -> Result<Self, Self::Error>;
}

impl ByteConverter<32> for Scalar {
    type Error = ();

    #[inline]
    fn as_serde_bytes(&self) -> [u8; 32] {
        self.to_bytes()
    }

    fn from_serde_bytes(bytes: &[u8; 32]) -> Result<Self, Self::Error> {
        let scalar = Self::from_bytes(bytes);
        if bool::from(scalar.is_some()) {
            Ok(scalar.unwrap())
        } else {
            Err(())
        }
    }
}

impl ByteConverter<96> for G1Affine {
    type Error = ();

    #[inline]
    fn as_serde_bytes(&self) -> [u8; 96] {
        self.to_uncompressed()
    }

    fn from_serde_bytes(bytes: &[u8; 96]) -> Result<Self, Self::Error> {
        let point = Self::from_uncompressed(bytes);
        if bool::from(point.is_some()) {
            Ok(point.unwrap())
        } else {
            Err(())
        }
    }
}

impl ByteConverter<96> for G1Projective {
    type Error = ();

    #[inline]
    fn as_serde_bytes(&self) -> [u8; 96] {
        G1Affine::from(self).as_serde_bytes()
    }

    fn from_serde_bytes(bytes: &[u8; 96]) -> Result<Self, Self::Error> {
        G1Affine::from_serde_bytes(bytes).map(Into::into)
    }
}

impl ByteConverter<192> for G2Affine {
    type Error = ();

    #[inline]
    fn as_serde_bytes(&self) -> [u8; 192] {
        self.to_uncompressed()
    }

    fn from_serde_bytes(bytes: &[u8; 192]) -> Result<Self, Self::Error> {
        let point = Self::from_uncompressed(bytes);
        if bool::from(point.is_some()) {
            Ok(point.unwrap())
        } else {
            Err(())
        }
    }
}

impl ByteConverter<192> for G2Projective {
    type Error = ();

    #[inline]
    fn as_serde_bytes(&self) -> [u8; 192] {
        G2Affine::from(self).as_serde_bytes()
    }

    fn from_serde_bytes(bytes: &[u8; 192]) -> Result<Self, Self::Error> {
        G2Affine::from_serde_bytes(bytes).map(Into::into)
    }
}

#[inline]
fn hash_with_domain_separation_1(msg: &[u8], domain_separator: &[u8]) -> G1Projective {
    <G1Projective as HashToCurve<ExpandMsgXmd<sha2::Sha256>>>::hash_to_curve(msg, domain_separator)
}

#[inline]
fn hash_with_domain_separation_2(msg: &[u8], domain_separator: &[u8]) -> G2Projective {
    <G2Projective as HashToCurve<ExpandMsgXmd<sha2::Sha256>>>::hash_to_curve(msg, domain_separator)
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
pub fn pairing<G1, G2>(g: G1, h: G2) -> Gt
where
    G1: Into<G1Affine>,
    G2: Into<G2Affine>,
{
    bls12_381::pairing(&g.into(), &h.into())
}

#[inline]
pub fn pairing_product(elements: &[(&G1G2, &G1G2)]) -> Gt {
    let terms: Vec<(G1Affine, G2Prepared)> = elements
        .iter()
        .map(|(lhs, rhs)| (lhs.0.into(), G2Prepared::from(G2Affine::from(rhs.1))))
        .collect();
    let refs: Vec<_> = terms.iter().map(|(lhs, rhs)| (lhs, rhs)).collect();
    bls12_381::multi_miller_loop(refs.as_slice()).final_exponentiation()
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct G1G2(pub G1Projective, pub G2Projective);

impl G1G2 {
    pub fn random(mut rng: impl RngCore) -> Self {
        Self(
            G1Projective::random(&mut rng),
            G2Projective::random(&mut rng),
        )
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
            (G1Projective::identity(), G2Projective::identity()),
            |(acc_1, acc_2), g1g2| (acc_1 + g1g2.0, acc_2 + g1g2.1),
        );
        G1G2(g_1, g_2)
    }
}

impl Sum<G1G2> for G1G2 {
    fn sum<I: Iterator<Item = G1G2>>(iter: I) -> Self {
        let (g_1, g_2) = iter.fold(
            (G1Projective::identity(), G2Projective::identity()),
            |(acc_1, acc_2), g1g2| (acc_1 + g1g2.0, acc_2 + g1g2.1),
        );
        G1G2(g_1, g_2)
    }
}

impl Mul<Scalar> for G1G2 {
    type Output = G1G2;

    fn mul(self, rhs: Scalar) -> Self::Output {
        G1G2(self.0 * rhs, self.1 * rhs)
    }
}

impl Mul<&Scalar> for G1G2 {
    type Output = G1G2;

    fn mul(self, rhs: &Scalar) -> Self::Output {
        G1G2(self.0 * rhs, self.1 * rhs)
    }
}

impl Mul<Scalar> for &G1G2 {
    type Output = G1G2;

    fn mul(self, rhs: Scalar) -> Self::Output {
        G1G2(self.0 * rhs, self.1 * rhs)
    }
}

impl Mul<&Scalar> for &G1G2 {
    type Output = G1G2;

    fn mul(self, rhs: &Scalar) -> Self::Output {
        G1G2(self.0 * rhs, self.1 * rhs)
    }
}

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

#[cfg(test)]
mod test {
    use group::Group;

    use super::*;

    #[test]
    fn pp() {
        let mut rng = rand::thread_rng();
        let lhs1 = G1G2(
            G1Projective::random(&mut rng),
            G2Projective::random(&mut rng),
        );
        let lhs2 = G1G2(
            G1Projective::random(&mut rng),
            G2Projective::random(&mut rng),
        );
        let rhs1 = G1G2(
            G1Projective::random(&mut rng),
            G2Projective::random(&mut rng),
        );
        let rhs2 = G1G2(
            G1Projective::random(&mut rng),
            G2Projective::random(&mut rng),
        );

        let check = pairing(&lhs1, &rhs1) + pairing(&lhs2, &rhs2);
        let pp = pairing_product(&[(&lhs1, &rhs1), (&lhs2, &rhs2)]);
        assert_eq!(check, pp);

        let check = pairing(&lhs1, &rhs1) - pairing(&lhs2, &rhs2);
        let pp = pairing_product(&[(&lhs1, &rhs1), (&-lhs2, &rhs2)]);
        assert_eq!(check, pp);
    }
}

pub mod gs {
    use ark_bls12_381::Bls12_381;
    use ark_ec::{AffineCurve, PairingEngine};
    use ark_ff::{bytes::FromBytes, Zero};
    use ark_serialize::CanonicalDeserialize;

    use super::ByteConverter;

    pub type G1Affine = <Bls12_381 as PairingEngine>::G1Affine;
    pub type G1Projective = <Bls12_381 as PairingEngine>::G1Projective;
    pub type G2Affine = <Bls12_381 as PairingEngine>::G2Affine;
    pub type G2Projective = <Bls12_381 as PairingEngine>::G2Projective;
    pub type Gt = <Bls12_381 as PairingEngine>::Fqk;
    pub type Scalar = <Bls12_381 as PairingEngine>::Fr;
    pub type CRS = groth_sahai::CRS<Bls12_381>;
    pub type PPE = groth_sahai::statement::PPE<Bls12_381>;
    pub type CProof = groth_sahai::prover::CProof<Bls12_381>;

    pub struct GSG1G2(pub(crate) G1Projective, pub(crate) G2Projective);

    impl From<&super::G1G2> for GSG1G2 {
        fn from(value: &super::G1G2) -> Self {
            let g1 = if value.0.is_identity().unwrap_u8() == 1 {
                G1Affine::zero()
            } else {
                let mut g1_bytes = value.0.as_serde_bytes().to_vec();
                // g1_bytes.push(0);
                // G1Affine::read(g1_bytes.as_slice()).unwrap()
                G1Affine::deserialize_uncompressed(g1_bytes.as_slice()).unwrap()
            };

            let g2 = if value.1.is_identity().unwrap_u8() == 1 {
                G2Affine::zero()
            } else {
                let mut g2_bytes = value.1.as_serde_bytes().to_vec();
                // g2_bytes.push(0);
                // G2Affine::read(g2_bytes.as_slice()).unwrap()
                G2Affine::deserialize_uncompressed(g2_bytes.as_slice()).unwrap()
            };

            Self(g1.into_projective(), g2.into_projective())
        }
    }

    pub fn pairing(lhs: &GSG1G2, rhs: &GSG1G2) -> Gt {
        Bls12_381::pairing(lhs.0, rhs.1)
    }

    #[cfg(test)]
    mod test {
        use crate::bls381_helpers::G1G2;

        use super::GSG1G2;

        #[test]
        fn conversion() {
            let g1g2 = G1G2::random(rand::thread_rng());
            let _ = GSG1G2::from(&g1g2);
        }
    }
}
