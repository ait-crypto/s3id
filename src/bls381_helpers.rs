use std::{
    iter::Sum,
    ops::{Add, Mul, Sub},
};

use bls12_381::{
    hash_to_curve::{ExpandMsgXmd, HashToCurve},
    G1Affine, G1Projective, G2Affine, G2Projective, Scalar,
};

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
        match bool::from(scalar.is_some()) {
            true => Ok(scalar.unwrap()),
            false => Err(()),
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
        match bool::from(point.is_some()) {
            true => Ok(point.unwrap()),
            false => Err(()),
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
        G1Affine::from_serde_bytes(bytes).map(|p| p.into())
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
        match bool::from(point.is_some()) {
            true => Ok(point.unwrap()),
            false => Err(()),
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
        G2Affine::from_serde_bytes(bytes).map(|p| p.into())
    }
}

#[inline]
pub fn hash_with_domain_separation_1(msg: &[u8], domain_separator: &[u8]) -> G1Projective {
    <G1Projective as HashToCurve<ExpandMsgXmd<sha2::Sha256>>>::hash_to_curve(msg, domain_separator)
}

#[inline]
pub fn hash_with_domain_separation_2(msg: &[u8], domain_separator: &[u8]) -> G2Projective {
    <G2Projective as HashToCurve<ExpandMsgXmd<sha2::Sha256>>>::hash_to_curve(msg, domain_separator)
}

#[inline]
pub fn hash_usize_1(size: usize) -> G1Projective {
    let bytes = (size as u64).to_le_bytes();
    hash_with_domain_separation_1(&bytes, b"hash-usize")
}

#[inline]
pub fn hash_usize_2(size: usize) -> G2Projective {
    let bytes = (size as u64).to_le_bytes();
    hash_with_domain_separation_2(&bytes, b"hash-usize")
}

#[inline]
pub fn pairing<G1, G2>(g: G1, h: G2) -> bls12_381::Gt
where
    G1: Into<G1Affine>,
    G2: Into<G2Affine>,
{
    bls12_381::pairing(&g.into(), &h.into())
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct G1G2(pub G1Projective, pub G2Projective);

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

impl Add<&G1G2> for &G1G2 {
    type Output = G1G2;

    fn add(self, rhs: &G1G2) -> Self::Output {
        G1G2(self.0 + rhs.0, self.1 + rhs.1)
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
