use std::marker::PhantomData;

use bls12_381::{
    hash_to_curve::{ExpandMsgXmd, HashToCurve},
    G1Affine, G1Projective, G2Affine, G2Projective, Scalar,
};
use serde::{
    de::{self},
    Deserializer, Serializer,
};
use sha2::{Digest, Sha512};

pub trait SerdeWrapper<const SIZE: usize>: Sized {
    type Error;

    fn as_serde_bytes(&self) -> [u8; SIZE];
    fn from_serde_bytes(bytes: &[u8; SIZE]) -> Result<Self, Self::Error>;
}

impl SerdeWrapper<32> for Scalar {
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

impl SerdeWrapper<96> for G1Affine {
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

impl SerdeWrapper<96> for G1Projective {
    type Error = ();

    #[inline]
    fn as_serde_bytes(&self) -> [u8; 96] {
        G1Affine::from(self).to_uncompressed()
    }

    fn from_serde_bytes(bytes: &[u8; 96]) -> Result<Self, Self::Error> {
        let point = G1Affine::from_uncompressed(bytes);
        match bool::from(point.is_some()) {
            true => Ok(point.unwrap().into()),
            false => Err(()),
        }
    }
}

impl SerdeWrapper<192> for G2Affine {
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

impl SerdeWrapper<192> for G2Projective {
    type Error = ();

    #[inline]
    fn as_serde_bytes(&self) -> [u8; 192] {
        G2Affine::from(self).to_uncompressed()
    }

    fn from_serde_bytes(bytes: &[u8; 192]) -> Result<Self, Self::Error> {
        let point = G2Affine::from_uncompressed(bytes);
        match bool::from(point.is_some()) {
            true => Ok(point.unwrap().into()),
            false => Err(()),
        }
    }
}

pub fn serialize<T, S, const SIZE: usize>(scalar: &T, serializer: S) -> Result<S::Ok, S::Error>
where
    T: SerdeWrapper<SIZE>,
    S: Serializer,
{
    serializer.serialize_bytes(&scalar.as_serde_bytes())
}

struct BytesVisitor<T, const SIZE: usize>(PhantomData<T>);

impl<'de2, T, const SIZE: usize> de::Visitor<'de2> for BytesVisitor<T, SIZE>
where
    T: SerdeWrapper<SIZE>,
{
    type Value = T;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a scalar encoded as {} bytes", 32)
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        v.try_into()
            .map_err(|_| E::invalid_length(v.len(), &self))
            .and_then(|bytes| {
                T::from_serde_bytes(bytes)
                    .map_err(|_| E::invalid_value(de::Unexpected::Bytes(v), &self))
            })
    }
}

pub fn deserialize<'de, D, T, const SIZE: usize>(deserializer: D) -> Result<T, D::Error>
where
    T: SerdeWrapper<SIZE>,
    D: Deserializer<'de>,
{
    deserializer.deserialize_bytes(BytesVisitor(PhantomData))
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
pub fn hash_1(msg: &[u8]) -> G1Projective {
    hash_with_domain_separation_1(msg, b"BLS-H2-G1")
}

#[inline]
pub fn hash_2(msg: &[u8]) -> G2Projective {
    hash_with_domain_separation_2(msg, b"BLS-H2-G2")
}

pub fn hash_to_scalar_with_domain_separation(message: &[u8], domain_separator: &[u8]) -> Scalar {
    let mut hasher = Sha512::new();
    hasher.update(domain_separator);
    hasher.update(message);
    let digest = hasher.finalize();
    Scalar::from_bytes_wide(&digest.as_slice().try_into().unwrap())
}

#[inline]
pub fn hash_to_scalar(message: &[u8]) -> Scalar {
    hash_to_scalar_with_domain_separation(message, b"hash-to-scalar")
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
