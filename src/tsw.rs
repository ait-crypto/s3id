use std::{
    fmt,
    iter::Sum,
    ops::{Add, Index, Mul, Sub},
};

use ark_ff::{Field, UniformRand, Zero};
use rand::thread_rng;
use thiserror::Error;

use crate::{
    bls381_helpers::{G1G2, Scalar, hash_usize, multi_pairing},
    lagrange::Lagrange,
    pedersen::{Commitment, get_parameters},
};

#[derive(Error, Debug)]
pub struct Error;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "verification error")
    }
}

impl Error {
    fn new() -> Self {
        Self {}
    }
}

#[derive(Debug)]
pub struct PublicParameters {
    hashed_indices: Vec<G1G2>,
}

impl PublicParameters {
    pub fn new(l: usize) -> Self {
        Self {
            hashed_indices: (0..l).map(hash_usize).collect(),
        }
    }
}

impl Index<usize> for PublicParameters {
    type Output = G1G2;

    fn index(&self, index: usize) -> &Self::Output {
        debug_assert!(index < self.hashed_indices.len());
        &self.hashed_indices[index]
    }
}

#[derive(Debug, Clone)]
pub struct SecretKey {
    pub(crate) sk: Scalar,
}

#[allow(clippy::new_without_default)]
impl SecretKey {
    pub fn new() -> Self {
        Self {
            sk: Scalar::rand(&mut thread_rng()),
        }
    }

    pub fn into_shares(&self, num_shares: usize, t: usize) -> Vec<Self> {
        let mut rng = thread_rng();
        let mut sks: Vec<_> = (0..t - 1).map(|_| Scalar::rand(&mut rng)).collect();

        let mut base_points: Vec<_> = (1..=t).map(|i| Scalar::from(i as u64)).collect();
        for k in t..=num_shares {
            base_points[t - 1] = Scalar::from(k as u64);
            let lagrange = Lagrange::new(&base_points);

            let base = self.sk
                - sks
                    .iter()
                    .take(t - 1)
                    .enumerate()
                    .map(|(j, sk)| *sk * lagrange.eval_j_0(j))
                    .sum::<Scalar>();

            sks.push(base * lagrange.eval_j_0(t - 1).inverse().unwrap());
        }
        sks.into_iter().map(|sk| Self { sk }).collect()
    }

    pub fn to_public_key(&self) -> PublicKey {
        let pp = get_parameters();
        PublicKey(&pp.g * self.sk)
    }

    pub fn sign_pedersen_commitment(
        &self,
        commitment: &Commitment,
        index: usize,
        pp: &PublicParameters,
    ) -> Signature {
        Signature((&pp[index] + &commitment.0) * self.sk)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PublicKey(pub(crate) G1G2);

impl PublicKey {
    pub fn from_secret_key_shares<'a, I>(shares: I, lagrange: &Lagrange) -> Self
    where
        I: Iterator<Item = &'a SecretKey>,
    {
        SecretKey {
            sk: shares
                .enumerate()
                .map(|(j, sk)| sk.sk * lagrange.eval_j_0(j))
                .sum(),
        }
        .to_public_key()
    }

    pub fn verify_pedersen_commitment(
        &self,
        commitment: &Commitment,
        index: usize,
        signature: &Signature,
        pp: &PublicParameters,
    ) -> Result<(), Error> {
        let pedersen_pp = get_parameters();

        let check = -(&pp[index] + &commitment.0);

        if multi_pairing(&[(&check, &self.0), (&signature.0, &pedersen_pp.g)]).is_zero()
            && multi_pairing(&[(&self.0, &check), (&pedersen_pp.g, &signature.0)]).is_zero()
        {
            Ok(())
        } else {
            Err(Error::new())
        }
    }
}

#[derive(Debug, Clone)]
pub struct Signature(pub(crate) G1G2);

impl Signature {
    pub fn from_shares(signatures: &[Self], lagrange: &Lagrange) -> Self {
        signatures
            .iter()
            .enumerate()
            .map(|(j, sig)| sig * lagrange.eval_j_0(j))
            .sum()
    }
}

impl PublicKey {
    pub fn is_valid(&self) -> bool {
        let pp = get_parameters();
        multi_pairing(&[(&-&self.0, &pp.g), (&pp.g, &self.0)]).is_zero()
    }
}

impl Mul<Scalar> for &PublicKey {
    type Output = PublicKey;

    #[inline]
    fn mul(self, rhs: Scalar) -> Self::Output {
        PublicKey(&self.0 * rhs)
    }
}

impl Mul<Scalar> for PublicKey {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Scalar) -> Self::Output {
        Self(self.0 * rhs)
    }
}

impl Add<&Self> for PublicKey {
    type Output = Self;

    #[inline]
    fn add(self, rhs: &Self) -> Self::Output {
        Self(self.0 + &rhs.0)
    }
}

impl Add<&PublicKey> for &PublicKey {
    type Output = PublicKey;

    #[inline]
    fn add(self, rhs: &PublicKey) -> Self::Output {
        PublicKey(&self.0 + &rhs.0)
    }
}

impl Sub<&PublicKey> for &PublicKey {
    type Output = PublicKey;

    #[inline]
    fn sub(self, rhs: &PublicKey) -> Self::Output {
        PublicKey(&self.0 - &rhs.0)
    }
}

impl<'a> Sum<&'a Self> for PublicKey {
    #[inline]
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        Self(iter.map(|v| &v.0).sum())
    }
}

impl Sum<Self> for PublicKey {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self(iter.map(|v| v.0).sum())
    }
}

// this is abuse of notation
impl Sub<&PublicKey> for Signature {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: &PublicKey) -> Self::Output {
        Self(self.0 - &rhs.0)
    }
}

impl Add<&PublicKey> for &Signature {
    type Output = Signature;

    #[inline]
    fn add(self, rhs: &PublicKey) -> Self::Output {
        Signature(&self.0 + &rhs.0)
    }
}

impl Add<PublicKey> for Signature {
    type Output = Self;

    #[inline]
    fn add(self, rhs: PublicKey) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Mul<Scalar> for Signature {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Scalar) -> Self::Output {
        Self(self.0 * rhs)
    }
}

impl Mul<Scalar> for &Signature {
    type Output = Signature;

    #[inline]
    fn mul(self, rhs: Scalar) -> Self::Output {
        Signature(&self.0 * rhs)
    }
}

impl Sum for Signature {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self(iter.map(|v| v.0).sum())
    }
}

impl<'a> Sum<&'a Self> for Signature {
    #[inline]
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        Self(iter.map(|v| &v.0).sum())
    }
}

#[cfg(test)]
mod test {
    use crate::{bls381_helpers::pairing, pedersen::MultiBasePublicParameters};

    use super::*;

    #[test]
    fn tsw() {
        let pp = PublicParameters::new(2);
        let n = 10;
        let t = n / 2 + 1;

        let (cm, _) = Commitment::commit(&Scalar::rand(&mut rand::thread_rng()));
        let sk = SecretKey::new();
        let sks = sk.into_shares(n, t);
        let sigs: Vec<_> = sks
            .iter()
            .map(|sk| sk.sign_pedersen_commitment(&cm, 0, &pp))
            .collect();

        let lagrange = Lagrange::new(
            (1..=t)
                .map(|i| Scalar::from(i as u64))
                .collect::<Vec<_>>()
                .as_ref(),
        );
        let pk = PublicKey::from_secret_key_shares(sks.iter().take(t), &lagrange);
        assert!(pk.is_valid());
        assert_eq!(pk, sk.to_public_key());

        let sig = Signature::from_shares(&sigs[..t], &lagrange);
        assert!(pk.verify_pedersen_commitment(&cm, 0, &sig, &pp).is_ok());

        let lagrange = Lagrange::new(
            (2..=t + 1)
                .map(|i| Scalar::from(i as u64))
                .collect::<Vec<_>>()
                .as_ref(),
        );
        let other_pk = PublicKey::from_secret_key_shares(sks.iter().skip(1).take(t), &lagrange);
        assert!(other_pk.is_valid());
        assert_eq!(other_pk, pk);

        let sig = Signature::from_shares(&sigs[1..=t], &lagrange);
        assert!(pk.verify_pedersen_commitment(&cm, 0, &sig, &pp).is_ok());

        let lagrange = Lagrange::new(
            (1..=n)
                .map(|i| Scalar::from(i as u64))
                .collect::<Vec<_>>()
                .as_ref(),
        );
        let pk = PublicKey::from_secret_key_shares(sks.iter(), &lagrange);
        assert!(pk.is_valid());
        assert_eq!(pk, sk.to_public_key());

        let sig = Signature::from_shares(&sigs, &lagrange);
        assert!(pk.verify_pedersen_commitment(&cm, 0, &sig, &pp).is_ok());
    }

    #[test]
    fn sw_commitment() {
        let pp = PublicParameters::new(3);
        let (cm, _) = Commitment::commit(&Scalar::rand(&mut rand::thread_rng()));

        let sk = SecretKey::new();
        let pk = sk.to_public_key();
        assert!(pk.is_valid());

        let sig = sk.sign_pedersen_commitment(&cm, 1, &pp);
        assert!(pk.verify_pedersen_commitment(&cm, 1, &sig, &pp).is_ok());
        assert!(pk.verify_pedersen_commitment(&cm, 2, &sig, &pp).is_err());
    }

    #[test]
    fn pk_sum() {
        let sk_1 = SecretKey::new();
        let sk_2 = SecretKey::new();

        let pk_1 = sk_1.to_public_key();
        let pk_2 = sk_2.to_public_key();

        assert_eq!(pk_1.clone() + &pk_2, [pk_1, pk_2].iter().sum());
    }

    #[test]
    fn sw_multi_index_commitment() {
        const L: usize = 10;

        let pedersen_pp = get_parameters();
        let pp = PublicParameters::new(L);
        let sk = SecretKey::new();
        let pk = sk.to_public_key();
        let multi_pp = MultiBasePublicParameters::new(L);
        let value_0 = Scalar::rand(&mut rand::thread_rng());

        let index_attributes = [
            (2, Scalar::rand(&mut rand::thread_rng())),
            (5, Scalar::rand(&mut rand::thread_rng())),
        ];

        let signatures: Vec<_> = index_attributes
            .iter()
            .map(|(idx, attribute)| {
                let (cm, o) = Commitment::index_commit(&value_0, *idx, attribute, &multi_pp);
                let sigma = sk.sign_pedersen_commitment(&cm, *idx, &pp);
                (cm, o, sigma)
            })
            .collect();
        let cm: Commitment = signatures.iter().map(|(cm, _, _)| cm).sum();
        let sigma: Signature = signatures.iter().map(|(_, _, sigma)| sigma).sum();

        let h = index_attributes
            .iter()
            .map(|(idx, _)| *idx)
            .fold(G1G2::default(), |h, idx| h + &pp[idx]);

        let check = h + cm.0;
        assert_eq!(pairing(&sigma.0, &pedersen_pp.g), pairing(&check, &pk.0));
        assert_eq!(pairing(&pedersen_pp.g, &sigma.0), pairing(&pk.0, &check));
    }
}
