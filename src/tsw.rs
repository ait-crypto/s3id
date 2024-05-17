use std::{
    fmt::Display,
    iter::Sum,
    ops::{Add, Mul, Sub},
};

use bls12_381::Scalar;
use group::ff::Field;
use rand::thread_rng;
use thiserror::Error;

use crate::{
    bls381_helpers::{hash_usize_1, hash_usize_2, pairing, G1G2},
    lagrange::Lagrange,
    pedersen::{get_parameters, Commitment},
};

#[derive(Error, Debug)]
pub struct Error;

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "verification error")
    }
}

impl Error {
    fn new() -> Self {
        Self {}
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
            sk: Scalar::random(thread_rng()),
        }
    }

    pub fn into_shares(&self, num_shares: usize, t: usize) -> Vec<SecretKey> {
        let mut rng = thread_rng();
        let mut sks: Vec<_> = (0..t - 1).map(|_| Scalar::random(&mut rng)).collect();

        let mut base_points: Vec<_> = (1..=t).map(|i| Scalar::from(i as u64)).collect();
        for k in t..=num_shares {
            base_points[t - 1] = Scalar::from(k as u64);
            let lagrange = Lagrange::new(&base_points);

            let base = self.sk
                - sks
                    .iter()
                    .take(t - 1)
                    .enumerate()
                    .map(|(j, sk)| sk * lagrange.eval_j_0(j))
                    .sum::<Scalar>();

            sks.push(base * lagrange.eval_j_0(t - 1).invert().unwrap());
        }
        sks.into_iter().map(|sk| SecretKey { sk }).collect()
    }

    pub fn to_public_key(&self) -> PublicKey {
        let pp = get_parameters();
        PublicKey(G1G2(pp.g * self.sk, pp.ghat * self.sk))
    }

    pub fn sign_pedersen_commitment(&self, commitment: &Commitment, index: usize) -> Signature {
        Signature(G1G2(
            (hash_usize_1(index) + commitment.cm_1) * self.sk,
            (hash_usize_2(index) + commitment.cm_2) * self.sk,
        ))
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PublicKey(pub(crate) G1G2);

impl PublicKey {
    pub fn from_secret_key_shares<'a, I>(shares: I, lagrange: &Lagrange) -> PublicKey
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
    ) -> Result<(), Error> {
        let pp = get_parameters();

        let hi_1 = hash_usize_1(index);
        let lhs = pairing(hi_1 + commitment.cm_1, &self.0);
        let rhs = pairing(&signature.0, pp.ghat);
        if lhs != rhs {
            return Err(Error::new());
        }

        let hi_2 = hash_usize_2(index);
        let lhs = pairing(&self.0, hi_2 + commitment.cm_2);
        let rhs = pairing(pp.g, &signature.0);
        match lhs == rhs {
            true => Ok(()),
            false => Err(Error::new()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Signature(pub(crate) G1G2);

impl Signature {
    pub fn from_shares(signatures: &[Signature], lagrange: &Lagrange) -> Signature {
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
        pairing(&self.0, pp.ghat) == pairing(pp.g, &self.0)
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
    type Output = PublicKey;

    #[inline]
    fn mul(self, rhs: Scalar) -> Self::Output {
        PublicKey(self.0 * rhs)
    }
}

impl Mul<&Scalar> for &PublicKey {
    type Output = PublicKey;

    #[inline]
    fn mul(self, rhs: &Scalar) -> Self::Output {
        PublicKey(&self.0 * rhs)
    }
}

impl Mul<&Scalar> for PublicKey {
    type Output = PublicKey;

    #[inline]
    fn mul(self, rhs: &Scalar) -> Self::Output {
        PublicKey(self.0 * rhs)
    }
}

impl Add<&PublicKey> for PublicKey {
    type Output = PublicKey;

    #[inline]
    fn add(self, rhs: &PublicKey) -> Self::Output {
        PublicKey(self.0 + &rhs.0)
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

impl<'a> Sum<&'a PublicKey> for PublicKey {
    fn sum<I: Iterator<Item = &'a PublicKey>>(iter: I) -> Self {
        PublicKey(iter.map(|v| &v.0).sum())
    }
}

impl Sum<PublicKey> for PublicKey {
    fn sum<I: Iterator<Item = PublicKey>>(iter: I) -> Self {
        PublicKey(iter.map(|v| v.0).sum())
    }
}

// this is abuse of notation
impl Sub<&PublicKey> for Signature {
    type Output = Signature;

    #[inline]
    fn sub(self, rhs: &PublicKey) -> Self::Output {
        Signature(self.0 - &rhs.0)
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
    type Output = Signature;

    #[inline]
    fn add(self, rhs: PublicKey) -> Self::Output {
        Signature(self.0 + rhs.0)
    }
}

impl Mul<Scalar> for Signature {
    type Output = Signature;

    #[inline]
    fn mul(self, rhs: Scalar) -> Self::Output {
        Signature(self.0 * rhs)
    }
}

impl Mul<&Scalar> for Signature {
    type Output = Signature;

    #[inline]
    fn mul(self, rhs: &Scalar) -> Self::Output {
        Signature(self.0 * rhs)
    }
}

impl Mul<Scalar> for &Signature {
    type Output = Signature;

    #[inline]
    fn mul(self, rhs: Scalar) -> Self::Output {
        Signature(&self.0 * rhs)
    }
}

impl Mul<&Scalar> for &Signature {
    type Output = Signature;

    #[inline]
    fn mul(self, rhs: &Scalar) -> Self::Output {
        Signature(&self.0 * rhs)
    }
}

impl Sum for Signature {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self(iter.map(|v| v.0).sum())
    }
}

impl<'a> Sum<&'a Signature> for Signature {
    fn sum<I: Iterator<Item = &'a Signature>>(iter: I) -> Self {
        Self(iter.map(|v| &v.0).sum())
    }
}

#[cfg(test)]
mod test {
    use bls12_381::{G1Projective, G2Projective};

    use crate::pedersen::MultiBasePublicParameters;

    use super::*;

    #[test]
    fn tsw() {
        let n = 10;
        let t = n / 2 + 1;

        let (cm, _) = Commitment::commit(&Scalar::random(rand::thread_rng()));
        let sk = SecretKey::new();
        let sks = sk.into_shares(n, t);
        let sigs: Vec<_> = sks
            .iter()
            .map(|sk| sk.sign_pedersen_commitment(&cm, 0))
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
        assert!(pk.verify_pedersen_commitment(&cm, 0, &sig).is_ok());

        let lagrange = Lagrange::new(
            (2..=t + 1)
                .map(|i| Scalar::from(i as u64))
                .collect::<Vec<_>>()
                .as_ref(),
        );
        let other_pk = PublicKey::from_secret_key_shares(sks.iter().skip(1).take(t), &lagrange);
        assert!(other_pk.is_valid());
        assert_eq!(other_pk, pk);

        let sig = Signature::from_shares(&sigs[1..t + 1], &lagrange);
        assert!(pk.verify_pedersen_commitment(&cm, 0, &sig).is_ok());

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
        assert!(pk.verify_pedersen_commitment(&cm, 0, &sig).is_ok());
    }

    #[test]
    fn sw_commitment() {
        let (cm, _) = Commitment::commit(&Scalar::random(rand::thread_rng()));

        let sk = SecretKey::new();
        let pk = sk.to_public_key();
        assert!(pk.is_valid());

        let sig = sk.sign_pedersen_commitment(&cm, 1);
        assert!(pk.verify_pedersen_commitment(&cm, 1, &sig).is_ok());
        assert!(pk.verify_pedersen_commitment(&cm, 2, &sig).is_err());
    }

    #[test]
    fn pk_sum() {
        let sk_1 = SecretKey::new();
        let sk_2 = SecretKey::new();

        let pk_1 = sk_1.to_public_key();
        let pk_2 = sk_2.to_public_key();

        assert_eq!(pk_1.clone() + &pk_2, [pk_1, pk_2].iter().sum())
    }

    #[test]
    fn sw_multi_index_commitment() {
        const L: usize = 10;

        let pp = get_parameters();
        let sk = SecretKey::new();
        let pk = sk.to_public_key();
        let multi_pp = MultiBasePublicParameters::new(L);
        let value_0 = Scalar::random(rand::thread_rng());

        let index_attributes = [
            (2, Scalar::random(rand::thread_rng())),
            (5, Scalar::random(rand::thread_rng())),
        ];

        let signatures: Vec<_> = index_attributes
            .iter()
            .map(|(idx, attribute)| {
                let (cm, o) = Commitment::index_commit(&value_0, *idx, attribute, &multi_pp);
                let sigma = sk.sign_pedersen_commitment(&cm, *idx);
                (cm, o, sigma)
            })
            .collect();
        let cm: Commitment = signatures.iter().map(|(cm, _, _)| cm).sum();
        let sigma: Signature = signatures.iter().map(|(_, _, sigma)| sigma).sum();

        let (h_1, h_2) = index_attributes.iter().map(|(idx, _)| *idx).fold(
            (G1Projective::identity(), G2Projective::identity()),
            |(h_1, h_2), idx| (h_1 + hash_usize_1(idx), h_2 + hash_usize_2(idx)),
        );

        assert_eq!(pairing(&sigma.0, pp.ghat), pairing(h_1 + cm.cm_1, &pk.0));
        assert_eq!(pairing(pp.g, &sigma.0), pairing(&pk.0, h_2 + cm.cm_2));
    }
}
