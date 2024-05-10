use std::{
    iter::Sum,
    ops::{Add, Mul, Sub},
};

use bls12_381::{Bls12, G1Projective, G2Projective, Scalar};
use group::ff::Field;
use pairing::Engine;
use rand::{thread_rng, RngCore};
use serde::{Deserialize, Serialize};
use signature::{Signer, Verifier};

use crate::{
    bls381_helpers::{self, hash_1, hash_2, hash_to_scalar, hash_usize_1, hash_usize_2, pairing},
    lagrange::Lagrange,
    pedersen::{get_g, get_ghat, get_u, get_uhat, Commitment},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecretKey {
    #[serde(with = "bls381_helpers")]
    pub(crate) sk: Scalar,
}

#[allow(clippy::new_without_default)]
impl SecretKey {
    pub fn new() -> Self {
        Self::new_from_rng(thread_rng())
    }

    pub fn into_shares(&self, num_shares: usize, t: usize) -> Vec<SecretKey> {
        let mut rng = thread_rng();
        let mut sks: Vec<_> = (0..t - 1).map(|_| Scalar::random(&mut rng)).collect();

        let mut base_points: Vec<_> = (1..=t - 1).map(|i| Scalar::from(i as u64)).collect();
        base_points.push(Scalar::from(t as u64));

        for _ in (t - 1)..num_shares {
            let lagrange = Lagrange::new(&base_points);

            let base = self.sk
                - sks
                    .iter()
                    .take(t - 1)
                    .enumerate()
                    .map(|(j, sk)| sk * lagrange.eval_j_0(j))
                    .sum::<Scalar>();

            sks.push(base * lagrange.eval_j_0(t - 1).invert().unwrap());
            base_points[t - 1] += Scalar::ONE;
        }
        sks.into_iter().map(|sk| SecretKey { sk }).collect()
    }

    pub fn new_from_rng(rng: impl RngCore) -> Self {
        Self {
            sk: Scalar::random(rng),
        }
    }

    pub fn to_public_key(&self) -> PublicKey {
        PublicKey {
            pk_1: (get_g() * self.sk),
            pk_2: (get_ghat() * self.sk),
        }
    }

    pub fn sign_pedersen_commitment(&self, commitment: &Commitment, index: usize) -> Signature {
        let hi_1 = hash_usize_1(index);
        let hi_2 = hash_usize_2(index);

        Signature {
            sigma_1: (commitment.cm_1 + hi_1) * self.sk,
            sigma_2: (commitment.cm_2 + hi_2) * self.sk,
        }
    }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct PublicKey {
    #[serde(with = "bls381_helpers")]
    pub(crate) pk_1: G1Projective,
    #[serde(with = "bls381_helpers")]
    pub(crate) pk_2: G2Projective,
}

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
    ) -> Result<(), signature::Error> {
        let hi_1 = hash_usize_1(index);
        let lhs = pairing(hi_1 + commitment.cm_1, self.pk_2);
        let rhs = pairing(signature.sigma_1, get_ghat());
        if lhs != rhs {
            return Err(signature::Error::new());
        }

        let hi_2 = hash_usize_2(index);
        let lhs = pairing(self.pk_1, hi_2 + commitment.cm_2);
        let rhs = pairing(get_g(), signature.sigma_2);
        match lhs == rhs {
            true => Ok(()),
            false => Err(signature::Error::new()),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Signature {
    #[serde(with = "bls381_helpers")]
    pub(crate) sigma_1: G1Projective,
    #[serde(with = "bls381_helpers")]
    pub(crate) sigma_2: G2Projective,
}

impl Signature {
    pub fn from_shares(signatures: &[Signature], lagrange: &Lagrange) -> Signature {
        signatures
            .iter()
            .enumerate()
            .map(|(j, sig)| sig * lagrange.eval_j_0(j))
            .sum()
    }
}

impl<'a> FromIterator<&'a Signature> for Signature {
    fn from_iter<T: IntoIterator<Item = &'a Signature>>(iter: T) -> Self {
        let (sigma_1, sigma_2) = iter.into_iter().fold(
            (G1Projective::identity(), G2Projective::identity()),
            |(acc_1, acc_2), sigma| (acc_1 + sigma.sigma_1, acc_2 + sigma.sigma_2),
        );
        Signature { sigma_1, sigma_2 }
    }
}

impl Signer<Signature> for SecretKey {
    fn try_sign(&self, msg: &[u8]) -> Result<Signature, signature::Error> {
        let m = hash_to_scalar(msg);
        Ok(Signature {
            sigma_1: ((hash_1(msg) + get_u() * m) * self.sk),
            sigma_2: ((hash_2(msg) + get_uhat() * m) * self.sk),
        })
    }
}

impl PublicKey {
    pub fn is_valid(&self) -> bool {
        Bls12::pairing(&self.pk_1.into(), &get_ghat().into())
            == Bls12::pairing(&get_g().into(), &self.pk_2.into())
    }
}

impl Verifier<Signature> for PublicKey {
    fn verify(&self, msg: &[u8], signature: &Signature) -> Result<(), signature::Error> {
        let m = hash_to_scalar(msg);
        let lhs = Bls12::pairing(&(hash_1(msg) + get_u() * m).into(), &self.pk_2.into());
        let rhs = Bls12::pairing(&signature.sigma_1.into(), &get_ghat().into());
        let lhsp = Bls12::pairing(&self.pk_1.into(), &(hash_2(msg) + get_uhat() * m).into());
        let rhsp = Bls12::pairing(&get_g().into(), &signature.sigma_2.into());
        match (lhs == rhs, lhsp == rhsp) {
            (true, true) => Ok(()),
            _ => Err(signature::Error::new()),
        }
    }
}

impl Mul<Scalar> for &PublicKey {
    type Output = PublicKey;

    fn mul(self, rhs: Scalar) -> Self::Output {
        PublicKey {
            pk_1: (self.pk_1 * rhs),
            pk_2: (self.pk_2 * rhs),
        }
    }
}

impl Mul<Scalar> for PublicKey {
    type Output = PublicKey;

    fn mul(self, rhs: Scalar) -> Self::Output {
        PublicKey {
            pk_1: (self.pk_1 * rhs),
            pk_2: (self.pk_2 * rhs),
        }
    }
}

impl Add<&PublicKey> for PublicKey {
    type Output = PublicKey;

    fn add(self, rhs: &PublicKey) -> Self::Output {
        PublicKey {
            pk_1: self.pk_1 + rhs.pk_1,
            pk_2: self.pk_2 + rhs.pk_2,
        }
    }
}

impl Add<&PublicKey> for &PublicKey {
    type Output = PublicKey;

    fn add(self, rhs: &PublicKey) -> Self::Output {
        PublicKey {
            pk_1: self.pk_1 + rhs.pk_1,
            pk_2: self.pk_2 + rhs.pk_2,
        }
    }
}

impl Sub<&PublicKey> for &PublicKey {
    type Output = PublicKey;

    fn sub(self, rhs: &PublicKey) -> Self::Output {
        PublicKey {
            pk_1: self.pk_1 - rhs.pk_1,
            pk_2: self.pk_2 - rhs.pk_2,
        }
    }
}

impl<'a> Sum<&'a PublicKey> for PublicKey {
    fn sum<I: Iterator<Item = &'a PublicKey>>(iter: I) -> Self {
        let (pk_1, pk_2) = iter.fold(
            (G1Projective::identity(), G2Projective::identity()),
            |(acc_1, acc_2), pk| (acc_1 + pk.pk_1, acc_2 + pk.pk_2),
        );

        PublicKey { pk_1, pk_2 }
    }
}

impl Sum<PublicKey> for PublicKey {
    fn sum<I: Iterator<Item = PublicKey>>(iter: I) -> Self {
        let mut pk_1 = G1Projective::identity();
        let mut pk_2 = G2Projective::identity();

        iter.for_each(|pk| {
            pk_1 = pk.pk_1 + pk_1;
            pk_2 = pk.pk_2 + pk_2;
        });

        PublicKey { pk_1, pk_2 }
    }
}

// this is abuse of notation
impl Sub<&PublicKey> for Signature {
    type Output = Signature;

    fn sub(self, rhs: &PublicKey) -> Self::Output {
        Signature {
            sigma_1: self.sigma_1 - rhs.pk_1,
            sigma_2: self.sigma_2 - rhs.pk_2,
        }
    }
}

impl Add<&PublicKey> for &Signature {
    type Output = Signature;

    fn add(self, rhs: &PublicKey) -> Self::Output {
        Signature {
            sigma_1: self.sigma_1 + rhs.pk_1,
            sigma_2: self.sigma_2 + rhs.pk_2,
        }
    }
}

impl Mul<Scalar> for Signature {
    type Output = Signature;

    fn mul(self, rhs: Scalar) -> Self::Output {
        Signature {
            sigma_1: self.sigma_1 * rhs,
            sigma_2: self.sigma_2 * rhs,
        }
    }
}

impl Mul<&Scalar> for Signature {
    type Output = Signature;

    fn mul(self, rhs: &Scalar) -> Self::Output {
        Signature {
            sigma_1: self.sigma_1 * rhs,
            sigma_2: self.sigma_2 * rhs,
        }
    }
}

impl Mul<Scalar> for &Signature {
    type Output = Signature;

    fn mul(self, rhs: Scalar) -> Self::Output {
        Signature {
            sigma_1: self.sigma_1 * rhs,
            sigma_2: self.sigma_2 * rhs,
        }
    }
}

impl Mul<&Scalar> for &Signature {
    type Output = Signature;

    fn mul(self, rhs: &Scalar) -> Self::Output {
        Signature {
            sigma_1: self.sigma_1 * rhs,
            sigma_2: self.sigma_2 * rhs,
        }
    }
}

impl Sum for Signature {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let (sigma_1, sigma_2) = iter.fold(
            (G1Projective::identity(), G2Projective::identity()),
            |(sigma_1, sigma_2), sigma| (sigma_1 + sigma.sigma_1, sigma_2 + sigma.sigma_2),
        );

        Signature { sigma_1, sigma_2 }
    }
}

impl<'a> Sum<&'a Signature> for Signature {
    fn sum<I: Iterator<Item = &'a Signature>>(iter: I) -> Self {
        let (sigma_1, sigma_2) = iter.fold(
            (G1Projective::identity(), G2Projective::identity()),
            |(sigma_1, sigma_2), sigma| (sigma_1 + sigma.sigma_1, sigma_2 + sigma.sigma_2),
        );

        Signature { sigma_1, sigma_2 }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn sw() {
        let sk = SecretKey::new();
        let pk = sk.to_public_key();
        assert!(pk.is_valid());

        let sig = sk.sign(b"test");
        assert!(pk.verify(b"test", &sig).is_ok());
    }

    #[test]
    fn tsw() {
        let n = 10;
        let t = n / 2 + 1;

        let sk = SecretKey::new();
        let sks = sk.into_shares(n, t);
        let sigs: Vec<_> = sks.iter().map(|sk| sk.sign(b"test")).collect();

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
        assert!(pk.verify(b"test", &sig).is_ok());

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
        assert!(pk.verify(b"test", &sig).is_ok());

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
        assert!(pk.verify(b"test", &sig).is_ok());
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
}
