use std::sync::OnceLock;

use bls12_381::{Bls12, G1Affine, G2Affine, Scalar};
use bls381_helpers::{hash_1, hash_2};
use group::ff::Field;
use pairing::Engine;
use rand::RngCore;
use serde::{Deserialize, Serialize};
use signature::{Signer, Verifier};

use crate::bls381_helpers::{hash_with_domain_separation_1, hash_with_domain_separation_2};

fn get_g() -> &'static G1Affine {
    static INSTANCE: OnceLock<G1Affine> = OnceLock::new();
    INSTANCE.get_or_init(|| hash_with_domain_separation_1(b"g", b"BLS-PP").into())
}

fn get_ghat() -> &'static G2Affine {
    static INSTANCE: OnceLock<G2Affine> = OnceLock::new();
    INSTANCE.get_or_init(|| hash_with_domain_separation_2(b"ghat", b"BLS-PP").into())
}

fn get_u() -> &'static G1Affine {
    static INSTANCE: OnceLock<G1Affine> = OnceLock::new();
    INSTANCE.get_or_init(|| hash_with_domain_separation_1(b"u", b"BLS-PP").into())
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecretKey {
    #[serde(with = "bls381_helpers")]
    sk: Scalar,
}

#[allow(clippy::new_without_default)]
impl SecretKey {
    pub fn new() -> Self {
        Self::new_from_rng(rand::thread_rng())
    }

    pub fn new_from_rng(rng: impl RngCore) -> Self {
        Self {
            sk: Scalar::random(rng),
        }
    }

    pub fn to_public_key(&self) -> PublicKey {
        PublicKey {
            pk_1: (get_g() * self.sk).into(),
            pk_2: (get_ghat() * self.sk).into(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PublicKey {
    #[serde(with = "bls381_helpers")]
    pk_1: G1Affine,
    #[serde(with = "bls381_helpers")]
    pk_2: G2Affine,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Signature {
    #[serde(with = "bls381_helpers")]
    sigma_1: G1Affine,
    #[serde(with = "bls381_helpers")]
    sigma_2: G2Affine,
}

impl Signer<Signature> for SecretKey {
    fn try_sign(&self, msg: &[u8]) -> Result<Signature, signature::Error> {
        Ok(Signature {
            sigma_1: (hash_1(msg) * self.sk).into(),
            sigma_2: (hash_2(msg) * self.sk).into(),
        })
    }
}

impl PublicKey {
    pub fn is_valid(&self) -> bool {
        Bls12::pairing(&self.pk_1, get_ghat()) == Bls12::pairing(get_g(), &self.pk_2)
    }
}

impl Verifier<Signature> for PublicKey {
    fn verify(&self, msg: &[u8], signature: &Signature) -> Result<(), signature::Error> {
        let lhs = Bls12::pairing(&hash_1(msg).into(), &self.pk_2);
        let rhs = Bls12::pairing(&signature.sigma_1, get_ghat());
        let lhsp = Bls12::pairing(&self.pk_1, &hash_2(msg).into());
        let rhsp = Bls12::pairing(get_g(), &signature.sigma_2);
        match (lhs == rhs, lhsp == rhsp) {
            (true, true) => Ok(()),
            _ => Err(signature::Error::new()),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn bls() {
        let sk = SecretKey::new();
        let pk = sk.to_public_key();
        assert!(pk.is_valid());

        let sig = sk.sign(b"test");
        assert!(pk.verify(b"test", &sig).is_ok());
    }
}
