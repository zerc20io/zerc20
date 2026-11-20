//! Spend authorization: the owner's Schnorr signature over Baby-JubJub (`ark-ed-on-bn254`, whose base field is BN254's
//! scalar field). A note's public key commits to the hash of the key that signs ([`primitives::public_key`]), so the
//! merge prover, which opens merge inputs to prove them, and the attester, which opens them to check them, learn the
//! signing key and the nullifying key but not the private key: they can spend nothing its owner did not sign.
//! JoinSplit and rage exit, which the wallet proves itself, open the private key instead and check no signature.
//!
//! A signature on `message` under `auth_key` is `(R, s)` with `s·G = R + c·auth_key`, where
//! `c = DomainHash4(SPEND_AUTH, R.x, R.y, auth_key_hash, message)` is taken as an integer below `p`. The merge step
//! checks it in-circuit ([`verify_var`]), the attester natively ([`verify`]).
//!
//! [`primitives::public_key`]: crate::primitives::public_key

use std::sync::LazyLock;

use ark_bn254::Fr;
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ed_on_bn254::{EdwardsAffine, EdwardsProjective, Fr as Scalar, constraints::EdwardsVar};
use ark_ff::{AdditiveGroup, BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::AllocVar, boolean::Boolean, convert::ToBitsGadget, eq::EqGadget, fields::fp::FpVar,
    groups::CurveVar,
};
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};
use sha2::{Digest, Sha512};

use crate::poseidon::{POSEIDON3, POSEIDON5, POSEIDON6};
use crate::primitives::{
    DOMAIN_AUTH_KEY, DOMAIN_MERGE_AUTH, DOMAIN_SPEND_AUTH, DOMAIN_TRANSACT_AUTH, domain_hash,
    domain_hash_var,
};

pub use ark_ed_on_bn254::Fr as AuthSecret;

/// A signing key's public half.
pub type AuthKey = EdwardsAffine;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Signature {
    pub r: EdwardsAffine,
    pub s: Scalar,
}

/// SHA-512 over `domain` and `fields`, each prefixed with its u32 big-endian length, reduced mod the group order: wide
/// enough that the reduction leaves no usable bias.
fn hash_to_scalar(domain: &[u8], fields: &[&[u8]]) -> Scalar {
    let mut h = Sha512::new();
    for f in [domain].iter().chain(fields) {
        h.update((f.len() as u32).to_be_bytes());
        h.update(f);
    }
    Scalar::from_be_bytes_mod_order(&h.finalize())
}

fn be(f: Fr) -> Vec<u8> {
    f.into_bigint().to_bytes_be()
}

/// The signing secret a private key derives, under domain `zerc20/keys/auth-secret/v1`. Zero has probability 2^-251.
pub fn secret_of(private_key: Fr) -> AuthSecret {
    hash_to_scalar(b"zerc20/keys/auth-secret/v1", &[&be(private_key)])
}

pub fn auth_key(secret: AuthSecret) -> AuthKey {
    (EdwardsProjective::generator() * secret).into_affine()
}

pub fn auth_key_hash(key: &AuthKey) -> Fr {
    domain_hash(&POSEIDON3, DOMAIN_AUTH_KEY, &[key.x, key.y])
}

fn challenge(r: &EdwardsAffine, auth_key_hash: Fr, message: Fr) -> Fr {
    domain_hash(
        &POSEIDON5,
        DOMAIN_SPEND_AUTH,
        &[r.x, r.y, auth_key_hash, message],
    )
}

/// Deterministic: the nonce is a hash of the secret and the message, so the wallet needs no randomness, and two
/// messages never share a nonce.
pub fn sign(secret: AuthSecret, message: Fr) -> Signature {
    let nonce = hash_to_scalar(
        b"zerc20/auth/nonce/v1",
        &[&secret.into_bigint().to_bytes_be(), &be(message)],
    );
    let r = auth_key(nonce);
    let c = challenge(&r, auth_key_hash(&auth_key(secret)), message);
    Signature {
        r,
        s: nonce + Scalar::from_be_bytes_mod_order(&be(c)) * secret,
    }
}

/// Whether `signature` signs `message` under `key`. A key or a nonce point off the curve or outside the prime-order
/// subgroup fails, and so does the identity key, under which anyone could sign.
pub fn verify(key: &AuthKey, message: Fr, signature: &Signature) -> bool {
    let valid = |p: &EdwardsAffine| p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve();
    if !valid(key) || key.is_zero() || !valid(&signature.r) {
        return false;
    }
    let c = challenge(&signature.r, auth_key_hash(key), message);
    EdwardsProjective::generator() * signature.s == key.mul_bigint(c.into_bigint()) + signature.r
}

/// What the owner of a transact's inputs signs: its statement's EIP-712 struct hash, which the attester signs too.
pub fn transact_message(struct_hash: [u8; 32]) -> Fr {
    let (hi, lo) = struct_hash.split_at(16);
    domain_hash(
        &POSEIDON3,
        DOMAIN_TRANSACT_AUTH,
        &[
            Fr::from_be_bytes_mod_order(hi),
            Fr::from_be_bytes_mod_order(lo),
        ],
    )
}

/// What the owner of every merge input signs: the merge's nullifiers (as the contract chains them), the output note's
/// owner and salt, and the fee. The roots are left out, so a merge proved again over a newer root needs no new
/// signature.
pub fn merge_message(
    nullifier_chain: Fr,
    out_public_key: Fr,
    out_salt: Fr,
    fee: Fr,
    fee_recipient: Fr,
) -> Fr {
    domain_hash(
        &POSEIDON6,
        DOMAIN_MERGE_AUTH,
        &[
            nullifier_chain,
            out_public_key,
            out_salt,
            fee,
            fee_recipient,
        ],
    )
}

// ---- in-circuit counterparts ----

pub(crate) fn auth_key_hash_var(key: &EdwardsVar) -> Result<FpVar<Fr>, SynthesisError> {
    domain_hash_var(&POSEIDON3, DOMAIN_AUTH_KEY, &[key.x.clone(), key.y.clone()])
}

pub(crate) fn merge_message_var(
    nullifier_chain: &FpVar<Fr>,
    out_public_key: &FpVar<Fr>,
    out_salt: &FpVar<Fr>,
    fee: &FpVar<Fr>,
    fee_recipient: &FpVar<Fr>,
) -> Result<FpVar<Fr>, SynthesisError> {
    let values = [
        nullifier_chain,
        out_public_key,
        out_salt,
        fee,
        fee_recipient,
    ]
    .map(Clone::clone);
    domain_hash_var(&POSEIDON6, DOMAIN_MERGE_AUTH, &values)
}

/// `2^i·G` for every bit of a scalar.
static GENERATOR_POWERS: LazyLock<Vec<EdwardsProjective>> = LazyLock::new(|| {
    std::iter::successors(Some(EdwardsProjective::generator()), |g| Some(g.double()))
        .take(Scalar::MODULUS_BIT_SIZE as usize)
        .collect()
});

/// Enforces [`verify`]. `key` is allocated as a witness, which puts it in the prime-order subgroup; so is `R`. `s` may
/// be at or above the group order, which only gives another encoding of the same signature.
pub(crate) fn verify_var(
    cs: ConstraintSystemRef<Fr>,
    key: &EdwardsVar,
    key_hash: &FpVar<Fr>,
    message: &FpVar<Fr>,
    signature: &Signature,
) -> Result<(), SynthesisError> {
    key.is_zero()?.enforce_equal(&Boolean::FALSE)?;
    let r = EdwardsVar::new_witness(cs.clone(), || Ok(signature.r))?;
    let s_bits = signature.s.into_bigint().to_bits_le();
    let s = Vec::<Boolean<Fr>>::new_witness(cs, || {
        Ok(s_bits[..Scalar::MODULUS_BIT_SIZE as usize].to_vec())
    })?;
    let c = domain_hash_var(
        &POSEIDON5,
        DOMAIN_SPEND_AUTH,
        &[r.x.clone(), r.y.clone(), key_hash.clone(), message.clone()],
    )?;
    let mut s_g = EdwardsVar::zero();
    s_g.precomputed_base_scalar_mul_le(s.iter().zip(GENERATOR_POWERS.iter()))?;
    (key.scalar_mul_le(c.to_bits_le()?.iter())? + &r).enforce_equal(&s_g)
}

#[cfg(test)]
mod tests {
    use ark_r1cs_std::GR1CSVar;
    use ark_relations::gr1cs::ConstraintSystem;

    use super::*;

    fn fr(v: u64) -> Fr {
        Fr::from(v)
    }

    fn vectors() -> serde_json::Value {
        serde_json::from_str::<serde_json::Value>(include_str!(
            "../test-vectors/circuit-vectors.json"
        ))
        .unwrap()["vectors"]
            .clone()
    }

    fn dec(v: &serde_json::Value) -> Fr {
        v.as_str().unwrap().parse().unwrap()
    }

    #[test]
    fn keys_and_signatures_match_the_vectors() {
        let v = vectors();
        for k in v["keys"].as_array().unwrap() {
            let keys = crate::primitives::Keys::of(dec(&k["private_key"]));
            let secret: AuthSecret = k["auth_secret"].as_str().unwrap().parse().unwrap();
            assert_eq!(keys.auth_secret, secret);
            assert_eq!(
                (keys.auth_key.x, keys.auth_key.y),
                (dec(&k["auth_key"][0]), dec(&k["auth_key"][1]))
            );
            assert_eq!(keys.auth_key_hash(), dec(&k["auth_key_hash"]));
            assert_eq!(keys.public_key, dec(&k["public_key"]));
        }
        for c in v["signatures"].as_array().unwrap() {
            let secret = secret_of(dec(&c["private_key"]));
            let sig = sign(secret, dec(&c["message"]));
            assert_eq!((sig.r.x, sig.r.y), (dec(&c["r"][0]), dec(&c["r"][1])));
            assert_eq!(sig.s, c["s"].as_str().unwrap().parse().unwrap());
            assert!(verify(&auth_key(secret), dec(&c["message"]), &sig));
        }
        for m in v["auth_messages"]["transact"].as_array().unwrap() {
            let hex = m["struct_hash"].as_str().unwrap().trim_start_matches("0x");
            let hash: [u8; 32] =
                std::array::from_fn(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap());
            assert_eq!(transact_message(hash), dec(&m["message"]));
        }
        for m in v["auth_messages"]["merge"].as_array().unwrap() {
            let f = |k: &str| dec(&m[k]);
            assert_eq!(
                merge_message(
                    f("nullifier_chain"),
                    f("out_public_key"),
                    f("out_salt"),
                    f("fee"),
                    f("fee_recipient")
                ),
                f("message")
            );
        }
    }

    #[test]
    fn the_generator_has_prime_order() {
        let g = EdwardsAffine::generator();
        assert!(g.is_in_correct_subgroup_assuming_on_curve() && !g.is_zero());
    }

    #[test]
    fn signatures_verify_for_their_message_and_key_only() {
        let secret = secret_of(fr(42));
        let key = auth_key(secret);
        let sig = sign(secret, fr(7));
        assert!(verify(&key, fr(7), &sig));
        assert!(!verify(&key, fr(8), &sig));
        assert!(!verify(&auth_key(secret_of(fr(43))), fr(7), &sig));
        let other_s = Signature {
            s: sig.s + Scalar::from(1u64),
            ..sig
        };
        assert!(!verify(&key, fr(7), &other_s));
        // the identity key, and a nonce point outside the subgroup
        let zero = AuthKey::zero();
        let forged = Signature {
            r: EdwardsAffine::generator(),
            s: Scalar::from(1u64),
        };
        assert!(!verify(&zero, fr(7), &forged));
        let low = EdwardsAffine::new_unchecked(Fr::from(0u64), -Fr::from(1u64));
        assert!(!verify(
            &key,
            fr(7),
            &Signature {
                r: (sig.r + low).into_affine(),
                ..sig
            }
        ));
    }

    fn check_var(key: AuthKey, message: Fr, sig: &Signature) -> bool {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let k = EdwardsVar::new_witness(cs.clone(), || Ok(key)).unwrap();
        let h = auth_key_hash_var(&k).unwrap();
        assert_eq!(h.value().unwrap(), auth_key_hash(&key));
        let m = FpVar::new_witness(cs.clone(), || Ok(message)).unwrap();
        verify_var(cs.clone(), &k, &h, &m, sig).unwrap();
        cs.is_satisfied().unwrap()
    }

    #[test]
    fn the_circuit_agrees_with_verify() {
        let secret = secret_of(fr(42));
        let key = auth_key(secret);
        let sig = sign(secret, fr(7));
        assert!(check_var(key, fr(7), &sig));
        assert!(!check_var(key, fr(8), &sig));
        assert!(!check_var(auth_key(secret_of(fr(43))), fr(7), &sig));
        assert!(!check_var(
            AuthKey::zero(),
            fr(7),
            &Signature {
                r: EdwardsAffine::generator(),
                s: Scalar::from(1u64)
            }
        ));
    }
}
