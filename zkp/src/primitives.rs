//! The protocol's keys, nullifiers, note hashes and burn addresses (`circom/lib/primitives.circom`), and the SHA-256
//! hash chain the contracts recompute over commitments and nullifiers. Both step circuits, the wallet and the backend
//! compute them the same way.

use std::iter;

use ark_bn254::Fr;
use ark_crypto_primitives::crh::sha256::constraints::Sha256Gadget;
use ark_ff::{BigInteger, MontFp, PrimeField};
use ark_r1cs_std::{
    boolean::Boolean, convert::ToBitsGadget, convert::ToBytesGadget, eq::EqGadget,
    fields::FieldVar, fields::fp::FpVar, uint8::UInt8,
};
use ark_relations::gr1cs::SynthesisError;
use sha2::{Digest, Sha256};

use crate::auth::{self, AuthKey, AuthSecret};
use crate::poseidon::{self, POSEIDON2, POSEIDON3, POSEIDON5, POSEIDON6, Poseidon};

// Protocol constants, mirrored from `circom/lib/constants.circom`.
pub(crate) const AMOUNT_BITS: usize = 248;
pub(crate) const ADDRESS_BITS: usize = 160;
pub(crate) const TOKEN_ID_BITS: usize = 32;
pub(crate) const CHAIN_ID_BITS: usize = 64;
pub(crate) const BURN_POW_BITS: usize = 16;
pub(crate) const FIELD_BIT_LENGTH: usize = 254;

pub(crate) const TRANSFER_FIELD0_BASE: Fr = MontFp!("15992936129728872448");
pub(crate) const NOTE_FIELD0_BASE: Fr = MontFp!("8691708596607516672");
pub(crate) const DOMAIN_NOTE: Fr =
    MontFp!("12890024175661825764581542883111592339070511154523346722771315793398079606973");
pub(crate) const DOMAIN_PUBLIC_KEY: Fr =
    MontFp!("12748143626193170683619257575461114475162050184551511165632901980951779591788");
pub(crate) const DOMAIN_NULLIFYING_KEY: Fr =
    MontFp!("17471194487513808174444331798961284844045019683771872456746961298409210755086");
pub(crate) const DOMAIN_NULLIFIER: Fr =
    MontFp!("21656625071485835455144987912439041855442440977080724417184138235324194035747");
pub(crate) const DOMAIN_DUMMY_NULLIFIER: Fr =
    MontFp!("7044432322484129783600934309074221576946257299516531409248588859126398254720");
pub(crate) const DOMAIN_BURN: Fr =
    MontFp!("7812678369084671832725575743163273348609229243038681297431930412876960276650");
pub(crate) const DOMAIN_ASP_LEAF: Fr =
    MontFp!("20989222074995585771835793404421254795991252548608321040973959344582939809523");
pub(crate) const DOMAIN_AUTH_KEY: Fr =
    MontFp!("10225447400557743590985446737842398671604622534850121808755795315749324473275");
pub(crate) const DOMAIN_SPEND_AUTH: Fr =
    MontFp!("8230886534581055996046092392097874170742872724656370212214393322619803652446");
pub(crate) const DOMAIN_TRANSACT_AUTH: Fr =
    MontFp!("13562453510417820550960573109771867520359186262900151110365996214945948233794");
pub(crate) const DOMAIN_MERGE_AUTH: Fr =
    MontFp!("16474997453874937243622623791033663138618536810477243309426195930856928586225");

pub(crate) fn domain_hash<const T: usize>(p: &Poseidon<T>, domain: Fr, values: &[Fr]) -> Fr {
    poseidon::hash(p, &[&[domain], values].concat())
}

/// The owner a note commits to: the hash of the key that signs its merges ([`crate::auth`]) and of its nullifying key.
/// JoinSplit and rage exit open the nullifying key from the private key instead, so only its holder spends there.
pub fn public_key(auth_key_hash: Fr, nullifying_key: Fr) -> Fr {
    domain_hash(
        &POSEIDON3,
        DOMAIN_PUBLIC_KEY,
        &[auth_key_hash, nullifying_key],
    )
}

pub fn nullifying_key(private_key: Fr) -> Fr {
    domain_hash(&POSEIDON2, DOMAIN_NULLIFYING_KEY, &[private_key])
}

/// What a private key derives: the signing secret (by the wallets' convention, [`auth::secret_of`]) and key, the
/// nullifying key, and the public key.
#[derive(Clone, Copy, Debug)]
pub struct Keys {
    pub private_key: Fr,
    pub auth_secret: AuthSecret,
    pub auth_key: AuthKey,
    pub nullifying_key: Fr,
    pub public_key: Fr,
}

impl Keys {
    pub fn of(private_key: Fr) -> Self {
        let auth_secret = auth::secret_of(private_key);
        let auth_key = auth::auth_key(auth_secret);
        let nullifying_key = nullifying_key(private_key);
        Keys {
            private_key,
            auth_secret,
            auth_key,
            nullifying_key,
            public_key: public_key(auth::auth_key_hash(&auth_key), nullifying_key),
        }
    }

    pub fn auth_key_hash(&self) -> Fr {
        auth::auth_key_hash(&self.auth_key)
    }
}

pub fn nullifier(chain_id: Fr, commitment_index: Fr, nullifying_key: Fr) -> Fr {
    let values = [chain_id, commitment_index, nullifying_key, Fr::from(0u64)];
    domain_hash(&POSEIDON5, DOMAIN_NULLIFIER, &values)
}

/// JoinSplit's padding nullifier for in1 (`DummyNullifier(1)`): `entropy + 1`
/// keeps it apart from a slot-0 dummy over the same entropy.
pub fn dummy_nullifier(chain_id: Fr, entropy: Fr) -> Fr {
    domain_hash(
        &POSEIDON3,
        DOMAIN_DUMMY_NULLIFIER,
        &[chain_id, entropy + Fr::from(1u64)],
    )
}

pub fn note_hash(chain_id: Fr, public_key: Fr, value: Fr, token_id: Fr, note_salt: Fr) -> Fr {
    let values = [chain_id, public_key, value, token_id, note_salt];
    domain_hash(&POSEIDON6, DOMAIN_NOTE, &values)
}

pub fn burn_digest(chain_id: Fr, public_key: Fr, burn_salt: Fr) -> Fr {
    let values = [chain_id, public_key, burn_salt, Fr::from(0u64)];
    domain_hash(&POSEIDON5, DOMAIN_BURN, &values)
}

/// The low `ADDRESS_BITS` of a burn digest.
pub(crate) fn digest_address(digest: Fr) -> Fr {
    Fr::from_le_bytes_mod_order(&digest.into_bigint().to_bytes_le()[..ADDRESS_BITS / 8])
}

/// The burn address of `(public_key, burn_salt)`, or `None` when the salt
/// misses the proof-of-work window (top `BURN_POW_BITS` of the digest zero).
pub fn burn_address(chain_id: Fr, public_key: Fr, burn_salt: Fr) -> Option<Fr> {
    let digest = burn_digest(chain_id, public_key, burn_salt);
    let pow_ok = digest.into_bigint().num_bits() as usize <= FIELD_BIT_LENGTH - BURN_POW_BITS;
    pow_ok.then(|| digest_address(digest))
}

/// `SHA256(prev || values) mod 2^248` over 32-byte big-endian words.
pub fn hash_chain(prev: Fr, values: &[Fr]) -> Fr {
    let mut hasher = Sha256::new();
    for value in iter::once(&prev).chain(values) {
        hasher.update(value.into_bigint().to_bytes_be());
    }
    Fr::from_be_bytes_mod_order(&hasher.finalize()[1..])
}

/// The chain of nullifiers that `Verifier.merge` computes and a merge's signature covers: [`hash_chain`] over each in
/// turn, from zero.
pub fn nullifier_chain(nullifiers: &[Fr]) -> Fr {
    nullifiers
        .iter()
        .fold(Fr::from(0u64), |chain, n| hash_chain(chain, &[*n]))
}

// ---- in-circuit counterparts ----

pub(crate) fn domain_hash_var<const T: usize>(
    p: &Poseidon<T>,
    domain: Fr,
    values: &[FpVar<Fr>],
) -> Result<FpVar<Fr>, SynthesisError> {
    poseidon::hash_var(p, &[&[FpVar::constant(domain)], values].concat())
}

pub(crate) fn note_hash_var(
    chain_id: &FpVar<Fr>,
    public_key: &FpVar<Fr>,
    value: &FpVar<Fr>,
    token_id: &FpVar<Fr>,
    note_salt: &FpVar<Fr>,
) -> Result<FpVar<Fr>, SynthesisError> {
    let values = [chain_id, public_key, value, token_id, note_salt].map(Clone::clone);
    domain_hash_var(&POSEIDON6, DOMAIN_NOTE, &values)
}

/// In-circuit counterpart of [`hash_chain`], which also enforces `prev < 2^248`.
pub(crate) fn hash_chain_var(
    prev: &FpVar<Fr>,
    values: &[FpVar<Fr>],
) -> Result<FpVar<Fr>, SynthesisError> {
    let mut input = Vec::with_capacity(32 * (1 + values.len()));
    for value in iter::once(prev).chain(values) {
        input.extend(value.to_bytes_le()?.into_iter().rev());
    }
    // prev < 2^248
    input[0].enforce_equal(&UInt8::constant(0))?;
    let digest = Sha256Gadget::digest(&input)?.0;
    let mut bits = Vec::with_capacity(248);
    for byte in digest[1..].iter().rev() {
        bits.extend(byte.to_bits_le()?);
    }
    Boolean::le_bits_to_fp(&bits)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fr(value: u64) -> Fr {
        Fr::from(value)
    }

    /// Values from `test-vectors/circuit-vectors.json`.
    #[test]
    fn primitives_match_circuit_vectors() {
        let pk: Fr =
            MontFp!("7144445268846560219109954919155704812968216008557741564245573277978554282524");
        let nk: Fr = MontFp!(
            "20982080707200587550847820511444872038547186978067397706303861926927192317571"
        );
        let keys = Keys::of(fr(42));
        assert_eq!(keys.public_key, pk);
        assert_eq!(keys.nullifying_key, nk);
        assert_eq!(
            keys.auth_key_hash(),
            MontFp!(
                "17681195958231059701268167412646292838960155012585722262908631477582403623144"
            )
        );
        assert_eq!(
            nullifier(fr(1), fr(1), nk),
            MontFp!(
                "17369299682365079466576940889940364394931367666048606068755860676128352680891"
            )
        );
        assert_eq!(
            dummy_nullifier(fr(1), fr(7777)),
            MontFp!(
                "10218035695484108171515221773315210087461494073680636701549577540083200890485"
            )
        );
        assert_eq!(
            note_hash(fr(1), pk, fr(1000), fr(1), fr(12345)),
            MontFp!(
                "21764968254724380195488301001684461380128384636375173342666080817419775315821"
            )
        );
        assert_eq!(
            burn_address(fr(1), pk, fr(2279)),
            Some(MontFp!("860193518660019323525381833616338350425480191313"))
        );
        assert_eq!(burn_address(fr(1), pk, fr(1)), None);
    }
}
