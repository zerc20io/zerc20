//! What a wallet derives from its 32-byte seed. The circuits accept any key and any burn salt; these are the
//! conventions that let a wallet restored from its seed find its notes and deposits again.
use crate::primitives::burn_address;
use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField, Zero};
use sha2::{Digest, Sha256};
use std::ops::RangeInclusive;

/// The first candidate that is a nonzero field element. A candidate is SHA-256 over `domain`, `fields` and a u32
/// big-endian counter from 0, each prefixed with its u32 big-endian length, with the top two bits cleared. It is taken
/// as is, never reduced, so about one in four is rejected.
#[expect(
    clippy::expect_used,
    reason = "three in four candidates pass, so one of 2^32 always does"
)]
fn derive(domain: &[u8], fields: &[&[u8]]) -> Fr {
    (0..=u32::MAX)
        .find_map(|counter| {
            let counter = counter.to_be_bytes();
            let mut h = Sha256::new();
            for f in [domain].iter().chain(fields).chain([&counter[..]].iter()) {
                h.update((f.len() as u32).to_be_bytes());
                h.update(f);
            }
            let mut d: [u8; 32] = h.finalize().into();
            d[0] &= 0x3f;
            let x = Fr::from_be_bytes_mod_order(&d);
            // canonical: reducing changed nothing
            (!x.is_zero() && x.into_bigint().to_bytes_be() == d).then_some(x)
        })
        .expect("a candidate passes")
}

/// The seed's spend secret (the circuits' `private_key`), one for every chain and token: `spend_secret_derivation` in
/// `test-vectors/circuit-vectors.json`.
pub fn spend_secret(seed: &[u8; 32]) -> Fr {
    derive(b"zerc20/keys/spend-secret/v1", &[seed])
}

/// The spend secret of a seed's `index`-th receive code for one chain and token: derived like [`spend_secret`] under
/// domain `zerc20/keys/code-spend-secret/v1` from `seed ‖ u64_be(chain_id) ‖ u32_be(token_id) ‖ u32_be(index)`.
/// A code hands its public key to the payer, so each code has its own and no two codes, nor a code and the
/// address's public key, can be linked by it.
pub fn code_spend_secret(seed: &[u8; 32], chain_id: u64, token_id: u32, index: u32) -> Fr {
    derive(
        b"zerc20/keys/code-spend-secret/v1",
        &[
            seed,
            &chain_id.to_be_bytes(),
            &token_id.to_be_bytes(),
            &index.to_be_bytes(),
        ],
    )
}

/// The `index`-th burn address of `public_key` on one chain and token, and its salt, if the salt's counter is in
/// `counters`.
///
/// The salt comes from `burn_key`: the wallet's own burn key, or a point of sale's. Both derive from the seed through
/// the view key, so the seed finds every address again. A salt needs no more protection than the view key gives: it
/// cannot spend anything, it only keeps others from linking the address to the public key.
///
/// Derivation: a start, derived like [`spend_secret`] under domain `zerc20/keys/burn-salt/v1` from
/// `burn_key ‖ u64_be(chain_id) ‖ u32_be(token_id) ‖ u32_be(index)`, then the salt `start + counter` for the first
/// counter whose burn digest has the proof of work (about 2^16 tries). Each try is one Poseidon hash, as it is for
/// anyone else searching. Searched in blocks of counters from 0, the result is the first block's hit, so blocks can be
/// searched in parallel.
pub fn derive_burn_address(
    burn_key: &[u8; 32],
    chain_id: u64,
    token_id: u32,
    index: u32,
    public_key: Fr,
    counters: RangeInclusive<u32>,
) -> Option<(Fr, Fr)> {
    let start = derive(
        b"zerc20/keys/burn-salt/v1",
        &[
            burn_key,
            &chain_id.to_be_bytes(),
            &token_id.to_be_bytes(),
            &index.to_be_bytes(),
        ],
    );
    let chain = Fr::from(chain_id);
    counters.into_iter().find_map(|counter| {
        let salt = start + Fr::from(counter);
        burn_address(chain, public_key, salt).map(|address| (salt, address))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::primitives::Keys;
    use ark_ff::MontFp;

    const ALL: RangeInclusive<u32> = 0..=u32::MAX;

    #[test]
    fn spend_secrets_match_the_vectors() {
        let v: serde_json::Value =
            serde_json::from_str(include_str!("../test-vectors/circuit-vectors.json")).unwrap();
        let cases = v["vectors"]["spend_secrets"].as_array().unwrap();
        assert!(
            cases.iter().any(|c| c["counter"] != 0),
            "no case needs a retry"
        );
        for c in cases {
            let dec = |k: &str| c[k].as_str().unwrap();
            let hex = dec("seed_hex");
            let seed: [u8; 32] =
                std::array::from_fn(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap());
            let sk = spend_secret(&seed);
            assert_eq!(sk.to_string(), dec("spend_secret"), "{}", c["name"]);
            assert_eq!(
                Keys::of(sk).public_key.to_string(),
                dec("public_key"),
                "{}",
                c["name"]
            );
        }
    }

    /// Pinned so that a change to the derivation, which would strand restored wallets' deposits, fails here.
    #[test]
    fn burn_addresses_are_stable() {
        let pk = Keys::of(spend_secret(&[7u8; 32])).public_key;
        let (salt, address) = derive_burn_address(&[9u8; 32], 1, 1, 0, pk, ALL).unwrap();
        assert_eq!(burn_address(Fr::from(1u64), pk, salt), Some(address));
        let pinned: (Fr, Fr) = (
            MontFp!(
                "20893846184009578192669090346967943966050224340320061993892750329206565895608"
            ),
            MontFp!("295177468225840628170542640476019746975487518238"),
        );
        assert_eq!((salt, address), pinned);
        assert_ne!(
            derive_burn_address(&[9u8; 32], 1, 1, 1, pk, ALL).unwrap().1,
            address
        );
        assert_ne!(
            derive_burn_address(&[9u8; 32], 1, 2, 0, pk, ALL).unwrap().1,
            address
        );
    }

    /// Searched in blocks, the address is the first block's that has one, the same as searched at once.
    #[test]
    fn burn_addresses_found_in_blocks_are_the_first() {
        let (key, pk) = ([7u8; 32], Fr::from(5u64));
        let mut blocks =
            (0u32..).map(|b| derive_burn_address(&key, 1, 1, 0, pk, b * 256..=b * 256 + 255));
        assert_eq!(
            blocks.find_map(|hit| hit),
            derive_burn_address(&key, 1, 1, 0, pk, ALL)
        );
    }

    /// Pinned like the burn addresses: a change would strand the notes paid to codes already handed out.
    #[test]
    fn code_spend_secrets_are_stable() {
        let seed = [7u8; 32];
        let sk = code_spend_secret(&seed, 1, 1, 0);
        assert_eq!(
            sk,
            MontFp!("796098259935533418586191825820630560305087870157112528974488438111747060064")
        );
        assert_ne!(sk, spend_secret(&seed));
        assert_ne!(sk, code_spend_secret(&seed, 1, 1, 1));
        assert_ne!(sk, code_spend_secret(&seed, 1, 2, 0));
    }
}
