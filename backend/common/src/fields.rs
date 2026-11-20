//! Commitments as the chain holds them (256-bit words) and as the circuits hash them (field elements).
use alloy::primitives::U256;
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::ark_ff::{BigInteger, PrimeField};
use zerc20_zkp::commitments::commitment_leaf;
use zerc20_zkp::primitives::hash_chain;

/// `Protocol.TRANSFER_TAG` and `Protocol.NOTE_HASH_TAG`: what a commitment is, in the high 32 bits of its `field0`,
/// above the token id.
pub const TRANSFER_TAG: u32 = 0xddf2_52ad;
pub const NOTE_HASH_TAG: u32 = 0x789f_26eb;

pub fn is_transfer(fields: &[U256; 4]) -> bool {
    fields[0] >> 32 == U256::from(TRANSFER_TAG)
}

pub fn is_note(fields: &[U256; 4]) -> bool {
    fields[0] >> 32 == U256::from(NOTE_HASH_TAG)
}

/// Field values from the ledger are canonical (< p), which `CommitmentLedger` enforces on commit.
pub fn fr(v: U256) -> Fr {
    Fr::from_be_bytes_mod_order(&v.to_be_bytes::<32>())
}

pub fn u256(f: Fr) -> U256 {
    U256::from_be_slice(&f.into_bigint().to_bytes_be())
}

/// A commitment's 4 fields from 128 bytes, as in `Committed` and the indexer's pages.
pub fn fields_of(b: &[u8]) -> [U256; 4] {
    std::array::from_fn(|i| U256::from_be_slice(&b[32 * i..32 * (i + 1)]))
}

/// A commitment's leaf in the commitment tree.
pub fn leaf(fields: &[U256; 4]) -> Fr {
    commitment_leaf(&fields.map(fr))
}

/// `CommitmentLedger` hash chain after appending `fields`.
pub fn next_hash_chain(prev: U256, fields: &[U256; 4]) -> U256 {
    u256(hash_chain(fr(prev), &fields.map(fr)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tags_are_the_protocols() {
        use alloy::primitives::keccak256;
        assert_eq!(
            TRANSFER_TAG.to_be_bytes(),
            keccak256("Transfer(address,address,uint256)")[..4]
        );
        assert_eq!(
            NOTE_HASH_TAG.to_be_bytes(),
            keccak256("NoteHash(uint256)")[..4]
        );
        let transfer = [
            U256::from(TRANSFER_TAG) << 32 | U256::from(7),
            U256::ZERO,
            U256::ZERO,
            U256::ZERO,
        ];
        let note = [
            U256::from(NOTE_HASH_TAG) << 32 | U256::from(7),
            U256::ZERO,
            U256::ZERO,
            U256::ZERO,
        ];
        assert!(is_transfer(&transfer) && !is_note(&transfer));
        assert!(is_note(&note) && !is_transfer(&note));
    }

    #[test]
    fn hash_chain_round_trips_through_u256() {
        // Ledger values: field0 = tag << 32 | token id, then addresses and an amount.
        let f = [
            U256::from(0xddf2_52ad_0000_0001_u64),
            U256::from(7),
            U256::from(8),
            U256::from(9),
        ];
        let c = next_hash_chain(U256::ZERO, &f);
        assert!(
            c < U256::from(1) << 248,
            "masked to 248 bits like Protocol.HASH_CHAIN_MASK"
        );
        assert_eq!(u256(fr(c)), c);
        let bytes: Vec<u8> = f.iter().flat_map(|w| w.to_be_bytes::<32>()).collect();
        assert_eq!(fields_of(&bytes), f);
    }
}
