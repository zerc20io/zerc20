//! The leaves of the commitment and ASP trees (`circom/lib/commitments.circom`).

use ark_bn254::Fr;

use crate::{
    poseidon::{self, POSEIDON2, POSEIDON4},
    primitives::{DOMAIN_ASP_LEAF, NOTE_FIELD0_BASE, TRANSFER_FIELD0_BASE, domain_hash},
};

pub const COMMITMENT_FIELDS: usize = 4;

/// The leaf of a commitment's `fields` as the ledger records them.
pub fn commitment_leaf(fields: &[Fr; COMMITMENT_FIELDS]) -> Fr {
    poseidon::hash(&POSEIDON4, fields)
}

pub fn note_leaf(token_id: Fr, note_hash: Fr) -> Fr {
    let zero = Fr::from(0u64);
    commitment_leaf(&[NOTE_FIELD0_BASE + token_id, note_hash, zero, zero])
}

pub fn transfer_leaf(token_id: Fr, from: Fr, to: Fr, value: Fr) -> Fr {
    commitment_leaf(&[TRANSFER_FIELD0_BASE + token_id, from, to, value])
}

pub fn asp_leaf(commitment_index: Fr) -> Fr {
    domain_hash(&POSEIDON2, DOMAIN_ASP_LEAF, &[commitment_index])
}

#[cfg(test)]
mod tests {
    use ark_ff::MontFp;

    use super::*;

    fn fr(value: u64) -> Fr {
        Fr::from(value)
    }

    /// Values from `test-vectors/circuit-vectors.json`.
    #[test]
    fn leaves_match_circuit_vectors() {
        let note_hash: Fr = MontFp!(
            "16991477113130354217921463462147087913240412348690556926355782564815468313682"
        );
        assert_eq!(
            note_leaf(fr(1), note_hash),
            MontFp!(
                "17635670013479729845606614847810079387367566746439219344543976679387274137443"
            )
        );
        assert_eq!(
            transfer_leaf(
                fr(u32::MAX.into()),
                fr(1),
                fr(2),
                MontFp!(
                    "452312848583266388373324160190187140051835877600158453279131187530910662655"
                )
            ),
            MontFp!(
                "15164484161265836099900255543543978043784884650872568513177795196812404926144"
            )
        );
        assert_eq!(
            asp_leaf(fr(u32::MAX.into())),
            MontFp!(
                "14014515224267278320396625734943104694116204786455306916083200816202142167985"
            )
        );
    }
}
