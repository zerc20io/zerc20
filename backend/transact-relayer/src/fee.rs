//! What a request pays the relayer.
use alloy::primitives::{Address, U256};
use anyhow::{Result, ensure};
use serde::Deserialize;
use zerc20_common::contracts::TransactSignals;
use zerc20_common::fields::{fr, u256};
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::ark_ff::{BigInteger, PrimeField};
use zerc20_zkp::primitives::note_hash;

/// The opening of the output note a request pays the relayer with. The rest of it is in the request (chain, token)
/// or the relayer's own (public key).
#[derive(Clone, Debug, Deserialize)]
pub struct FeeNote {
    pub value: U256,
    pub salt: U256,
}

fn modulus() -> U256 {
    U256::from_be_slice(&Fr::MODULUS.to_bytes_be())
}

/// What `s` pays the relayer: the public withdrawal to `relayer` net of the protocol's `withdraw_fee` on it, plus
/// `note` if given. Also returns which output (0 or 1) is `note`. `pk` is the relayer's public key.
pub fn paid(
    s: &TransactSignals,
    note: Option<&FeeNote>,
    relayer: Address,
    pk: Fr,
    withdraw_fee: U256,
) -> Result<(U256, Option<usize>)> {
    let mut paid = U256::ZERO;
    if s.withdrawRecipient == U256::from_be_slice(relayer.as_slice()) {
        paid = s.withdrawAmount.saturating_sub(withdraw_fee);
    }
    let Some(n) = note else {
        return Ok((paid, None));
    };
    // what the circuit accepts as an output, so the note can be spent
    ensure!(
        n.value < U256::ONE << 248,
        "fee note value is 2^248 or more"
    );
    ensure!(
        n.salt < modulus(),
        "fee note salt is not below the field modulus"
    );
    let h = u256(note_hash(
        fr(s.chainId),
        pk,
        fr(n.value),
        fr(s.tokenId),
        fr(n.salt),
    ));
    let slot = [s.noteHash1, s.noteHash2]
        .iter()
        .position(|&x| x == h)
        .ok_or_else(|| anyhow::anyhow!("the fee note matches neither noteHash1 nor noteHash2"))?;
    Ok((paid + n.value, Some(slot)))
}

/// What a merge pays the relayer: its fee, if paid to `relayer`, net of the protocol's `withdraw_fee` on it.
pub fn merge_paid(fee: U256, recipient: U256, relayer: Address, withdraw_fee: U256) -> U256 {
    match recipient == U256::from_be_slice(relayer.as_slice()) {
        true => fee.saturating_sub(withdraw_fee),
        false => U256::ZERO,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zerc20_zkp::primitives::Keys;

    #[test]
    fn paid_counts_both_slots() {
        let relayer = Address::repeat_byte(9);
        let pk = Keys::of(Fr::from(42u64)).public_key;
        let note = FeeNote {
            value: U256::from(70),
            salt: U256::from(12345),
        };
        let h = u256(note_hash(
            Fr::from(1u64),
            pk,
            Fr::from(70u64),
            Fr::from(3u64),
            Fr::from(12345u64),
        ));
        let mut s = TransactSignals {
            tokenId: U256::from(3),
            chainId: U256::from(1),
            commitmentRoot: U256::ZERO,
            aspRoot: U256::ZERO,
            nullifier0: U256::from(1),
            nullifier1: U256::from(2),
            withdrawRecipient: U256::from_be_slice(Address::repeat_byte(8).as_slice()),
            withdrawAmount: U256::from(500),
            withdrawIntent: U256::ZERO,
            noteHash1: U256::from(77),
            noteHash2: h,
        };
        let fee = U256::from(5);
        // a withdrawal to someone else pays nothing
        assert_eq!(
            paid(&s, None, relayer, pk, fee).unwrap(),
            (U256::ZERO, None)
        );
        assert_eq!(
            paid(&s, Some(&note), relayer, pk, fee).unwrap(),
            (U256::from(70), Some(1))
        );
        // a withdrawal to the relayer pays net of the protocol fee
        s.withdrawRecipient = U256::from_be_slice(relayer.as_slice());
        assert_eq!(
            paid(&s, None, relayer, pk, fee).unwrap(),
            (U256::from(495), None)
        );
        assert_eq!(
            paid(&s, Some(&note), relayer, pk, fee).unwrap(),
            (U256::from(565), Some(1))
        );

        let wrong = |n: FeeNote| paid(&s, Some(&n), relayer, pk, fee).is_err();
        assert!(wrong(FeeNote {
            salt: U256::from(12346),
            ..note.clone()
        }));
        assert!(wrong(FeeNote {
            value: U256::from(71),
            ..note.clone()
        }));
        assert!(
            wrong(FeeNote {
                salt: U256::from(12345) + modulus(),
                ..note.clone()
            }),
            "reduced salt"
        );
        assert!(wrong(FeeNote {
            value: U256::ONE << 248,
            ..note.clone()
        }));
        assert!(
            paid(
                &s,
                Some(&note),
                relayer,
                Keys::of(Fr::from(43u64)).public_key,
                fee
            )
            .is_err(),
            "another key"
        );
    }

    #[test]
    fn a_merge_pays_its_fee_to_the_relayer_only() {
        let relayer = Address::repeat_byte(9);
        let to = |a: Address| U256::from_be_slice(a.as_slice());
        let paid =
            |fee: u64, recipient| merge_paid(U256::from(fee), recipient, relayer, U256::from(2));
        assert_eq!(paid(100, to(relayer)), U256::from(98));
        assert_eq!(paid(100, to(Address::repeat_byte(8))), U256::ZERO);
        assert_eq!(paid(1, to(relayer)), U256::ZERO);
    }
}
