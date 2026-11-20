//! The events this indexer reads, how one getLogs answer decodes into a batch, and the per-transaction
//! consistency check that makes silently dropped `NullifierSpent` logs detectable.
use alloy::primitives::{Address, B256, U256, keccak256};
use alloy::rpc::types::Log;
use alloy::sol_types::SolEvent;
use std::collections::BTreeMap;
pub use zerc20_common::contracts::ILedger::{
    Committed, Recovered, RootProved, hashChainCall, nextIndexCall, rootStateCall,
};
pub use zerc20_common::contracts::IVerifier::{Merged, NullifierSpent, RageExited, Transacted};
use zerc20_common::fields::is_note;

/// 4-byte tag a wallet matches against without naming its key: `keccak256(field0 ‖ key)[..4]`, where the key is the
/// note hash of a note and the recipient (`to`) of a transfer, so burn deposits and received notes both show up.
pub fn tag(fields: &[U256; 4]) -> [u8; 4] {
    let key = if is_note(fields) {
        fields[1]
    } else {
        fields[2]
    };
    let mut pre = [0u8; 64];
    pre[..32].copy_from_slice(&fields[0].to_be_bytes::<32>());
    pre[32..].copy_from_slice(&key.to_be_bytes::<32>());
    let [a, b, c, d, ..] = keccak256(pre).0;
    [a, b, c, d]
}

/// topic0 of every event fetched, in one getLogs call: fetching them together means a lagging node or a truncated
/// answer that loses verifier logs also loses ledger logs, which the ledger's index and hash chain do catch.
pub fn topics() -> Vec<B256> {
    vec![
        Committed::SIGNATURE_HASH,
        RootProved::SIGNATURE_HASH,
        Recovered::SIGNATURE_HASH,
        NullifierSpent::SIGNATURE_HASH,
        Transacted::SIGNATURE_HASH,
        Merged::SIGNATURE_HASH,
        RageExited::SIGNATURE_HASH,
    ]
}

#[derive(Clone, Copy, Debug)]
pub struct Meta {
    pub block: u64,
    pub log_index: u64,
    pub block_hash: B256,
    pub tx_hash: B256,
}

pub struct Commitment {
    pub meta: Meta,
    pub index: u64,
    pub fields: [U256; 4],
}
pub struct Nullifier {
    pub meta: Meta,
    pub nullifier: U256,
}
pub struct RootProof {
    pub meta: Meta,
    pub old_index: u64,
    pub new_index: u64,
    pub root: U256,
}

/// What each transaction did, for [`check_ops`].
#[derive(Default, Debug)]
pub struct TxOps {
    pub block: u64,
    pub nullifiers: Vec<U256>,
    pub notes: u64,
    pub transacts: u64,
    pub merges: u64,
    pub merge_inputs: u64,
    pub rage_exits: Vec<U256>,
}

#[derive(Default)]
pub struct Batch {
    pub commitments: Vec<Commitment>,
    pub nullifiers: Vec<Nullifier>,
    pub roots: Vec<RootProof>,
    pub ops: BTreeMap<B256, TxOps>,
}

fn u64_of(v: U256, what: &str) -> Result<u64, String> {
    u64::try_from(v).map_err(|_| format!("{what} {v} does not fit u64"))
}

/// Decodes logs already sorted by (block, log index). Every log must come from the contract that emits its event.
pub fn decode(logs: &[Log], ledger: Address, verifier: Address) -> Result<Batch, String> {
    let mut b = Batch::default();
    for l in logs {
        let meta = Meta {
            block: l.block_number.ok_or("log without block number")?,
            log_index: l.log_index.ok_or("log without log index")?,
            block_hash: l.block_hash.ok_or("log without block hash")?,
            tx_hash: l.transaction_hash.ok_or("log without tx hash")?,
        };
        let (topic0, from) = (l.topics().first().copied().unwrap_or_default(), l.address());
        let bad = |e: alloy::sol_types::Error| {
            format!("undecodable log {}:{}: {e}", meta.block, meta.log_index)
        };
        let expect = |want: Address| -> Result<(), String> {
            (from == want)
                .then_some(())
                .ok_or_else(|| format!("event {topic0} from unexpected address {from}"))
        };
        let tx = b.ops.entry(meta.tx_hash).or_insert_with(|| TxOps {
            block: meta.block,
            ..Default::default()
        });
        match topic0 {
            Committed::SIGNATURE_HASH => {
                expect(ledger)?;
                let e = Committed::decode_log_data(l.data()).map_err(bad)?;
                if is_note(&e.fields) {
                    tx.notes += 1;
                }
                b.commitments.push(Commitment {
                    meta,
                    index: e.index,
                    fields: e.fields,
                });
            }
            RootProved::SIGNATURE_HASH => {
                expect(ledger)?;
                let e = RootProved::decode_log_data(l.data()).map_err(bad)?;
                b.roots.push(RootProof {
                    meta,
                    old_index: e.oldIndex,
                    new_index: e.newIndex,
                    root: e.newRoot,
                });
            }
            // the root stream steps back to an earlier root; its old index chains like a RootProved's
            Recovered::SIGNATURE_HASH => {
                expect(ledger)?;
                let e = Recovered::decode_log_data(l.data()).map_err(bad)?;
                b.roots.push(RootProof {
                    meta,
                    old_index: e.oldIndex,
                    new_index: e.newIndex,
                    root: e.newRoot,
                });
            }
            NullifierSpent::SIGNATURE_HASH => {
                expect(verifier)?;
                let e = NullifierSpent::decode_log_data(l.data()).map_err(bad)?;
                tx.nullifiers.push(e.nullifier);
                b.nullifiers.push(Nullifier {
                    meta,
                    nullifier: e.nullifier,
                });
            }
            Transacted::SIGNATURE_HASH => {
                expect(verifier)?;
                Transacted::decode_log_data(l.data()).map_err(bad)?;
                tx.transacts += 1;
            }
            Merged::SIGNATURE_HASH => {
                expect(verifier)?;
                let e = Merged::decode_log_data(l.data()).map_err(bad)?;
                tx.merges += 1;
                tx.merge_inputs += u64_of(e.inputCount, "merge input count")?;
            }
            RageExited::SIGNATURE_HASH => {
                expect(verifier)?;
                let e = RageExited::decode_log_data(l.data()).map_err(bad)?;
                tx.rage_exits.push(e.nullifier);
            }
            t => return Err(format!("unexpected topic0 {t}")),
        }
    }
    Ok(b)
}

/// `NullifierSpent` carries no sequence number, so a dropped one is checked against the rest of its transaction:
/// a transact spends 2 nullifiers and commits 2 notes, a merge spends `inputCount` and commits 1, a rage exit spends
/// the nullifier it names and commits nothing, and only the Verifier commits notes. The ledger's index already
/// proves every note commitment is here, so any dropped transact/merge log breaks an equation. Returns the block of
/// the first inconsistent transaction.
///
/// Blind spot: a rage exit whose two logs are both dropped. A missed nullifier only makes a wallet try to spend a
/// spent note, which the contract rejects.
pub fn check_ops(ops: &BTreeMap<B256, TxOps>) -> Result<(), (u64, String)> {
    let bad = ops
        .iter()
        .filter(|(_, o)| {
            let spent = 2 * o.transacts + o.merge_inputs + o.rage_exits.len() as u64;
            o.nullifiers.len() as u64 != spent
                || o.notes != 2 * o.transacts + o.merges
                || o.rage_exits.iter().any(|n| !o.nullifiers.contains(n))
        })
        .min_by_key(|(_, o)| o.block);
    match bad {
        None => Ok(()),
        Some((tx, o)) => Err((
            o.block,
            format!("tx {tx} in block {} is incomplete: {o:?}", o.block),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zerc20_common::fields::NOTE_HASH_TAG;

    fn ops(
        nullifiers: u64,
        notes: u64,
        transacts: u64,
        merges: u64,
        merge_inputs: u64,
        rage: &[u64],
    ) -> TxOps {
        TxOps {
            block: 7,
            nullifiers: (0..nullifiers).map(U256::from).collect(),
            notes,
            transacts,
            merges,
            merge_inputs,
            rage_exits: rage.iter().map(|&n| U256::from(n)).collect(),
        }
    }

    fn check(o: TxOps) -> bool {
        check_ops(&BTreeMap::from([(B256::ZERO, o)])).is_ok()
    }

    /// wallet/core pins the same tags, which it computes from a note hash or a burn address alone.
    #[test]
    fn tags_are_what_wallets_compute() {
        let note = |token: u64| U256::from(0x789f26ebu64 << 32 | token);
        let transfer = |token: u64| U256::from(0xddf252adu64 << 32 | token);
        let n = [note(1), U256::from(12345), U256::ZERO, U256::ZERO];
        assert!(is_note(&n));
        assert_eq!(tag(&n), 0x5f67ca8au32.to_be_bytes());
        let t = [
            transfer(1),
            U256::from(0xabc),
            U256::from(0xbeef),
            U256::from(5),
        ];
        assert_eq!(tag(&t), 0x4e66b741u32.to_be_bytes());
    }

    #[test]
    fn complete_transactions_pass() {
        assert!(check(ops(2, 2, 1, 0, 0, &[])), "transact");
        assert!(check(ops(3, 1, 0, 1, 3, &[])), "merge of 3");
        assert!(check(ops(1, 0, 0, 0, 0, &[0])), "rage exit");
        assert!(
            check(ops(6, 3, 1, 1, 3, &[0])),
            "transact + merge + rage exit in one tx"
        );
        assert!(check(ops(0, 0, 0, 0, 0, &[])), "a plain transfer");
    }

    #[test]
    fn any_dropped_log_is_caught() {
        assert!(!check(ops(1, 2, 1, 0, 0, &[])), "transact lost a nullifier");
        assert!(
            !check(ops(2, 2, 0, 0, 0, &[])),
            "transact lost its Transacted"
        );
        assert!(
            !check(ops(0, 2, 0, 0, 0, &[])),
            "transact lost Transacted and both nullifiers"
        );
        assert!(!check(ops(2, 1, 1, 0, 0, &[])), "transact lost a note");
        assert!(!check(ops(2, 1, 0, 1, 3, &[])), "merge lost a nullifier");
        assert!(
            !check(ops(0, 1, 0, 0, 0, &[])),
            "merge lost Merged and every nullifier"
        );
        assert!(
            !check(ops(0, 0, 0, 0, 0, &[0])),
            "rage exit lost its nullifier"
        );
        assert!(!check(ops(1, 0, 0, 0, 0, &[])), "rage exit lost RageExited");
        assert!(
            !check(ops(1, 0, 0, 0, 0, &[5])),
            "rage exit names a nullifier that is not there"
        );
    }

    #[test]
    fn tags_key_on_recipient_or_note_hash() {
        let note = [
            (U256::from(NOTE_HASH_TAG) << 32) | U256::from(1),
            U256::from(42),
            U256::ZERO,
            U256::ZERO,
        ];
        let transfer = [
            U256::from(0xddf252adu64) << 32 | U256::from(1),
            U256::from(7),
            U256::from(42),
            U256::from(5),
        ];
        assert!(is_note(&note) && !is_note(&transfer));
        let mut other_sender = transfer;
        other_sender[1] = U256::from(8);
        assert_eq!(
            tag(&transfer),
            tag(&other_sender),
            "the sender is not part of the key"
        );
        let mut other_note = note;
        other_note[1] = U256::from(43);
        assert_ne!(tag(&note), tag(&other_note));
    }
}
