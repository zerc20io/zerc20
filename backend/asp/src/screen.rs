//! Decides positions in commitment index order: each final transfer's sender is screened with Chainalysis once its
//! block is `SCREEN_DELAY_SECS` old, so that freshly stolen funds have time to get labeled. A sender Chainalysis keeps
//! failing on is decided by the protocol's Blocklist alone, so one bad answer cannot hold back every later deposit.
use crate::App;
use alloy::primitives::{Address, B256, U256};
use alloy::providers::Provider;
use anyhow::{Context, Result, bail};
use futures::{StreamExt, stream};
use serde_json::Value;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::Duration;
use tracing::{info, warn};
use zerc20_common::contracts::{IBlocklist, ILedger};
use zerc20_common::fields::is_transfer;
use zerc20_common::{RateLimited, now};
use zerc20_zkp::tree::CHUNK;

const POLL: Duration = Duration::from_secs(5);
/// Chainalysis allows 40 requests a second.
const CONCURRENCY: usize = 4;
/// Failed screenings of one sender in a row (one per tick) before the Blocklist alone decides it.
const FALLBACK_AFTER: u32 = 5;

pub async fn run(app: Arc<App>) -> Result<()> {
    check_indexer(&app).await?;
    // failed screenings in a row, per sender; in memory, so a restart counts again
    let mut failures = HashMap::new();
    loop {
        if let Err(e) = tick(&app, &mut failures).await {
            warn!("screening stalled: {e:#}");
        }
        // screening more often than publishing gains nothing; publishing more often than screening waits on it
        tokio::time::sleep(POLL.min(app.publish_every)).await;
    }
}

/// Decisions are keyed by position only, so an indexer of another chain would have its senders approve positions
/// here. A root the indexer reports must be one this chain's ledger proved, accepted now or not (an emergency bounds
/// the roots): its latest honest one, or else the forged one it names. Until there is one no wallet can spend anyway,
/// so screening waits for it.
async fn check_indexer(app: &App) -> Result<()> {
    // a chain no one has deposited on waits for days: said once
    let mut said = false;
    loop {
        let reported = app.indexer.status().await.map(|s| match &s["latest_root"] {
            Value::Null => s["mismatch"].clone(),
            r => r.clone(),
        });
        match reported {
            Ok(Value::Null) if !said => {
                info!("waiting for the indexer to see a proved root");
                said = true;
            }
            Ok(Value::Null) => {}
            Ok(r) => {
                let index = r["index"].as_u64().context("root index")?;
                let root: U256 = r["root"].as_str().context("root")?.parse()?;
                match ILedger::new(app.ledger, &app.provider)
                    .provedIn(index, root)
                    .call()
                    .await
                {
                    Ok(era) if era != 0 => return Ok(()),
                    Ok(_) => bail!(
                        "the indexer at {} serves another chain: its root {root:#066x} over {index} is not proved here",
                        app.indexer.base()
                    ),
                    Err(e) => warn!("provedIn failed: {e:#}"),
                }
            }
            Err(e) => warn!("indexer status failed: {e:#}"),
        }
        tokio::time::sleep(POLL).await;
    }
}

async fn tick(app: &App, failures: &mut HashMap<Address, u32>) -> Result<()> {
    let (_, fin) = app.indexer.commitment_counts().await?;
    let next = app.tree.lock().decided();
    if next >= fin {
        return Ok(());
    }
    let c = next / CHUNK;
    let ((_, commitments), blocks) =
        tokio::try_join!(app.indexer.commitments(c), app.indexer.blocks(c))?;
    let lo = c * CHUNK;
    let upto = fin
        .min(lo + commitments.len() as u64)
        .min(lo + blocks.len() as u64);
    let block = |i: u64| blocks[(i - lo) as usize];

    // Positions come in block order, so the old enough ones are a prefix: bisect for its end.
    let cutoff = now().saturating_sub(app.delay);
    let (mut ready, mut hi) = (next, upto);
    while ready < hi {
        let mid = (ready + hi) / 2;
        if block_time(app, block(mid)).await? <= cutoff {
            ready = mid + 1;
        } else {
            hi = mid;
        }
    }
    let fields = &commitments[(next - lo) as usize..(ready - lo) as usize];

    // ponytail: dedupes senders within one tick only; cache verdicts briefly if the per-call cost matters
    let senders: HashSet<Address> = fields.iter().filter_map(sender).collect();
    let mut verdicts: HashMap<Address, Result<bool>> = stream::iter(senders)
        .map(|a| async move { (a, screen(app, a).await) })
        .buffer_unordered(CONCURRENCY)
        .collect()
        .await;
    for (a, v) in &mut verdicts {
        let Err(e) = v else {
            failures.remove(a);
            continue;
        };
        // Chainalysis answers, so this is no outage, and anyone can cause it with deposits and with withdrawals through
        // the attester, which shares the key: counting it would let them time a fallback
        if e.is::<RateLimited>() {
            continue;
        }
        let n = failures.entry(*a).or_default();
        *n += 1;
        if *n >= FALLBACK_AFTER {
            warn!(
                "screening {a} failed {n} times in a row, deciding by the Blocklist alone; last: {e:#}"
            );
            *v = IBlocklist::new(app.blocklist, &app.provider)
                .isBlocked(*a)
                .call()
                .await
                .map(|blocked| !blocked)
                .map_err(Into::into);
            if v.is_ok() {
                failures.remove(a); // its next deposit gets Chainalysis again
            }
        }
    }
    let mut bits = Vec::new();
    for (f, i) in fields.iter().zip(next..) {
        bits.push(match sender(f) {
            None => false,
            Some(a) => match &verdicts[&a] {
                Ok(true) => true,
                Ok(false) => {
                    warn!("rejected position {i}: sender {a}");
                    false
                }
                // a screening that has not finished holds back every later position
                Err(e) => {
                    warn!("screening {a} (position {i}) failed, retrying: {e:#}");
                    break;
                }
            },
        });
    }
    if !bits.is_empty() {
        app.tree.lock().append(&bits)?;
        let approved = bits.iter().filter(|&&b| b).count();
        info!(
            "decided {next}..{}: {approved} approved",
            next + bits.len() as u64
        );
    }
    Ok(())
}

/// The sender a transfer commitment records. None for a note, which spends a note rather than taking a deposit, and
/// for any other tag, so whatever is not a transfer is never approved.
fn sender(f: &[U256; 4]) -> Option<Address> {
    is_transfer(f).then(|| Address::from_word(B256::from(f[1])))
}

async fn screen(app: &App, a: Address) -> Result<bool> {
    if app.chainalysis.passes_all() {
        return Ok(!app.dev_reject.contains(&a));
    }
    app.chainalysis.passes(a).await
}

async fn block_time(app: &App, n: u64) -> Result<u64> {
    let b = app
        .provider
        .get_block_by_number(n.into())
        .await?
        .with_context(|| format!("block {n} not found"))?;
    Ok(b.header.timestamp)
}

#[cfg(test)]
mod tests {
    use super::*;
    use zerc20_common::fields::{NOTE_HASH_TAG, TRANSFER_TAG};

    #[test]
    fn only_transfers_have_a_sender() {
        let from = Address::repeat_byte(0xab);
        let token = U256::from(7);
        let transfer = [
            U256::from(TRANSFER_TAG) << 32 | token,
            U256::from_be_slice(from.as_slice()),
            U256::from(1),
            U256::from(100),
        ];
        assert_eq!(sender(&transfer), Some(from));
        let note = [
            U256::from(NOTE_HASH_TAG) << 32 | token,
            U256::from(5),
            U256::ZERO,
            U256::ZERO,
        ];
        assert_eq!(sender(&note), None);
    }
}
