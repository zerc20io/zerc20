//! The sync loop: follow the head, roll back on reorgs, and never commit a batch that
//! might have lost logs. Each batch is checked by
//! - the ledger's dense `Committed.index` and the old -> new chain of `RootProved` and `Recovered` (a gap anywhere),
//! - [`events::check_ops`] (a `NullifierSpent` dropped from a transaction whose other logs arrived),
//! - headers: parent links, each log's block hash (logs from another fork), and logsBloom for whole Verifier
//!   transactions that went missing ([`Indexer::check_blooms`]),
//! - inside the reorg window, the ledger's `nextIndex`, `hashChain` and `rootState` read at the exact block
//!   (EIP-1898), which catches loss at the tail and content that differs from the chain.
use crate::db::{self, NewCommitment, NewRoot};
use crate::events::{self, Batch};
use crate::rpc::{Fail, Header, RangeCtl, Rpc, Source, Verdict, backoff};
use alloy::primitives::{Address, B256, BloomInput, U256};
use alloy::rpc::types::{Filter, Log};
use alloy::sol_types::{SolCall, SolEvent};
use anyhow::{Context, Result};
use futures::{StreamExt, TryStreamExt};
use parking_lot::Mutex;
use sqlx::PgPool;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tracing::{debug, error, info, warn};
use zerc20_common::fields::{fields_of, leaf, next_hash_chain, u256};
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::tree::{self, CHUNK_BITS, PAGE_BITS};

pub struct Config {
    pub ledger: Address,
    pub verifier: Address,
    /// Required on first start (no cursor yet); ignored afterwards.
    pub start_block: Option<u64>,
    /// Reorg window where the chain has no `safe` tag; with one, the window reaches down to it.
    pub reorg_depth: u64,
    pub batch_initial: u64,
    pub batch_max: u64,
    /// How long a cursor block may stay *missing* before we believe the chain really got shorter.
    pub missing_grace: Duration,
    /// How long the loop rests once it has caught up with the head. Each look at the head costs about seven calls
    /// however few blocks it finds, so looking at every block of a sub-second chain would multiply the RPC bill.
    pub poll: Duration,
    /// Index only what is final, never the reorg window. The window costs a header per block, most of the bill on a
    /// fast chain, and an indexer that only watches for forged roots can see them that much later.
    pub final_only: bool,
}

impl Config {
    /// Where indexing starts while there is no cursor.
    fn start_block(&self) -> Result<u64> {
        self.start_block.context(
            "START_BLOCK is required on first start (set it to the ledger's deployment block)",
        )
    }
}

/// What the sync loop reports in `/status`.
pub struct Status {
    pub head: u64,
    pub cursor: u64,
    /// Blocks below this cannot reorg: `safe + 1`, or `head - REORG_DEPTH` where that is lower or there is no
    /// tag. Data in them is final, so the API may let CDNs cache it forever.
    pub window_start: u64,
    pub width: u64,
    pub cap: u64,
    pub last_ok: Instant,
    pub stall: Duration,
    pub gap_repairs: u64,
    pub last_gap: String,
    pub paranoid_width: Option<u64>,
}
pub struct Shared {
    pub rpc: Rpc,
    pub status: Mutex<Status>,
}
impl Shared {
    pub fn new(rpc: Rpc, stall: Duration) -> Self {
        Self {
            rpc,
            status: Mutex::new(Status {
                head: 0,
                cursor: 0,
                window_start: 0,
                width: 0,
                cap: 0,
                last_ok: Instant::now(),
                stall,
                gap_repairs: 0,
                last_gap: String::new(),
                paranoid_width: None,
            }),
        }
    }
    pub fn json(&self) -> serde_json::Value {
        let s = self.status.lock();
        serde_json::json!({
            "head": s.head, "cursor": s.cursor, "final_block": s.window_start.checked_sub(1),
            "lag": s.head.saturating_sub(s.cursor), "width": s.width, "cap": s.cap,
            "last_ok_secs": s.last_ok.elapsed().as_secs(), "stalled": s.last_ok.elapsed() > s.stall,
            "gap_repairs": s.gap_repairs, "last_gap": s.last_gap, "paranoid_width": s.paranoid_width,
            "sources": self.rpc.snapshot(),
        })
    }
}

#[derive(Debug, PartialEq)]
pub enum IndexIssue {
    /// An index we should have seen is missing (dropped logs).
    Gap { expected: u64, got: u64 },
    /// An index repeated or went backwards.
    Regress { expected: u64, got: u64 },
}

/// `got` are the indices of one batch in (block, log_index) order; they must continue from `expected`.
pub fn check_indices(expected: u64, got: &[u64]) -> Result<(), IndexIssue> {
    let mut e = expected;
    for &g in got {
        match g.cmp(&e) {
            std::cmp::Ordering::Equal => e += 1,
            std::cmp::Ordering::Greater => {
                return Err(IndexIssue::Gap {
                    expected: e,
                    got: g,
                });
            }
            std::cmp::Ordering::Less => {
                return Err(IndexIssue::Regress {
                    expected: e,
                    got: g,
                });
            }
        }
    }
    Ok(())
}

/// Max blocks per step once inside the reorg window: each one costs a header request, and a step that needs
/// dozens of requests all succeeding is hopeless on a flaky provider. Small steps persist progress as they go.
const MAX_WINDOW_STEP: u64 = 16;

const MIN_PARANOID: u64 = 4; // narrowest range used while repairing a gap
const MIN_REPAIR_WIDTH: u64 = 16; // a repair never shrinks the normal batch width below this

/// A couple of quick local retries for cheap idempotent reads, so one hiccup doesn't throw away the whole step.
async fn retry_local<T, Fut: std::future::Future<Output = Result<T, Fail>>>(
    mut f: impl FnMut() -> Fut,
) -> Result<T, Fail> {
    let mut attempt = 0;
    loop {
        match f().await {
            Err(e)
                if attempt < 2 && matches!(e.verdict, Verdict::Transient | Verdict::BehindHead) =>
            {
                tokio::time::sleep(backoff(attempt, 50, 400)).await;
                attempt += 1;
            }
            r => return r,
        }
    }
}

fn inconsistent(msg: impl Into<String>) -> Fail {
    Fail::new(Verdict::Inconsistent, msg)
}

/// What the ledger says at the end of a batch, versus what the batch leads to locally.
enum Onchain {
    Agrees,
    /// The chain has more: logs were lost. Refetch from this block.
    Missing {
        from_block: u64,
        why: String,
    },
}

struct Indexer {
    pool: PgPool,
    shared: Arc<Shared>,
    c: Config,
    ctl: RangeCtl,
    executed: u64,   // width of the range currently in flight (for AIMD)
    fails: u32,      // consecutive transient failures
    lag_streak: u32, // consecutive BehindHead / Inconsistent
    suspect: Option<(u64, Instant, u32)>, // (cursor block, first seen, observations) awaiting reorg confirmation
    paranoid: Option<(u64, u64)>, // (stay careful until cursor passes this block, max width meanwhile)
    state_warned: Vec<bool>, // per source: already told the user that eth_call at a block is unavailable
    chunk_roots: Vec<Fr>,    // full chunks' and pages' roots, mirrored from their tables
    page_roots: Vec<Fr>,
}

pub async fn run(pool: PgPool, shared: Arc<Shared>, c: Config) -> Result<()> {
    // a first start without START_BLOCK fails here, rather than at each step
    if db::cursor(&pool).await?.is_none() {
        c.start_block()?;
    }
    let ctl = RangeCtl::new(c.batch_initial, c.batch_max);
    let n_src = shared.rpc.sources.len();
    let (chunk_roots, page_roots) = db::subtree_roots(&pool).await?;
    let mut ix = Indexer {
        pool,
        shared,
        c,
        ctl,
        executed: 0,
        fails: 0,
        lag_streak: 0,
        suspect: None,
        paranoid: None,
        state_warned: vec![false; n_src],
        chunk_roots,
        page_roots,
    };
    ix.publish(None, None, None);
    if let Err(e) = time_roots(&ix.pool, &ix.shared.rpc).await {
        warn!("roots' block times not filled in, so the settle time waits for new roots: {e:#}");
    }
    loop {
        let si = ix.shared.rpc.pick()?;
        match ix.step(si).await {
            Ok(more) => {
                ix.shared.rpc.mark_ok(si);
                ix.fails = 0;
                ix.lag_streak = 0;
                ix.shared.status.lock().last_ok = Instant::now();
                if !more {
                    tokio::time::sleep(ix.c.poll).await;
                }
            }
            Err(e) => {
                if let Some(d) = ix.on_error(si, &e)? {
                    tokio::time::sleep(d).await;
                }
            }
        }
    }
}

/// Fills in the block time of each root the settle time is measured over that lacks one, from the header at its
/// height, so that `/status` has the settle time from the start rather than once enough roots are proved anew. A root
/// inside the reorg window whose block is dropped is written again, with its own block's time.
async fn time_roots(pool: &PgPool, rpc: &Rpc) -> Result<()> {
    let roots = db::untimed_roots(pool).await?;
    if roots.is_empty() {
        return Ok(());
    }
    let src = &rpc.sources[rpc.pick()?];
    let blocks: Vec<u64> = roots.iter().map(|r| r.1).collect();
    let headers: Vec<Header> = futures::stream::iter(blocks)
        .map(|n| retry_local(move || src.header(n)))
        .buffered(8)
        .try_collect()
        .await?;
    let times: Vec<(u64, u64)> = roots
        .iter()
        .zip(&headers)
        .map(|(r, h)| (r.0, h.timestamp))
        .collect();
    db::set_root_times(pool, &times).await?;
    info!("filled in the block times of {} roots", times.len());
    Ok(())
}

impl Indexer {
    fn publish(&self, head: Option<u64>, cursor: Option<u64>, window_start: Option<u64>) {
        let mut s = self.shared.status.lock();
        s.width = self.ctl.width;
        s.cap = self.ctl.cap;
        s.head = head.unwrap_or(s.head);
        s.cursor = cursor.unwrap_or(s.cursor);
        s.window_start = window_start.unwrap_or(s.window_start);
    }

    /// Decide what to do after a failed step. `Ok(None)` = retry immediately; Err = unrecoverable.
    fn on_error(&mut self, si: usize, e: &anyhow::Error) -> Result<Option<Duration>> {
        let rpc = &self.shared.rpc;
        let name = rpc.sources[si].name.clone();
        let stalled = {
            let s = self.shared.status.lock();
            (s.last_ok.elapsed() > s.stall).then(|| s.last_ok.elapsed().as_secs())
        };
        if let Some(secs) = stalled {
            error!(
                "indexer stalled: no successful step for {secs}s (last error from {name}: {e:#})"
            );
        }
        let Some(f) = e.downcast_ref::<Fail>() else {
            // DB or other local error: not the source's fault
            warn!("indexer step failed: {e:#}");
            self.fails += 1;
            return Ok(Some(backoff(self.fails - 1, 500, 10_000)));
        };
        warn!("rpc[{name}] {f}");
        match &f.verdict {
            Verdict::RangeTooLarge { .. } | Verdict::TooManyResults => {
                if self.ctl.on_error(&f.verdict, self.executed) {
                    info!(
                        "narrowing getLogs range to {} blocks (cap {})",
                        self.ctl.width, self.ctl.cap
                    );
                    self.fails = 0; // progress in the adaptation, not a failure of the source
                    self.publish(None, None, None);
                    return Ok(None);
                }
                Ok(Some(self.transient(si, &f.msg))) // even the narrowest range is refused: treat as a failure
            }
            // never shrink the range on a rate limit: it would just make more requests
            Verdict::RateLimited => {
                rpc.mark_failed(si, &f.msg);
                self.fails += 1;
                Ok(Some(backoff(self.fails - 1, 1_000, 30_000)))
            }
            Verdict::BehindHead | Verdict::Inconsistent => {
                self.lag_streak += 1;
                if self.lag_streak >= 12 {
                    rpc.mark_failed(si, &f.msg); // ~10s of this: give another source a chance
                }
                Ok(Some(backoff(self.lag_streak - 1, 100, 1_000)))
            }
            Verdict::SourceFatal => {
                warn!("disabling rpc[{name}]: {}", f.msg);
                rpc.disable(si, &f.msg);
                rpc.pick()?; // errors out if nothing is left
                Ok(None)
            }
            Verdict::Transient | Verdict::StateUnavailable => Ok(Some(self.transient(si, &f.msg))),
        }
    }

    fn transient(&mut self, si: usize, why: &str) -> Duration {
        self.fails += 1;
        if self.fails >= 2 {
            self.shared.rpc.mark_failed(si, why); // fail over after the second consecutive failure
        }
        backoff(self.fails - 1, 200, 30_000)
    }

    /// Is the cursor block really gone from the chain? Rolling back is safe but costs re-indexing the window,
    /// so wait for confirmation instead of reacting to the first odd answer from a possibly lagging node.
    async fn confirm_reorg(&mut self, si: usize, n: u64, h: B256, missing: bool) -> Result<bool> {
        let e = self.suspect.get_or_insert((n, Instant::now(), 0));
        if e.0 != n {
            *e = (n, Instant::now(), 0);
        }
        e.2 += 1;
        let (since, count) = (e.1, e.2);
        if missing && since.elapsed() < self.c.missing_grace {
            return Ok(false);
        }
        if !missing && count < 2 {
            return Ok(false);
        }
        // another source still vouching for our cursor hash vetoes the rollback: this source is the odd one out
        for (j, o) in self
            .shared
            .rpc
            .sources
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != si)
        {
            if let Ok(Some(b)) = o.header_opt(n).await
                && b.hash == h
            {
                return Err(inconsistent(format!(
                    "source disagrees with cursor at {n} but rpc[{}] agrees",
                    self.shared.rpc.sources[j].name
                ))
                .into());
            }
        }
        Ok(true)
    }

    async fn rollback(&mut self, target: u64, hash: Option<B256>) -> Result<()> {
        db::rollback(&self.pool, target, hash).await?;
        (self.chunk_roots, self.page_roots) = db::subtree_roots(&self.pool).await?;
        Ok(())
    }

    /// One iteration. Ok(true) = more to do right away (don't sleep): still behind the head, or rolled back.
    async fn step(&mut self, si: usize) -> Result<bool> {
        let shared = self.shared.clone(); // local handles so `self` stays free for &mut calls below
        let src = &shared.rpc.sources[si];
        let pool = self.pool.clone();
        let cur = db::cursor(&pool).await?;

        // Reorg check: block hashes chain, so if the cursor block is unchanged, everything below is too.
        if let Some((n, Some(h))) = cur {
            let seen = src.header_opt(n).await?;
            if seen.as_ref().map(|b| b.hash) == Some(h) {
                self.suspect = None;
            } else if !self.confirm_reorg(si, n, h, seen.is_none()).await? {
                return Err(inconsistent(format!(
                    "cursor block {n} changed or missing; waiting to confirm reorg"
                ))
                .into());
            } else {
                let (target, th) = common_ancestor(&pool, src, n, self.c.reorg_depth).await?;
                warn!("reorg at {n}, rolling back to {target}");
                self.rollback(target, th).await?;
                self.suspect = None;
                return Ok(true);
            }
        }

        let head = src.head().await?;
        // A node without the tag (or a hiccup asking for it) falls back to the fixed depth for this step.
        let fin = src.safe().await.ok().flatten();
        let window_start = head
            .saturating_sub(self.c.reorg_depth)
            .min(fin.map_or(u64::MAX, |f| f + 1));
        let from = match cur {
            Some((n, _)) => n + 1,
            None => self.c.start_block()?,
        };
        self.publish(Some(head), cur.map(|c| c.0), Some(window_start));
        let end = if self.c.final_only {
            window_start.saturating_sub(1)
        } else {
            head
        };
        if from > end {
            return Ok(false);
        }
        let mut width = self.ctl.width;
        if let Some((until, pw)) = self.paranoid {
            if from > until {
                self.paranoid = None; // repaired region is behind us
                self.shared.status.lock().paranoid_width = None;
            } else {
                width = width.min(pw);
            }
        }
        let mut to = end.min(from + width - 1);
        // cross into the window in two phases (cheap backfill part first), then small steps inside it
        to = if from < window_start {
            to.min(window_start - 1)
        } else {
            to.min(from + MAX_WINDOW_STEP - 1)
        };
        self.executed = to - from + 1;
        let t_rpc = Instant::now();

        let filter = Filter::new()
            .address(vec![self.c.ledger, self.c.verifier])
            .event_signature(events::topics())
            .from_block(from)
            .to_block(to);
        let mut logs = src.logs(&filter).await?;
        self.validate_logs(&mut logs, from, to)?;
        let batch = events::decode(&logs, self.c.ledger, self.c.verifier).map_err(inconsistent)?;
        let st = db::state(&pool).await?;
        // where a lost log can be, at the earliest: after the last stored one of its stream (maybe in its block)
        let start = self.c.start_block.unwrap_or(0);
        let before = move |b: Option<u64>| b.unwrap_or(start).saturating_sub(1);

        let idx: Vec<u64> = batch.commitments.iter().map(|c| c.index).collect();
        if let Err(issue) = check_indices(st.commitments, &idx) {
            let why = format!("commitments {issue:?} in {from}..={to}");
            return self
                .repair(si, before(st.last_commitment_block), from, to, why)
                .await;
        }
        let mut root_index = st.root_index;
        for r in &batch.roots {
            if r.old_index != root_index {
                let why = format!(
                    "root {} -> {} follows {root_index} in {from}..={to}",
                    r.old_index, r.new_index
                );
                return self
                    .repair(si, before(st.last_root_block), from, to, why)
                    .await;
            }
            root_index = r.new_index;
        }
        if let Err((block, why)) = events::check_ops(&batch.ops) {
            return self
                .repair(si, block.saturating_sub(1), from, to, why)
                .await;
        }

        // Headers: the whole reorg window, or just `to` when backfilling far behind head. Always get `to`, from this
        // same source, after the logs: a node that serves block `to` has caught up at least that far. Its hash pins
        // the check against the ledger's state and becomes the cursor's.
        let hstart = from.max(window_start).min(to);
        let (mut headers, last) = futures::try_join!(
            futures::stream::iter(hstart..to)
                .map(|n| retry_local(move || src.header(n)))
                .buffered(8)
                .try_collect::<Vec<Header>>(),
            retry_local(|| src.header(to)),
        )?;
        let to_hash = last.hash;
        headers.push(last);
        self.check_headers(&headers, &logs, cur)?;
        if let Some(block) = self.check_blooms(src, &headers, &logs).await? {
            let why = format!("block {block} has Verifier logs the {from}..={to} answer lacked");
            return self
                .repair(si, block.saturating_sub(1), from, to, why)
                .await;
        }

        // Each commitment's and proved root's block time: wallets date what they find by it the same way on every
        // device, and the time between the two is how long commitments wait for a root. The window's headers have it,
        // and a backfill fetches the header of each block holding either.
        let mut times: HashMap<u64, (B256, u64)> = headers
            .iter()
            .map(|h| (h.number, (h.hash, h.timestamp)))
            .collect();
        let lacking: BTreeSet<u64> = batch
            .commitments
            .iter()
            .map(|c| c.meta.block)
            .chain(batch.roots.iter().map(|r| r.meta.block))
            .filter(|b| !times.contains_key(b))
            .collect();
        let fetched: Vec<Header> = futures::stream::iter(lacking)
            .map(|n| retry_local(move || src.header(n)))
            .buffered(8)
            .try_collect()
            .await?;
        times.extend(fetched.iter().map(|h| (h.number, (h.hash, h.timestamp))));

        let mut chain = st.hash_chain;
        let mut commitments: Vec<NewCommitment> = Vec::with_capacity(batch.commitments.len());
        for c in &batch.commitments {
            let (hash, time) = times[&c.meta.block];
            if hash != c.meta.block_hash {
                return Err(inconsistent(format!(
                    "the commitment at {} is from a different fork than its block's header",
                    c.meta.block
                ))
                .into());
            }
            chain = next_hash_chain(chain, &c.fields);
            commitments.push(NewCommitment {
                meta: c.meta,
                fields: c.fields,
                hash_chain: chain,
                time,
            });
        }

        // Compare with the ledger's own state while it is still within reach of a non-archive node: inside the window,
        // or at the newest final block where the indexer stops there.
        if to >= window_start || to == end {
            let k = st.commitments + commitments.len() as u64;
            let last_root = batch.roots.last().map(|r| r.root).or(st.root);
            match self
                .check_onchain(src, to_hash, k, chain, root_index, last_root, &st, &before)
                .await
            {
                Ok(Onchain::Agrees) => {}
                Ok(Onchain::Missing { from_block, why }) => {
                    return self.repair(si, from_block, from, to, why).await;
                }
                Err(f) if f.verdict == Verdict::StateUnavailable => {
                    if !std::mem::replace(&mut self.state_warned[si], true) {
                        warn!(
                            "rpc[{}] cannot serve eth_call at recent blocks ({}); relying on index continuity there",
                            src.name, f.msg
                        );
                    }
                }
                Err(f) => return Err(f.into()),
            }
        }
        let rpc_ms = t_rpc.elapsed().as_millis();

        // Chunks and pages this batch completes, then the local tree at each proved size.
        let t_tree = Instant::now();
        let (k0, k1) = (st.commitments, st.commitments + commitments.len() as u64);
        let mut new_chunks = vec![];
        for c in k0 >> CHUNK_BITS..k1 >> CHUNK_BITS {
            let leaves = self
                .leaves(c << CHUNK_BITS, (c + 1) << CHUNK_BITS, k0, &batch)
                .await?;
            new_chunks.push((c, tree::chunk_root(leaves)));
        }
        // chunk roots lo..hi, stored or new
        let chunk_roots = |lo: u64, hi: u64| -> Vec<Fr> {
            let all = self
                .chunk_roots
                .iter()
                .chain(new_chunks.iter().map(|c| &c.1));
            all.skip(lo as usize)
                .take((hi - lo) as usize)
                .copied()
                .collect()
        };
        let mut new_pages = vec![];
        for p in k0 >> PAGE_BITS..k1 >> PAGE_BITS {
            let r = tree::page_root(chunk_roots(p << CHUNK_BITS, (p + 1) << CHUNK_BITS));
            new_pages.push((p, r));
        }
        let pages: Vec<Fr> = self
            .page_roots
            .iter()
            .copied()
            .chain(new_pages.iter().map(|p| p.1))
            .collect();
        let mut roots = vec![];
        for r in &batch.roots {
            let n = r.new_index;
            if n > k1 {
                return Err(inconsistent(format!(
                    "root size {n} exceeds the {k1} commitments seen"
                ))
                .into());
            }
            let partial_leaves = self
                .leaves(n >> CHUNK_BITS << CHUNK_BITS, n, k0, &batch)
                .await?;
            let page_chunks = chunk_roots(n >> PAGE_BITS << CHUNK_BITS, n >> CHUNK_BITS);
            let tree = tree::sized(n, &pages, &page_chunks, partial_leaves);
            let local_root = u256(tree.root);
            if local_root != r.root {
                // the other nodes trust this indexer, not the contract: a circuit bug could prove a forged root
                error!(
                    "on-chain root {:#066x} at size {n} differs from the indexer's {local_root:#066x}",
                    r.root
                );
            }
            let (hash, time) = times[&r.meta.block];
            if hash != r.meta.block_hash {
                return Err(inconsistent(format!(
                    "the root proved at {} is from a different fork than its block's header",
                    r.meta.block
                ))
                .into());
            }
            roots.push(NewRoot {
                proof: r,
                local_root,
                partial_chunk_root: tree.partial_chunk.map(u256),
                partial_page_root: tree.partial_page.map(u256),
                time,
            });
        }
        let tree_ms = t_tree.elapsed().as_millis();

        let t_db = Instant::now();
        let blocks: Vec<Header> = headers
            .iter()
            .filter(|h| h.number >= window_start)
            .cloned()
            .collect();
        db::write_batch(
            &pool,
            db::Batch {
                first_commitment: k0,
                commitments: &commitments,
                first_nullifier: st.nullifiers,
                nullifiers: &batch.nullifiers,
                first_root: st.roots,
                roots: &roots,
                chunk_roots: &new_chunks
                    .iter()
                    .map(|&(c, r)| (c, u256(r)))
                    .collect::<Vec<_>>(),
                page_roots: &new_pages
                    .iter()
                    .map(|&(p, r)| (p, u256(r)))
                    .collect::<Vec<_>>(),
                blocks: &blocks,
                cursor: (to, Some(to_hash)),
                keep_from: window_start,
            },
        )
        .await?;
        self.chunk_roots.extend(new_chunks.iter().map(|c| c.1));
        self.page_roots = pages;

        self.suspect = None;
        self.ctl.on_success(self.executed);
        self.publish(Some(head), Some(to), None);
        let line = format!(
            "batch {from}..={to} commitments={} nullifiers={} roots={} rpc_ms={rpc_ms} tree_ms={tree_ms} db_ms={} width={}",
            commitments.len(),
            batch.nullifiers.len(),
            roots.len(),
            t_db.elapsed().as_millis(),
            self.ctl.width
        );
        // at the head a batch comes every few seconds on every chain: an empty one there would bury the rest of the
        // log, and rotate it away within days
        match from >= window_start
            && commitments.is_empty()
            && batch.nullifiers.is_empty()
            && roots.is_empty()
        {
            true => debug!("{line}"),
            false => info!("{line}"),
        }
        Ok(to < head)
    }

    /// Leaves `lo..hi`: stored commitments below `k0`, then this batch's.
    async fn leaves(&self, lo: u64, hi: u64, k0: u64, batch: &Batch) -> Result<Vec<Fr>> {
        let stored = db::commitments(&self.pool, lo, hi.min(k0)).await?;
        anyhow::ensure!(
            stored.len() as u64 == hi.min(k0).saturating_sub(lo),
            "stored commitments {lo}..{} are incomplete",
            hi.min(k0)
        );
        let fresh = batch
            .commitments
            .iter()
            .skip(lo.saturating_sub(k0) as usize)
            .take(hi.saturating_sub(lo.max(k0)) as usize);
        Ok(stored
            .iter()
            .map(|(_, f)| leaf(&fields_of(f)))
            .chain(fresh.map(|c| leaf(&c.fields)))
            .collect())
    }

    /// The ledger's `nextIndex`, `hashChain` and `rootState` at block `at`, against what this batch leads to.
    #[allow(clippy::too_many_arguments)]
    async fn check_onchain(
        &self,
        src: &Source,
        at: B256,
        k: u64,
        chain: U256,
        root_index: u64,
        root: Option<U256>,
        st: &db::State,
        before: &impl Fn(Option<u64>) -> u64,
    ) -> Result<Onchain, Fail> {
        let ledger = self.c.ledger;
        let call = |data: Vec<u8>| src.call_at(ledger, data.into(), at);
        let (next, hc, rs) = tokio::try_join!(
            call(events::nextIndexCall {}.abi_encode()),
            call(events::hashChainCall {}.abi_encode()),
            call(events::rootStateCall {}.abi_encode()),
        )?;
        let bad =
            |e: alloy::sol_types::Error| inconsistent(format!("undecodable ledger getter: {e}"));
        let next = events::nextIndexCall::abi_decode_returns(&next).map_err(bad)?;
        let hc = events::hashChainCall::abi_decode_returns(&hc).map_err(bad)?;
        let rs = events::rootStateCall::abi_decode_returns(&rs).map_err(bad)?;
        let rs_index = rs.index;

        if next > k {
            let why = format!("ledger says next index {next} at {at}, we have {k}");
            return Ok(Onchain::Missing {
                from_block: before(st.last_commitment_block),
                why,
            });
        }
        if next < k {
            return Err(Fail::new(
                Verdict::BehindHead,
                format!("node's state at {at} (next index {next}) is behind its logs ({k})"),
            ));
        }
        if hc != chain {
            // same count, different content: logs from another fork or a broken answer. Retry; a source that keeps
            // doing this gets failed over.
            return Err(inconsistent(format!(
                "ledger hash chain {hc} at {at} differs from ours {chain}"
            )));
        }
        if rs_index > root_index {
            let why = format!("ledger says root index {rs_index} at {at}, we have {root_index}");
            return Ok(Onchain::Missing {
                from_block: before(st.last_root_block),
                why,
            });
        }
        if rs_index < root_index {
            return Err(Fail::new(
                Verdict::BehindHead,
                format!("node's root state at {at} ({rs_index}) is behind its logs ({root_index})"),
            ));
        }
        if root.is_some_and(|r| r != rs.root) {
            return Err(inconsistent(format!(
                "ledger root {} at {at} differs from the last root entry",
                rs.root
            )));
        }
        Ok(Onchain::Agrees)
    }

    /// Silent log loss detected: never commit this batch. Whatever is missing lies after block `target` (the
    /// caller picks it per stream: the missing log may share a block with the last stored one). Drop from there and
    /// refetch with narrow ranges, preferably from another node, until the region has been passed.
    async fn repair(
        &mut self,
        si: usize,
        target: u64,
        from: u64,
        to: u64,
        why: String,
    ) -> Result<bool> {
        let target = target.min(from.saturating_sub(1)); // never skip blocks that were not fetched yet
        warn!("silent log loss: {why}; rolling back to block {target} and refetching carefully");
        self.rollback(target, None).await?;
        // Same region failed again: go narrower, but not below MIN_PARANOID. Size-dependent loss (providers that
        // truncate wide ranges) is cured by a modest width; below that, repeated failures are random damage and
        // shrinking further only slows the retry down.
        let pw = match self.paranoid {
            Some((_, pw)) => (pw.min(self.executed) / 2).max(MIN_PARANOID),
            None => (self.executed / 4).max(MIN_PARANOID),
        };
        self.paranoid = Some((self.paranoid.map_or(to, |(u, _)| u.max(to)), pw));
        // this width loses logs on this provider: don't return to it right after the repaired region
        self.ctl.width = self
            .ctl
            .width
            .min(((self.executed as f64 * 0.8) as u64).max(MIN_REPAIR_WIDTH));
        self.shared.rpc.mark_failed(si, &why); // prefer another node for the retry, if there is one
        self.suspect = None;
        let mut st = self.shared.status.lock();
        st.gap_repairs += 1;
        st.last_gap = why;
        st.paranoid_width = Some(pw);
        st.cursor = target;
        Ok(true)
    }

    /// Structural checks on a getLogs answer; any violation means "this answer can't be trusted, ask again".
    fn validate_logs(&self, logs: &mut Vec<Log>, from: u64, to: u64) -> Result<(), Fail> {
        let topics = events::topics();
        for l in logs.iter() {
            let ok = !l.removed
                && (l.address() == self.c.ledger || l.address() == self.c.verifier)
                && l.topics().first().is_some_and(|t| topics.contains(t))
                && l.block_number.is_some_and(|n| (from..=to).contains(&n))
                && l.block_hash.is_some()
                && l.transaction_hash.is_some()
                && l.log_index.is_some();
            if !ok {
                return Err(inconsistent(format!(
                    "malformed or out-of-range log in {from}..={to}"
                )));
            }
        }
        logs.sort_by_key(|l| (l.block_number, l.log_index)); // don't trust provider ordering
        logs.dedup_by_key(|l| (l.block_number, l.log_index));
        Ok(())
    }

    /// Closes [`events::check_ops`]'s blind spot (a rage exit losing both its logs, e.g. to a truncated tail) for
    /// every header we fetched: all of the window, and `to` while backfilling. logsBloom has no false negatives, so a
    /// block whose bloom holds the Verifier and `NullifierSpent` or `RageExited`, yet returned no such log, is asked
    /// again on its own by hash (EIP-234). Logs there mean the answer lost them; three empty answers mean the bloom
    /// matched by chance, which busy blocks do. Chains that leave the bloom empty get no check.
    async fn check_blooms(
        &self,
        src: &Source,
        headers: &[Header],
        logs: &[Log],
    ) -> Result<Option<u64>, Fail> {
        let v = self.c.verifier;
        for h in headers.iter().filter(|h| !h.bloom.is_zero()) {
            for topic in [
                events::NullifierSpent::SIGNATURE_HASH,
                events::RageExited::SIGNATURE_HASH,
            ] {
                let promised = h.bloom.contains_input(BloomInput::Raw(v.as_slice()))
                    && h.bloom.contains_input(BloomInput::Raw(topic.as_slice()));
                let seen = logs.iter().any(|l| {
                    l.block_number == Some(h.number)
                        && l.address() == v
                        && l.topics().first() == Some(&topic)
                });
                if !promised || seen {
                    continue;
                }
                let f = Filter::new()
                    .at_block_hash(h.hash)
                    .address(v)
                    .event_signature(topic);
                for _ in 0..3 {
                    if !retry_local(|| src.logs(&f)).await?.is_empty() {
                        return Ok(Some(h.number));
                    }
                }
            }
        }
        Ok(None)
    }

    fn check_headers(
        &self,
        headers: &[Header],
        logs: &[Log],
        cur: Option<(u64, Option<B256>)>,
    ) -> Result<(), Fail> {
        if let (Some((pn, Some(ph))), Some(h0)) = (cur, headers.first())
            && h0.number == pn + 1
            && h0.parent_hash != ph
        {
            return Err(inconsistent(format!(
                "block {} does not extend our cursor",
                h0.number
            )));
        }
        for w in headers.windows(2) {
            if w[1].parent_hash != w[0].hash {
                return Err(inconsistent(format!(
                    "headers {}..{} are not one chain",
                    w[0].number, w[1].number
                )));
            }
        }
        for h in headers {
            if logs
                .iter()
                .any(|l| l.block_number == Some(h.number) && l.block_hash != Some(h.hash))
            {
                return Err(inconsistent(format!(
                    "logs of block {} are from a different fork than its header",
                    h.number
                )));
            }
        }
        Ok(())
    }
}

/// Newest stored window block whose hash still matches the chain. A missing block never matches. If nothing matches,
/// the reorg is deeper than the window, which the window is sized never to see, so its floor is taken as the ancestor.
async fn common_ancestor(
    pool: &PgPool,
    src: &Source,
    bad: u64,
    depth: u64,
) -> Result<(u64, Option<B256>)> {
    let w = db::window(pool).await?;
    for (n, h) in &w {
        if *n < bad && src.header_opt(*n).await?.map(|b| b.hash) == Some(*h) {
            return Ok((*n, Some(*h)));
        }
    }
    let floor = w
        .last()
        .map_or(bad.saturating_sub(depth), |(n, _)| n.saturating_sub(1));
    Ok((floor, None))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn index_continuity() {
        assert_eq!(check_indices(5, &[]), Ok(()));
        assert_eq!(check_indices(5, &[5, 6, 7]), Ok(()));
        assert_eq!(check_indices(0, &[0]), Ok(()));
        // head loss, middle loss: both are gaps
        assert_eq!(
            check_indices(5, &[6, 7]),
            Err(IndexIssue::Gap {
                expected: 5,
                got: 6
            })
        );
        assert_eq!(
            check_indices(5, &[5, 6, 8, 9]),
            Err(IndexIssue::Gap {
                expected: 7,
                got: 8
            })
        );
        // duplicates / going backwards
        assert_eq!(
            check_indices(5, &[5, 5]),
            Err(IndexIssue::Regress {
                expected: 6,
                got: 5
            })
        );
        assert_eq!(
            check_indices(5, &[5, 6, 4]),
            Err(IndexIssue::Regress {
                expected: 7,
                got: 4
            })
        );
        assert_eq!(
            check_indices(5, &[3]),
            Err(IndexIssue::Regress {
                expected: 5,
                got: 3
            })
        );
    }
}
