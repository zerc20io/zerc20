use crate::events::{Meta, Nullifier, RootProof};
use crate::rpc::Header;
use alloy::primitives::{B256, U256};
use anyhow::Result;
use sqlx::{PgConnection, PgPool, Row};
use zerc20_common::fields::fr;
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::tree::{CHUNK_BITS, PAGE_BITS};

pub async fn init(url: &str) -> Result<PgPool> {
    let pool = PgPool::connect(url).await?;
    sqlx::raw_sql(include_str!("schema.sql"))
        .execute(&pool)
        .await?;
    Ok(pool)
}

fn u(b: &[u8]) -> U256 {
    U256::from_be_slice(b)
}
fn h(b: &[u8]) -> B256 {
    B256::from_slice(b)
}
fn words(v: &[U256]) -> Vec<u8> {
    v.iter().flat_map(|w| w.to_be_bytes::<32>()).collect()
}

/// Where each stream stands, read before a batch is applied on top.
pub struct State {
    pub commitments: u64,
    pub hash_chain: U256,
    pub last_commitment_block: Option<u64>,
    pub nullifiers: u64,
    pub roots: u64,
    /// `newIndex` and root of the last root entry, `RootProved` or `Recovered` (0 and None before the first).
    pub root_index: u64,
    pub root: Option<U256>,
    pub last_root_block: Option<u64>,
}

pub async fn state(pool: &PgPool) -> Result<State> {
    let c = sqlx::query(
        "SELECT idx, block_number, hash_chain FROM commitments ORDER BY idx DESC LIMIT 1",
    )
    .fetch_optional(pool)
    .await?;
    let r = sqlx::query(
        "SELECT new_index, root, block_number, pos FROM roots ORDER BY pos DESC LIMIT 1",
    )
    .fetch_optional(pool)
    .await?;
    let nullifiers = nullifier_count(pool).await?;
    Ok(State {
        commitments: c.as_ref().map_or(0, |c| c.get::<i64, _>(0) as u64 + 1),
        hash_chain: c.as_ref().map_or(U256::ZERO, |c| u(c.get(2))),
        last_commitment_block: c.as_ref().map(|c| c.get::<i64, _>(1) as u64),
        nullifiers,
        roots: r.as_ref().map_or(0, |r| r.get::<i64, _>(3) as u64 + 1),
        root_index: r.as_ref().map_or(0, |r| r.get::<i64, _>(0) as u64),
        root: r.as_ref().map(|r| u(r.get(1))),
        last_root_block: r.as_ref().map(|r| r.get::<i64, _>(2) as u64),
    })
}

pub async fn cursor(pool: &PgPool) -> Result<Option<(u64, Option<B256>)>> {
    let r = sqlx::query("SELECT block_number, block_hash FROM cursor WHERE id = 1")
        .fetch_optional(pool)
        .await?;
    Ok(r.map(|r| {
        (
            r.get::<i64, _>(0) as u64,
            r.get::<Option<Vec<u8>>, _>(1).map(|b| h(&b)),
        )
    }))
}

/// Stored window blocks, newest first.
pub async fn window(pool: &PgPool) -> Result<Vec<(u64, B256)>> {
    let rows = sqlx::query("SELECT number, hash FROM blocks ORDER BY number DESC")
        .fetch_all(pool)
        .await?;
    Ok(rows
        .iter()
        .map(|r| (r.get::<i64, _>(0) as u64, h(r.get(1))))
        .collect())
}

/// Every full chunk's and every full page's root, in order.
pub async fn subtree_roots(pool: &PgPool) -> Result<(Vec<Fr>, Vec<Fr>)> {
    let chunks = sqlx::query_scalar("SELECT root FROM chunk_roots ORDER BY chunk").fetch_all(pool);
    let pages = sqlx::query_scalar("SELECT root FROM page_roots ORDER BY page").fetch_all(pool);
    let (chunks, pages): (Vec<Vec<u8>>, Vec<Vec<u8>>) = tokio::try_join!(chunks, pages)?;
    Ok((
        chunks.iter().map(|b| fr(u(b))).collect(),
        pages.iter().map(|b| fr(u(b))).collect(),
    ))
}

/// Roots of full chunks `lo..hi`, in order.
pub async fn chunk_roots(pool: &PgPool, lo: u64, hi: u64) -> Result<Vec<Vec<u8>>> {
    Ok(sqlx::query_scalar(
        "SELECT root FROM chunk_roots WHERE chunk >= $1 AND chunk < $2 ORDER BY chunk",
    )
    .bind(lo as i64)
    .bind(hi as i64)
    .fetch_all(pool)
    .await?)
}

pub async fn chunk_count(pool: &PgPool) -> Result<u64> {
    let n: i64 = sqlx::query_scalar("SELECT COALESCE(MAX(chunk) + 1, 0) FROM chunk_roots")
        .fetch_one(pool)
        .await?;
    Ok(n as u64)
}

pub async fn page_roots(pool: &PgPool) -> Result<Vec<Vec<u8>>> {
    Ok(
        sqlx::query_scalar("SELECT root FROM page_roots ORDER BY page")
            .fetch_all(pool)
            .await?,
    )
}

/// Block of commitment `idx`, if stored.
pub async fn commitment_block(pool: &PgPool, idx: u64) -> Result<Option<u64>> {
    let b: Option<i64> = sqlx::query_scalar("SELECT block_number FROM commitments WHERE idx = $1")
        .bind(idx as i64)
        .fetch_optional(pool)
        .await?;
    Ok(b.map(|b| b as u64))
}

/// `(block, fields)` of commitments `lo..hi`, in order. Fewer rows than asked means they aren't (or no longer) there.
pub async fn commitments(pool: &PgPool, lo: u64, hi: u64) -> Result<Vec<(u64, Vec<u8>)>> {
    let rows = sqlx::query(
        "SELECT block_number, fields FROM commitments WHERE idx >= $1 AND idx < $2 ORDER BY idx",
    )
    .bind(lo as i64)
    .bind(hi as i64)
    .fetch_all(pool)
    .await?;
    Ok(rows
        .iter()
        .map(|r| (r.get::<i64, _>(0) as u64, r.get(1)))
        .collect())
}

/// How many of the latest roots the settle time is measured over: enough that a few slow rounds, as after an outage,
/// do not move it, and few enough to follow the provers' pace as it changes.
const SETTLE_ROOTS: i64 = 20;
/// How many it takes to measure it at all, so that one odd round does not set it.
const SETTLE_MIN_ROOTS: usize = 5;

/// How long a commitment waits for a proved root to cover it. Each of the latest roots newly covers the commitments
/// since the round before reserved its own; the earliest of them waited longest, from its block's time to the root's.
/// This is the median of those waits. Anyone may prove roots, at any pace, so it is measured rather than configured.
/// Only roots the indexer derives itself and that move forward count, and only ones whose time is known.
pub async fn settle_secs(pool: &PgPool) -> Result<Option<u64>> {
    let waits: Vec<i64> = sqlx::query_scalar(
        "SELECT r.block_time - min(c.block_time) FROM \
         (SELECT pos, old_index, new_index, block_time FROM roots \
          WHERE block_time IS NOT NULL AND root = local_root AND new_index > old_index ORDER BY pos DESC LIMIT $1) r \
         JOIN commitments c ON c.idx >= r.old_index AND c.idx < r.new_index \
         GROUP BY r.pos, r.block_time",
    )
    .bind(SETTLE_ROOTS)
    .fetch_all(pool)
    .await?;
    Ok(median_wait(waits))
}

/// `(pos, block)` of the latest roots the settle time could be measured over whose time is unknown.
pub async fn untimed_roots(pool: &PgPool) -> Result<Vec<(u64, u64)>> {
    let rows = sqlx::query(
        "SELECT pos, block_number FROM \
         (SELECT pos, block_number, block_time FROM roots \
          WHERE root = local_root AND new_index > old_index ORDER BY pos DESC LIMIT $1) r \
         WHERE block_time IS NULL",
    )
    .bind(SETTLE_ROOTS)
    .fetch_all(pool)
    .await?;
    Ok(rows
        .iter()
        .map(|r| (r.get::<i64, _>(0) as u64, r.get::<i64, _>(1) as u64))
        .collect())
}

/// Sets roots' block times, `(pos, unix seconds)`.
pub async fn set_root_times(pool: &PgPool, times: &[(u64, u64)]) -> Result<()> {
    sqlx::query(
        "UPDATE roots SET block_time = t.time \
         FROM UNNEST($1::bigint[], $2::bigint[]) AS t(pos, time) WHERE roots.pos = t.pos",
    )
    .bind(times.iter().map(|t| t.0 as i64).collect::<Vec<_>>())
    .bind(times.iter().map(|t| t.1 as i64).collect::<Vec<_>>())
    .execute(pool)
    .await?;
    Ok(())
}

/// The median of rounds' `waits`, in seconds, once there are enough of them.
fn median_wait(mut waits: Vec<i64>) -> Option<u64> {
    if waits.len() < SETTLE_MIN_ROOTS {
        return None;
    }
    waits.sort_unstable();
    Some(waits[waits.len() / 2].max(0) as u64)
}

/// `(block, block time)` of commitments `lo..hi`, in order.
pub async fn times(pool: &PgPool, lo: u64, hi: u64) -> Result<Vec<(u64, u64)>> {
    let rows = sqlx::query("SELECT block_number, block_time FROM commitments WHERE idx >= $1 AND idx < $2 ORDER BY idx")
        .bind(lo as i64)
        .bind(hi as i64)
        .fetch_all(pool)
        .await?;
    Ok(rows
        .iter()
        .map(|r| (r.get::<i64, _>(0) as u64, r.get::<i64, _>(1) as u64))
        .collect())
}

/// `(block, nullifier)` at positions `lo..hi`, in order.
pub async fn nullifiers(pool: &PgPool, lo: u64, hi: u64) -> Result<Vec<(u64, Vec<u8>)>> {
    let rows = sqlx::query(
        "SELECT block_number, nullifier FROM nullifiers WHERE pos >= $1 AND pos < $2 ORDER BY pos",
    )
    .bind(lo as i64)
    .bind(hi as i64)
    .fetch_all(pool)
    .await?;
    Ok(rows
        .iter()
        .map(|r| (r.get::<i64, _>(0) as u64, r.get(1)))
        .collect())
}

/// Ledger hash chain right before commitment `idx` (the chain is 0 before the first one).
pub async fn hash_chain_before(pool: &PgPool, idx: u64) -> Result<Option<U256>> {
    if idx == 0 {
        return Ok(Some(U256::ZERO));
    }
    let b: Option<Vec<u8>> =
        sqlx::query_scalar("SELECT hash_chain FROM commitments WHERE idx = $1")
            .bind(idx as i64 - 1)
            .fetch_optional(pool)
            .await?;
    Ok(b.map(|b| u(&b)))
}

pub async fn commitment_count(pool: &PgPool) -> Result<u64> {
    let n: i64 = sqlx::query_scalar("SELECT COALESCE(MAX(idx) + 1, 0) FROM commitments")
        .fetch_one(pool)
        .await?;
    Ok(n as u64)
}

pub async fn nullifier_count(pool: &PgPool) -> Result<u64> {
    let n: i64 = sqlx::query_scalar("SELECT COALESCE(MAX(pos) + 1, 0) FROM nullifiers")
        .fetch_one(pool)
        .await?;
    Ok(n as u64)
}

/// How many commitments / nullifiers sit in blocks before `block` (both streams are ordered by block).
pub async fn final_counts(pool: &PgPool, block: u64) -> Result<(u64, u64)> {
    let c: Option<i64> = sqlx::query_scalar(
        "SELECT idx FROM commitments WHERE block_number < $1 ORDER BY block_number DESC, idx DESC LIMIT 1",
    )
    .bind(block as i64)
    .fetch_optional(pool)
    .await?;
    let n: Option<i64> = sqlx::query_scalar(
        "SELECT pos FROM nullifiers WHERE block_number < $1 ORDER BY block_number DESC, pos DESC LIMIT 1",
    )
    .bind(block as i64)
    .fetch_optional(pool)
    .await?;
    Ok((c.map_or(0, |c| c as u64 + 1), n.map_or(0, |n| n as u64 + 1)))
}

/// `(block, nullifiers before it)` for commitment pages `lo..hi` that have begun: the block of commitment `k * 4096`,
/// and how many nullifiers sit in strictly earlier blocks. A note at `i` is spent only after a root over it is proved,
/// which needs a later block, so its nullifier sits at or after the count of page `i / 4096`.
pub async fn marks(pool: &PgPool, lo: u64, hi: u64) -> Result<Vec<(u64, u64)>> {
    let rows = sqlx::query(
        "SELECT c.block_number, COALESCE((SELECT n.pos + 1 FROM nullifiers n WHERE n.block_number < c.block_number \
         ORDER BY n.block_number DESC, n.pos DESC LIMIT 1), 0) \
         FROM generate_series($1::bigint, $2::bigint - 1) AS k JOIN commitments c ON c.idx = k * $3 ORDER BY k",
    )
    .bind(lo as i64)
    .bind(hi as i64)
    .bind(1i64 << CHUNK_BITS)
    .fetch_all(pool)
    .await?;
    Ok(rows
        .iter()
        .map(|r| (r.get::<i64, _>(0) as u64, r.get::<i64, _>(1) as u64))
        .collect())
}

pub struct RootRow {
    pub new_index: u64,
    pub root: U256,
    pub local_root: U256,
    pub partial_chunk_root: Option<U256>,
    pub partial_page_root: Option<U256>,
    pub block: u64,
}

/// A row selected as `new_index, root, local_root, partial_chunk_root, partial_page_root, block_number`.
fn root_row(r: &sqlx::postgres::PgRow) -> RootRow {
    let opt = |b: Option<Vec<u8>>| b.map(|b| u(&b));
    RootRow {
        new_index: r.get::<i64, _>(0) as u64,
        root: u(r.get(1)),
        local_root: u(r.get(2)),
        partial_chunk_root: opt(r.get(3)),
        partial_page_root: opt(r.get(4)),
        block: r.get::<i64, _>(5) as u64,
    }
}

/// Proved roots at positions `lo..hi`, in order of proof.
pub async fn roots(pool: &PgPool, lo: u64, hi: u64) -> Result<Vec<RootRow>> {
    let rows = sqlx::query(
        "SELECT new_index, root, local_root, partial_chunk_root, partial_page_root, block_number FROM roots \
         WHERE pos >= $1 AND pos < $2 ORDER BY pos",
    )
    .bind(lo as i64)
    .bind(hi as i64)
    .fetch_all(pool)
    .await?;
    Ok(rows.iter().map(root_row).collect())
}

/// The first proved root since the last recovery that differs from the indexer's own, and the newest root before
/// it that does not: the one a proof can still use.
pub async fn usable_root(pool: &PgPool) -> Result<(Option<RootRow>, Option<RootRow>)> {
    let bad = sqlx::query(
        "SELECT new_index, root, local_root, partial_chunk_root, partial_page_root, block_number, pos FROM roots \
         WHERE root <> local_root AND pos >= (SELECT COALESCE(MAX(pos), 0) FROM roots WHERE new_index <= old_index) \
         ORDER BY pos LIMIT 1",
    )
    .fetch_optional(pool)
    .await?;
    let before = bad.as_ref().map_or(i64::MAX, |r| r.get::<i64, _>(6));
    let good = sqlx::query(
        "SELECT new_index, root, local_root, partial_chunk_root, partial_page_root, block_number FROM roots \
         WHERE root = local_root AND pos < $1 ORDER BY pos DESC LIMIT 1",
    )
    .bind(before)
    .fetch_optional(pool)
    .await?;
    Ok((good.as_ref().map(root_row), bad.as_ref().map(root_row)))
}

pub async fn root_count(pool: &PgPool) -> Result<u64> {
    let n: i64 = sqlx::query_scalar("SELECT COALESCE(MAX(pos) + 1, 0) FROM roots")
        .fetch_one(pool)
        .await?;
    Ok(n as u64)
}

pub struct NewCommitment {
    pub meta: Meta,
    pub fields: [U256; 4],
    pub hash_chain: U256,
    /// Its block's time, unix seconds.
    pub time: u64,
}
pub struct NewRoot<'a> {
    pub proof: &'a RootProof,
    pub local_root: U256,
    pub partial_chunk_root: Option<U256>,
    pub partial_page_root: Option<U256>,
    /// Its block's time, unix seconds.
    pub time: u64,
}

/// Everything one verified batch adds, written in one transaction so a crash can't leave the streams, the chunk
/// roots, the reorg window and the cursor out of step.
pub struct Batch<'a> {
    pub first_commitment: u64,
    pub commitments: &'a [NewCommitment],
    pub first_nullifier: u64,
    pub nullifiers: &'a [Nullifier],
    pub first_root: u64,
    pub roots: &'a [NewRoot<'a>],
    pub chunk_roots: &'a [(u64, U256)],
    pub page_roots: &'a [(u64, U256)],
    pub blocks: &'a [Header],
    pub cursor: (u64, Option<B256>),
    /// Window blocks below this are pruned.
    pub keep_from: u64,
}

fn col<T, V>(xs: &[T], f: impl Fn(&T) -> V) -> Vec<V> {
    xs.iter().map(f).collect()
}

pub async fn write_batch(pool: &PgPool, b: Batch<'_>) -> Result<()> {
    let mut tx = pool.begin().await?;
    let cs = b.commitments;
    sqlx::query(
        "INSERT INTO commitments (idx, block_number, log_index, block_hash, tx_hash, fields, hash_chain, block_time) \
         SELECT * FROM UNNEST($1::bigint[], $2::bigint[], $3::bigint[], $4::bytea[], $5::bytea[], $6::bytea[], $7::bytea[], $8::bigint[])",
    )
    .bind((0..cs.len()).map(|j| (b.first_commitment + j as u64) as i64).collect::<Vec<_>>())
    .bind(col(cs, |c| c.meta.block as i64))
    .bind(col(cs, |c| c.meta.log_index as i64))
    .bind(col(cs, |c| c.meta.block_hash.to_vec()))
    .bind(col(cs, |c| c.meta.tx_hash.to_vec()))
    .bind(col(cs, |c| words(&c.fields)))
    .bind(col(cs, |c| words(&[c.hash_chain])))
    .bind(col(cs, |c| c.time as i64))
    .execute(&mut *tx)
    .await?;
    let ns = b.nullifiers;
    sqlx::query(
        "INSERT INTO nullifiers (pos, nullifier, block_number, log_index, block_hash, tx_hash) \
         SELECT * FROM UNNEST($1::bigint[], $2::bytea[], $3::bigint[], $4::bigint[], $5::bytea[], $6::bytea[])",
    )
    .bind((0..ns.len()).map(|j| (b.first_nullifier + j as u64) as i64).collect::<Vec<_>>())
    .bind(col(ns, |n| words(&[n.nullifier])))
    .bind(col(ns, |n| n.meta.block as i64))
    .bind(col(ns, |n| n.meta.log_index as i64))
    .bind(col(ns, |n| n.meta.block_hash.to_vec()))
    .bind(col(ns, |n| n.meta.tx_hash.to_vec()))
    .execute(&mut *tx)
    .await?;
    let rs = b.roots;
    sqlx::query(
        "INSERT INTO roots (pos, new_index, old_index, root, local_root, partial_chunk_root, partial_page_root, \
         block_number, log_index, block_time) SELECT * FROM UNNEST($1::bigint[], $2::bigint[], $3::bigint[], \
         $4::bytea[], $5::bytea[], $6::bytea[], $7::bytea[], $8::bigint[], $9::bigint[], $10::bigint[])",
    )
    .bind((0..rs.len()).map(|j| (b.first_root + j as u64) as i64).collect::<Vec<_>>())
    .bind(col(rs, |r| r.proof.new_index as i64))
    .bind(col(rs, |r| r.proof.old_index as i64))
    .bind(col(rs, |r| words(&[r.proof.root])))
    .bind(col(rs, |r| words(&[r.local_root])))
    .bind(col(rs, |r| r.partial_chunk_root.map(|p| words(&[p]))))
    .bind(col(rs, |r| r.partial_page_root.map(|p| words(&[p]))))
    .bind(col(rs, |r| r.proof.meta.block as i64))
    .bind(col(rs, |r| r.proof.meta.log_index as i64))
    .bind(col(rs, |r| r.time as i64))
    .execute(&mut *tx)
    .await?;
    sqlx::query(
        "INSERT INTO chunk_roots (chunk, root) SELECT * FROM UNNEST($1::bigint[], $2::bytea[])",
    )
    .bind(col(b.chunk_roots, |c| c.0 as i64))
    .bind(col(b.chunk_roots, |c| words(&[c.1])))
    .execute(&mut *tx)
    .await?;
    sqlx::query(
        "INSERT INTO page_roots (page, root) SELECT * FROM UNNEST($1::bigint[], $2::bytea[])",
    )
    .bind(col(b.page_roots, |p| p.0 as i64))
    .bind(col(b.page_roots, |p| words(&[p.1])))
    .execute(&mut *tx)
    .await?;
    sqlx::query(
        "INSERT INTO blocks (number, hash, parent_hash) SELECT * FROM UNNEST($1::bigint[], $2::bytea[], $3::bytea[]) \
         ON CONFLICT (number) DO UPDATE SET hash = EXCLUDED.hash, parent_hash = EXCLUDED.parent_hash",
    )
    .bind(col(b.blocks, |h| h.number as i64))
    .bind(col(b.blocks, |h| h.hash.to_vec()))
    .bind(col(b.blocks, |h| h.parent_hash.to_vec()))
    .execute(&mut *tx)
    .await?;
    sqlx::query("DELETE FROM blocks WHERE number < $1")
        .bind(b.keep_from as i64)
        .execute(&mut *tx)
        .await?;
    set_cursor(&mut tx, b.cursor).await?;
    tx.commit().await?;
    Ok(())
}

async fn set_cursor(tx: &mut PgConnection, c: (u64, Option<B256>)) -> Result<()> {
    sqlx::query("INSERT INTO cursor VALUES (1, $1, $2) ON CONFLICT (id) DO UPDATE SET block_number = $1, block_hash = $2")
        .bind(c.0 as i64)
        .bind(c.1.map(|h| h.to_vec()))
        .execute(tx)
        .await?;
    Ok(())
}

/// Drop everything above block `target` (the common ancestor, or the start of a region to refetch). Every stream
/// is ordered by block, so this cuts a suffix off each; chunks and pages that are no longer full lose their root.
pub async fn rollback(pool: &PgPool, target: u64, target_hash: Option<B256>) -> Result<()> {
    let mut tx = pool.begin().await?;
    for q in [
        "DELETE FROM commitments WHERE block_number > $1",
        "DELETE FROM nullifiers WHERE block_number > $1",
        "DELETE FROM roots WHERE block_number > $1",
    ] {
        sqlx::query(q).bind(target as i64).execute(&mut *tx).await?;
    }
    let k: i64 = sqlx::query_scalar("SELECT COALESCE(MAX(idx) + 1, 0) FROM commitments")
        .fetch_one(&mut *tx)
        .await?;
    sqlx::query("DELETE FROM chunk_roots WHERE (chunk + 1) << $1 > $2")
        .bind(CHUNK_BITS as i32)
        .bind(k)
        .execute(&mut *tx)
        .await?;
    sqlx::query("DELETE FROM page_roots WHERE (page + 1) << $1 > $2")
        .bind(PAGE_BITS as i32)
        .bind(k)
        .execute(&mut *tx)
        .await?;
    sqlx::query("DELETE FROM blocks WHERE number > $1")
        .bind(target as i64)
        .execute(&mut *tx)
        .await?;
    set_cursor(&mut tx, (target, target_hash)).await?;
    tx.commit().await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn settle_time_is_the_median_round_once_there_are_enough() {
        assert_eq!(
            median_wait(vec![300, 420, 360, 380]),
            None,
            "too few rounds"
        );
        // an outage's catch-up round does not move it
        assert_eq!(median_wait(vec![300, 7200, 420, 360, 380]), Some(380));
        assert_eq!(
            median_wait(vec![-1, -1, -1, 5, 6]),
            Some(0),
            "never below zero"
        );
    }
}
