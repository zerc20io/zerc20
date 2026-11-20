//! Bulk, identical-for-everyone reads, shaped for a CDN in front: no endpoint names a leaf, an address or a nullifier.
//!
//! Every list that grows is served in numbered pages of 4096 entries (entry `i` is on page `i / 4096`), including
//! the page still filling up. An answer therefore always says where its entries sit, whatever `/status` said a
//! moment earlier, and nothing a wallet polls grows with the chain. A page that is full and whose last entry is final
//! never changes again and is cached forever; anything newer is cached for seconds.
use crate::db::{self, RootRow};
use crate::events;
use crate::sync::Shared;
use alloy::primitives::U256;
use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::http::header::{CACHE_CONTROL, CONTENT_TYPE};
use axum::response::{IntoResponse, Response};
use axum::routing::get;
use axum::{Json, Router};
use serde_json::json;
use sqlx::PgPool;
use std::sync::Arc;
use tower_http::compression::CompressionLayer;
use zerc20_common::fields::fields_of;
use zerc20_zkp::tree::{CHUNK, CHUNK_BITS, PAGE_BITS};

const IMMUTABLE: &str = "public, max-age=31536000, immutable";
/// Full, but not final yet: a reorg may still rewrite it.
const RECENT: &str = "public, max-age=5";
/// Still filling up, and status: every wallet polls them, so even 2s spares the origin.
const LIVE: &str = "public, max-age=2";

#[derive(Clone)]
struct App {
    pool: PgPool,
    shared: Arc<Shared>,
}
impl App {
    fn window_start(&self) -> u64 {
        self.shared.status.lock().window_start
    }
}

type Res = Result<Response, Response>;

fn e500(e: impl std::fmt::Display) -> Response {
    (
        StatusCode::INTERNAL_SERVER_ERROR,
        [(CACHE_CONTROL, "no-store")],
        e.to_string(),
    )
        .into_response()
}
fn missing() -> Response {
    (
        StatusCode::NOT_FOUND,
        [(CACHE_CONTROL, "no-store")],
        "not found",
    )
        .into_response()
}
fn bin(body: Vec<u8>, cache: &'static str) -> Response {
    (
        [
            (CONTENT_TYPE, "application/octet-stream"),
            (CACHE_CONTROL, cache),
        ],
        body,
    )
        .into_response()
}
fn hex(v: U256) -> String {
    format!("{v:#066x}")
}

/// Positions `lo..lo + 4096` of page `{p}` of a list with `count` entries. The page filling up is served too, even
/// while empty; one beyond it is not there yet.
fn span(p: &str, count: u64) -> Option<(u64, u64)> {
    let lo = p.parse::<u64>().ok()?.checked_mul(CHUNK)?;
    (lo <= count).then_some((lo, lo + CHUNK))
}

/// Cache policy for a page of `len` entries whose last one sits in `last_block`: forever only once the page is full
/// and that block is final.
fn policy(len: usize, last_block: Option<u64>, window_start: u64) -> &'static str {
    match last_block {
        _ if len as u64 != CHUNK => LIVE,
        Some(b) if b < window_start => IMMUTABLE,
        _ => RECENT,
    }
}

/// Hash chain before the chunk (32 bytes, for rage exits), then each commitment's 4 fields (128 bytes).
async fn commitments(State(a): State<App>, Path(p): Path<String>) -> Res {
    let count = db::commitment_count(&a.pool).await.map_err(e500)?;
    let (lo, hi) = span(&p, count).ok_or_else(missing)?;
    let rows = db::commitments(&a.pool, lo, hi).await.map_err(e500)?;
    let prev = db::hash_chain_before(&a.pool, lo)
        .await
        .map_err(e500)?
        .ok_or_else(missing)?;
    let mut body = prev.to_be_bytes::<32>().to_vec();
    rows.iter().for_each(|(_, f)| body.extend_from_slice(f));
    Ok(bin(
        body,
        policy(rows.len(), rows.last().map(|r| r.0), a.window_start()),
    ))
}

/// One 4-byte [`events::tag`] per commitment, so a wallet finds its deposits and notes without naming them.
async fn tags(State(a): State<App>, Path(p): Path<String>) -> Res {
    let count = db::commitment_count(&a.pool).await.map_err(e500)?;
    let (lo, hi) = span(&p, count).ok_or_else(missing)?;
    let rows = db::commitments(&a.pool, lo, hi).await.map_err(e500)?;
    let body = rows
        .iter()
        .flat_map(|(_, f)| events::tag(&fields_of(f)))
        .collect();
    Ok(bin(
        body,
        policy(rows.len(), rows.last().map(|r| r.0), a.window_start()),
    ))
}

/// The block of each commitment, 8 bytes big-endian: the ASP screens a deposit only once its block is old enough.
async fn blocks(State(a): State<App>, Path(p): Path<String>) -> Res {
    let count = db::commitment_count(&a.pool).await.map_err(e500)?;
    let (lo, hi) = span(&p, count).ok_or_else(missing)?;
    let rows = db::commitments(&a.pool, lo, hi).await.map_err(e500)?;
    let body = rows.iter().flat_map(|(b, _)| b.to_be_bytes()).collect();
    Ok(bin(
        body,
        policy(rows.len(), rows.last().map(|r| r.0), a.window_start()),
    ))
}

/// The time of each commitment's block, 8 bytes big-endian unix seconds: wallets date what they find by it, the same
/// on every device.
async fn times(State(a): State<App>, Path(p): Path<String>) -> Res {
    let count = db::commitment_count(&a.pool).await.map_err(e500)?;
    let (lo, hi) = span(&p, count).ok_or_else(missing)?;
    let rows = db::times(&a.pool, lo, hi).await.map_err(e500)?;
    let body = rows.iter().flat_map(|(_, t)| t.to_be_bytes()).collect();
    Ok(bin(
        body,
        policy(rows.len(), rows.last().map(|r| r.0), a.window_start()),
    ))
}

/// The first 8 bytes of each spent nullifier, in the order they were spent. 8 bytes keep false "spent" matches
/// negligible (about 5e-11 for 100 notes against 10M nullifiers).
async fn nullifiers(State(a): State<App>, Path(p): Path<String>) -> Res {
    let count = db::nullifier_count(&a.pool).await.map_err(e500)?;
    let (lo, hi) = span(&p, count).ok_or_else(missing)?;
    let rows = db::nullifiers(&a.pool, lo, hi).await.map_err(e500)?;
    let body = rows.iter().flat_map(|(_, n)| n[..8].to_vec()).collect();
    Ok(bin(
        body,
        policy(rows.len(), rows.last().map(|r| r.0), a.window_start()),
    ))
}

/// One entry per page of 4096 commitments: the block of the page's first commitment (8 bytes) and the number of
/// nullifiers in earlier blocks (8 bytes). A wallet reads its notes' nullifiers from there on, so restoring an old
/// wallet does not mean reading every nullifier since genesis.
async fn marks(State(a): State<App>, Path(p): Path<String>) -> Res {
    let count = db::commitment_count(&a.pool).await.map_err(e500)?;
    let (lo, hi) = span(&p, count.div_ceil(CHUNK)).ok_or_else(missing)?;
    let rows = db::marks(&a.pool, lo, hi).await.map_err(e500)?;
    let body = rows
        .iter()
        .flat_map(|(b, n)| [b.to_be_bytes(), n.to_be_bytes()].concat())
        .collect();
    Ok(bin(
        body,
        policy(rows.len(), rows.last().map(|r| r.0), a.window_start()),
    ))
}

/// Page `{p}`: the roots of full chunks `p * 4096 ..`, 32 bytes each. A wallet needs only the page holding its
/// chunk, plus `page-roots`.
async fn chunk_roots(State(a): State<App>, Path(p): Path<String>) -> Res {
    let count = db::chunk_count(&a.pool).await.map_err(e500)?;
    let (lo, hi) = span(&p, count).ok_or_else(missing)?;
    let rows = db::chunk_roots(&a.pool, lo, hi).await.map_err(e500)?;
    // a full page is final once the last commitment under it is
    let last = db::commitment_block(&a.pool, (hi << CHUNK_BITS) - 1)
        .await
        .map_err(e500)?;
    Ok(bin(
        rows.concat(),
        policy(rows.len(), last, a.window_start()),
    ))
}

/// Roots of full pages (2^24 commitments each), 32 bytes each: at most 256, since the tree has 2^32 leaves.
async fn page_roots(State(a): State<App>) -> Res {
    let rows = db::page_roots(&a.pool).await.map_err(e500)?;
    Ok(bin(rows.concat(), LIVE))
}

/// One proved root as 105 bytes: its size (8, big-endian), the root (32), the roots of the partial chunk and page at
/// that size (32 each, zero where the size ends on a boundary), and 1 if the indexer derives the same root, else 0.
/// A wallet builds a path against it from its chunk, its page of `chunk-roots` and `page-roots`.
fn root_entry(r: &RootRow) -> Vec<u8> {
    let mut e = r.new_index.to_be_bytes().to_vec();
    for w in [Some(r.root), r.partial_chunk_root, r.partial_page_root] {
        e.extend(w.unwrap_or_default().to_be_bytes::<32>());
    }
    e.push((r.root == r.local_root) as u8);
    e
}

/// Page `{p}` of proved roots in the order they were proved. The latest one is also in `/status`.
async fn roots(State(a): State<App>, Path(p): Path<String>) -> Res {
    let count = db::root_count(&a.pool).await.map_err(e500)?;
    let (lo, hi) = span(&p, count).ok_or_else(missing)?;
    let rows = db::roots(&a.pool, lo, hi).await.map_err(e500)?;
    let body = rows.iter().flat_map(root_entry).collect();
    Ok(bin(
        body,
        policy(rows.len(), rows.last().map(|r| r.block), a.window_start()),
    ))
}

/// Counts tell a wallet which pages exist. `*_final` counts are what downstream nodes (the ASP) may act on:
/// they cannot be reorged away.
///
/// `latest_root` is the newest proved root the indexer derives itself, before any it does not: the one every node
/// and wallet proves against. `mismatch` is the first proved root since the last recovery that the indexer does not
/// derive: a forged one, which puts the ledger in an emergency. `settle_secs` is how long a commitment usually waits for
/// a root, which wallets tell a settling coin's time by.
async fn status(State(a): State<App>) -> Res {
    let (
        commitments,
        nullifiers,
        roots,
        (commitments_final, nullifiers_final),
        (latest, mismatch),
        settle_secs,
    ) = tokio::try_join!(
        db::commitment_count(&a.pool),
        db::nullifier_count(&a.pool),
        db::root_count(&a.pool),
        db::final_counts(&a.pool, a.window_start()),
        db::usable_root(&a.pool),
        db::settle_secs(&a.pool)
    )
    .map_err(e500)?;
    let latest = latest.map(|r| {
        json!({
            "index": r.new_index, "root": hex(r.root), "matches": r.root == r.local_root,
            "partial_chunk_root": r.partial_chunk_root.map(hex), "partial_page_root": r.partial_page_root.map(hex),
        })
    });
    let body = json!({
        "commitments": commitments, "commitments_final": commitments_final,
        "nullifiers": nullifiers, "nullifiers_final": nullifiers_final,
        "chunks": commitments >> CHUNK_BITS, "pages": commitments >> PAGE_BITS,
        "roots": roots, "latest_root": latest,
        "mismatch": mismatch.map(|r| json!({ "index": r.new_index, "root": hex(r.root) })),
        "settle_secs": settle_secs,
        "indexer": a.shared.json(),
    });
    Ok(([(CACHE_CONTROL, LIVE)], Json(body)).into_response())
}

pub fn router(pool: PgPool, shared: Arc<Shared>) -> Router {
    Router::new()
        .route("/status", get(status))
        .route("/commitments/{p}", get(commitments))
        .route("/tags/{p}", get(tags))
        .route("/blocks/{p}", get(blocks))
        .route("/times/{p}", get(times))
        .route("/nullifiers/{p}", get(nullifiers))
        .route("/marks/{p}", get(marks))
        .route("/chunk-roots/{p}", get(chunk_roots))
        .route("/page-roots", get(page_roots))
        .route("/roots/{p}", get(roots))
        .with_state(App { pool, shared })
        // CloudFront does not compress application/octet-stream itself
        .layer(CompressionLayer::new())
        .layer(zerc20_common::cors())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spans_and_cache_policy() {
        assert_eq!(
            span("0", 0),
            Some((0, CHUNK)),
            "the first page, still empty"
        );
        assert_eq!(span("1", CHUNK + 5), Some((CHUNK, 2 * CHUNK)), "filling up");
        assert_eq!(span("1", CHUNK), Some((CHUNK, 2 * CHUNK)), "just started");
        assert_eq!(span("2", CHUNK + 5), None, "not there yet");
        assert_eq!(span("x", 2 * CHUNK), None);
        assert_eq!(span(&u64::MAX.to_string(), 2 * CHUNK), None, "no overflow");

        let full = CHUNK as usize;
        assert_eq!(policy(full, Some(9), 10), IMMUTABLE);
        assert_eq!(
            policy(full, Some(10), 10),
            RECENT,
            "last entry not final yet"
        );
        assert_eq!(policy(full, None, 10), RECENT, "rolled back meanwhile");
        assert_eq!(policy(5, Some(0), 10), LIVE, "still filling, even if final");
        assert_eq!(policy(0, None, 10), LIVE);
    }

    #[test]
    fn root_entries_are_fixed_width() {
        let r = RootRow {
            new_index: CHUNK,
            root: U256::from(1),
            local_root: U256::from(1),
            partial_chunk_root: None,
            partial_page_root: Some(U256::from(2)),
            block: 0,
        };
        let e = root_entry(&r);
        assert_eq!(e.len(), 105);
        assert_eq!(e[..8], CHUNK.to_be_bytes());
        assert_eq!(
            (e[71], e[103], e[104]),
            (0, 2, 1),
            "absent chunk root is zero; page root; matches"
        );
    }
}
