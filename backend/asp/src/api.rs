//! Serves the ASP tree the way the indexer serves the commitment tree: the same bytes to everyone, in pages numbered
//! like the indexer's. A wallet fetches the bitmap with the same number as its commitment chunk, so the ASP learns
//! nothing the indexer does not. Decisions are final, so a full page never changes.
use crate::App;
use crate::tree::Record;
use alloy::primitives::U256;
use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::http::header::{CACHE_CONTROL, CONTENT_TYPE};
use axum::response::{IntoResponse, Response};
use axum::routing::get;
use axum::{Json, Router};
use serde_json::json;
use std::sync::Arc;
use zerc20_common::fields::u256;
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::tree::CHUNK;

const IMMUTABLE: &str = "public, max-age=31536000, immutable";
/// Still filling up, and status: every wallet polls them, so even 2s spares the origin.
const LIVE: &str = "public, max-age=2";

fn missing() -> Response {
    (
        StatusCode::NOT_FOUND,
        [(CACHE_CONTROL, "no-store")],
        "not found",
    )
        .into_response()
}

fn octets(cache: &'static str, body: Vec<u8>) -> Response {
    (
        [
            (CONTENT_TYPE, "application/octet-stream"),
            (CACHE_CONTROL, cache),
        ],
        body,
    )
        .into_response()
}

/// 32 bytes each, big-endian.
fn words(roots: &[Fr]) -> impl Iterator<Item = u8> + '_ {
    roots.iter().flat_map(|&f| u256(f).to_be_bytes::<32>())
}

/// Entries `p * 4096 ..` of `list` and their cache policy. The page filling up is served too, even while empty; one
/// beyond it is not there yet.
fn page<'a, T, B: IntoIterator<Item = u8>>(
    list: &'a [T],
    p: &str,
    bytes: impl Fn(&'a [T]) -> B,
) -> Response {
    let lo = p
        .parse::<u64>()
        .ok()
        .and_then(|p| p.checked_mul(CHUNK))
        .and_then(|lo| usize::try_from(lo).ok());
    let Some(rest) = lo.and_then(|lo| list.get(lo..)) else {
        return missing();
    };
    let page = &rest[..rest.len().min(CHUNK as usize)];
    let cache = if page.len() == CHUNK as usize {
        IMMUTABLE
    } else {
        LIVE
    };
    octets(cache, bytes(page).into_iter().collect())
}

/// 4096 bits, 512 bytes: position `c * 4096 + j` is bit `j % 8` (least significant first) of byte `j / 8`, set if
/// approved. Positions not decided yet read 0, so a wallet clears every bit at or past the size of the root it proves
/// against.
async fn bitmap(State(app): State<Arc<App>>, Path(c): Path<String>) -> Response {
    page(app.tree.lock().bits(), &c, |bits| {
        let mut m = [0u8; CHUNK as usize / 8];
        bits.iter()
            .enumerate()
            .for_each(|(j, &b)| m[j / 8] |= (b as u8) << (j % 8));
        m
    })
}

/// Page `{p}`: the roots of full chunks `p * 4096 ..`, 32 bytes each.
async fn chunk_roots(State(app): State<Arc<App>>, Path(p): Path<String>) -> Response {
    page(app.tree.lock().chunk_roots(), &p, words)
}

/// Roots of full pages (2^24 positions each), 32 bytes each: at most 256.
async fn page_roots(State(app): State<Arc<App>>) -> Response {
    octets(LIVE, words(app.tree.lock().page_roots()).collect())
}

/// Page `{p}` of recorded roots, in the order they were recorded, 104 bytes each: the size (8, big-endian), the root,
/// and the roots of the partial chunk and page at that size (32 each, zero where the size ends on a boundary). Every
/// root is recorded before it is published, so the one on chain is always here.
async fn roots(State(app): State<Arc<App>>, Path(p): Path<String>) -> Response {
    page(app.tree.lock().records(), &p, |r| {
        r.iter().flat_map(Record::bytes)
    })
}

/// The latest recorded root. Wallets prove against `Verifier.latestAspRoot`, which is this one unless its publish is
/// still pending; otherwise they look it up in `/roots/{p}`.
async fn status(State(app): State<Arc<App>>) -> Response {
    let t = app.tree.lock();
    let hex = |v: U256| (!v.is_zero()).then(|| format!("{v:#066x}"));
    let latest = t.records().last().map(|r| {
        json!({
            "index": r.size, "root": hex(r.root),
            "partial_chunk_root": hex(r.partial_chunk), "partial_page_root": hex(r.partial_page),
        })
    });
    // The delay lets a wallet tell when a deposit should be decided. While Chainalysis is down, deposits and
    // withdrawals are screened by the Blocklist alone, which the watcher tells people about.
    let body = json!({
        "decided": t.decided(), "roots": t.records().len(), "latest_root": latest, "delay_secs": app.delay,
        "chainalysis_down_secs": app.chainalysis.down_for().as_secs(),
    });
    ([(CACHE_CONTROL, LIVE)], Json(body)).into_response()
}

pub fn router(app: Arc<App>) -> Router {
    Router::new()
        .route("/status", get(status))
        .route("/bitmap/{c}", get(bitmap))
        .route("/chunk-roots/{p}", get(chunk_roots))
        .route("/page-roots", get(page_roots))
        .route("/roots/{p}", get(roots))
        .with_state(app)
        .layer(zerc20_common::cors())
}
