//! Fault-injecting JSON-RPC proxy for testing the indexer against flaky providers.
//!   UPSTREAM=http://127.0.0.1:8545 LISTEN=127.0.0.1:8546 cargo run --example chaos_proxy
//! Requests pinned to a block hash (EIP-1898 eth_call, EIP-234 getLogs) get the same lag / pruning treatment as
//! the block's number would.
//! Knobs (env, probabilities in 0..1): P5XX P429 PBAD (truncated JSON)  PLAG (request is served by a node that is
//! LAG blocks behind: stale head, null for newer blocks, newer logs missing)  LAG  LATENCY_MS (max random delay)
//! RANGE_LIMIT (max getLogs block span)  LOG_LIMIT (max logs per getLogs)
//! Silent loss (HTTP 200, no error): PDROP (drop 1-3 logs from the middle)  PTRUNC (drop 1-3 logs from the tail)
//! PEMPTY (answer [] for a range that has logs)  DROP_WIDE=N (ranges wider than N blocks always lose every 5th log)
//! NOARCHIVE=K (eth_call at blocks older than head-K fails like a pruned node)
//! Control: GET /_dead/1 (always 503) | /_dead/0 | /_stats
#![allow(
    clippy::unwrap_used,
    reason = "a test harness: an upstream call that fails drops the connection, one more fault for the indexer"
)]
use axum::{
    Json, Router,
    extract::State,
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::{get, post},
};
use serde_json::{Value, json};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
use std::time::Duration;

fn envf(k: &str, d: f64) -> f64 {
    std::env::var(k)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(d)
}

#[derive(Default)]
struct Counters {
    reqs: AtomicU64,
    e5xx: AtomicU64,
    e429: AtomicU64,
    bad: AtomicU64,
    range: AtomicU64,
    toomany: AtomicU64,
    lagged: AtomicU64,
    dropped: AtomicU64,
    truncated: AtomicU64,
    emptied: AtomicU64,
    wide: AtomicU64,
    nostate: AtomicU64,
    dead: AtomicU64,
    ok: AtomicU64,
}
struct App {
    upstream: String,
    http: reqwest::Client,
    dead: AtomicBool,
    c: Counters,
    p5xx: f64,
    p429: f64,
    pbad: f64,
    plag: f64,
    lag: u64,
    latency: u64,
    range_limit: u64,
    log_limit: usize,
    pdrop: f64,
    ptrunc: f64,
    pempty: f64,
    drop_wide: u64,
    noarchive: u64,
}

fn hex(v: &Value) -> Option<u64> {
    u64::from_str_radix(v.as_str()?.trim_start_matches("0x"), 16).ok()
}
fn envelope(id: &Value, r: Result<Value, (i64, String)>) -> Response {
    match r {
        Ok(v) => Json(json!({"jsonrpc":"2.0","id":id,"result":v})).into_response(),
        Err((code, message)) => {
            Json(json!({"jsonrpc":"2.0","id":id,"error":{"code":code,"message":message}}))
                .into_response()
        }
    }
}

impl App {
    /// Number of the block `hash`, or None if upstream doesn't know it.
    async fn number_of(&self, hash: &Value) -> Option<u64> {
        hex(&self.fwd(&json!({"jsonrpc":"2.0","id":0,"method":"eth_getBlockByHash","params":[hash, false]})).await["result"]["number"])
    }
    async fn fwd(&self, req: &Value) -> Value {
        self.http
            .post(&self.upstream)
            .json(req)
            .send()
            .await
            .unwrap()
            .json()
            .await
            .unwrap()
    }
    async fn head(&self) -> u64 {
        hex(&self
            .fwd(&json!({"jsonrpc":"2.0","id":0,"method":"eth_blockNumber","params":[]}))
            .await["result"])
        .unwrap()
    }
}

async fn rpc(State(a): State<Arc<App>>, Json(req): Json<Value>) -> Response {
    a.c.reqs.fetch_add(1, Relaxed);
    if a.dead.load(Relaxed) {
        a.c.dead.fetch_add(1, Relaxed);
        return (StatusCode::SERVICE_UNAVAILABLE, "upstream unavailable").into_response();
    }
    if a.latency > 0 {
        tokio::time::sleep(Duration::from_millis(fastrand::u64(0..=a.latency))).await;
    }
    let r = fastrand::f64();
    if r < a.p5xx {
        a.c.e5xx.fetch_add(1, Relaxed);
        return (StatusCode::BAD_GATEWAY, "bad gateway").into_response();
    }
    if r < a.p5xx + a.p429 {
        a.c.e429.fetch_add(1, Relaxed);
        return (StatusCode::TOO_MANY_REQUESTS, "Too Many Requests").into_response();
    }
    if r < a.p5xx + a.p429 + a.pbad {
        a.c.bad.fetch_add(1, Relaxed);
        return (StatusCode::OK, "{\"jsonrpc\":\"2.0\",\"id\":1,\"res").into_response();
    }
    let (id, method) = (
        req["id"].clone(),
        req["method"].as_str().unwrap_or("").to_string(),
    );
    let lag = if fastrand::f64() < a.plag {
        fastrand::u64(1..=a.lag)
    } else {
        0
    };
    if lag > 0 {
        a.c.lagged.fetch_add(1, Relaxed);
    }
    match method.as_str() {
        "eth_blockNumber" if lag > 0 => envelope(
            &id,
            Ok(json!(format!("0x{:x}", a.head().await.saturating_sub(lag)))),
        ),
        "eth_getBlockByNumber" if lag > 0 => {
            let n = hex(&req["params"][0]);
            let seen = a.head().await.saturating_sub(lag);
            if n.is_some_and(|n| n > seen) {
                envelope(&id, Ok(Value::Null))
            } else {
                Json(a.fwd(&req).await).into_response()
            }
        }
        "eth_getLogs" => {
            let f = &req["params"][0];
            if !f["blockHash"].is_null() {
                // EIP-234: a node that doesn't have the block yet says so instead of answering []
                let n = a.number_of(&f["blockHash"]).await.unwrap_or(u64::MAX);
                if lag > 0 && n > a.head().await.saturating_sub(lag) {
                    return envelope(&id, Err((-32000, "unknown block".into())));
                }
            }
            let (from, to) = match f["blockHash"].is_null() {
                true => (
                    hex(&f["fromBlock"]).unwrap_or(0),
                    hex(&f["toBlock"]).unwrap_or(u64::MAX),
                ),
                false => (0, 0),
            };
            if a.range_limit > 0 && to.saturating_sub(from) + 1 > a.range_limit {
                a.c.range.fetch_add(1, Relaxed);
                return envelope(
                    &id,
                    Err((
                        -32600,
                        format!("eth_getLogs is limited to a {} blocks range", a.range_limit),
                    )),
                );
            }
            let mut req = req.clone();
            if lag > 0 && f["blockHash"].is_null() {
                // a node whose log index is `lag` blocks stale silently omits the newest logs
                let seen = a.head().await.saturating_sub(lag);
                if from > seen {
                    return envelope(&id, Ok(json!([])));
                }
                req["params"][0]["toBlock"] = json!(format!("0x{:x}", to.min(seen)));
            }
            let mut up = a.fwd(&req).await;
            if let Some(arr) = up["result"].as_array_mut().filter(|a| !a.is_empty()) {
                if a.drop_wide > 0 && to.saturating_sub(from) + 1 > a.drop_wide {
                    let mut i = 0;
                    arr.retain(|_| {
                        i += 1;
                        i % 5 != 0
                    });
                    a.c.wide.fetch_add(1, Relaxed);
                }
                let r = fastrand::f64();
                if r < a.pempty {
                    arr.clear();
                    a.c.emptied.fetch_add(1, Relaxed);
                } else if r < a.pempty + a.ptrunc {
                    let n = fastrand::usize(1..=3).min(arr.len());
                    arr.truncate(arr.len() - n);
                    a.c.truncated.fetch_add(1, Relaxed);
                } else if r < a.pempty + a.ptrunc + a.pdrop && arr.len() >= 3 {
                    for _ in 0..fastrand::usize(1..=3).min(arr.len() - 2) {
                        arr.remove(fastrand::usize(1..arr.len() - 1));
                    }
                    a.c.dropped.fetch_add(1, Relaxed);
                }
            }
            if a.log_limit > 0
                && up["result"]
                    .as_array()
                    .is_some_and(|l| l.len() > a.log_limit)
            {
                a.c.toomany.fetch_add(1, Relaxed);
                return envelope(
                    &id,
                    Err((
                        -32005,
                        format!("query returned more than {} results", a.log_limit),
                    )),
                );
            }
            a.c.ok.fetch_add(1, Relaxed);
            Json(up).into_response()
        }
        "eth_call" => {
            let at = &req["params"][1];
            let n = match at["blockHash"].is_null() {
                true => hex(at),
                false => a.number_of(&at["blockHash"]).await,
            };
            if let Some(n) = n {
                let head = a.head().await;
                if a.noarchive > 0 && n + a.noarchive < head {
                    a.c.nostate.fetch_add(1, Relaxed);
                    return envelope(
                        &id,
                        Err((
                            -32000,
                            "missing trie node 6f2c (path ) state 0x6f2c is not available".into(),
                        )),
                    );
                }
                if lag > 0 && n > head.saturating_sub(lag) {
                    return envelope(&id, Err((-32000, "header not found".into())));
                }
            }
            Json(a.fwd(&req).await).into_response()
        }
        _ => Json(a.fwd(&req).await).into_response(),
    }
}

#[tokio::main]
async fn main() {
    let a = Arc::new(App {
        upstream: std::env::var("UPSTREAM").unwrap_or("http://127.0.0.1:8545".into()),
        http: reqwest::Client::new(),
        dead: AtomicBool::new(false),
        c: Counters::default(),
        p5xx: envf("P5XX", 0.0),
        p429: envf("P429", 0.0),
        pbad: envf("PBAD", 0.0),
        plag: envf("PLAG", 0.0),
        lag: envf("LAG", 3.0) as u64,
        latency: envf("LATENCY_MS", 0.0) as u64,
        range_limit: envf("RANGE_LIMIT", 0.0) as u64,
        log_limit: envf("LOG_LIMIT", 0.0) as usize,
        pdrop: envf("PDROP", 0.0),
        ptrunc: envf("PTRUNC", 0.0),
        pempty: envf("PEMPTY", 0.0),
        drop_wide: envf("DROP_WIDE", 0.0) as u64,
        noarchive: envf("NOARCHIVE", 0.0) as u64,
    });
    let app = Router::new()
        .route("/", post(rpc))
        .route("/_dead/{v}", get(|State(a): State<Arc<App>>, axum::extract::Path(v): axum::extract::Path<u8>| async move { a.dead.store(v == 1, Relaxed); "ok" }))
        .route(
            "/_stats",
            get(|State(a): State<Arc<App>>| async move {
                let c = &a.c;
                Json(json!({"requests":c.reqs.load(Relaxed),"5xx":c.e5xx.load(Relaxed),"429":c.e429.load(Relaxed),"bad_json":c.bad.load(Relaxed),"range_err":c.range.load(Relaxed),
                    "too_many_err":c.toomany.load(Relaxed),"lagged_requests":c.lagged.load(Relaxed),"dropped_mid":c.dropped.load(Relaxed),"truncated":c.truncated.load(Relaxed),
                    "emptied":c.emptied.load(Relaxed),"wide_dropped":c.wide.load(Relaxed),"no_state":c.nostate.load(Relaxed),"dead_503":c.dead.load(Relaxed),"getlogs_ok":c.ok.load(Relaxed)}))
            }),
        )
        .with_state(a);
    let l =
        tokio::net::TcpListener::bind(std::env::var("LISTEN").unwrap_or("127.0.0.1:8546".into()))
            .await
            .unwrap();
    axum::serve(l, app).await.unwrap();
}
