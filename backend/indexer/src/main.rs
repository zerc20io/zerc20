//! Indexes each chain's commitments, nullifiers and proved roots.
use anyhow::Result;
use std::sync::Arc;
use std::time::Duration;
use zerc20_common::{Chain, each_chain, serve};
use zerc20_indexer::rpc::Rpc;
use zerc20_indexer::sync::Shared;
use zerc20_indexer::{api, db, sync};

#[tokio::main]
async fn main() -> Result<()> {
    zerc20_common::init_logging()?;
    each_chain(run).await
}

async fn run(c: Chain) -> Result<()> {
    let pool = db::init(&c.env("DATABASE_URL")?).await?;
    // RPC_URLS: comma-separated, first = primary, the rest are failover
    let urls: Vec<String> = c
        .env("RPC_URLS")?
        .split(',')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect();
    let rpc = Rpc::new(
        &urls,
        Duration::from_secs(c.env_u64("RPC_TIMEOUT_SECS", 20)),
    )?;
    let shared = Arc::new(Shared::new(
        rpc,
        Duration::from_secs(c.env_u64("STALL_SECS", 300)),
    ));
    let cfg = sync::Config {
        ledger: c.env("LEDGER")?.parse()?,
        verifier: c.env("VERIFIER")?.parse()?,
        start_block: c.var("START_BLOCK").map(|v| v.parse()).transpose()?, // required on first start
        reorg_depth: c.env_u64("REORG_DEPTH", 64),
        batch_initial: c.env_u64("BATCH_BLOCKS", 2000),
        batch_max: c.env_u64("BATCH_MAX_BLOCKS", 10_000),
        missing_grace: Duration::from_secs(c.env_u64("MISSING_GRACE_SECS", 30)),
        poll: Duration::from_secs(c.env_u64("POLL_SECS", 5)),
        final_only: c.var("FINAL_ONLY").is_some_and(|v| v == "1"),
    };
    let listen = c.var("LISTEN").unwrap_or("0.0.0.0:3000".into());
    tokio::select! {
        r = sync::run(pool.clone(), shared.clone(), cfg) => r,
        r = serve(&listen, api::router(pool, shared)) => r,
    }
}
