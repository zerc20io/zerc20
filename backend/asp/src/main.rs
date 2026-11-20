//! Screens deposit senders and publishes ASP roots.
mod api;
mod screen;
mod tree;

use alloy::primitives::{Address, U256};
use alloy::providers::{DynProvider, Provider};
use anyhow::{Result, ensure};
use parking_lot::Mutex;
use std::collections::HashSet;
use std::sync::Arc;
use std::time::Duration;
use tracing::{info, warn};
use zerc20_common::contracts::{IVerifier, ledger_and_blocklist};
use zerc20_common::{Chain, Chainalysis, Indexer, Sender, each_chain, serve};

pub struct App {
    /// Publishes with the `aspPublisher` key.
    sender: Sender,
    /// `sender`'s, for reads.
    provider: DynProvider,
    verifier: Address,
    ledger: Address,
    /// The protocol's sanctions list, shared by every token: the last resort when Chainalysis keeps failing.
    blocklist: Address,
    /// This chain's. It is trusted: it says who sent each deposit.
    indexer: Indexer,
    chainalysis: Chainalysis,
    /// Development only (`DEV_REJECT`), where Chainalysis passes everyone: senders that fail, so that rejections can
    /// be tested.
    dev_reject: HashSet<Address>,
    /// Seconds a deposit's block must be old before its sender is screened.
    delay: u64,
    publish_every: Duration,
    tree: Mutex<tree::Tree>,
}

#[tokio::main]
async fn main() -> Result<()> {
    zerc20_common::init_logging()?;
    each_chain(run).await
}

async fn run(c: Chain) -> Result<()> {
    let sender = Sender::new(&c.env("RPC_URL")?, &c.env("PRIVATE_KEY")?)?;
    let provider = sender.provider().clone();
    let verifier = c.contract(&provider, "VERIFIER").await?;
    let (ledger, blocklist) = ledger_and_blocklist(&provider, verifier).await?;
    let chainalysis = Chainalysis::from_env(&c)?;
    let dev_reject: HashSet<Address> = c
        .var("DEV_REJECT")
        .unwrap_or_default()
        .split(',')
        .filter(|a| !a.trim().is_empty())
        .map(|a| a.trim().parse())
        .collect::<Result<_, _>>()?;
    ensure!(
        dev_reject.is_empty() || chainalysis.passes_all(),
        "DEV_REJECT is for development, with DEV_PASS_ALL=1"
    );
    // CREATE3 gives the Verifier one address on every chain, so the chain id keys the files too
    let chain = provider.get_chain_id().await?;
    let dir = c.var("DATA_DIR").unwrap_or("asp-data".into());
    std::fs::create_dir_all(&dir)?;
    let tree = tree::Tree::open(&format!("{dir}/{chain}-{verifier:#x}"))?;
    info!(
        "publishing from {} on chain {chain}; {} positions decided",
        sender.address(),
        tree.decided()
    );
    let app = Arc::new(App {
        sender,
        provider,
        verifier,
        ledger,
        blocklist,
        indexer: Indexer::new(&c.env("INDEXER_URL")?)?,
        chainalysis,
        dev_reject,
        delay: c.env_u64("SCREEN_DELAY_SECS", 600),
        publish_every: Duration::from_secs(c.env_u64("PUBLISH_SECS", 300)),
        tree: Mutex::new(tree),
    });
    let listen = c.var("LISTEN").unwrap_or("0.0.0.0:3001".into());
    tokio::select! {
        r = screen::run(app.clone()) => r,
        r = publish_loop(app.clone()) => r,
        // what `/status` says of it, for the watcher
        r = app.chainalysis.watch() => r,
        r = serve(&listen, api::router(app.clone())) => r,
    }
}

async fn publish_loop(app: Arc<App>) -> Result<()> {
    loop {
        if let Err(e) = publish(&app).await {
            warn!("publish failed: {e:#}");
        }
        tokio::time::sleep(app.publish_every).await;
    }
}

/// Publishes the current root unless it is the one on chain already. That also covers a first start, a new
/// publisher (which resets the root to 0) and a dropped transaction.
async fn publish(app: &App) -> Result<()> {
    let v = IVerifier::new(app.verifier, &app.provider);
    let publisher = v.aspPublisher().call().await?;
    if publisher != app.sender.address() {
        warn!("not publishing: the ASP publisher is {publisher}");
        return Ok(());
    }
    let latest = v.latestAspRoot().call().await?;
    let r = {
        let mut t = app.tree.lock();
        let r = t.current();
        if r.root == latest {
            return Ok(());
        }
        if latest != U256::ZERO && !t.knows(latest) {
            warn!(
                "latestAspRoot {latest:#066x} is not one of ours: another publisher, or a leaked key?"
            );
        }
        t.record(r)?;
        r
    };
    let receipt = app
        .sender
        .send(v.publishAspRoot(r.root).into_transaction_request())
        .await?;
    info!(
        "published {:#066x} over {} positions in {}",
        r.root, r.size, receipt.transaction_hash
    );
    Ok(())
}
