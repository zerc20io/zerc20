//! The attester's host: checks a statement's public side, then has the enclave check its witness and sign.
mod api;

use alloy::primitives::{Address, U256};
use alloy::providers::{DynProvider, Provider, ProviderBuilder};
use alloy::signers::local::PrivateKeySigner;
use anyhow::{Context, Result, anyhow, ensure};
use parking_lot::RwLock;
use std::collections::HashSet;
use std::sync::Arc;
use std::time::Duration;
use tracing::{info, warn};
use zerc20_attester::{Enclave, PORT, Request};
use zerc20_common::contracts::{ILedger, ledger_and_blocklist};
use zerc20_common::{Chain, Chainalysis, Indexer, each_chain, env, env_u64, serve};
use zerc20_enclave::{Reply, Target, kms_decrypt};
use zerc20_zkp::tree::CHUNK;

const POLL: Duration = Duration::from_secs(2);
const KEY_POLL: Duration = Duration::from_secs(10);
/// How long the enclave may take over a request.
const TIMEOUT: Duration = Duration::from_secs(30);

/// The signing key pair's private half, encrypted under a KMS key that releases it only to the enclave's image.
struct Kms {
    key_id: String,
    blob: String,
}

pub struct App {
    provider: DynProvider,
    chain: u64,
    verifier: Address,
    ledger: Address,
    /// The protocol's sanctions list, shared by every token: what decides once Chainalysis keeps failing.
    blocklist: Address,
    /// This chain's. It is trusted: only roots it derived itself are attested, since a circuit soundness bug could put
    /// a forged root into `provedRoots`.
    indexer: Indexer,
    chainalysis: Chainalysis,
    /// Every chain's, since they share one key.
    quota: Arc<api::Quota>,
    fallback_after: Duration,
    enclave: Target,
    /// Every proved root the indexer derived itself. Only grows: one reorged away fails on chain anyway.
    roots: RwLock<HashSet<U256>>,
}

impl App {
    /// One request over a fresh connection.
    async fn ask(&self, request: Request) -> Result<Reply> {
        self.enclave.ask(request, TIMEOUT).await
    }
}

/// For requests the enclave can only fail at by fault of the host.
async fn must(enclave: Target, request: Request) -> Result<serde_json::Value> {
    enclave.ask(request, TIMEOUT).await?.map_err(|e| anyhow!(e))
}

#[tokio::main]
async fn main() -> Result<()> {
    zerc20_common::init_logging()?;
    let vsock = || anyhow::Ok(Target::Vsock(env_u64("ENCLAVE_CID", 16).try_into()?, PORT));
    // `load-key` is root's, run apart: KMS takes the instance's credentials, which the host that serves never holds
    if std::env::args().nth(1).as_deref() == Some("load-key") {
        let kms = Kms {
            key_id: env("KMS_KEY_ID")?,
            blob: env("ATTESTER_KEY_BLOB")?,
        };
        return load_key(vsock()?, &kms).await;
    }
    let enclave = match std::env::var("DEV_SIGNING_KEY").ok() {
        Some(key) => {
            let signer: PrivateKeySigner = key.parse()?;
            warn!(
                "DEV_SIGNING_KEY: the enclave's logic runs in this process and signs as {}. Never register this \
                 key where funds are real.",
                signer.address()
            );
            let e = Arc::new(Enclave::default());
            e.load(signer).map_err(|e| anyhow!(e))?;
            Target::local(Arc::new(move |r, _| e.handle(r)))?
        }
        None => vsock()?,
    };
    // serve only once the enclave can sign
    let address = loop {
        match must(enclave, Request::Attestation).await {
            Ok(info) => match info["address"].as_str() {
                Some(a) => break a.to_owned(),
                None => info!("waiting for the enclave's signing key (zerc20-attester load-key)"),
            },
            Err(e) => warn!("asking the enclave: {e:#}"),
        }
        tokio::time::sleep(KEY_POLL).await;
    };
    info!(
        "the enclave signs as {address}; only the address of the KMS key pair's public key may be registered"
    );
    // one enclave signs for every chain
    let quota = Arc::new(api::Quota::new());
    each_chain(move |c| run(c, enclave, quota.clone())).await
}

async fn run(c: Chain, enclave: Target, quota: Arc<api::Quota>) -> Result<()> {
    let provider = ProviderBuilder::new()
        .connect_http(c.env("RPC_URL")?.parse()?)
        .erased();
    let verifier = c.contract(&provider, "VERIFIER").await?;
    let (ledger, blocklist) = ledger_and_blocklist(&provider, verifier).await?;
    let chainalysis = Chainalysis::from_env(&c)?;
    let chain = provider.get_chain_id().await?;
    let app = Arc::new(App {
        provider,
        chain,
        verifier,
        ledger,
        blocklist,
        indexer: Indexer::new(&c.env("INDEXER_URL")?)?,
        chainalysis,
        quota,
        fallback_after: Duration::from_secs(c.env_u64("FALLBACK_SECS", 300)),
        enclave,
        roots: RwLock::default(),
    });
    info!("attesting on chain {chain} for Verifier {verifier}");
    let listen = c.var("LISTEN").unwrap_or("0.0.0.0:3002".into());
    tokio::select! {
        r = roots_loop(app.clone()) => r,
        r = app.chainalysis.watch() => r,
        r = serve(&listen, api::router(app.clone())) => r,
    }
}

/// KMS decrypts the key for the enclave's attestation document, re-encrypted to the RSA key in it: the host sees only
/// ciphertext, and the key policy refuses any other image. Nothing to do while the enclave has a key, so a deployment
/// runs it every minute, which also loads the key again after the enclave restarts.
async fn load_key(enclave: Target, kms: &Kms) -> Result<()> {
    if !must(enclave, Request::Attestation).await?["address"].is_null() {
        return Ok(());
    }
    let document = must(enclave, Request::KmsAttestation).await?;
    let document = document.as_str().context("KmsAttestation")?;
    let cms = kms_decrypt(&kms.key_id, &kms.blob, document).await?;
    let address = must(enclave, Request::LoadKey { cms }).await?;
    let address = address.as_str().context("LoadKey")?;
    info!(
        "the enclave signs as {address}; only the address of the KMS key pair's public key may be registered"
    );
    Ok(())
}

async fn roots_loop(app: Arc<App>) -> Result<()> {
    let mut read = 0;
    loop {
        match refresh_roots(&app, read).await {
            Ok(n) => read = n,
            Err(e) => warn!("reading the indexer's roots failed: {e:#}"),
        }
        tokio::time::sleep(POLL).await;
    }
}

/// Adds the roots past the first `read` entries of `/roots`, and returns how many entries are read.
async fn refresh_roots(app: &App, read: u64) -> Result<u64> {
    let count = app.indexer.status().await?["roots"]
        .as_u64()
        .context("roots")?;
    // a reorg can take roots back; read their places again
    let mut read = read.min(count);
    let mut fresh = Vec::new();
    while read < count {
        let page = read / CHUNK;
        let entries = app.indexer.proved_roots(page).await?;
        let skip = (read % CHUNK) as usize;
        let n = entries.len().saturating_sub(skip);
        ensure!(n > 0, "roots page {page} ends before /status says");
        fresh.extend(
            entries[skip..]
                .iter()
                .filter(|e| e.2)
                .map(|&(size, root, _)| (size, root)),
        );
        read += n as u64;
    }
    // Only this chain's ledger may vouch for roots here, or another chain's indexer would have its roots attested.
    // Proved at all, not accepted now: in an emergency the ledger bounds the roots, and the contract checks that.
    if let Some(&(size, root)) = fresh.last() {
        let era = ILedger::new(app.ledger, &app.provider)
            .provedIn(size, root)
            .call()
            .await?;
        ensure!(
            era != 0,
            "the indexer at {} serves another chain: its root {root:#066x} over {size} is not proved here",
            app.indexer.base()
        );
        app.roots.write().extend(fresh.iter().map(|&(_, r)| r));
        info!("{read} roots read, the latest one derived {root:#066x} over {size}");
    }
    Ok(read)
}
