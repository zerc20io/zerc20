//! Submits `transact` and `merge` on behalf of users, for a flat fee per token.
mod api;
mod fee;

use alloy::primitives::{Address, U256};
use alloy::providers::{DynProvider, Provider};
use anyhow::{Context, Result, ensure};
use parking_lot::Mutex;
use serde::Serialize;
use std::collections::HashSet;
use std::sync::Arc;
use zerc20_common::contracts::IVerifier;
use zerc20_common::fields::{fr, u256};
use zerc20_common::{AppendFile, Chain, Fees, Sender, each_chain, serve, whole_lines};
use zerc20_zkp::ark_bn254::Fr;

/// One line of the fee-notes file: what spending a fee note needs besides its owner's key. A note's line is written
/// before its transaction is sent, and again with `index` once it is mined; the later line wins.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct FeeNoteLine {
    chain_id: u64,
    token_id: u32,
    value: U256,
    salt: U256,
    note_hash: U256,
    #[serde(skip_serializing_if = "Option::is_none")]
    index: Option<u64>,
}

pub struct App {
    /// Sends with the relayer key, which pays the gas.
    sender: Sender,
    /// `sender`'s, for reads.
    provider: DynProvider,
    verifier: Address,
    chain_id: u64,
    /// Where the fees paid as withdrawals, and merges' fees, go.
    fee_recipient: Address,
    /// The fee per token, in its base units. Only these tokens are relayed.
    fees: Fees,
    /// The public key fee notes must be owned by: a wallet's, which alone spends them.
    public_key: Fr,
    /// Nullifiers of the requests being relayed.
    in_flight: Mutex<HashSet<U256>>,
    reverted_unwraps: api::RevertedUnwraps,
    /// ponytail: only grows, and the relayer never reads it back; the tool that spends fee notes will.
    fee_notes: Mutex<AppendFile>,
}

impl App {
    /// Durable before it returns.
    fn record(&self, l: &FeeNoteLine) -> Result<()> {
        let mut line = serde_json::to_vec(l)?;
        line.push(b'\n');
        self.fee_notes.lock().append(&line)
    }
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
    let chain_id = provider.get_chain_id().await?;
    let public_key: U256 = c
        .env("FEE_PUBLIC_KEY")?
        .parse()
        .context("FEE_PUBLIC_KEY is not a number")?;
    ensure!(
        u256(fr(public_key)) == public_key,
        "FEE_PUBLIC_KEY is not a field element"
    );
    let registry = IVerifier::new(verifier, &provider).factory().call().await?;
    // by default the relayer's key; in a deployment, the treasurer
    let fee_recipient = match c.var("FEE_RECIPIENT") {
        Some(a) => a.parse().context("FEE_RECIPIENT is not an address")?,
        None => sender.address(),
    };
    tracing::info!(
        "relaying from {} on chain {chain_id}, fees to {fee_recipient}",
        sender.address()
    );
    let app = Arc::new(App {
        fees: Fees::new(&c, provider.clone(), registry).await?,
        sender,
        provider,
        verifier,
        chain_id,
        fee_recipient,
        public_key: fr(public_key),
        in_flight: Mutex::new(HashSet::new()),
        reverted_unwraps: Default::default(),
        // a line torn by a crash was never acknowledged: its request failed before sending
        fee_notes: Mutex::new(
            AppendFile::open(
                &c.var("FEE_NOTES").unwrap_or("fee-notes.jsonl".into()),
                whole_lines,
            )?
            .0,
        ),
    });
    let listen = c.var("LISTEN").unwrap_or("127.0.0.1:8080".into());
    tokio::select! {
        r = app.fees.run() => r,
        r = serve(&listen, api::router(app.clone())) => r,
    }
}
