//! Flushes deposit addresses once funds reach them, paying the gas and taking a flat fee out of each.
use anyhow::{Context, Result};
use parking_lot::Mutex;
use std::sync::Arc;
use std::time::Duration;
use zerc20_common::{Chain, Fees, Sender, each_chain, serve};
use zerc20_deposit_relayer::contracts::IDepositAddressFactory;
use zerc20_deposit_relayer::store::Store;
use zerc20_deposit_relayer::{App, api, watch};

#[tokio::main]
async fn main() -> Result<()> {
    zerc20_common::init_logging()?;
    each_chain(run).await
}

async fn run(c: Chain) -> Result<()> {
    let sender = Sender::new(&c.env("RPC_URL")?, &c.env("PRIVATE_KEY")?)?;
    tracing::info!("relaying from {}", sender.address());
    let provider = sender.provider().clone();
    let factory = c.contract(&provider, "DEPOSIT_ADDRESS_FACTORY").await?;
    let registry = IDepositAddressFactory::new(factory, &provider)
        .registry()
        .call()
        .await?;
    // by default the relayer's key; in a deployment, the treasurer
    let fee_recipient = match c.var("FEE_RECIPIENT") {
        Some(a) => a.parse().context("FEE_RECIPIENT is not an address")?,
        None => sender.address(),
    };
    tracing::info!("fees go to {fee_recipient}");
    let app = Arc::new(App {
        fees: Fees::new(&c, provider.clone(), registry).await?,
        sender,
        provider,
        factory,
        fee_recipient,
        store: Mutex::new(Store::open(
            &c.var("STORE").unwrap_or("registrations.jsonl".into()),
        )?),
    });
    let listen = c.var("LISTEN").unwrap_or("127.0.0.1:8080".into());
    tokio::select! {
        r = app.fees.run() => r,
        r = watch::run(app.clone(), Duration::from_secs(c.env_u64("POLL_SECS", 15))) => r,
        r = serve(&listen, api::router(app.clone())) => r,
    }
}
