//! Keeps the nodes' accounts in gas out of the relayers' fees, which come to it, and sends what it does not need to a
//! cold wallet.
use alloy::primitives::{Address, U256, keccak256};
use alloy::providers::Provider;
use alloy::rpc::types::TransactionRequest;
use alloy::signers::SignerSync;
use alloy::signers::local::PrivateKeySigner;
use anyhow::{Context, Result, ensure};
use std::time::Duration;
use tokio::time::Instant;
use tracing::{info, warn};
use zerc20_common::contracts::{IFactory, IVerifier, IZERC20, NATIVE};
use zerc20_common::fields::u256;
use zerc20_common::{Chain, Sender, each_chain, pairs};
use zerc20_zkp::primitives::Keys;
use zerc20_zkp::wallet_keys::spend_secret;

#[tokio::main]
async fn main() -> Result<()> {
    // `wallet-key` prints the public key the transact-relayer's fee notes are owned by (its FEE_PUBLIC_KEY)
    if std::env::args().nth(1).as_deref() == Some("wallet-key") {
        let key = std::env::var("PRIVATE_KEY").context("PRIVATE_KEY is not set")?;
        println!("{:#x}", wallet_key(&key.parse().context("PRIVATE_KEY")?)?);
        return Ok(());
    }
    zerc20_common::init_logging()?;
    each_chain(run).await
}

/// The public key of the account's zERC20 wallet, as the wallet SDK derives it from the account's signature
/// (`seedFromSignature` in `wallet/sdk/src/seed.ts`): opened from this account, the wallet owns what is paid to it.
fn wallet_key(account: &PrivateKeySigner) -> Result<U256> {
    let message = [
        "zERC20 wallet seed",
        "WARNING: signing this gives control of your private zERC20 funds.",
        "Sign it only in an app you trust to hold them.",
        &format!("address: {:#x}", account.address()),
        "tag: zerc20/wallet/seed/v1",
    ]
    .join("\n");
    // the canonical form, as the wallet's: low s and v = 27/28
    let signature = account
        .sign_message_sync(message.as_bytes())?
        .normalized_s();
    let seed = keccak256(signature.as_bytes());
    Ok(u256(Keys::of(spend_secret(&seed.0)).public_key))
}

struct Treasurer {
    sender: Sender,
    /// The native asset's zERC20, which the merges' fees come in, and its name.
    znative: Option<(Address, String)>,
    /// How often it is unwrapped, and when next: in memory, so a start unwraps at once.
    unwrap_every: Duration,
    next_unwrap: Instant,
    accounts: Vec<(String, Address)>,
    top_up_to: U256,
    keep: U256,
    sweep_to: Option<Address>,
}

async fn run(c: Chain) -> Result<()> {
    let sender = Sender::new(&c.env("RPC_URL")?, &c.env("PRIVATE_KEY")?)?;
    let p = sender.provider().clone();
    let me = sender.address();
    let verifier = c.contract(&p, "VERIFIER").await?;
    let factory = IFactory::new(IVerifier::new(verifier, &p).factory().call().await?, &p);
    let znative = match factory.tokenIdOf(NATIVE).call().await? {
        0 => None,
        id => {
            let token = factory.tokenById(id).call().await?;
            Some((token, IZERC20::new(token, &p).symbol().call().await?))
        }
    };
    let wei = |k: &str| -> Result<U256> {
        let v: U256 = c
            .env(k)?
            .parse()
            .with_context(|| format!("{k} is not a number of wei"))?;
        ensure!(!v.is_zero(), "{k} is 0");
        Ok(v)
    };
    let mut t = Treasurer {
        // `name=0x…,…`: the accounts whose gas the nodes spend
        accounts: pairs(&c.env("ACCOUNTS")?).context("ACCOUNTS")?,
        top_up_to: wei("TOP_UP_TO")?,
        keep: wei("KEEP")?,
        sweep_to: c
            .var("SWEEP_TO")
            .map(|a| a.parse())
            .transpose()
            .context("SWEEP_TO")?,
        znative,
        unwrap_every: Duration::from_secs(c.env_u64("UNWRAP_SECS", 3600)),
        next_unwrap: Instant::now(),
        sender,
    };
    ensure!(
        t.sweep_to != Some(me) && t.accounts.iter().all(|(_, a)| *a != me),
        "the treasurer {me} is among its own ACCOUNTS or SWEEP_TO"
    );
    info!(
        "treasurer {me}: tops up {} accounts to {} wei, keeps {} wei{}",
        t.accounts.len(),
        t.top_up_to,
        t.keep,
        t.sweep_to
            .map_or(String::new(), |s| format!(", sweeps the rest to {s}"))
    );
    let every = Duration::from_secs(c.env_u64("TICK_SECS", 60));
    loop {
        if let Err(e) = t.tick().await {
            warn!("tick failed: {e:#}");
        }
        tokio::time::sleep(every).await;
    }
}

impl Treasurer {
    /// Unwraps when due, tops up, then sweeps, each on the balances it reads. A send that fails is only warned of: one
    /// the treasurer cannot afford fails at estimation, costs nothing, and the watcher reports the account once it is
    /// low.
    async fn tick(&mut self) -> Result<()> {
        let p = self.sender.provider();
        let me = self.sender.address();
        if let Some((znative, name)) = &self.znative
            && Instant::now() >= self.next_unwrap
        {
            let token = IZERC20::new(*znative, p);
            let z = token.balanceOf(me).call().await?;
            self.next_unwrap = Instant::now() + self.unwrap_every;
            if !z.is_zero() {
                self.send(
                    format!("unwrapped {z} wei of {name}"),
                    token.unwrap(z, me).into_transaction_request(),
                )
                .await;
            }
        }
        for (name, a) in &self.accounts {
            if let Some(v) = top_up(p.get_balance(*a).await?, self.top_up_to) {
                self.send(
                    format!("topped up {name} with {v} wei"),
                    TransactionRequest::default().to(*a).value(v),
                )
                .await;
            }
        }
        if let Some(to) = self.sweep_to
            && let Some(v) = sweep(p.get_balance(me).await?, self.keep)
        {
            self.send(
                format!("swept {v} wei to {to}"),
                TransactionRequest::default().to(to).value(v),
            )
            .await;
        }
        Ok(())
    }

    async fn send(&self, what: String, tx: TransactionRequest) {
        match self.sender.send(tx).await {
            Ok(r) => info!("{what} in {}", r.transaction_hash),
            Err(e) => warn!("not {what}: {e:#}"),
        }
    }
}

/// What an account holding `balance` is sent: back up to `to`, once it is below half of that.
fn top_up(balance: U256, to: U256) -> Option<U256> {
    (balance < to / U256::from(2)).then(|| to - balance)
}

/// What the treasurer holding `balance` sweeps: down to `keep`, once it holds twice that.
fn sweep(balance: U256, keep: U256) -> Option<U256> {
    (balance > keep.saturating_mul(U256::from(2))).then(|| balance - keep)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u(x: u64) -> U256 {
        U256::from(x)
    }

    #[test]
    fn wallet_key_is_the_wallet_pages() {
        let v: serde_json::Value =
            serde_json::from_str(include_str!("../../../zkp/test-vectors/wallet-seed.json"))
                .unwrap();
        let account: PrivateKeySigner = v["privateKey"].as_str().unwrap().parse().unwrap();
        let want: U256 = v["publicKey"].as_str().unwrap().parse().unwrap();
        assert_eq!(wallet_key(&account).unwrap(), want);
    }

    #[test]
    fn decisions() {
        assert_eq!(top_up(u(49), u(100)), Some(u(51)));
        assert_eq!(top_up(u(50), u(100)), None, "half is enough");
        assert_eq!(top_up(u(0), u(100)), Some(u(100)));

        assert_eq!(sweep(u(201), u(100)), Some(u(101)));
        assert_eq!(sweep(u(200), u(100)), None, "twice is kept");
    }
}
