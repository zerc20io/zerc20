//! One signing key's transactions, sent one at a time and repriced until mined.
use alloy::eips::BlockId;
use alloy::eips::eip1559::Eip1559Estimation;
use alloy::primitives::{Address, TxHash};
use alloy::providers::{DynProvider, Provider, ProviderBuilder};
use alloy::rpc::types::{TransactionReceipt, TransactionRequest};
use alloy::signers::local::PrivateKeySigner;
use anyhow::{Context, Result, anyhow, ensure};
use std::time::Duration;
use tokio::time::{Instant, sleep};

const BUMP_AFTER: Duration = Duration::from_secs(30);
const POLL: Duration = Duration::from_secs(1);
/// Fee rounds per send, refusals included, so fees stop near 1.25^10 ≈ 9.3 times the market estimate.
const MAX_BUMPS: usize = 10;

/// A transaction mined and reverted: unlike a send that fails otherwise, it paid for its gas.
#[derive(Debug)]
pub struct Reverted(pub TxHash);

impl std::fmt::Display for Reverted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "transaction {} reverted", self.0)
    }
}

impl std::error::Error for Reverted {}

/// Sends a key's transactions. The key must be this node's alone: the nonce comes from the mined count, so anything
/// else pending under the key gets outbid.
pub struct Sender {
    provider: DynProvider,
    from: Address,
    lock: tokio::sync::Mutex<()>,
    bump_after: Duration,
}

impl Sender {
    /// The provider fills no nonce, gas or fee, so a transaction sent around [`Sender::send`] fails instead of taking
    /// a nonce. (The recommended fillers' cached nonce advances even when gas estimation fails, and the gap stalls
    /// every later transaction.) Reads go through [`Sender::provider`] as usual.
    pub fn new(rpc_url: &str, private_key: &str) -> Result<Self> {
        let signer: PrivateKeySigner = private_key.parse().context("not a private key")?;
        let from = signer.address();
        let provider = ProviderBuilder::new()
            .disable_recommended_fillers()
            .fetch_chain_id()
            .wallet(signer)
            .connect_http(rpc_url.parse()?)
            .erased();
        Ok(Self {
            provider,
            from,
            lock: tokio::sync::Mutex::new(()),
            bump_after: BUMP_AFTER,
        })
    }

    pub fn provider(&self) -> &DynProvider {
        &self.provider
    }

    pub fn address(&self) -> Address {
        self.from
    }

    /// Sends `tx` and returns its receipt once it is mined and succeeded; one mined but reverted fails with
    /// [`Reverted`]. One that would revert fails at gas estimation and costs nothing, and so does one that needs more
    /// gas than a gas limit set on `tx`, the most it may take. It goes with [`headroom`] over the estimate. Fees start
    /// at the market estimate and rise by a quarter for every 30 s unmined.
    ///
    /// ponytail: one transaction in flight per key, each waited for; pipeline nonces, bumping each, if a node needs
    /// more than one per block.
    pub async fn send(&self, tx: TransactionRequest) -> Result<TransactionReceipt> {
        let _one = self.lock.lock().await;
        let p = &self.provider;
        let tx = tx.from(self.from);
        // on the latest state, which a transaction of ours stuck in the pool cannot skew. A node searches no higher
        // than the gas limit, and one that ignores it is held to it here.
        let gas = p.estimate_gas(tx.clone()).block(BlockId::latest()).await?;
        if let Some(cap) = tx.gas {
            ensure!(gas <= cap, "needs {gas} gas, over its limit of {cap}");
        }
        // the mined count: a transaction of ours stuck from earlier, even from an earlier run, is outbid, not queued behind
        let nonce = p.get_transaction_count(self.from).latest().await?;
        let limit = headroom(gas, tx.gas);
        let tx = tx.nonce(nonce).gas_limit(limit);
        let (mut fee, mut tip, mut sent) = (0, 0, Vec::new());
        for _ in 0..=MAX_BUMPS {
            let fresh = market_fees(p).await?;
            fee = bump(fee, fresh.max_fee_per_gas);
            tip = bump(tip, fresh.max_priority_fee_per_gas);
            let priced = tx
                .clone()
                .max_fee_per_gas(fee)
                .max_priority_fee_per_gas(tip);
            match p.send_transaction(priced).await {
                Ok(pending) => sent.push(*pending.tx_hash()),
                // something pricier holds the nonce: raise at once
                Err(e) if outbid(&e.to_string()) => continue,
                Err(e) => return self.mined(nonce, &sent).await?.ok_or(e.into()),
            }
            let until = Instant::now() + self.bump_after;
            while Instant::now() < until {
                if let Some(r) = self.mined(nonce, &sent).await? {
                    return Ok(r);
                }
                sleep(POLL).await;
            }
        }
        self.mined(nonce, &sent)
            .await?
            .ok_or_else(|| anyhow!("nonce {nonce} still unmined after {MAX_BUMPS} fee bumps"))
    }

    /// The receipt of whichever of `sent` took `nonce`, once one did. None also when another transaction took it, or
    /// the node has no receipt yet; the next send at that nonce tells which.
    async fn mined(&self, nonce: u64, sent: &[TxHash]) -> Result<Option<TransactionReceipt>> {
        if self
            .provider
            .get_transaction_count(self.from)
            .latest()
            .await?
            <= nonce
        {
            return Ok(None);
        }
        for h in sent {
            if let Some(r) = self.provider.get_transaction_receipt(*h).await? {
                ensure!(r.status(), Reverted(*h));
                return Ok(Some(r));
            }
        }
        Ok(None)
    }
}

/// The market's fees: alloy's estimate from the last blocks' tips, with the node's own suggestion as the least tip.
/// After ten blocks without a tip the estimate falls to 1 wei, which a chain with a least price refuses (BNB Smart
/// Chain 0.1 gwei, Polygon 25 gwei); where the estimate is higher, as on Sepolia, it stands.
pub(crate) async fn market_fees(p: &DynProvider) -> Result<Eip1559Estimation> {
    let (mut f, least) =
        tokio::try_join!(p.estimate_eip1559_fees(), p.get_max_priority_fee_per_gas())?;
    let raise = least.saturating_sub(f.max_priority_fee_per_gas);
    f.max_priority_fee_per_gas += raise;
    f.max_fee_per_gas += raise;
    Ok(f)
}

/// The gas limit a transaction estimated at `gas` goes with: a quarter more, and at most `cap`, a limit set on it. Its
/// cost moves with the state it lands on, as a balance another transaction empties first takes a fresh storage slot to
/// fill again (17,100 gas more: the treasurer's unwraps do this to every relayer fee paid in zETH), and gas left over
/// is not paid for.
fn headroom(gas: u64, cap: Option<u64>) -> u64 {
    let roomy = gas.saturating_add(gas / 4);
    cap.map_or(roomy, |cap| roomy.min(cap))
}

/// A quarter more, rounded up, or the market if that is higher. geth and reth refuse a replacement without a tenth
/// more on both fees; anvil wants any rise. Keeps the tip at most the fee, since it does the same to both.
fn bump(prev: u128, fresh: u128) -> u128 {
    (prev + prev / 4 + 1).max(fresh)
}

/// The pool holds a transaction at this nonce priced at least as high: geth and reth say "replacement transaction
/// underpriced" or "already known", anvil "transaction already imported".
fn outbid(msg: &str) -> bool {
    let m = msg.to_lowercase();
    ["underpriced", "already known", "already imported"]
        .iter()
        .any(|s| m.contains(s))
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy::primitives::U256;
    use std::process::{Child, Command, Stdio};

    #[test]
    fn bumps() {
        assert_eq!(bump(0, 7), 7, "the first round takes the market");
        assert_eq!(bump(100, 1), 126);
        assert_eq!(bump(1, 1), 2, "rises even when tiny");
        assert_eq!(bump(100, 500), 500, "follows the market up");
        let (fee, tip) = (bump(1000, 900), bump(10, 950));
        assert!(tip <= fee);
        assert!(outbid("replacement transaction underpriced"));
        assert!(outbid(
            "server returned an error response: error code -32003: Transaction already imported"
        ));
        assert!(outbid("already known"));
        assert!(!outbid("nonce too low"));
    }

    #[test]
    fn leaves_headroom_up_to_the_cap() {
        assert_eq!(headroom(100_000, None), 125_000);
        assert_eq!(
            headroom(100_000, Some(110_000)),
            110_000,
            "never over the cap"
        );
        assert_eq!(headroom(100_000, Some(200_000)), 125_000);
    }

    /// anvil on a free port, stopped on drop.
    struct Anvil(Child, String);
    impl Drop for Anvil {
        fn drop(&mut self) {
            let _ = self.0.kill();
        }
    }

    #[tokio::test]
    #[ignore = "spawns anvil, and HTTP clients panic inside the Claude Code sandbox"]
    async fn bumps_until_mined_on_anvil() {
        let port = std::net::TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
            .port();
        let child = Command::new("anvil")
            .args(["--no-mining", "--silent", "--port", &port.to_string()])
            .stdout(Stdio::null())
            .spawn()
            .expect("anvil on PATH");
        let anvil = Anvil(child, format!("http://127.0.0.1:{port}"));
        // anvil account 0
        let key = "0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80";
        let mut s = Sender::new(&anvil.1, key).unwrap();
        s.bump_after = Duration::from_secs(1);
        let p = s.provider().clone();
        for _ in 0..50 {
            if p.get_block_number().await.is_ok() {
                break;
            }
            sleep(Duration::from_millis(100)).await;
        }
        let transfer = |to: u8| {
            TransactionRequest::default()
                .to(Address::repeat_byte(to))
                .value(U256::from(1))
        };
        let mine = |after: Duration| {
            let p = p.clone();
            async move {
                sleep(after).await;
                p.raw_request::<_, serde_json::Value>("evm_mine".into(), serde_json::json!([]))
                    .await
                    .unwrap();
            }
        };

        assert!(
            p.send_transaction(transfer(1)).await.is_err(),
            "around the Sender nothing fills a nonce, gas or fee"
        );

        // unmined for a few rounds: mined at a raised fee. The node's suggestion is read first: it follows the tips
        // mined since.
        let least = p.get_max_priority_fee_per_gas().await.unwrap();
        let (r, ()) = tokio::join!(s.send(transfer(1)), mine(Duration::from_millis(3500)));
        let r = r.unwrap();
        let block = p
            .get_block_by_number(r.block_number.unwrap().into())
            .await
            .unwrap()
            .unwrap();
        let base = block.header.base_fee_per_gas.unwrap() as u128;
        assert!(
            r.effective_gas_price > base + least,
            "the tip starts at the node's suggestion, over alloy's 1 wei estimate, and rose from there"
        );

        // a pricier transaction stuck at the next nonce, as if from an earlier run, is outbid
        let fresh = p.estimate_eip1559_fees().await.unwrap();
        let stuck = transfer(2)
            .from(s.address())
            .nonce(1)
            .gas_limit(21_000)
            .max_fee_per_gas(fresh.max_fee_per_gas * 3)
            .max_priority_fee_per_gas(fresh.max_priority_fee_per_gas * 3);
        let stuck = *p.send_transaction(stuck).await.unwrap().tx_hash();
        let (r, ()) = tokio::join!(s.send(transfer(3)), mine(Duration::from_secs(1)));
        let r = r.unwrap();
        assert_ne!(r.transaction_hash, stuck);
        assert!(p.get_transaction_receipt(stuck).await.unwrap().is_none());
        assert_eq!(p.get_transaction_count(s.address()).await.unwrap(), 2);

        // a gas limit caps the gas: a call that needs more is refused at estimation and sends nothing. The callee
        // counts down from 1024: PUSH2 0x0400, JUMPDEST, PUSH1 1, SWAP1, SUB, DUP1, PUSH1 3, JUMPI, STOP (~48k gas).
        let burner = Address::repeat_byte(9);
        p.raw_request::<_, serde_json::Value>(
            "anvil_setCode".into(),
            serde_json::json!([burner, "0x6104005b600190038060035700"]),
        )
        .await
        .unwrap();
        let call = |cap| TransactionRequest::default().to(burner).gas_limit(cap);
        assert!(s.send(call(40_000)).await.is_err());
        assert_eq!(p.get_transaction_count(s.address()).await.unwrap(), 2);
        let (r, ()) = tokio::join!(s.send(call(60_000)), mine(Duration::from_secs(1)));
        assert!((40_000..60_000).contains(&r.unwrap().gas_used));
    }
}
