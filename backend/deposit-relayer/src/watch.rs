//! Polls every watched balance and flushes the deposit addresses that hold enough.
use crate::App;
use crate::contracts::{IDepositAddressFactory, IERC20, IMulticall3};
use crate::store::Reg;
use alloy::eips::BlockId;
use alloy::primitives::{TxHash, U256};
use alloy::providers::{CallItem, MULTICALL3_ADDRESS, Provider};
use alloy::sol_types::SolCall;
use anyhow::Context;
use std::sync::Arc;
use std::time::Duration;
use tracing::{info, warn};
use zerc20_common::contracts::NATIVE;
use zerc20_common::{Reverted, now};

/// Balance reads per aggregate3 call.
const BATCH: usize = 500;

pub async fn run(app: Arc<App>, poll: Duration) -> anyhow::Result<()> {
    loop {
        if let Err(e) = tick(&app).await {
            warn!("balance poll failed: {e:#}");
        }
        tokio::time::sleep(poll).await;
    }
}

/// ponytail: reads every watched balance each tick (N / BATCH eth_calls); drive ERC-20 deposits from
/// Transfer logs instead if the watched set gets large.
async fn tick(app: &App) -> anyhow::Result<()> {
    let regs = app.store.lock().watched(now());
    for chunk in regs.chunks(BATCH) {
        for (r, balance) in chunk
            .iter()
            .zip(balances(app, chunk, BlockId::latest()).await?)
        {
            // the fee pays for the flush, so dust costs the relayer nothing: it is never flushed. The referral comes
            // out of what is left after the fee, so it never stops a balance above the fee from flushing.
            if balance.is_some_and(|b| b > r.fee)
                && let Err(e) = flush(app, r).await
            {
                warn!("flush of {} failed: {e:#}", r.deposit_address);
                if let Some(&Reverted(tx)) = e.downcast_ref()
                    && let Err(e) = after_revert(app, r, tx).await
                {
                    warn!("after the reverted flush of {}: {e:#}", r.deposit_address);
                }
            }
        }
    }
    Ok(())
}

/// Stops flushing `r` for good when its flush `tx` reverted on chain and [`stops`] says so of the balance at the block
/// that mined it: a later block may hold a deposit made after.
async fn after_revert(app: &App, r: &Reg, tx: TxHash) -> anyhow::Result<()> {
    let block = app
        .provider
        .get_transaction_receipt(tx)
        .await?
        .and_then(|t| t.block_number)
        .context("no receipt")?;
    let left = balances(app, std::slice::from_ref(r), block.into()).await?;
    if stops(r, left.first().copied().flatten()) {
        warn!(
            "{} keeps its funds after a flush reverted: no longer flushed",
            r.deposit_address
        );
        app.store.lock().reverted(r.deposit_address)?;
    }
    Ok(())
}

/// Whether a reverted flush of `r` that left `left` at its address is reason to stop flushing it for good. Paying a
/// referrer in the native asset calls it, and a referrer can pass gas estimation and still revert on chain, at the
/// relayer's cost, on every tick. An ERC-20 referral calls no referrer, so a revert there has another cause, such as
/// gas the estimate fell short of, and passes. Neither does a flush that lost a race to another, which finds the funds
/// gone, or one whose balance is unknown: the next tick decides, which costs at most one more revert.
fn stops(r: &Reg, left: Option<U256>) -> bool {
    r.underlying == NATIVE && left.is_some_and(|b| b > r.fee)
}

/// The underlying balance of each of `regs`' deposit addresses at `block`, in one Multicall3 call; None where a read
/// failed.
async fn balances(app: &App, regs: &[Reg], block: BlockId) -> anyhow::Result<Vec<Option<U256>>> {
    let calls = regs.iter().map(|r| balance_call(r).allow_failure(true));
    let read = app
        .provider
        .multicall()
        .dynamic()
        .extend_calls(calls)
        .block(block)
        .aggregate3()
        .await?;
    Ok(read.into_iter().map(Result::ok).collect())
}

/// Both getters return one uint256, so balanceOf's decoder reads getEthBalance too.
fn balance_call(r: &Reg) -> CallItem<IERC20::balanceOfCall> {
    let (target, input) = if r.underlying == NATIVE {
        (
            MULTICALL3_ADDRESS,
            IMulticall3::getEthBalanceCall {
                addr: r.deposit_address,
            }
            .abi_encode(),
        )
    } else {
        (
            r.underlying,
            IERC20::balanceOfCall {
                account: r.deposit_address,
            }
            .abi_encode(),
        )
    };
    CallItem::new(target, input.into())
}

/// ponytail: one transaction at a time, each awaited; batch through Multicall3 if flushes queue up.
async fn flush(app: &App, r: &Reg) -> anyhow::Result<()> {
    let mut flush = IDepositAddressFactory::new(app.factory, &app.provider)
        .flush(
            r.token,
            r.burn_address,
            r.refund_address,
            r.refund_signer,
            r.fee_recipient,
            r.fee,
            r.referrer,
            r.referral_bps,
        )
        .into_transaction_request();
    // paying a referrer in the native asset calls it, which could burn gas the fee does not pay for: a flush may take
    // no more than the fee pays for, in estimation or on chain
    if let Some(max) = app.fees.max_gas() {
        flush = flush.gas_limit(max);
    }
    let receipt = app.sender.send(flush).await?;
    info!(
        "flushed {} in {}",
        r.deposit_address, receipt.transaction_hash
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy::primitives::Address;

    #[test]
    fn only_a_native_flush_that_left_its_funds_stops() {
        let reg = |underlying| Reg {
            token: Address::repeat_byte(1),
            burn_address: Address::repeat_byte(2),
            refund_address: Address::repeat_byte(3),
            refund_signer: Address::ZERO,
            deposit_address: Address::repeat_byte(10),
            underlying,
            fee_recipient: Address::repeat_byte(4),
            fee: U256::from(5),
            referrer: Address::repeat_byte(6),
            referral_bps: 30,
            at: 1,
            reverted: false,
        };
        let native = reg(NATIVE);
        assert!(stops(&native, Some(U256::from(6))));
        assert!(
            !stops(&native, Some(U256::from(5))),
            "another flush took it"
        );
        assert!(!stops(&native, None), "unknown: the next tick decides");
        assert!(
            !stops(&reg(Address::repeat_byte(7)), Some(U256::from(6))),
            "an ERC-20 calls no referrer"
        );
    }
}
