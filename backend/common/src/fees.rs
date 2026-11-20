//! A relayer's fee per token, which follows the chain's gas price: the same for everyone at a time, and changed seldom.
use crate::contracts::{IAggregator, IFactory, IZERC20, NATIVE};
use crate::sender::market_fees;
use crate::{Chain, now, pairs};
use alloy::eips::BlockNumberOrTag;
use alloy::primitives::{Address, U256};
use alloy::providers::{DynProvider, Provider};
use anyhow::{Context, Result, ensure};
use parking_lot::Mutex;
use std::collections::HashMap;
use std::time::Duration;
use tracing::{info, warn};

const UPDATE: Duration = Duration::from_secs(60);
/// A relay is priced at the highest gas price of this long: the tips `Sender` bids can swing by orders of magnitude
/// from one minute to the next (Sepolia: from 2 wei to 1 gwei), and a fee that followed them would change all the time
/// and, through the grace period, be paid at its lowest.
const WINDOW_SECS: u64 = 3600;
/// A feed this old is taken as broken, and the token's fee stays where it is. Chainlink's slowest heartbeat is a day.
const STALE_SECS: u64 = 2 * 86_400;

/// A Chainlink USD feed, and the decimals of its answer.
#[derive(Clone, Copy)]
struct Usd {
    feed: Address,
    decimals: u8,
}

/// The USD feeds a token's fee follows the gas price through: the native asset's, and its own.
#[derive(Clone, Copy)]
struct Feeds {
    native: Usd,
    token: Usd,
}

/// How a token's fee follows the gas price.
#[derive(Clone, Copy)]
enum Price {
    /// The native asset's zERC20: the fee is the gas cost in wei.
    Native,
    /// Any other: the gas cost through its feeds, in the token's decimals.
    Feed(Feeds, u8),
}

struct Fee {
    now: U256,
    /// Fees replaced, each with when: still accepted for the grace period.
    before: Vec<(U256, u64)>,
}

/// A token of `TOKENS`, which the factory may make only after the relayer starts.
struct Token {
    name: String,
    underlying: Address,
    /// Its fee from `FEES`.
    fixed: Option<U256>,
    /// The USD feeds its fee follows the gas price through, if it does.
    feeds: Option<Feeds>,
    /// 0 until the factory makes it, as the factory's `tokenIdOf` says.
    id: u32,
    /// How its fee follows the gas price, once it has an id.
    price: Option<Price>,
}

pub struct Fees {
    provider: DynProvider,
    /// The token factory, which says what each token's id is.
    registry: Address,
    /// The gas a relay is priced at. None: the fees stay as `FEES` sets them.
    gas: Option<u64>,
    margin_pct: u64,
    grace: u64,
    tokens: Mutex<Vec<Token>>,
    /// The gas prices of the window, each with when it was read.
    seen: Mutex<Vec<(u64, u128)>>,
    fees: Mutex<HashMap<u32, Fee>>,
}

impl Fees {
    /// From the chain's settings:
    /// - `TOKENS`, `name=underlying,...`: the tokens relayed, the native asset's by its stand-in `0xEeee…EEeE`, each
    ///   under the name the settings below give it. One the factory has not made yet is relayed once it is;
    /// - `FEES`, `name=fee,...`: a token's fee until it follows the gas price, and for good if it does not;
    /// - `FEE_GAS`: the gas a relay is priced at, without which no fee follows the gas price;
    /// - `PRICE_FEEDS`, `name=feed,...`: the Chainlink token/USD feeds, with `NATIVE_USD_FEED` for the native
    ///   asset, of the tokens besides the native one whose fee follows the gas price;
    /// - `FEE_MARGIN_PCT` (default 150) and `FEE_GRACE_SECS` (default 3600).
    ///
    /// `registry` is the token factory, which says what each token's id is.
    pub async fn new(c: &Chain, provider: DynProvider, registry: Address) -> Result<Self> {
        let gas: Option<u64> = c
            .var("FEE_GAS")
            .map(|g| g.parse())
            .transpose()
            .context("FEE_GAS")?;
        let margin_pct = c.env_u64("FEE_MARGIN_PCT", 150);
        ensure!(
            margin_pct >= 100,
            "FEE_MARGIN_PCT below 100 would relay at a loss"
        );
        let native_usd = match c.var("NATIVE_USD_FEED") {
            Some(_) => Some(usd(&provider, c.contract(&provider, "NATIVE_USD_FEED").await?).await?),
            None => None,
        };
        let listed = listed(
            &c.var("TOKENS").unwrap_or_default(),
            &c.var("FEES").unwrap_or_default(),
            &c.var("PRICE_FEEDS").unwrap_or_default(),
            gas.is_some(),
        )?;
        let mut tokens = vec![];
        for t in listed {
            // without FEE_GAS no fee follows a feed
            let feeds = match (t.feed, gas) {
                (Some(feed), Some(_)) => {
                    let native = native_usd.context("PRICE_FEEDS needs NATIVE_USD_FEED")?;
                    ensure!(
                        !provider.get_code_at(feed).await?.is_empty(),
                        "no feed at {feed}, for {}",
                        t.name
                    );
                    Some(Feeds {
                        native,
                        token: usd(&provider, feed).await?,
                    })
                }
                _ => None,
            };
            tokens.push(Token {
                name: t.name,
                underlying: t.underlying,
                fixed: t.fixed,
                feeds,
                id: 0,
                price: None,
            });
        }
        let fees = Self {
            provider,
            registry,
            gas,
            margin_pct,
            grace: c.env_u64("FEE_GRACE_SECS", 3600),
            tokens: Mutex::new(tokens),
            seen: Mutex::new(vec![]),
            fees: Mutex::new(HashMap::new()),
        };
        fees.look_up().await?;
        // said once, so that a wrong underlying, which no token ever has, shows
        for t in fees.tokens.lock().iter().filter(|t| t.id == 0) {
            warn!(
                "{} is not made yet: relayed once the factory makes it",
                t.name
            );
        }
        Ok(fees)
    }

    /// Gives each token the factory has made since the last look its id, and from then relays it.
    async fn look_up(&self) -> Result<()> {
        let waiting: Vec<(usize, Address, Option<Feeds>)> = self
            .tokens
            .lock()
            .iter()
            .enumerate()
            .filter(|(_, t)| t.id == 0)
            .map(|(i, t)| (i, t.underlying, t.feeds))
            .collect();
        let factory = IFactory::new(self.registry, &self.provider);
        for (i, underlying, feeds) in waiting {
            let id = factory.tokenIdOf(underlying).call().await?;
            if id == 0 {
                continue;
            }
            let price = match feeds {
                _ if self.gas.is_none() => None,
                _ if underlying == NATIVE => Some(Price::Native),
                Some(f) => {
                    let token = factory.tokenById(id).call().await?;
                    let decimals = IZERC20::new(token, &self.provider)
                        .decimals()
                        .call()
                        .await?;
                    Some(Price::Feed(f, decimals))
                }
                None => None,
            };
            let mut tokens = self.tokens.lock();
            let t = &mut tokens[i];
            (t.id, t.price) = (id, price);
            if let Some(now) = t.fixed {
                self.fees.lock().insert(
                    id,
                    Fee {
                        now,
                        before: vec![],
                    },
                );
            }
            info!("{} is token {id}", t.name);
        }
        Ok(())
    }

    /// The most gas a relay may take: what its fee pays for at the window's highest gas price, `FEE_GAS` with the
    /// margin. None without `FEE_GAS`, when nothing says what a fee pays for.
    pub fn max_gas(&self) -> Option<u64> {
        self.gas.map(|g| g.saturating_mul(self.margin_pct) / 100)
    }

    /// The fee to ask for `token` now, if it is relayed.
    pub fn get(&self, token: u32) -> Option<U256> {
        self.fees.lock().get(&token).map(|f| f.now)
    }

    /// Every relayed token's fee now.
    pub fn all(&self) -> Vec<(u32, U256)> {
        self.fees.lock().iter().map(|(t, f)| (*t, f.now)).collect()
    }

    /// Whether `paid` pays `token`'s fee: the one now, or a lower one replaced within the grace period, so that a
    /// proof made before a rise still goes through.
    pub fn accepts(&self, token: u32, paid: U256) -> bool {
        let now = now();
        self.fees
            .lock()
            .get(&token)
            .is_some_and(|f| paid >= lowest(f, now, self.grace))
    }

    /// Until the process ends: relays each token once the factory makes it, and with `FEE_GAS` follows the gas price.
    pub async fn run(&self) -> Result<()> {
        loop {
            if let Err(e) = self.look_up().await {
                warn!("tokens not looked up: {e:#}");
            }
            if let Some(gas) = self.gas
                && let Err(e) = self.update(gas).await
            {
                warn!("fees not updated: {e:#}");
            }
            tokio::time::sleep(UPDATE).await;
        }
    }

    /// ponytail: prices only the gas, so an L2's L1 data fee is left to the margin (Base: well under 1% of a
    /// transact's cost); add OP Stack's `GasPriceOracle.getL1FeeUpperBound` if it grows.
    async fn update(&self, gas: u64) -> Result<()> {
        let read = self.gas_price().await?;
        let price = highest(&mut self.seen.lock(), now(), read, WINDOW_SECS);
        let wei = U256::from(gas) * U256::from(price);
        let prices: Vec<(u32, Price)> = self
            .tokens
            .lock()
            .iter()
            .filter_map(|t| Some((t.id, t.price?)))
            .collect();
        for (id, p) in prices {
            let cost = match p {
                Price::Native => wei,
                Price::Feed(f, decimals) => match self.in_token_now(wei, f, decimals).await {
                    Ok(cost) => cost,
                    Err(e) => {
                        warn!("token {id}'s fee stays: {e:#}");
                        continue;
                    }
                },
            };
            let mut fees = self.fees.lock();
            let old = fees.get(&id).map(|f| f.now);
            let new = next_fee(old, cost, self.margin_pct);
            if old == Some(new) {
                continue;
            }
            info!(
                "token {id}: fee {} -> {new}, at {price} wei of gas",
                old.map_or("none".into(), |o| o.to_string())
            );
            let now = now();
            let f = fees.entry(id).or_insert(Fee {
                now: new,
                before: vec![],
            });
            if let Some(o) = old {
                f.before.retain(|(_, at)| at + self.grace > now);
                f.before.push((o, now));
            }
            f.now = new;
        }
        Ok(())
    }

    /// `wei` of the native asset in base units of a token with `decimals`, at the USD prices its `feeds` answer now.
    async fn in_token_now(&self, wei: U256, feeds: Feeds, decimals: u8) -> Result<U256> {
        let native = answer(&self.provider, feeds.native)
            .await
            .context("NATIVE_USD_FEED")?;
        let token = answer(&self.provider, feeds.token)
            .await
            .with_context(|| format!("its feed {}", feeds.token.feed))?;
        Ok(in_token(wei, native, token, decimals))
    }

    /// What `Sender` pays for a unit of gas now: the base fee, and the tip it bids. Not `eth_gasPrice`, whose tip can be
    /// far below that: on Sepolia it says 18 wei, while `Sender` has bid tips of up to 1 gwei.
    async fn gas_price(&self) -> Result<u128> {
        let tip = market_fees(&self.provider).await?.max_priority_fee_per_gas;
        let block = self
            .provider
            .get_block_by_number(BlockNumberOrTag::Latest)
            .await?
            .context("no latest block")?;
        Ok(u128::from(block.header.base_fee_per_gas.unwrap_or_default()) + tip)
    }
}

/// A token as the settings list it.
struct Listed {
    name: String,
    underlying: Address,
    fixed: Option<U256>,
    feed: Option<Address>,
}

/// The tokens of `TOKENS`, each with its fee from `FEES` and its feed from `PRICE_FEEDS`. Each must have a fee: its
/// own, or with `FEE_GAS` (`gas`) one that follows the gas price, the native asset's directly and another's through
/// its feed. A setting that names a token `TOKENS` does not list is a mistake, as is a token listed twice.
fn listed(tokens: &str, fees: &str, feeds: &str, gas: bool) -> Result<Vec<Listed>> {
    let tokens: Vec<(String, Address)> = pairs(tokens).context("TOKENS")?;
    let mut fees: HashMap<String, U256> = pairs(fees).context("FEES")?;
    let mut feeds: HashMap<String, Address> = pairs(feeds).context("PRICE_FEEDS")?;
    ensure!(!tokens.is_empty(), "no token is relayed: set TOKENS");
    let mut out: Vec<Listed> = vec![];
    for (name, underlying) in tokens {
        ensure!(
            out.iter()
                .all(|t| t.name != name && t.underlying != underlying),
            "TOKENS lists {name}, or its underlying, twice"
        );
        let native = underlying == NATIVE;
        let t = Listed {
            fixed: fees.remove(&name),
            feed: feeds.remove(&name),
            name,
            underlying,
        };
        ensure!(
            !native || t.feed.is_none(),
            "{} is the native asset's, whose fee follows the gas price without a feed",
            t.name
        );
        ensure!(
            t.fixed.is_some() || (gas && (native || t.feed.is_some())),
            "{} has no fee: set FEES, or FEE_GAS{}",
            t.name,
            if native { "" } else { " and PRICE_FEEDS" }
        );
        out.push(t);
    }
    let unlisted: Vec<_> = fees.keys().chain(feeds.keys()).collect();
    ensure!(unlisted.is_empty(), "not in TOKENS: {unlisted:?}");
    Ok(out)
}

async fn usd(provider: &DynProvider, feed: Address) -> Result<Usd> {
    let decimals = IAggregator::new(feed, provider).decimals().call().await?;
    Ok(Usd { feed, decimals })
}

/// The feed's latest price, and its decimals. A price below zero or a stale one is an error.
async fn answer(provider: &DynProvider, u: Usd) -> Result<(U256, u8)> {
    let r = IAggregator::new(u.feed, provider)
        .latestRoundData()
        .call()
        .await?;
    ensure!(r.answer.is_positive(), "price {}", r.answer);
    ensure!(
        r.updatedAt + U256::from(STALE_SECS) > U256::from(now()),
        "last updated at {}",
        r.updatedAt
    );
    Ok((r.answer.into_raw(), u.decimals))
}

/// `wei` of the native asset in base units of a token with `decimals`, at USD prices `native` and `token`, each with
/// its feed's decimals. Rounded up, so that a fee never falls short of the cost. Saturates rather than wraps.
fn in_token(wei: U256, native: (U256, u8), token: (U256, u8), decimals: u8) -> U256 {
    let ten = |n: u8| U256::from(10).pow(U256::from(n));
    let num = wei
        .saturating_mul(native.0)
        .saturating_mul(ten(token.1))
        .saturating_mul(ten(decimals));
    num.div_ceil(token.0 * ten(native.1) * ten(18))
}

/// `x` rounded up to two significant digits: a fee takes few distinct values, each within a tenth of the next.
fn round_up_2sig(x: U256) -> U256 {
    let mut unit = U256::from(1);
    while x > U256::from(99).saturating_mul(unit) {
        unit *= U256::from(10);
    }
    x.div_ceil(unit).saturating_mul(unit)
}

/// The fee after `fee`, for a relay that costs `cost`. The aim is the cost with `margin_pct` on top. The fee is raised
/// to it at once when it no longer covers the cost, and lowered to it only once it is over twice the aim, so that it
/// changes seldom.
fn next_fee(fee: Option<U256>, cost: U256, margin_pct: u64) -> U256 {
    let aim = round_up_2sig(
        cost.saturating_mul(U256::from(margin_pct))
            .div_ceil(U256::from(100)),
    );
    match fee {
        Some(f) if cost <= f && aim.saturating_mul(U256::from(2)) >= f => f,
        _ => aim,
    }
}

/// The highest gas price of the `window` up to `now`, `price` among them. Drops what has left the window.
fn highest(seen: &mut Vec<(u64, u128)>, now: u64, price: u128, window: u64) -> u128 {
    seen.retain(|(at, _)| at + window > now);
    seen.push((now, price));
    seen.iter().map(|(_, p)| *p).max().unwrap_or(price)
}

/// The lowest fee `f` accepts at `now`: its own, or one it replaced within `grace`.
fn lowest(f: &Fee, now: u64, grace: u64) -> U256 {
    f.before
        .iter()
        .filter(|(_, at)| at + grace > now)
        .map(|(v, _)| *v)
        .fold(f.now, U256::min)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u(x: u64) -> U256 {
        U256::from(x)
    }

    #[test]
    fn rounds_up_to_two_digits() {
        assert_eq!(round_up_2sig(u(0)), u(0));
        assert_eq!(round_up_2sig(u(7)), u(7));
        assert_eq!(round_up_2sig(u(99)), u(99));
        assert_eq!(round_up_2sig(u(100)), u(100));
        assert_eq!(round_up_2sig(u(101)), u(110));
        assert_eq!(round_up_2sig(u(1234)), u(1300));
        assert_eq!(round_up_2sig(u(991)), u(1000));
        assert_eq!(round_up_2sig(u(4_500_000_000_000)), u(4_500_000_000_000));
    }

    #[test]
    fn fee_rises_at_once_and_falls_only_far() {
        // the aim: 1000 with 50% on top
        assert_eq!(next_fee(None, u(1000), 150), u(1500));
        assert_eq!(next_fee(Some(u(1500)), u(1000), 150), u(1500));
        // the cost passes the fee: up at once
        assert_eq!(next_fee(Some(u(1500)), u(1501), 150), u(2300));
        // the cost falls, but the fee is not yet over twice the aim
        assert_eq!(next_fee(Some(u(1500)), u(600), 150), u(1500), "aim 900");
        assert_eq!(
            next_fee(Some(u(1500)), u(500), 150),
            u(1500),
            "aim 750, exactly half"
        );
        assert_eq!(next_fee(Some(u(1500)), u(490), 150), u(740));
        assert_eq!(next_fee(Some(u(10)), u(0), 150), u(0), "a free chain");
    }

    #[test]
    fn converts_through_usd() {
        // 0.001 ETH at $2453.10, in USDC at $0.9999 (feeds of 8 decimals): $2.4531 / 0.9999, rounded up
        let wei = u(1_000_000_000_000_000);
        let eth = (u(245_310_000_000), 8);
        let usdc = (u(99_990_000), 8);
        assert_eq!(in_token(wei, eth, usdc, 6), u(2_453_346));
        // a token of 18 decimals at the ETH price, through feeds of other decimals, is the wei itself
        assert_eq!(
            in_token(
                wei,
                eth,
                (U256::from(2_453_100_000_000_000_000_000u128), 18),
                18
            ),
            wei
        );
        assert_eq!(in_token(u(1), eth, usdc, 6), u(1), "never rounds to free");
    }

    #[test]
    fn a_relay_is_priced_at_the_windows_highest_gas_price() {
        let mut seen = vec![];
        assert_eq!(highest(&mut seen, 1000, 18, 3600), 18);
        assert_eq!(
            highest(&mut seen, 1060, 1_000_000_000, 3600),
            1_000_000_000,
            "a spike, at once"
        );
        assert_eq!(
            highest(&mut seen, 1120, 2, 3600),
            1_000_000_000,
            "held for the window"
        );
        assert_eq!(highest(&mut seen, 4660, 30, 3600), 30, "gone an hour later");
        assert_eq!(seen.len(), 2);
    }

    #[test]
    fn a_replaced_fee_is_accepted_for_the_grace_period() {
        let f = Fee {
            now: u(200),
            before: vec![(u(100), 1000), (u(150), 2000)],
        };
        assert_eq!(lowest(&f, 2000, 3600), u(100));
        assert_eq!(
            lowest(&f, 4600, 3600),
            u(150),
            "the first replaced an hour ago"
        );
        assert_eq!(lowest(&f, 5600, 3600), u(200));
        let lower = Fee {
            now: u(50),
            before: vec![(u(100), 1000)],
        };
        assert_eq!(lowest(&lower, 1000, 3600), u(50), "a fall is taken at once");
    }

    #[test]
    fn every_listed_token_has_a_fee_and_every_setting_a_listed_token() {
        let eth = "ETH=0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE";
        let usdc = "USDC=0x0000000000000000000000000000000000000002";
        let both = format!("{eth},{usdc}");
        let feed = "USDC=0x0000000000000000000000000000000000000003";
        // with FEE_GAS the native asset needs nothing more, and another token its feed
        let t = listed(&both, "", feed, true).unwrap();
        assert_eq!((t[0].fixed, t[0].feed), (None, None));
        assert!(t[1].feed.is_some());
        assert!(listed(&both, "", "", true).is_err(), "USDC has no fee");
        assert!(
            listed(eth, "", "", false).is_err(),
            "no fee follows the gas price"
        );
        assert_eq!(
            listed(eth, "ETH=5", "", false).unwrap()[0].fixed,
            Some(u(5))
        );
        assert!(
            listed(eth, "ETH=5,USDT=1", "", false).is_err(),
            "USDT is not listed"
        );
        assert!(listed(eth, "", feed, true).is_err(), "USDC is not listed");
        let eth_feed = "ETH=0x0000000000000000000000000000000000000003";
        assert!(
            listed(eth, "", eth_feed, true).is_err(),
            "the native asset takes no feed"
        );
        assert!(listed("", "", "", true).is_err(), "nothing is relayed");
        assert!(listed(&format!("{eth},{eth}"), "", "", true).is_err());
    }
}
