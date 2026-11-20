//! Watches each chain's protocol and tells people through Slack when something needs them. It holds no key and sends
//! nothing on chain: acting is for the nodes (the root-prover enters an emergency itself) and for people.
mod checks;
mod notify;

use alloy::eips::BlockNumberOrTag;
use alloy::primitives::{Address, U256};
use alloy::providers::{DynProvider, Provider, ProviderBuilder};
use alloy::rpc::types::Filter;
use alloy::sol_types::SolEvent;
use anyhow::{Context, Result};
use checks::{Alert, Stale};
use notify::{Notifier, Slack};
use serde_json::Value;
use std::path::PathBuf;
use std::time::{Duration, Instant};
use tracing::error;
use zerc20_common::contracts::IAccessManager::{OperationScheduled, RoleGranted};
use zerc20_common::contracts::IUpgradeable::Upgraded;
use zerc20_common::contracts::{IFactory, ILedger, IVerifier};
use zerc20_common::{Chain, Indexer, chains, each_chain, pairs};

/// So that one read that hangs does not hold back every other check.
const TIMEOUT: Duration = Duration::from_secs(20);

async fn read<T>(f: impl Future<Output = Result<T>>) -> Result<T> {
    tokio::time::timeout(TIMEOUT, f)
        .await
        .context("timed out")?
}

struct Watch {
    provider: DynProvider,
    verifier: Address,
    ledger: Address,
    indexer: Indexer,
    asp: Indexer,
    /// Whether this chain reports Chainalysis for the network. One key serves every chain, so one alert covers them
    /// all: the first chain's.
    chainalysis: bool,
    accounts: Vec<(String, Address)>,
    min_balance: U256,
    root_stale: Duration,
    asp_stale: Duration,
    roots: Stale<u64>,
    decided: Stale<u64>,
    published: Stale<U256>,
}

impl Watch {
    /// Everything wrong now, and a line on where things stand. A read that fails is an alert, never a pass.
    async fn round(&mut self, now: Instant) -> (Vec<Alert>, String) {
        let mut alerts = vec![];
        let mut summary = vec![];

        let status = read(self.indexer.status()).await;
        match &status {
            Ok(s) => {
                alerts.extend(checks::forged(s));
                alerts.extend(checks::stalled(s));
                summary.push(format!(
                    "{} commitments ({} final)",
                    s["commitments"], s["commitments_final"]
                ));
            }
            Err(e) => alerts.push(Alert::critical(
                "indexer",
                format!(
                    "the indexer at {} does not answer: {e:#}",
                    self.indexer.base()
                ),
            )),
        }

        let l = ILedger::new(self.ledger, &self.provider);
        let ledger = read(async {
            Ok((
                l.bound().call().await?,
                l.rootState().call().await?.index,
                l.nextIndex().call().await?,
            ))
        })
        .await;
        match ledger {
            Ok((bound, root, next)) => {
                summary.push(format!("root over {root} of {next}"));
                match checks::emergency(bound) {
                    // roots cannot move, which that alert says already
                    Some(a) => alerts.push(a),
                    None => {
                        if let Some(d) = self
                            .roots
                            .behind(root, root < next, now)
                            .filter(|d| *d >= self.root_stale)
                        {
                            alerts.push(Alert::warning(
                                "roots",
                                format!(
                                    "no root proved for {} min, with {} commitments waiting: is the root-prover up?",
                                    d.as_secs() / 60,
                                    next - root
                                ),
                            ));
                        }
                    }
                }
            }
            Err(e) => alerts.push(Alert::warning(
                "ledger",
                format!("cannot read the ledger: {e:#}"),
            )),
        }

        match read(self.asp_state()).await {
            Ok((decided, recorded, published, chainalysis_down)) => {
                summary.push(format!("ASP decided {decided}"));
                if self.chainalysis {
                    alerts.extend(checks::chainalysis(chainalysis_down));
                }
                if let Ok(s) = &status {
                    let fin = s["commitments_final"].as_u64().unwrap_or(0);
                    if let Some(d) = self
                        .decided
                        .behind(decided, decided < fin, now)
                        .filter(|d| *d >= self.asp_stale)
                    {
                        alerts.push(Alert::warning(
                            "asp-decided",
                            format!(
                                "the ASP has decided {decided} of {fin} final commitments, and none for {} min",
                                d.as_secs() / 60
                            ),
                        ));
                    }
                }
                if let Some(r) = recorded
                    && let Some(d) = self
                        .published
                        .behind(r, r != published, now)
                        .filter(|d| *d >= self.asp_stale)
                {
                    alerts.push(Alert::warning(
                        "asp-root",
                        format!(
                            "the ASP's root {r:#066x} has not been on chain for {} min (the chain has {published:#066x}): \
                             spends of new deposits wait for it",
                            d.as_secs() / 60
                        ),
                    ));
                }
            }
            Err(e) => alerts.push(Alert::warning(
                "asp",
                format!("cannot read the ASP at {}: {e:#}", self.asp.base()),
            )),
        }

        for (name, account) in &self.accounts {
            match read(async { Ok(self.provider.get_balance(*account).await?) }).await {
                Ok(b) => alerts.extend(checks::low(name, *account, b, self.min_balance)),
                Err(e) => alerts.push(Alert::warning(
                    format!("balance:{name}"),
                    format!("cannot read the balance of {name} ({account}): {e:#}"),
                )),
            }
        }
        (alerts, summary.join(", "))
    }

    /// The ASP's decided count and latest recorded root, the root the Verifier accepts now, and how long the ASP has
    /// found Chainalysis down.
    async fn asp_state(&self) -> Result<(u64, Option<U256>, U256, Duration)> {
        let s: Value = self.asp.status().await?;
        let decided = s["decided"].as_u64().context("decided")?;
        let chainalysis_down = Duration::from_secs(
            s["chainalysis_down_secs"]
                .as_u64()
                .context("chainalysis_down_secs")?,
        );
        let recorded = match s["latest_root"]["root"].as_str() {
            Some(r) => Some(r.parse()?),
            None => None,
        };
        let published = IVerifier::new(self.verifier, &self.provider)
            .latestAspRoot()
            .call()
            .await?;
        Ok((decided, recorded, published, chainalysis_down))
    }
}

/// The AccessManager's and its contracts' governance events, each reported once: a call scheduled is what the admin's
/// delay gives people the time to look at, and a role granted or an upgrade is what changes who can do what. Logs are
/// read up to the final block, so that a reorg cannot add one behind the cursor. The cursor is saved, by deployment
/// (the chain id and the ledger, whose address is the same on every chain), once Slack has taken what was read: a
/// restart reads again from there, and at worst reports an event twice.
struct Governance {
    provider: DynProvider,
    names: Vec<(&'static str, Address)>,
    file: PathBuf,
    /// The next block to read, and the one saved.
    next: u64,
    saved: u64,
    /// Blocks per getLogs, which providers cap.
    range: u64,
    /// How far below the head a block is final: where the chain has no `safe` tag, or its `safe` block is higher.
    reorg_depth: u64,
}

impl Governance {
    async fn new(c: &Chain, watch: &Watch) -> Result<Self> {
        let p = &watch.provider;
        let v = IVerifier::new(watch.verifier, p);
        let (manager, factory) =
            read(async { Ok((v.owner().call().await?, v.factory().call().await?)) })
                .await
                .context("the Verifier's owner and factory")?;
        let f = IFactory::new(factory, p);
        let (blocklist, beacon) =
            read(async { Ok((f.blocklist().call().await?, f.tokenBeacon().call().await?)) })
                .await
                .context("the factory's blocklist and token beacon")?;
        let chain_id = read(async { Ok(p.get_chain_id().await?) })
            .await
            .context("the chain id")?;
        let file = PathBuf::from(c.env("DATA_DIR")?)
            .join(format!("governance-{chain_id}-{:#x}", watch.ledger));
        let next = match std::fs::read_to_string(&file) {
            Ok(s) => s
                .trim()
                .parse()
                .with_context(|| file.display().to_string())?,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => c.env("START_BLOCK")?.parse()?,
            Err(e) => return Err(e).with_context(|| file.display().to_string()),
        };
        Ok(Self {
            provider: p.clone(),
            names: vec![
                ("the AccessManager", manager),
                ("the Verifier", watch.verifier),
                ("the ledger", watch.ledger),
                ("the factory", factory),
                ("the Blocklist", blocklist),
                ("the tokens' beacon", beacon),
                (
                    "the deposit address factory",
                    c.env("DEPOSIT_ADDRESS_FACTORY")?.parse()?,
                ),
            ],
            file,
            next,
            saved: next,
            range: c.env_u64("LOG_BLOCKS", 1000),
            reorg_depth: c.env_u64("REORG_DEPTH", 64),
        })
    }

    /// The events since the last call, up to the final block, and what stopped the reading short.
    async fn events(&mut self) -> (Vec<Alert>, Result<()>) {
        let mut events = vec![];
        let p = &self.provider;
        let last = match read(async {
            let head = p.get_block_number().await?;
            let safe = p
                .get_block_by_number(BlockNumberOrTag::Safe)
                .await
                .ok()
                .flatten();
            Ok(head
                .saturating_sub(self.reorg_depth)
                .min(safe.map_or(u64::MAX, |b| b.header.number)))
        })
        .await
        {
            Ok(last) => last,
            Err(e) => return (events, Err(e)),
        };
        while self.next <= last {
            let to = last.min(self.next + self.range - 1);
            let filter = Filter::new()
                .address(self.names.iter().map(|(_, a)| *a).collect::<Vec<_>>())
                .event_signature(vec![
                    OperationScheduled::SIGNATURE_HASH,
                    RoleGranted::SIGNATURE_HASH,
                    Upgraded::SIGNATURE_HASH,
                ])
                .from_block(self.next)
                .to_block(to);
            match read(async { Ok(p.get_logs(&filter).await?) }).await {
                Ok(logs) => {
                    let now = zerc20_common::now();
                    events.extend(
                        logs.iter()
                            .filter_map(|l| checks::governance(l, &self.names, now)),
                    );
                    self.next = to + 1;
                }
                Err(e) => {
                    return (
                        events,
                        Err(e.context(format!("logs of blocks {}..={to}", self.next))),
                    );
                }
            }
        }
        (events, Ok(()))
    }

    /// Saves how far it has read, once what it read is out.
    fn save(&mut self) -> Result<()> {
        if self.saved != self.next {
            let tmp = self.file.with_extension("tmp");
            std::fs::write(&tmp, self.next.to_string())?;
            std::fs::rename(&tmp, &self.file)?;
            self.saved = self.next;
        }
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    zerc20_common::init_logging()?;
    // one round of every chain, printed: for a cron job or a look by hand. Exits 1 if anything is wrong.
    if std::env::args().any(|a| a == "--once") {
        let mut wrong = false;
        for c in chains() {
            let (chain, mut watch) = watch(&c).await?;
            let (alerts, summary) = watch.round(Instant::now()).await;
            println!("{chain}: {summary}");
            for a in &alerts {
                println!("{} {}", a.level(), a.text);
            }
            wrong |= !alerts.is_empty();
        }
        std::process::exit(i32::from(wrong));
    }
    each_chain(run).await
}

/// The chain's name in messages, and what to check on it.
async fn watch(c: &Chain) -> Result<(String, Watch)> {
    let chain = c.env("CHAIN")?;
    let provider = ProviderBuilder::new()
        .connect_http(c.env("RPC_URL")?.parse()?)
        .erased();
    let verifier: Address = c.env("VERIFIER")?.parse()?;
    let ledger = read(async { Ok(IVerifier::new(verifier, &provider).ledger().call().await?) })
        .await
        .context("Verifier.ledger")?;
    // `name=0x…,…`: the accounts whose gas the nodes spend
    let accounts: Vec<(String, Address)> =
        pairs(&c.var("WATCH_ADDRESSES").unwrap_or_default()).context("WATCH_ADDRESSES")?;
    // The treasurer tops an account up to TOP_UP_TO once it holds less than half of that: one below a quarter is one
    // it is not keeping up, which still has gas for some sends.
    let min_balance = if accounts.is_empty() {
        U256::ZERO
    } else {
        c.env("TOP_UP_TO")?.parse::<U256>().context("TOP_UP_TO")? / U256::from(4)
    };
    let watch = Watch {
        provider,
        verifier,
        ledger,
        indexer: Indexer::new(&c.env("INDEXER_URL")?)?,
        asp: Indexer::new(&c.env("ASP_URL")?)?,
        chainalysis: chains().first() == Some(c),
        accounts,
        min_balance,
        root_stale: Duration::from_secs(c.env_u64("ROOT_STALE_SECS", 1800)),
        asp_stale: Duration::from_secs(c.env_u64("ASP_STALE_SECS", 1800)),
        roots: Stale::default(),
        decided: Stale::default(),
        published: Stale::default(),
    };
    Ok((chain, watch))
}

async fn run(c: Chain) -> Result<()> {
    let (chain, mut watch) = watch(&c).await?;
    let mut governance = Governance::new(&c, &watch).await?;
    let mut notifier = Notifier::new(&chain, Duration::from_secs(c.env_u64("REPEAT_SECS", 3600)));
    let mut slack = Slack::new(c.var("SLACK_WEBHOOK_URL"))?;
    let every = Duration::from_secs(c.env_u64("CHECK_SECS", 60));
    let heartbeat = Duration::from_secs(c.env_u64("HEARTBEAT_SECS", 86_400));
    let mut beat: Option<Instant> = None;
    loop {
        let now = Instant::now();
        let (mut alerts, mut summary) = watch.round(now).await;
        let (events, read) = governance.events().await;
        if let Err(e) = read {
            alerts.push(Alert::warning(
                "governance",
                format!("cannot read the governance events: {e:#}"),
            ));
        }
        summary.push_str(&format!(
            ", governance events read below block {}",
            governance.next
        ));
        let mut messages = notifier.round(&alerts, now);
        messages.extend(events.iter().map(|e| notifier.once(e)));
        // a silent watcher must mean a healthy chain, not a dead watcher
        if beat.is_none_or(|b| now - b >= heartbeat) {
            let first = if beat.is_none() {
                "started"
            } else {
                "watching"
            };
            messages.push(format!(
                "[{chain}] watcher {first}: {summary}; {} alerts open",
                notifier.active()
            ));
            beat = Some(now);
        }
        if slack.send(messages).await
            && let Err(e) = governance.save()
        {
            // the cursor is behind, so a restart reports what was read again rather than skipping it
            error!(
                "cannot save the governance cursor to {}: {e:#}",
                governance.file.display()
            );
        }
        tokio::time::sleep(every).await;
    }
}
