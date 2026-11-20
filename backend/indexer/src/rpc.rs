//! Fault-tolerant RPC layer: error classification, adaptive getLogs range, backoff, multi-source health.
//! Backoff has jitter so that retries don't synchronize, a 429 never shrinks the range (narrower ranges only mean
//! more requests), and nothing retries silently forever: a stall shows in `/status`.
use alloy::eips::{BlockId, BlockNumberOrTag};
use alloy::primitives::{Address, B256, Bloom, Bytes};
use alloy::providers::{DynProvider, Provider, ProviderBuilder};
use alloy::rpc::types::{Filter, Log, TransactionRequest};
use parking_lot::Mutex;
use regex::Regex;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------- classification

#[derive(Debug, Clone, PartialEq)]
pub enum Verdict {
    /// Provider caps the block range. `structural`: a standing cap of this source, not a one-off hint.
    RangeTooLarge {
        suggested: Option<u64>,
        structural: bool,
    },
    /// Result-count / response-size cap: shrink the range, no number given.
    TooManyResults,
    RateLimited,
    /// Node doesn't have the block yet (lagging node behind a load balancer).
    BehindHead,
    /// Response contradicts itself / other data (wrong fork, bad fields, on-chain state that disagrees).
    Inconsistent,
    /// eth_call at a block whose state this node no longer has (non-archive node). Not a failure: skip the check.
    StateUnavailable,
    /// This source can't serve the request at all (method unsupported).
    SourceFatal,
    Transient,
}

#[derive(Debug)]
pub struct Fail {
    pub verdict: Verdict,
    pub msg: String,
}
impl std::fmt::Display for Fail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}: {}", self.verdict, self.msg)
    }
}
impl std::error::Error for Fail {}
impl Fail {
    pub fn new(verdict: Verdict, msg: impl Into<String>) -> Self {
        Self {
            verdict,
            msg: msg.into(),
        }
    }
}

/// What a source's error message says: the patterns of the providers' messages, compiled once, with the source.
pub struct Classifier {
    /// (regex, fixed interval if the pattern has no capture group). Order matters: the specific
    /// "maximum allowed is N blocks" must be tried before Base's bare "block range too large".
    ranges: Vec<(Regex, Option<u64>)>,
    too_many: Regex,
    rate: Regex,
    state: Regex,
    behind: Regex,
    fatal: Regex,
}

impl Classifier {
    pub fn new() -> Result<Self, regex::Error> {
        Ok(Self {
            ranges: [
                (r"(?i)retry with the range (\d+)-(\d+)", None), // handled specially (two groups)
                (r"(?i)limited to a (\d+) blocks? range", None), // QuickNode, 1RPC, Blast
                (r"(?i)up to a (\d+) block range", None),        // Alchemy
                (r"(?i)Max range: (\d+)", None),                 // Cloudflare
                (
                    r"(?i)Maximum allowed number of requested blocks is (\d+)",
                    None,
                ), // Thirdweb
                (r"(?i)limited to (\d+) blocks?", None),         // BlockPI
                (r"(?i)maximum allowed is (\d+) blocks", None),  // sei & co
                (
                    r"(?i)exceeds the range allowed for your plan \(\d+ > (\d+)\)",
                    None,
                ), // Blast paid
                (r"(?i)please limit the query to at most (\d+) blocks", None), // Coinbase
                (r"(?i)maximum block range: (\d+)", None),       // PublicNode
                (r"(?i)query exceeds max block range (\d+)", None), // Hyperliquid
                (r"(?i)Block range limit exceeded\.", Some(10_000)), // Chainstack
                (r"(?i)block range too large", Some(2_000)),     // Base
            ]
            .into_iter()
            .map(|(p, f)| Ok((Regex::new(p)?, f)))
            .collect::<Result<_, regex::Error>>()?,
            too_many: Regex::new(
                r"(?i)more than \d+ (logs|results)|\d+ logs returned|too many logs|query returned more than|query exceeds max results|response size (should not|exceeded)|(backend )?response too large|logs matched by query exceeds limit|block range is too wide|log response size exceeded",
            )?,
            rate: Regex::new(
                r"(?i)\b429\b|rate.?limit|too many requests|exceeded .*(capacity|quota|compute units)|throttl",
            )?,
            state: Regex::new(
                r"(?i)missing trie node|historical state|state (is )?(not available|unavailable|pruned)|no state available|old data not available|state .* (has been )?pruned",
            )?,
            // "not currently canonical": an EIP-1898 call pinned to a hash that a reorg just replaced; "beyond current
            // head": a load-balanced node behind the one that answered eth_blockNumber
            behind: Regex::new(
                r"(?i)header not found|unknown block|block not found|block #?\d+ not found|not yet (available|indexed)|after last accepted block|not currently canonical|beyond current head",
            )?,
            fatal: Regex::new(
                r"(?i)method .*(not found|not supported|not available)|unsupported method|-32601",
            )?,
        })
    }

    pub fn classify(&self, msg: &str) -> Verdict {
        for (i, (rx, fixed)) in self.ranges.iter().enumerate() {
            if let Some(c) = rx.captures(msg) {
                let n = if i == 0 {
                    let (a, b): (u64, u64) = (c[1].parse().unwrap_or(0), c[2].parse().unwrap_or(0));
                    (b >= a).then(|| b - a + 1)
                } else {
                    fixed.or_else(|| c.get(1).and_then(|m| m.as_str().parse().ok()))
                };
                match n.filter(|&n| n > 0) {
                    Some(n) => {
                        return Verdict::RangeTooLarge {
                            suggested: Some(n),
                            structural: i != 0,
                        };
                    }
                    None => continue, // 0 or unparsable: not a usable suggestion
                }
            }
        }
        if self.too_many.is_match(msg) {
            return Verdict::TooManyResults;
        }
        if self.rate.is_match(msg) {
            return Verdict::RateLimited;
        }
        if self.state.is_match(msg) {
            return Verdict::StateUnavailable;
        }
        if self.behind.is_match(msg) {
            return Verdict::BehindHead;
        }
        if self.fatal.is_match(msg) {
            return Verdict::SourceFatal;
        }
        Verdict::Transient
    }
}

// ---------------------------------------------------------------- adaptive range (AIMD)

/// ponytail: learned width/cap live in memory only (relearned after a restart, costs a few failed requests);
/// persist per provider host if restarts become frequent.
pub struct RangeCtl {
    pub width: u64,
    pub cap: u64,
}
impl RangeCtl {
    pub fn new(initial: u64, max: u64) -> Self {
        Self {
            width: initial.clamp(1, max.max(1)),
            cap: max.max(1),
        }
    }
    /// Gentle increase (+10%, min 1), only when the full width was actually used (a head-clamped range proves nothing).
    pub fn on_success(&mut self, executed: u64) {
        if executed >= self.width {
            self.width = (self.width + (self.width / 10).max(1)).min(self.cap);
        }
    }
    /// Returns true if the caller should retry *immediately* with a strictly narrower range.
    /// A suggestion that isn't narrower than what failed is an ordinary failure (guards against echo loops).
    pub fn on_error(&mut self, v: &Verdict, executed: u64) -> bool {
        let new = match v {
            Verdict::RangeTooLarge {
                suggested: Some(n),
                structural,
            } => {
                if *structural {
                    self.cap = self.cap.min(*n); // standing cap: only ever tightens
                }
                *n
            }
            Verdict::TooManyResults => (executed as f64 * 0.8) as u64,
            _ => return false,
        };
        let new = new.min(self.cap).max(1);
        if new < executed {
            self.width = new;
            true
        } else {
            false
        }
    }
}

/// Exponential backoff, 50–100% jitter, capped.
pub fn backoff(n: u32, base_ms: u64, cap_ms: u64) -> Duration {
    let full = base_ms.saturating_mul(1u64 << n.min(20)).min(cap_ms);
    Duration::from_millis(full / 2 + fastrand::u64(0..=full / 2))
}

// ---------------------------------------------------------------- sources

#[derive(Clone)]
pub struct Header {
    pub number: u64,
    pub hash: B256,
    pub parent_hash: B256,
    pub bloom: Bloom,
    /// Unix seconds.
    pub timestamp: u64,
}

#[derive(Default, Clone)]
pub struct Health {
    pub failures: u64,
    pub last_failed: Option<Instant>,
    pub last_error: String,
    pub disabled: bool,
}

pub struct Source {
    pub name: String, // host only: URLs often carry API keys
    url: String,
    provider: DynProvider,
    timeout: Duration,
    classifier: Classifier,
    pub health: Mutex<Health>,
}

const RECOVERY: Duration = Duration::from_secs(60);

impl Source {
    pub fn new(url: &str, timeout: Duration) -> anyhow::Result<Self> {
        let u: alloy::transports::http::reqwest::Url = url.parse()?;
        let name = format!(
            "{}{}",
            u.host_str().unwrap_or("?"),
            u.port().map(|p| format!(":{p}")).unwrap_or_default()
        );
        Ok(Self {
            name,
            url: u.as_str().into(),
            provider: ProviderBuilder::new().connect_http(u).erased(),
            timeout,
            classifier: Classifier::new()?,
            health: Default::default(),
        })
    }

    async fn call<T>(
        &self,
        fut: impl std::future::Future<Output = Result<T, impl std::fmt::Display>>,
    ) -> Result<T, Fail> {
        match tokio::time::timeout(self.timeout, fut).await {
            Ok(Ok(v)) => Ok(v),
            // a transport error names the URL, and /status serves the message
            Ok(Err(e)) => {
                let msg = e.to_string().replace(&self.url, &self.name);
                Err(Fail::new(self.classifier.classify(&msg), msg))
            }
            Err(_) => Err(Fail::new(
                Verdict::Transient,
                format!("timeout after {:?}", self.timeout),
            )),
        }
    }

    pub async fn head(&self) -> Result<u64, Fail> {
        self.call(self.provider.get_block_number()).await
    }

    /// The `safe` block number, or None if this node doesn't serve the tag. Only bounds the reorg window
    /// and the final watermark; never used as a getLogs toBlock (load-balanced nodes disagree about it).
    pub async fn safe(&self) -> Result<Option<u64>, Fail> {
        let b = self
            .call(std::future::IntoFuture::into_future(
                self.provider.get_block_by_number(BlockNumberOrTag::Safe),
            ))
            .await?;
        Ok(b.map(|b| b.header.number))
    }

    pub async fn header_opt(&self, n: u64) -> Result<Option<Header>, Fail> {
        let b = self
            .call(std::future::IntoFuture::into_future(
                self.provider
                    .get_block_by_number(BlockNumberOrTag::Number(n)),
            ))
            .await?;
        Ok(b.map(|b| Header {
            number: n,
            hash: b.header.hash,
            parent_hash: b.header.parent_hash,
            bloom: b.header.logs_bloom,
            timestamp: b.header.timestamp,
        }))
    }

    /// Like `header_opt`, but a missing block is a lagging node, not "absent".
    pub async fn header(&self, n: u64) -> Result<Header, Fail> {
        self.header_opt(n)
            .await?
            .ok_or_else(|| Fail::new(Verdict::BehindHead, format!("block {n} not found")))
    }

    /// `eth_call` pinned to the canonical block `at` (EIP-1898), so the answer is about exactly the chain the
    /// checked logs came from. Fails with `StateUnavailable` when this node has pruned that block's state.
    pub async fn call_at(&self, to: Address, data: Bytes, at: B256) -> Result<Bytes, Fail> {
        let tx = TransactionRequest::default().to(to).input(data.into());
        let out = self
            .call(std::future::IntoFuture::into_future(
                self.provider.call(tx).block(BlockId::hash_canonical(at)),
            ))
            .await?;
        if out.is_empty() {
            // no contract at that block (e.g. before deployment), or a wrong getter
            return Err(Fail::new(
                Verdict::StateUnavailable,
                format!("empty eth_call answer at block {at}"),
            ));
        }
        Ok(out)
    }

    pub async fn logs(&self, f: &Filter) -> Result<Vec<Log>, Fail> {
        self.call(self.provider.get_logs(f)).await
    }
}

pub struct Rpc {
    pub sources: Vec<Source>,
}

impl Rpc {
    pub fn new(urls: &[String], timeout: Duration) -> anyhow::Result<Self> {
        anyhow::ensure!(!urls.is_empty(), "no RPC url configured");
        Ok(Self {
            sources: urls
                .iter()
                .map(|u| Source::new(u, timeout))
                .collect::<anyhow::Result<_>>()?,
        })
    }

    /// Primary-first among healthy sources; failed ones come back after RECOVERY. If none is healthy,
    /// the one that failed longest ago. Err only if every source is permanently disabled.
    pub fn pick(&self) -> anyhow::Result<usize> {
        let now = Instant::now();
        let hs: Vec<Health> = self
            .sources
            .iter()
            .map(|s| s.health.lock().clone())
            .collect();
        if let Some(i) = hs
            .iter()
            .position(|h| !h.disabled && h.last_failed.is_none_or(|t| now - t >= RECOVERY))
        {
            return Ok(i);
        }
        hs.iter()
            .enumerate()
            .filter(|(_, h)| !h.disabled)
            .min_by_key(|(_, h)| h.last_failed)
            .map(|(i, _)| i)
            .ok_or_else(|| anyhow::anyhow!("all RPC sources are disabled (unsupported methods)"))
    }

    pub fn mark_failed(&self, i: usize, why: &str) {
        let mut h = self.sources[i].health.lock();
        h.failures += 1;
        h.last_failed = Some(Instant::now());
        h.last_error = why.chars().take(200).collect();
    }
    pub fn mark_ok(&self, i: usize) {
        self.sources[i].health.lock().last_failed = None;
    }
    pub fn disable(&self, i: usize, why: &str) {
        let mut h = self.sources[i].health.lock();
        h.disabled = true;
        h.last_error = why.chars().take(200).collect();
    }

    pub fn snapshot(&self) -> serde_json::Value {
        let now = Instant::now();
        self.sources
            .iter()
            .map(|s| {
                let h = s.health.lock();
                serde_json::json!({
                    "source": s.name, "failures": h.failures, "last_error": h.last_error, "disabled": h.disabled,
                    "healthy": !h.disabled && h.last_failed.is_none_or(|t| now - t >= RECOVERY),
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn range(n: u64, structural: bool) -> Verdict {
        Verdict::RangeTooLarge {
            suggested: Some(n),
            structural,
        }
    }

    #[test]
    fn classify_provider_messages() {
        let classifier = Classifier::new().unwrap();
        let classify = |msg: &str| classifier.classify(msg);
        let cases = [
            (
                "eth_getLogs is limited to a 100 blocks range",
                range(100, true),
            ), // QuickNode
            (
                "Log response size exceeded. You can make eth_getLogs requests with up to a 2000 block range",
                range(2000, true),
            ), // Alchemy (digits form)
            ("Max range: 500", range(500, true)), // Cloudflare
            (
                "Maximum allowed number of requested blocks is 1000",
                range(1000, true),
            ), // Thirdweb
            ("range limited to 1000 blocks", range(1000, true)), // BlockPI-ish
            (
                "block range too large (2000), maximum allowed is 1000 blocks",
                range(1000, true),
            ), // order: specific beats Base
            ("block range too large", range(2000, true)), // Base
            ("Block range limit exceeded.", range(10_000, true)), // Chainstack
            ("query exceeds max block range 1000", range(1000, true)), // Hyperliquid
            (
                "please limit the query to at most 5000 blocks",
                range(5000, true),
            ), // Coinbase
            ("maximum block range: 10000", range(10_000, true)), // PublicNode
            (
                "query exceeds the range allowed for your plan (5000 > 500)",
                range(500, true),
            ), // Blast paid
            ("retry with the range 0x1-0x64", Verdict::Transient), // hex form is not parsed
            (
                "query returned more than 10000 results",
                Verdict::TooManyResults,
            ), // Infura/Alchemy cap
            ("Log response size exceeded", Verdict::TooManyResults),
            (
                "response size should not greater than 10000000 bytes",
                Verdict::TooManyResults,
            ),
            ("HTTP error 429 Too Many Requests", Verdict::RateLimited),
            (
                "daily request count exceeded, request rate limited",
                Verdict::RateLimited,
            ),
            ("header not found", Verdict::BehindHead),
            (
                "error code -32602: block range extends beyond current head block",
                Verdict::BehindHead,
            ), // Alchemy
            (
                "hash 0x12ab is not currently canonical",
                Verdict::BehindHead,
            ), // geth, EIP-1898
            (
                "missing trie node 12ab (path ) state 0x12 is not available",
                Verdict::StateUnavailable,
            ), // geth/nitro, non-archive
            (
                "historical state is not available",
                Verdict::StateUnavailable,
            ),
            ("state at block 100 is pruned", Verdict::StateUnavailable),
            (
                "the method eth_getLogs does not exist/is not available",
                Verdict::SourceFatal,
            ),
            ("connection reset by peer", Verdict::Transient),
            ("HTTP 502 Bad Gateway", Verdict::Transient),
        ];
        for (msg, want) in cases {
            assert_eq!(classify(msg), want, "{msg}");
        }
        // decimal "retry with the range" suggestion is one-off (non-structural)
        assert_eq!(
            classify("please retry with the range 100-199"),
            range(100, false)
        );
        // a zero cap is never a usable suggestion
        assert_eq!(classify("limited to a 0 blocks range"), Verdict::Transient);
        // "4290" must not look like HTTP 429
        assert_eq!(classify("block 4290 failed"), Verdict::Transient);
    }

    #[test]
    fn aimd_behaviour() {
        let mut c = RangeCtl::new(2000, 10_000);
        // grows only on full-width success
        c.on_success(100);
        assert_eq!(c.width, 2000);
        c.on_success(2000);
        assert_eq!(c.width, 2200);
        // density error: x0.8, strictly narrower, floor 1
        assert!(c.on_error(&Verdict::TooManyResults, 2200));
        assert_eq!(c.width, 1760);
        c.width = 2000;
        let mut one = RangeCtl::new(1, 10);
        assert!(
            !one.on_error(&Verdict::TooManyResults, 1),
            "width 1 cannot shrink further"
        );
        // structural cap only tightens, and clamps growth
        assert!(c.on_error(&range(300, true), 2000));
        assert_eq!((c.width, c.cap), (300, 300));
        assert!(
            !c.on_error(&range(5000, true), 300),
            "wider suggestion is not an improvement"
        );
        assert_eq!(c.cap, 300);
        c.on_success(300);
        assert_eq!(c.width, 300, "growth clamped by cap");
        let mut tiny = RangeCtl::new(5, 100);
        tiny.on_success(5);
        assert_eq!(tiny.width, 6, "always grows by at least 1");
        // one-off suggestion narrows width without touching the cap
        let mut d = RangeCtl::new(1000, 10_000);
        assert!(d.on_error(&range(100, false), 1000));
        assert_eq!((d.width, d.cap), (100, 10_000));
        // echo (suggestion not narrower than what failed) is an ordinary failure
        assert!(!d.on_error(&range(100, false), 100));
        // unrelated verdicts never touch the range
        assert!(!d.on_error(&Verdict::RateLimited, 100));
        assert_eq!(d.width, 100);
    }

    #[test]
    fn backoff_is_bounded_and_jittered() {
        for n in 0..40 {
            for _ in 0..50 {
                let d = backoff(n, 200, 30_000).as_millis() as u64;
                let full = (200u64 << n.min(20)).min(30_000);
                assert!(d >= full / 2 && d <= full, "n={n} d={d} full={full}");
            }
        }
        let s: std::collections::HashSet<_> = (0..50)
            .map(|_| backoff(5, 200, 30_000).as_millis())
            .collect();
        assert!(s.len() > 5, "no jitter");
    }

    #[tokio::test]
    async fn a_failure_names_the_host_not_the_url() {
        let port = std::net::TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
            .port();
        let s = Source::new(
            &format!("http://127.0.0.1:{port}/v2/KEY"),
            Duration::from_secs(5),
        )
        .unwrap();
        let f = s.head().await.err().unwrap();
        assert!(!f.msg.contains("KEY"), "{}", f.msg);
        assert!(f.msg.contains(&s.name), "the URL was there: {}", f.msg);
    }
}
