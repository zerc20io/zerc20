//! What every backend node shares: sending transactions with fee bumping, the contracts' interfaces, reading the
//! indexer, screening with Chainalysis, the relayers' fees, append-only files, commitments as words and as field
//! elements, logging, serving HTTP, reading its environment, and serving several chains.
mod append;
mod chainalysis;
pub mod contracts;
mod fees;
pub mod fields;
mod indexer;
mod sender;

pub use append::{AppendFile, whole_lines};
pub use chainalysis::{Chainalysis, RateLimited};
pub use fees::Fees;
pub use indexer::Indexer;
pub use sender::{Reverted, Sender};

use alloy::primitives::Address;
use alloy::providers::Provider;
use anyhow::{Context, Result, ensure};
use axum::http::StatusCode;
use std::future::Future;
use std::io::IsTerminal;
use std::str::FromStr;
use std::time::{Duration, UNIX_EPOCH};
use tower_http::cors::{Any, CorsLayer};
use tracing::Instrument;
use tracing_subscriber::EnvFilter;

/// Logs to stderr at `RUST_LOG` (default `info`), in color only on a terminal.
///
/// arkworks' constraint gadgets open an INFO span per operation that records the whole constraint system, which makes
/// proving quadratic, so those targets stay off whatever `RUST_LOG` says.
pub fn init_logging() -> Result<()> {
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| "info".into())
        .add_directive("gr1cs=off".parse()?)
        .add_directive("r1cs=off".parse()?);
    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_writer(std::io::stderr)
        .with_ansi(std::io::stderr().is_terminal())
        .init();
    Ok(())
}

/// Lets a wallet in a browser call a node directly, from any origin. The origin is a static `*`, so a CDN
/// keeps one copy of each answer.
pub fn cors() -> CorsLayer {
    CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any)
}

/// Serves `router` on `listen` until it fails. Its handlers log in the caller's span, which names the chain: axum runs
/// each connection on a task of its own, outside it.
pub async fn serve(listen: &str, router: axum::Router) -> Result<()> {
    let listener = tokio::net::TcpListener::bind(listen)
        .await
        .with_context(|| format!("listening on {listen}"))?;
    let span = tracing::Span::current();
    let router = router.layer(axum::middleware::from_fn(
        move |req: axum::extract::Request, next: axum::middleware::Next| {
            next.run(req).instrument(span.clone())
        },
    ));
    Ok(axum::serve(listener, router).await?)
}

/// What a client is told when the chain's RPC fails. The failure's own message stays in the log: a transport error names
/// the RPC URL, and with it the API key such a URL often carries.
const RPC_FAILED: &str = "the chain's RPC failed";

/// A call or gas estimate that failed, as an HTTP error: a revert is the request's fault, and costs no gas; anything
/// else is the chain's.
pub fn rpc_error(e: alloy::contract::Error) -> (StatusCode, String) {
    if e.as_revert_data().is_some() {
        return (StatusCode::BAD_REQUEST, e.to_string());
    }
    tracing::warn!("RPC call failed: {e}");
    (StatusCode::BAD_GATEWAY, RPC_FAILED.into())
}

/// `e`'s message for a client, unless it is a transport error's (see `RPC_FAILED`).
pub fn for_client(e: &anyhow::Error) -> String {
    match e.downcast_ref::<alloy::transports::TransportError>() {
        Some(alloy::transports::RpcError::Transport(_)) => {
            tracing::warn!("RPC failed: {e:#}");
            RPC_FAILED.into()
        }
        _ => format!("{e:#}"),
    }
}

pub fn env(k: &str) -> Result<String> {
    std::env::var(k).map_err(|_| anyhow::anyhow!("env {k} is required"))
}

pub fn env_u64(k: &str, d: u64) -> u64 {
    std::env::var(k)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(d)
}

/// The `key=value` pairs of a comma-separated setting, such as `FEES=ETH=100,USDC=250`.
pub fn pairs<K: FromStr, V: FromStr, C: FromIterator<(K, V)>>(s: &str) -> Result<C>
where
    K::Err: std::error::Error + Send + Sync + 'static,
    V::Err: std::error::Error + Send + Sync + 'static,
{
    s.split(',')
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .map(|p| {
            let (k, v) = p
                .split_once('=')
                .with_context(|| format!("{p:?} is not key=value"))?;
            Ok((k.trim().parse()?, v.trim().parse()?))
        })
        .collect()
}

/// Unix seconds; a clock set before 1970 reads 0.
pub fn now() -> u64 {
    UNIX_EPOCH.elapsed().map_or(0, |d| d.as_secs())
}

/// One of the chains a node serves. `CHAINS` names them (`sepolia base-sepolia`), and each reads a setting `K` as
/// `<CHAIN>_K` (`BASE_SEPOLIA_RPC_URL`), else as `K`: what every chain shares is given once, under its plain name.
/// Without `CHAINS`, the node serves one chain from the plain names.
#[derive(Clone, Debug, PartialEq)]
pub struct Chain {
    /// Empty for the one chain without `CHAINS`.
    pub name: String,
}

pub fn chains() -> Vec<Chain> {
    chains_in(std::env::var("CHAINS").ok().as_deref())
}

fn chains_in(names: Option<&str>) -> Vec<Chain> {
    let names: Vec<Chain> = names
        .unwrap_or_default()
        .split(|c: char| c.is_whitespace() || c == ',')
        .filter(|n| !n.is_empty())
        .map(|n| Chain { name: n.into() })
        .collect();
    match names.is_empty() {
        true => vec![Chain {
            name: String::new(),
        }],
        false => names,
    }
}

impl Chain {
    pub fn var(&self, k: &str) -> Option<String> {
        self.var_in(k, |k| std::env::var(k).ok())
    }

    fn var_in(&self, k: &str, get: impl Fn(&str) -> Option<String>) -> Option<String> {
        let own = (!self.name.is_empty()).then(|| {
            get(&format!(
                "{}_{k}",
                self.name.to_uppercase().replace('-', "_")
            ))
        });
        own.flatten().or_else(|| get(k))
    }

    pub fn env(&self, k: &str) -> Result<String> {
        self.var(k)
            .ok_or_else(|| anyhow::anyhow!("env {k} is required"))
    }

    pub fn env_u64(&self, k: &str, d: u64) -> u64 {
        self.var(k).and_then(|v| v.parse().ok()).unwrap_or(d)
    }

    /// The address in setting `k`, which must hold a contract: a wrong address fails at start rather than at its
    /// first call.
    pub async fn contract(&self, provider: &impl Provider, k: &str) -> Result<Address> {
        let a: Address = self
            .env(k)?
            .parse()
            .with_context(|| format!("{k} is not an address"))?;
        ensure!(
            !provider.get_code_at(a).await?.is_empty(),
            "no contract at {k} {a}"
        );
        Ok(a)
    }
}

/// After a chain's run fails, how long before it starts again.
const RESTART: Duration = Duration::from_secs(10);

/// Runs `f` for every chain, each in its own task, logged under its name. A run that ends, as on an error, starts
/// again on its own, so one chain's RPC going down stops no other chain. Returns only once a run panics, which ends
/// the process.
pub async fn each_chain<F, Fut>(f: F) -> Result<()>
where
    F: Fn(Chain) -> Fut + Clone + Send + 'static,
    Fut: Future<Output = Result<()>> + Send + 'static,
{
    let mut runs = tokio::task::JoinSet::new();
    for chain in chains() {
        let f = f.clone();
        let span = match chain.name.is_empty() {
            true => tracing::Span::none(),
            false => tracing::info_span!("chain", name = %chain.name),
        };
        runs.spawn(
            async move {
                loop {
                    match f(chain.clone()).await {
                        Ok(()) => tracing::warn!("stopped; starting again"),
                        Err(e) => tracing::warn!("stopped: {e:#}; starting again"),
                    }
                    tokio::time::sleep(RESTART).await;
                }
            }
            .instrument(span),
        );
    }
    // a run never ends but by panicking
    runs.join_next().await.transpose()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn pairs_parse() {
        let fees: HashMap<u32, u64> = pairs(" 1=100, 2 = 250 ,").unwrap();
        assert_eq!(fees, HashMap::from([(1, 100), (2, 250)]));
        let named: Vec<(String, Address)> =
            pairs("asp=0x0000000000000000000000000000000000000002").unwrap();
        assert_eq!(named[0].0, "asp");
        assert!(pairs::<u32, u64, Vec<_>>("").unwrap().is_empty());
        assert!(pairs::<u32, u64, Vec<_>>("1").is_err());
        assert!(pairs::<u32, u64, Vec<_>>("x=1").is_err());
    }

    #[test]
    fn chains_read_their_own_settings_then_the_shared_ones() {
        let one = chains_in(None);
        assert_eq!(
            one,
            vec![Chain {
                name: String::new()
            }]
        );
        assert_eq!(chains_in(Some(" ")), one);
        let two = chains_in(Some("sepolia base-sepolia"));
        assert_eq!(two.len(), 2);
        assert_eq!(chains_in(Some("sepolia,base-sepolia")), two);

        let env = |k: &str| match k {
            "BASE_SEPOLIA_RPC_URL" => Some("base".to_string()),
            "RPC_URL" => Some("plain".to_string()),
            "PROVE_SECS" => Some("600".to_string()),
            _ => None,
        };
        assert_eq!(two[1].var_in("RPC_URL", env).as_deref(), Some("base"));
        assert_eq!(two[0].var_in("RPC_URL", env).as_deref(), Some("plain"));
        assert_eq!(two[1].var_in("PROVE_SECS", env).as_deref(), Some("600"));
        assert_eq!(two[1].var_in("LEDGER", env), None);
        assert_eq!(one[0].var_in("RPC_URL", env).as_deref(), Some("plain"));
    }

    #[test]
    fn a_client_is_not_told_the_rpc_url() {
        let transport = || {
            alloy::transports::TransportErrorKind::custom_str(
                "error sending request for url (https://rpc.example/v2/KEY)",
            )
        };
        assert_eq!(for_client(&transport().into()), RPC_FAILED);
        assert_eq!(
            rpc_error(transport().into()),
            (StatusCode::BAD_GATEWAY, RPC_FAILED.into())
        );
        let ours = anyhow::anyhow!("transaction 0x12 reverted");
        assert_eq!(for_client(&ours), "transaction 0x12 reverted");
    }

    /// On the test's one thread, where the subscriber set for it also sees axum's connection tasks.
    #[tokio::test]
    async fn handlers_log_in_the_chain_span() {
        #[derive(Clone)]
        struct Buf(std::sync::Arc<parking_lot::Mutex<Vec<u8>>>);
        impl std::io::Write for Buf {
            fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
                self.0.lock().extend_from_slice(b);
                Ok(b.len())
            }
            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        let buf = Buf(Default::default());
        let w = buf.clone();
        let _log = tracing::subscriber::set_default(
            tracing_subscriber::fmt()
                .with_writer(move || w.clone())
                .with_ansi(false)
                .finish(),
        );
        let port = std::net::TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
            .port();
        let router = axum::Router::new().route(
            "/",
            axum::routing::get(|| async {
                tracing::info!("handled");
            }),
        );
        let listen = format!("127.0.0.1:{port}");
        tokio::spawn(
            async move { serve(&listen, router).await }
                .instrument(tracing::info_span!("chain", name = %"base")),
        );
        let url = format!("http://127.0.0.1:{port}/");
        let mut answered = None;
        for _ in 0..50 {
            answered = alloy::transports::http::reqwest::get(&url).await.ok();
            if answered.is_some() {
                break;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
        assert!(answered.is_some(), "the server did not answer");
        let log = String::from_utf8(buf.0.lock().clone()).unwrap();
        assert!(
            log.contains("chain{name=base}: zerc20_common::tests: handled"),
            "{log}"
        );
    }
}
