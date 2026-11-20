//! Chainalysis's risk screening, which asp asks about deposit senders and the attester's host about withdrawal
//! recipients.
use crate::Chain;
use alloy::primitives::Address;
use alloy::transports::http::reqwest;
use anyhow::{Result, bail, ensure};
use parking_lot::Mutex;
use serde_json::Value;
use std::time::{Duration, Instant};

/// How often [`Chainalysis::watch`] checks that Chainalysis answers.
const PROBE: Duration = Duration::from_secs(30);

/// Chainalysis refused a screening for its rate limit. It is answering, so this is no outage: anyone can cause it, with
/// deposits and withdrawals to screen.
#[derive(Debug)]
pub struct RateLimited;

impl std::fmt::Display for RateLimited {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("Chainalysis's rate limit (429)")
    }
}

impl std::error::Error for RateLimited {}

pub struct Chainalysis {
    http: reqwest::Client,
    /// Base URL and API key; None in development mode, where every address passes.
    api: Option<(String, String)>,
    /// Since when [`Chainalysis::watch`] has found Chainalysis down, without a break; None while it answers.
    down_since: Mutex<Option<Instant>>,
}

impl Chainalysis {
    /// Screens with `CHAINALYSIS_API_KEY`, at `CHAINALYSIS_API_BASE_URL` if set, or passes every address with
    /// `DEV_PASS_ALL=1` for development: exactly one of the two.
    pub fn from_env(c: &Chain) -> Result<Self> {
        let key = c.var("CHAINALYSIS_API_KEY").unwrap_or_default();
        let api = match (key.is_empty(), c.var("DEV_PASS_ALL").as_deref()) {
            (false, None) => Some((
                c.var("CHAINALYSIS_API_BASE_URL")
                    .unwrap_or("https://api.chainalysis.com".into()),
                key,
            )),
            (true, Some("1")) => {
                tracing::warn!(
                    "DEV_PASS_ALL=1: every address passes unscreened. Never run this where funds are real."
                );
                None
            }
            _ => bail!("set exactly one of CHAINALYSIS_API_KEY and DEV_PASS_ALL=1"),
        };
        let http = reqwest::Client::builder()
            .timeout(Duration::from_secs(20))
            .build()?;
        Ok(Self {
            http,
            api,
            down_since: Mutex::default(),
        })
    }

    /// Whether every address passes unscreened, as with `DEV_PASS_ALL=1`.
    pub fn passes_all(&self) -> bool {
        self.api.is_none()
    }

    /// Whether `a` passes, by the risk the Chainalysis organization's settings give it. A 429 is [`RateLimited`].
    pub async fn passes(&self, a: Address) -> Result<bool> {
        let Some(r) = self.ask(a).await? else {
            return Ok(true);
        };
        if r.status() == reqwest::StatusCode::TOO_MANY_REQUESTS {
            return Err(RateLimited.into());
        }
        verdict(&r.error_for_status()?.json().await?)
    }

    /// Chainalysis's answer about `a`; None in development mode.
    async fn ask(&self, a: Address) -> Result<Option<reqwest::Response>> {
        let Some((base, key)) = &self.api else {
            return Ok(None);
        };
        let r = self
            .http
            .get(format!("{base}/api/risk/v2/entities/{a:#x}"))
            .header("Token", key)
            .header("Accept", "application/json")
            .send()
            .await?;
        Ok(Some(r))
    }

    /// Asks about a fixed address every 30 s, to keep [`Chainalysis::down_for`] current. Screenings cannot tell an
    /// outage from failures a flood or a timed request brings about; this asks on its own schedule, and takes a 429 for
    /// the answer it is.
    pub async fn watch(&self) -> Result<()> {
        if self.api.is_none() {
            return std::future::pending().await;
        }
        loop {
            let up = self.probe().await;
            {
                let mut d = self.down_since.lock();
                *d = match up {
                    true => None,
                    false => Some(d.unwrap_or_else(Instant::now)),
                };
            }
            tokio::time::sleep(PROBE).await;
        }
    }

    /// Whether Chainalysis answers, whatever it answers about the address.
    async fn probe(&self) -> bool {
        match self.ask(Address::ZERO).await {
            Ok(Some(r)) => {
                r.status().is_success() || r.status() == reqwest::StatusCode::TOO_MANY_REQUESTS
            }
            _ => false,
        }
    }

    /// How long Chainalysis has been down without a break, as [`Chainalysis::watch`] finds it; zero unless it runs.
    pub fn down_for(&self) -> Duration {
        self.down_since
            .lock()
            .map_or(Duration::ZERO, |t| t.elapsed())
    }
}

/// Low and Medium pass, High and Severe fail. A rejection is final, so any other answer is an error to retry, never a
/// rejection.
fn verdict(v: &Value) -> Result<bool> {
    ensure!(v["status"] == "COMPLETE", "screening not complete: {v}");
    match v["risk"].as_str() {
        Some("Low" | "Medium") => Ok(true),
        Some("High" | "Severe") => Ok(false),
        _ => bail!("unexpected risk in {v}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn verdicts() {
        let v = |risk: &str| verdict(&json!({"status": "COMPLETE", "risk": risk}));
        assert!(v("Low").unwrap());
        assert!(v("Medium").unwrap());
        assert!(!v("High").unwrap());
        assert!(!v("Severe").unwrap());
        assert!(v("severe").is_err(), "unknown risk");
        assert!(verdict(&json!({"risk": "Low"})).is_err(), "no status");
        assert!(verdict(&json!({"status": "PENDING", "risk": "Severe"})).is_err());
    }

    /// A Chainalysis that answers every request with `status`, on a free port.
    fn answering(status: &'static str) -> Chainalysis {
        use std::io::{Read, Write};
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let base = format!("http://{}", listener.local_addr().unwrap());
        std::thread::spawn(move || {
            for mut s in listener.incoming().flatten() {
                let _ = s.read(&mut [0; 4096]);
                let _ = write!(
                    s,
                    "HTTP/1.1 {status}\r\ncontent-length: 0\r\nconnection: close\r\n\r\n"
                );
            }
        });
        at(base)
    }

    fn at(base: String) -> Chainalysis {
        Chainalysis {
            http: reqwest::Client::new(),
            api: Some((base, "key".into())),
            down_since: Mutex::default(),
        }
    }

    /// Whether one round of `watch` finds `c` down.
    async fn found_down(c: &Chainalysis) -> bool {
        tokio::select! {
            _ = c.watch() => unreachable!(),
            _ = tokio::time::sleep(Duration::from_millis(500)) => {}
        }
        c.down_since.lock().is_some()
    }

    #[tokio::test]
    async fn a_429_is_no_outage() {
        let limited = answering("429 Too Many Requests");
        let e = limited.passes(Address::ZERO).await.unwrap_err();
        assert!(e.is::<RateLimited>());
        assert!(!found_down(&limited).await, "a 429 is an answer");

        let failing = answering("500 Internal Server Error");
        let e = failing.passes(Address::ZERO).await.unwrap_err();
        assert!(!e.is::<RateLimited>());
        assert!(found_down(&failing).await);

        let port = std::net::TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
            .port();
        let unreachable = at(format!("http://127.0.0.1:{port}"));
        assert!(found_down(&unreachable).await, "nothing listens");
        assert_eq!(
            answering("200 OK").down_for(),
            Duration::ZERO,
            "zero unless watched"
        );
    }
}
