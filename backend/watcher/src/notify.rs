//! Turns each round's alerts into messages, and posts them to Slack.
use crate::checks::Alert;
use alloy::transports::http::reqwest;
use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};
use tracing::{error, info};

/// Messages kept for a Slack that does not answer, oldest dropped first.
const OUTBOX: usize = 100;

/// Remembers what it reported: a critical alert goes out when it first appears, a warning once it is there a second
/// round in a row, either again every `repeat` while it lasts, and once more as resolved when it is gone. So one
/// failed read, such as a blip of the network, stays quiet. Kept in memory, so a restart reports what is wrong once more.
pub struct Notifier {
    chain: String,
    repeat: Duration,
    active: HashMap<String, (Instant, String)>,
    /// the last round's warnings, not reported yet
    pending: HashSet<String>,
}

impl Notifier {
    pub fn new(chain: &str, repeat: Duration) -> Self {
        Self {
            chain: chain.into(),
            repeat,
            active: HashMap::new(),
            pending: HashSet::new(),
        }
    }

    pub fn active(&self) -> usize {
        self.active.len()
    }

    /// The message for an alert that is reported once, such as an event.
    pub fn once(&self, a: &Alert) -> String {
        format!("{} [{}] {}", a.level(), self.chain, a.text)
    }

    /// The messages this round calls for.
    pub fn round(&mut self, alerts: &[Alert], now: Instant) -> Vec<String> {
        let mut out = vec![];
        let pending = std::mem::take(&mut self.pending);
        for a in alerts {
            if !a.critical && !self.active.contains_key(&a.key) && !pending.contains(&a.key) {
                self.pending.insert(a.key.clone());
                continue;
            }
            if self
                .active
                .get(&a.key)
                .is_none_or(|(sent, _)| now - *sent >= self.repeat)
            {
                out.push(self.once(a));
                self.active.insert(a.key.clone(), (now, a.text.clone()));
            }
        }
        let mut gone: Vec<(String, String)> = self
            .active
            .extract_if(|k, _| !alerts.iter().any(|a| &a.key == k))
            .map(|(k, (_, text))| (k, text))
            .collect();
        gone.sort();
        for (_, text) in gone {
            out.push(format!("RESOLVED [{}] {text}", self.chain));
        }
        out
    }
}

/// Posts to a Slack incoming webhook; without one, messages only go to the log. What a post loses is sent again with
/// the next round's.
pub struct Slack {
    http: reqwest::Client,
    url: Option<String>,
    outbox: Vec<String>,
}

impl Slack {
    pub fn new(url: Option<String>) -> anyhow::Result<Self> {
        Ok(Self {
            http: reqwest::Client::builder()
                .timeout(Duration::from_secs(20))
                .build()?,
            url: url.filter(|u| !u.is_empty()),
            outbox: vec![],
        })
    }

    /// Whether everything sent so far is out: posted, or logged where there is no webhook.
    pub async fn send(&mut self, messages: Vec<String>) -> bool {
        for m in &messages {
            info!("{m}");
        }
        let Some(url) = &self.url else { return true };
        self.outbox.extend(messages);
        if self.outbox.is_empty() {
            return true;
        }
        let body = serde_json::json!({ "text": self.outbox.join("\n") }).to_string();
        let posted = self
            .http
            .post(url)
            .header(reqwest::header::CONTENT_TYPE, "application/json")
            .body(body)
            .send()
            .await
            .and_then(|r| r.error_for_status());
        match posted {
            Ok(_) => {
                self.outbox.clear();
                true
            }
            Err(e) => {
                error!(
                    "Slack did not take {} messages, trying again next round: {e}",
                    self.outbox.len()
                );
                let over = self.outbox.len().saturating_sub(OUTBOX);
                self.outbox.drain(..over);
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_repeated_and_resolved() {
        let (t, s) = (Instant::now(), Duration::from_secs);
        let mut n = Notifier::new("sepolia", s(3600));
        let forged = Alert::critical("forged-root", "a forged root");
        let low = Alert::warning("balance:asp", "asp is low");

        assert_eq!(
            n.round(&[forged.clone(), low.clone()], t),
            ["CRITICAL [sepolia] a forged root"],
            "a warning waits a round"
        );
        assert_eq!(
            n.round(&[forged.clone(), low.clone()], t + s(60)),
            ["WARNING [sepolia] asp is low"]
        );
        assert!(
            n.round(&[forged.clone(), low], t + s(120)).is_empty(),
            "already sent"
        );
        assert_eq!(
            n.round(std::slice::from_ref(&forged), t + s(180)),
            ["RESOLVED [sepolia] asp is low"]
        );
        assert_eq!(n.active(), 1);
        assert_eq!(
            n.round(&[forged], t + s(3600)),
            ["CRITICAL [sepolia] a forged root"],
            "repeated while it lasts"
        );
        assert_eq!(
            n.round(&[], t + s(3700)),
            ["RESOLVED [sepolia] a forged root"]
        );
        assert!(n.round(&[], t + s(3800)).is_empty());
    }

    #[test]
    fn a_warning_of_one_round_stays_quiet() {
        let (t, s) = (Instant::now(), Duration::from_secs);
        let mut n = Notifier::new("sepolia", s(3600));
        let blip = Alert::warning("asp", "cannot read the ASP");
        assert!(n.round(std::slice::from_ref(&blip), t).is_empty());
        assert!(n.round(&[], t + s(60)).is_empty(), "nothing to resolve");
        assert!(n.round(&[blip], t + s(120)).is_empty(), "counted afresh");
    }
}
