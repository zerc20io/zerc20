//! What counts as wrong, apart from reading it: each check takes what was read and says what needs someone.
use alloy::primitives::{Address, U256};
use alloy::rpc::types::Log;
use alloy::sol_types::SolEvent;
use serde_json::Value;
use std::time::{Duration, Instant};
use zerc20_common::contracts::IAccessManager::{OperationScheduled, RoleGranted};
use zerc20_common::contracts::IUpgradeable::Upgraded;

#[derive(Clone, Debug, PartialEq)]
pub struct Alert {
    /// One per thing watched: an alert is new, repeated or resolved by its key.
    pub key: String,
    pub critical: bool,
    pub text: String,
}

impl Alert {
    pub fn critical(key: impl Into<String>, text: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            critical: true,
            text: text.into(),
        }
    }

    pub fn warning(key: impl Into<String>, text: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            critical: false,
            text: text.into(),
        }
    }

    pub fn level(&self) -> &'static str {
        if self.critical { "CRITICAL" } else { "WARNING" }
    }
}

/// A proved root the indexer does not derive: the ledger goes into an emergency, which only the admin ends.
pub fn forged(status: &Value) -> Option<Alert> {
    let m = status.get("mismatch").filter(|m| !m.is_null())?;
    let honest = &status["latest_root"]["index"];
    Some(Alert::critical(
        "forged-root",
        format!(
            "the ledger proved root {} over {} commitments, which the indexer does not derive. The last honest root \
             is over {}. A guardian puts the ledger in an emergency; the admin's recover ends it (contracts/README.md)",
            m["root"].as_str().unwrap_or("?"),
            m["index"],
            if honest.is_null() {
                "0 (genesis)".into()
            } else {
                honest.to_string()
            }
        ),
    ))
}

pub fn stalled(status: &Value) -> Option<Alert> {
    (status["indexer"]["stalled"] == Value::Bool(true)).then(|| {
        Alert::critical(
            "indexer-stalled",
            format!(
                "the indexer has not stepped forward for {} s (cursor {}, head {})",
                status["indexer"]["last_ok_secs"],
                status["indexer"]["cursor"],
                status["indexer"]["head"]
            ),
        )
    })
}

pub fn emergency(bound: u64) -> Option<Alert> {
    (bound != u64::MAX).then(|| {
        Alert::critical(
            "emergency",
            format!(
                "the ledger is in an emergency: it accepts no root above {bound} commitments and proves none. \
                 Resolved by a recovery (contracts/README.md)"
            ),
        )
    })
}

/// The attester's default `FALLBACK_SECS`: from then on it screens withdrawals by the Blocklist alone, as the ASP does
/// deposits already.
const CHAINALYSIS_DOWN: Duration = Duration::from_secs(300);

/// Chainalysis not answering the ASP's probe, `down` long. One key serves every chain, so it speaks for all of them.
pub fn chainalysis(down: Duration) -> Option<Alert> {
    (down >= CHAINALYSIS_DOWN).then(|| {
        Alert::warning(
            "chainalysis",
            format!(
                "Chainalysis has not answered for {} min, so deposits and withdrawals on every chain are screened by \
                 the Blocklist alone until it does: an outage at Chainalysis, or a key it no longer takes",
                down.as_secs() / 60
            ),
        )
    })
}

pub fn low(name: &str, account: Address, balance: U256, min: U256) -> Option<Alert> {
    (balance < min).then(|| {
        Alert::warning(
            format!("balance:{name}"),
            format!("{name} ({account}) holds {balance} wei, less than {min}"),
        )
    })
}

/// What a governance event says, for a person to judge within the delay: a call scheduled on the AccessManager, a
/// role granted, or a contract upgraded. `names` names the contracts watched; `now` is Unix seconds.
pub fn governance(log: &Log, names: &[(&str, Address)], now: u64) -> Option<Alert> {
    let name = |a: Address| match names.iter().find(|(_, x)| *x == a) {
        Some((n, _)) => format!("{n} ({a})"),
        None => a.to_string(),
    };
    let tx = log.transaction_hash.unwrap_or_default();
    let text = match *log.topic0()? {
        OperationScheduled::SIGNATURE_HASH => {
            let e = OperationScheduled::decode_log_data(log.data()).ok()?;
            let at = e.schedule.to::<u64>();
            let mins = at.saturating_sub(now) / 60;
            format!(
                "{} scheduled a call to {}, executable in {} h {} min (Unix {at}): data {}",
                e.caller,
                name(e.target),
                mins / 60,
                mins % 60,
                e.data
            )
        }
        RoleGranted::SIGNATURE_HASH => {
            let e = RoleGranted::decode_log_data(log.data()).ok()?;
            let role = match e.roleId {
                0 => "ADMIN".into(),
                1 => "OPERATOR".into(),
                2 => "PAUSER".into(),
                id => format!("role {id}"),
            };
            format!(
                "{} is granted {role} with an execution delay of {} s, from Unix {}{}",
                e.account,
                e.delay,
                e.since,
                if e.newMember {
                    ""
                } else {
                    ", a member already, whose delay this changes"
                }
            )
        }
        Upgraded::SIGNATURE_HASH => {
            let e = Upgraded::decode_log_data(log.data()).ok()?;
            format!(
                "{} is upgraded to implementation {}",
                name(log.address()),
                e.implementation
            )
        }
        _ => return None,
    };
    Some(Alert::critical(
        format!("governance:{tx}:{}", log.log_index.unwrap_or_default()),
        format!("{text}; tx {tx}"),
    ))
}

/// How long something has had work waiting without moving: roots behind the commitments, ASP decisions behind the
/// final commitments, a recorded ASP root not on chain. Only the time spent behind counts, so a quiet chain is never
/// stale, and the first transfer after a quiet spell does not alert.
#[derive(Default)]
pub struct Stale<T> {
    since: Option<(T, Instant)>,
}

impl<T: PartialEq> Stale<T> {
    /// `at` is where it stands, `behind` whether anything waits for it. How long it has been behind at `at`.
    pub fn behind(&mut self, at: T, behind: bool, now: Instant) -> Option<Duration> {
        match &self.since {
            Some((was, since)) if behind && *was == at => Some(now - *since),
            _ => {
                self.since = Some((at, now));
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn a_forged_root_names_the_honest_one() {
        let ok = json!({ "latest_root": { "index": 70 }, "mismatch": null });
        assert_eq!(forged(&ok), None);
        let bad =
            json!({ "latest_root": { "index": 70 }, "mismatch": { "index": 90, "root": "0x12" } });
        let a = forged(&bad).unwrap();
        assert!(
            a.critical && a.text.contains("over 90") && a.text.contains("is over 70"),
            "{}",
            a.text
        );
        let genesis = json!({ "latest_root": null, "mismatch": { "index": 90, "root": "0x12" } });
        assert!(forged(&genesis).unwrap().text.contains("genesis"));
    }

    #[test]
    fn chainalysis_down_once_the_attester_falls_back() {
        assert_eq!(chainalysis(Duration::ZERO), None);
        assert_eq!(chainalysis(Duration::from_secs(299)), None);
        let a = chainalysis(Duration::from_secs(420)).unwrap();
        assert!(!a.critical && a.key == "chainalysis" && a.text.contains("for 7 min"));
    }

    #[test]
    fn emergency_and_balances() {
        assert_eq!(emergency(u64::MAX), None);
        assert!(emergency(70).unwrap().critical);
        let a = Address::repeat_byte(1);
        assert_eq!(low("asp", a, U256::from(10), U256::from(10)), None);
        assert_eq!(
            low("asp", a, U256::from(9), U256::from(10)).unwrap().key,
            "balance:asp"
        );
    }

    #[test]
    fn governance_events_say_what_and_when() {
        let (manager, verifier, safe) = (
            Address::repeat_byte(1),
            Address::repeat_byte(2),
            Address::repeat_byte(3),
        );
        let names = [("the AccessManager", manager), ("the Verifier", verifier)];
        let log = |address, data| Log {
            inner: alloy::primitives::Log { address, data },
            transaction_hash: Some(alloy::primitives::B256::repeat_byte(9)),
            ..Default::default()
        };
        let scheduled = OperationScheduled {
            operationId: Default::default(),
            nonce: 1,
            schedule: alloy::primitives::aliases::U48::from(1_000 + 3 * 3600 + 120),
            caller: safe,
            target: verifier,
            data: vec![0x3e, 0x90, 0x86, 0x12].into(),
        };
        let a = governance(&log(manager, scheduled.encode_log_data()), &names, 1_000).unwrap();
        assert!(a.critical);
        assert!(
            a.text.contains(&format!(
                "{safe} scheduled a call to the Verifier ({verifier})"
            )) && a.text.contains("in 3 h 2 min")
                && a.text.contains("data 0x3e908612")
                && a.text
                    .contains(&format!("tx {}", alloy::primitives::B256::repeat_byte(9))),
            "{}",
            a.text
        );

        let granted = RoleGranted {
            roleId: 0,
            account: safe,
            delay: 259_200,
            since: alloy::primitives::aliases::U48::from(1_000),
            newMember: true,
        };
        let a = governance(&log(manager, granted.encode_log_data()), &names, 1_000).unwrap();
        assert!(
            a.text.contains(&format!(
                "{safe} is granted ADMIN with an execution delay of 259200 s"
            )),
            "{}",
            a.text
        );

        let upgraded = Upgraded {
            implementation: safe,
        };
        let a = governance(&log(verifier, upgraded.encode_log_data()), &names, 1_000).unwrap();
        assert!(
            a.text.contains(&format!(
                "the Verifier ({verifier}) is upgraded to implementation {safe}"
            )),
            "{}",
            a.text
        );

        let other = log(
            manager,
            alloy::primitives::LogData::new_unchecked(vec![Default::default()], Default::default()),
        );
        assert_eq!(governance(&other, &names, 1_000), None);
    }

    #[test]
    fn only_time_spent_behind_counts() {
        let (t, s) = (Instant::now(), Duration::from_secs);
        let mut roots = Stale::default();
        assert_eq!(roots.behind(5, false, t), None);
        assert_eq!(roots.behind(5, false, t + s(600)), None, "quiet, not stale");
        assert_eq!(
            roots.behind(5, true, t + s(700)),
            Some(s(100)),
            "behind since the last quiet round"
        );
        assert_eq!(roots.behind(5, true, t + s(900)), Some(s(300)));
        assert_eq!(roots.behind(8, true, t + s(950)), None, "it moved");
        assert_eq!(roots.behind(8, true, t + s(1000)), Some(s(50)));
    }
}
