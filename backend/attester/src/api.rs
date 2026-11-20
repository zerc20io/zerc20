//! Wallets get attestations here. A statement is checked in order of cost: chain and root here, the witness in the
//! enclave, and last the recipient with Chainalysis, so that only spends with a valid witness use its quota.
use crate::App;
use alloy::primitives::{Address, B256, Bytes, U256};
use axum::Router;
use axum::extract::{Json, State};
use axum::http::StatusCode;
use axum::routing::{get, post};
use parking_lot::Mutex;
use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tracing::warn;
use zerc20_attester::{Merge, NO_KEY, Request, Transact};
use zerc20_common::contracts::IBlocklist;

/// The attester's share of the Chainalysis key, which the ASP screens deposits with too: 10 screenings a second of the
/// 40 Chainalysis allows, for every chain together.
const EVERY: Duration = Duration::from_millis(100);
/// How long a screening may wait for its turn before the client gets 429 instead.
const QUEUE: Duration = Duration::from_secs(2);
/// A note's screenings: `NOTE_BURST` at once, then one per `NOTE_EVERY`, whatever the recipients. A client with one
/// note cannot take the attester's share; to take it for good it has to hold `NOTE_EVERY / EVERY` notes.
const NOTE_EVERY: Duration = Duration::from_secs(300);
const NOTE_BURST: u32 = 3;

type Res = Result<Json<Value>, (StatusCode, String)>;

/// Turns at Chainalysis: the attester's, and each note's within them. A turn is taken only for a statement the enclave
/// signed, so junk takes none, and a refused one never reaches Chainalysis nor counts toward the Blocklist fallback.
pub struct Quota(Mutex<Turns>);

struct Turns {
    /// When the next screening may start.
    next: Instant,
    /// When each recently screened nullifier has all its turns back, one per `NOTE_EVERY`; it takes another while fewer
    /// than `NOTE_BURST` are out.
    notes: HashMap<U256, Instant>,
}

impl Quota {
    pub fn new() -> Self {
        Self(Mutex::new(Turns {
            next: Instant::now(),
            notes: HashMap::new(),
        }))
    }

    /// Books a screening at `now` for a statement that spends `nullifiers`: when it may start, or the 429 to answer.
    /// Every nullifier counts, so a transact's dummy `in1`, which is free to pick, cannot stand in for its real `in0`.
    fn book(&self, nullifiers: &[U256], now: Instant) -> Result<Instant, (StatusCode, String)> {
        let busy = |m: &str| Err((StatusCode::TOO_MANY_REQUESTS, m.into()));
        let mut t = self.0.lock();
        let ahead = now + NOTE_EVERY * (NOTE_BURST - 1);
        if nullifiers
            .iter()
            .any(|n| t.notes.get(n).is_some_and(|&due| due > ahead))
        {
            return busy("these notes were screened too often; retry in a few minutes");
        }
        let start = t.next.max(now);
        if start > now + QUEUE {
            return busy("the attester is screening too many withdrawals; retry shortly");
        }
        t.next = start + EVERY;
        t.notes.retain(|_, due| *due > now);
        for &n in nullifiers {
            let due = t.notes.entry(n).or_insert(now);
            *due += NOTE_EVERY;
        }
        Ok(start)
    }
}

#[derive(Deserialize)]
struct Body<T> {
    statement: T,
    /// The witness, sealed to the enclave's key (`zerc20_attester_proto::seal` with `WITNESS`).
    witness: Bytes,
}

pub fn router(app: Arc<App>) -> Router {
    Router::new()
        .route("/attestation", get(attestation))
        .route("/transact", post(transact))
        .route("/merge", post(merge))
        .with_state(app)
        .layer(zerc20_common::cors())
}

/// The key to seal witnesses to, the attestation document that vouches for it, and the attester's address.
async fn attestation(State(app): State<Arc<App>>) -> Res {
    enclave(&app, Request::Attestation).await.map(Json)
}

async fn transact(State(app): State<Arc<App>>, Json(b): Json<Body<Transact>>) -> Res {
    let s = b.statement;
    public(&app, s.chainId, s.commitmentRoot)?;
    let recipient = (!s.withdrawAmount.is_zero()).then_some(s.withdrawRecipient);
    let nullifiers = [s.nullifier0, s.nullifier1];
    let request = Request::Transact {
        verifier: app.verifier,
        statement: s,
        witness: b.witness,
    };
    let attestation = enclave(&app, request).await?;
    // the enclave saw it below 2^160
    if let Some(r) = recipient {
        screen(&app, Address::from_word(B256::from(r)), &nullifiers).await?;
    }
    Ok(Json(json!({ "attestation": attestation })))
}

async fn merge(State(app): State<Arc<App>>, Json(b): Json<Body<Merge>>) -> Res {
    let s = b.statement;
    public(&app, s.chainId, s.commitmentRoot)?;
    // the fee is a public withdrawal to its recipient: screened like any, or a large fee to oneself would skip it
    let recipient = (!s.fee.is_zero()).then_some(s.feeRecipient);
    let nullifiers = s.nullifiers.clone();
    let request = Request::Merge {
        verifier: app.verifier,
        statement: s,
        witness: b.witness,
    };
    let attestation = enclave(&app, request).await?;
    // the enclave saw it below 2^160
    if let Some(r) = recipient {
        screen(&app, Address::from_word(B256::from(r)), &nullifiers).await?;
    }
    Ok(Json(json!({ "attestation": attestation })))
}

/// The statement is for this chain, against a root the indexer derived itself.
fn public(app: &App, chain: U256, root: U256) -> Result<(), (StatusCode, String)> {
    if chain != U256::from(app.chain) {
        return Err((
            StatusCode::BAD_REQUEST,
            format!("chainId is not {}", app.chain),
        ));
    }
    if !app.roots.read().contains(&root) {
        return Err((
            StatusCode::BAD_REQUEST,
            "commitmentRoot is not a root the indexer derived; retry once it has".into(),
        ));
    }
    Ok(())
}

/// The enclave rejecting a witness is the client's fault; not reaching it, or it having no key yet, is not.
async fn enclave(app: &App, request: Request) -> Result<Value, (StatusCode, String)> {
    let unavailable = || {
        (
            StatusCode::SERVICE_UNAVAILABLE,
            "the enclave is unavailable".into(),
        )
    };
    match app.ask(request).await {
        Ok(Ok(v)) => Ok(v),
        Ok(Err(e)) if e == NO_KEY => Err(unavailable()),
        Ok(Err(e)) => Err((StatusCode::BAD_REQUEST, e)),
        Err(e) => {
            warn!("{e:#}");
            Err(unavailable())
        }
    }
}

/// Chainalysis decides whether `to` may receive a withdrawal. Once Chainalysis has been down for `FALLBACK_SECS`, a
/// screening it fails is decided by the protocol's Blocklist alone, at once, so that an outage holds withdrawals back
/// only that long. Down is what its probe finds, on a schedule no client sets: a client chooses when its own screenings
/// fail, flooding them into the rate limit or retrying until one hits a blip, so those count for nothing.
async fn screen(app: &App, to: Address, nullifiers: &[U256]) -> Result<(), (StatusCode, String)> {
    let start = app.quota.book(nullifiers, Instant::now())?;
    tokio::time::sleep_until(start.into()).await;
    let retry = || {
        (
            StatusCode::SERVICE_UNAVAILABLE,
            "screening the recipient failed; retry later".into(),
        )
    };
    let passes = match app.chainalysis.passes(to).await {
        Ok(passes) => passes,
        Err(e) => {
            let down = app.chainalysis.down_for();
            if down < app.fallback_after {
                warn!("screening {to} failed: {e:#}");
                return Err(retry());
            }
            warn!(
                "screening {to} failed with Chainalysis down for {}s, deciding by the Blocklist alone: {e:#}",
                down.as_secs()
            );
            let blocked = IBlocklist::new(app.blocklist, &app.provider)
                .isBlocked(to)
                .call()
                .await
                .map_err(|e| {
                    warn!("isBlocked({to}) failed: {e:#}");
                    retry()
                })?;
            !blocked
        }
    };
    if !passes {
        warn!("refused a withdrawal to {to}");
        return Err((
            StatusCode::FORBIDDEN,
            "the withdrawal recipient fails screening".into(),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_note_and_the_attester_take_their_turns() {
        let (quota, queue) = (Quota::new(), Quota::new());
        let t0 = Instant::now();
        let [a, b] = [U256::from(1), U256::from(2)];
        // a note's first turns come at once, paced by the attester's
        for k in 0..NOTE_BURST {
            assert_eq!(quota.book(&[a], t0), Ok(t0 + EVERY * k));
        }
        let refused = quota.book(&[a], t0).unwrap_err();
        assert_eq!(refused.0, StatusCode::TOO_MANY_REQUESTS);
        // nor with a fresh nullifier beside it, which takes no turn
        assert!(quota.book(&[b, a], t0).is_err());
        assert_eq!(quota.book(&[b], t0), Ok(t0 + EVERY * NOTE_BURST));
        assert!(quota.book(&[a], t0 + NOTE_EVERY).is_ok());

        // fresh notes at one instant wait their turn until the queue is full
        let mut fresh = (10u64..).map(|n| [U256::from(n)]);
        let queued = fresh
            .by_ref()
            .take_while(|n| queue.book(n, t0).is_ok())
            .count() as u128;
        assert_eq!(queued, QUEUE.as_millis() / EVERY.as_millis() + 1);
        assert!(queue.book(&fresh.next().unwrap(), t0 + EVERY).is_ok());
    }
}
