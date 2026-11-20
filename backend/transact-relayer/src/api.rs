//! `GET /fee` publishes what to pay; `POST /transact` and `POST /merge` check that a request pays it, then submit it.
use crate::fee::{self, FeeNote};
use crate::{App, FeeNoteLine};
use alloy::primitives::U256;
use axum::Router;
use axum::extract::{Json, State};
use axum::http::StatusCode;
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use parking_lot::Mutex;
use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::HashSet;
use std::fmt::Display;
use std::sync::Arc;
use tokio::sync::oneshot;
use tracing::{Instrument, info, warn};
use zerc20_common::contracts::IVerifier::{self, Merged, Transacted};
use zerc20_common::contracts::{MergeRequest, TransactRequest};
use zerc20_common::fields::u256;
use zerc20_common::{Reverted, for_client, rpc_error};

/// A refused request, logged as it is answered, so that the operator sees what wallets are told: the relayer's own
/// failures as warnings, the requests' as information.
struct Error(StatusCode, String);

impl From<(StatusCode, String)> for Error {
    fn from((status, message): (StatusCode, String)) -> Self {
        Self(status, message)
    }
}

impl Error {
    fn log(&self) {
        let Self(status, message) = self;
        match status.is_server_error() {
            true => warn!("refused ({status}): {message}"),
            false => info!("refused ({status}): {message}"),
        }
    }
}

impl IntoResponse for Error {
    fn into_response(self) -> Response {
        self.log();
        (self.0, self.1).into_response()
    }
}

fn bad(e: impl Display) -> Error {
    Error(StatusCode::BAD_REQUEST, e.to_string())
}

pub fn router(app: Arc<App>) -> Router {
    Router::new()
        .route("/fee", get(fees))
        .route("/transact", post(transact))
        .route("/merge", post(merge))
        .with_state(app)
        .layer(zerc20_common::cors())
}

async fn fees(State(app): State<Arc<App>>) -> Json<Value> {
    let fees: serde_json::Map<String, Value> = app
        .fees
        .all()
        .into_iter()
        .map(|(t, f)| (t.to_string(), json!({ "fee": f })))
        .collect();
    Json(json!({
        "chainId": app.chain_id,
        "relayer": app.fee_recipient,
        "sender": app.sender.address(),
        "publicKey": u256(app.public_key),
        "fees": fees,
    }))
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct TransactReq {
    request: TransactRequest,
    fee_note: Option<FeeNote>,
}

/// Claims a request's nullifiers until dropped. Without it, one valid request sent many times at once would pass
/// estimation every time, and the relayer would pay for every copy but the first to revert. A transaction from
/// elsewhere that spends one first is beyond it: the relayer's then reverts on chain, though before the proof, so for
/// little gas.
struct InFlight(Arc<App>, Vec<U256>);

impl InFlight {
    fn claim(app: &Arc<App>, n: Vec<U256>) -> Result<Self, Error> {
        let mut set = app.in_flight.lock();
        if n.iter().any(|x| set.contains(x)) {
            return Err(Error(
                StatusCode::CONFLICT,
                "a request with these nullifiers is being relayed".into(),
            ));
        }
        set.extend(n.iter().copied());
        Ok(Self(app.clone(), n))
    }
}

impl Drop for InFlight {
    fn drop(&mut self) {
        let mut set = self.0.in_flight.lock();
        for x in &self.1 {
            set.remove(x);
        }
    }
}

/// Nullifiers of unwraps that reverted on chain. Paying out the native asset calls the recipient, which can pass
/// estimation and still revert on chain, after the proof, at the relayer's cost. A revert spends no note, so without
/// this the same notes could do that again and again; refused here, each further try first pays to move its notes.
/// ponytail: in memory, so a restart allows each one more revert; persist it if that ever costs much.
#[derive(Default)]
pub struct RevertedUnwraps(Mutex<HashSet<U256>>);

impl RevertedUnwraps {
    fn check(&self, nullifiers: &[U256]) -> Result<(), Error> {
        let set = self.0.lock();
        match nullifiers.iter().any(|n| set.contains(n)) {
            true => Err(bad("an unwrap of these notes reverted on chain")),
            false => Ok(()),
        }
    }

    /// Remembers `nullifiers` when `e` is their unwrap reverting on chain, the one failed send that paid for gas.
    fn remember(&self, nullifiers: &[U256], e: &anyhow::Error) {
        if e.is::<Reverted>() {
            self.0.lock().extend(nullifiers);
        }
    }
}

/// The token a request spends, if it is relayed, and its fee now.
fn relayed(app: &App, token: U256) -> Result<(u32, U256), Error> {
    u32::try_from(token)
        .ok()
        .and_then(|t| Some((t, app.fees.get(t)?)))
        .ok_or_else(|| bad(format!("token {token} is not relayed")))
}

/// Whether `paid` pays the fee, which may be one quoted before it rose (see `Fees::accepts`).
fn pays(app: &App, token_id: u32, paid: U256, fee: U256) -> Result<(), Error> {
    match app.fees.accepts(token_id, paid) {
        true => Ok(()),
        false => Err(bad(format!("pays {paid}, the fee is {fee}"))),
    }
}

/// Runs `send` on its own task, in the request's span, holding `claim` until it ends. So a client that hangs up cancels
/// neither a transaction already in the pool, which the next send would then outbid, nor what `send` does once it is
/// mined, and frees no nullifier still in flight. `send` logs what it relayed itself, and a failure no client waits for
/// any more is logged here, as no answer logs it: a wallet whose page closed sends the same request again, and the log
/// shows the first one's fate. ponytail: relays go one at a time, each until mined (see Sender).
async fn detached<T: Send + 'static>(
    claim: impl Send + 'static,
    send: impl Future<Output = anyhow::Result<T>> + Send + 'static,
) -> Result<T, Error> {
    let (answer, answered) = oneshot::channel();
    tokio::spawn(
        async move {
            let _claim = claim;
            let sent = send
                .await
                .map_err(|e| Error(StatusCode::BAD_GATEWAY, for_client(&e)));
            if let Err(Err(e)) = answer.send(sent) {
                e.log();
            }
        }
        .in_current_span(),
    );
    answered
        .await
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?
}

async fn transact(
    State(app): State<Arc<App>>,
    Json(req): Json<TransactReq>,
) -> Result<Json<Value>, Error> {
    let s = &req.request.publicSignals;
    let (token_id, fee) = relayed(&app, s.tokenId)?;
    let nullifiers = [s.nullifier0, s.nullifier1];
    // the only nonzero intent the verifier takes
    let unwrap = !s.withdrawIntent.is_zero();
    if unwrap {
        app.reverted_unwraps.check(&nullifiers)?;
    }
    let verifier = IVerifier::new(app.verifier, &app.provider);
    // read now, not when the proof was made: the schedule applies at execution
    let withdraw_fee = verifier
        .withdrawFee(token_id, s.withdrawAmount)
        .call()
        .await
        .map_err(rpc_error)?;
    let (paid, slot) = fee::paid(
        s,
        req.fee_note.as_ref(),
        app.fee_recipient,
        app.public_key,
        withdraw_fee,
    )
    .map_err(bad)?;
    pays(&app, token_id, paid, fee)?;
    let line = req.fee_note.as_ref().zip(slot).map(|(n, i)| FeeNoteLine {
        chain_id: app.chain_id,
        token_id,
        value: n.value,
        salt: n.salt,
        note_hash: [s.noteHash1, s.noteHash2][i],
        index: None,
    });
    let claim = InFlight::claim(&app, nullifiers.to_vec())?;

    let call = verifier.transact(req.request);
    let gas = call.estimate_gas().await.map_err(rpc_error)?;
    // a withdrawal of the native asset calls its recipient, which could burn gas the fee does not pay for: the
    // transaction may take no more than the fee pays for, in estimation or on chain
    let max_gas = app.fees.max_gas();
    if let Some(max) = max_gas
        && gas > max
    {
        return Err(bad(format!(
            "takes {gas} gas, more than the fee pays for ({max})"
        )));
    }
    // a fee note that reaches the chain always has its opening on disk
    if let Some(l) = &line {
        app.record(l)
            .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    }
    let mut request = call.into_transaction_request();
    if let Some(max) = max_gas {
        request = request.gas_limit(max);
    }
    let (tx, block, indices) = detached(claim, {
        let app = app.clone();
        async move {
            let receipt = app.sender.send(request).await.inspect_err(|e| {
                if unwrap {
                    app.reverted_unwraps.remember(&nullifiers, e);
                }
            })?;
            let tx = receipt.transaction_hash;
            // the wallet finds its outputs by these, without asking a node about its own transaction
            let indices = receipt
                .decoded_log::<Transacted>()
                .map(|ev| [ev.noteIndex1, ev.noteIndex2]);
            if indices.is_none() {
                warn!("{tx} has no Transacted log");
            }
            if let (Some(mut l), Some(i), Some(indices)) = (line, slot, indices) {
                // ponytail: lost if this fails or the send gives up; then find the index by the note's tag in the indexer
                l.index = Some(indices[i]);
                if let Err(e) = app.record(&l) {
                    warn!(
                        "recording the index of fee note {:#066x}: {e:#}",
                        l.note_hash
                    );
                }
            }
            info!("relayed {tx}, paid {paid} of token {token_id}");
            // a wallet takes the transaction for dropped only once the indexer is past its block
            anyhow::Ok((tx, receipt.block_number, indices))
        }
    })
    .await?;
    let [i1, i2] = indices.map_or([None; 2], |i| i.map(Some));
    Ok(Json(
        json!({ "txHash": tx, "block": block, "noteIndex1": i1, "noteIndex2": i2 }),
    ))
}

#[derive(Deserialize)]
struct MergeReq {
    request: MergeRequest,
}

/// A merge pays the relayer with its `fee`, minted publicly to `feeRecipient`: no note to record. Its gas is not capped:
/// it calls no address a request names, so its gas follows its inputs alone.
async fn merge(
    State(app): State<Arc<App>>,
    Json(req): Json<MergeReq>,
) -> Result<Json<Value>, Error> {
    let r = &req.request;
    let (token_id, fee) = relayed(&app, r.tokenId)?;
    let verifier = IVerifier::new(app.verifier, &app.provider);
    // read now, not when the proof was made: the schedule applies at execution
    let withdraw_fee = verifier
        .withdrawFee(token_id, r.fee)
        .call()
        .await
        .map_err(rpc_error)?;
    let paid = fee::merge_paid(r.fee, r.feeRecipient, app.fee_recipient, withdraw_fee);
    pays(&app, token_id, paid, fee)?;
    let claim = InFlight::claim(&app, r.nullifiers.clone())?;

    let call = verifier.merge(req.request);
    call.estimate_gas().await.map_err(rpc_error)?;
    let request = call.into_transaction_request();
    let (tx, block, index) = detached(claim, {
        let app = app.clone();
        async move {
            let receipt = app.sender.send(request).await?;
            let tx = receipt.transaction_hash;
            let index = receipt.decoded_log::<Merged>().map(|ev| ev.noteIndex);
            if index.is_none() {
                warn!("{tx} has no Merged log");
            }
            info!("relayed merge {tx}, paid {paid} of token {token_id}");
            anyhow::Ok((tx, receipt.block_number, index))
        }
    })
    .await?;
    Ok(Json(
        json!({ "txHash": tx, "block": block, "noteIndex": index }),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy::primitives::TxHash;

    #[test]
    fn notes_whose_unwrap_reverted_on_chain_are_not_unwrapped_again() {
        let r = RevertedUnwraps::default();
        let [a, b, c] = [1, 2, 3].map(U256::from);
        r.remember(
            &[a, b],
            &anyhow::anyhow!("nonce 4 still unmined after 10 fee bumps"),
        );
        assert!(
            r.check(&[a, b]).is_ok(),
            "a send that failed otherwise paid no gas"
        );
        r.remember(&[a, b], &Reverted(TxHash::ZERO).into());
        assert!(r.check(&[c, b]).is_err(), "either note");
        assert!(r.check(&[c]).is_ok());
    }

    /// A send that fails once its client hung up is logged by the task, in the request's span; one a client still waits
    /// for is logged by its answer alone.
    #[tokio::test]
    async fn a_failed_send_is_logged_once_whether_its_client_waits_or_not() {
        #[derive(Clone)]
        struct Buf(Arc<parking_lot::Mutex<Vec<u8>>>);
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
        let refused = || {
            let log = String::from_utf8(buf.0.lock().clone()).unwrap();
            log.matches("chain{name=base}: zerc20_transact_relayer::api: refused (502 Bad Gateway): nonce 4 still unmined")
                .count()
        };
        let span = tracing::info_span!("chain", name = %"base");
        let failing = || async {
            tokio::time::sleep(std::time::Duration::from_millis(50)).await;
            Err::<(), _>(anyhow::anyhow!("nonce 4 still unmined"))
        };

        let hung_up = tokio::time::timeout(
            std::time::Duration::from_millis(10),
            detached((), failing()).instrument(span.clone()),
        )
        .await;
        assert!(hung_up.is_err());
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        assert_eq!(refused(), 1);

        let answer = detached((), failing()).instrument(span.clone()).await;
        assert_eq!(refused(), 1);
        let _ = span.in_scope(|| answer.unwrap_err().into_response());
        assert_eq!(refused(), 2);
    }
}
