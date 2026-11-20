//! `POST /register`: how the relayer learns of a deposit address, since an undeployed one leaves no
//! trace on chain. `POST /rewatch`: how a wallet has one watched again once its window is over.
use crate::App;
use crate::contracts::IDepositAddressFactory;
use crate::store::Reg;
use alloy::primitives::Address;
use axum::Router;
use axum::extract::{Json, State};
use axum::http::StatusCode;
use axum::routing::post;
use serde::Deserialize;
use std::sync::Arc;
use zerc20_common::contracts::IZERC20;
use zerc20_common::{now, rpc_error};

pub fn router(app: Arc<App>) -> Router {
    Router::new()
        .route("/register", post(register))
        .route("/rewatch", post(rewatch))
        .with_state(app)
        .layer(zerc20_common::cors())
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct RegisterReq {
    token: Address,
    burn_address: Address,
    /// One of the two, the other absent: a fixed refund address, or the key that signs where each refund goes.
    #[serde(default)]
    refund_address: Address,
    #[serde(default)]
    refund_signer: Address,
    /// The app that hands the address out, and its share of each deposit; none when absent.
    #[serde(default)]
    referrer: Address,
    #[serde(default)]
    referral_bps: u16,
}

/// ponytail: no rate limit, so spam grows the watched set, and its polling, for 7 days; cap registrations per client
/// if it shows up.
async fn register(
    State(app): State<Arc<App>>,
    Json(req): Json<RegisterReq>,
) -> Result<Json<serde_json::Value>, (StatusCode, String)> {
    let token = IZERC20::new(req.token, &app.provider);
    let token_id = token.tokenId().call().await.map_err(|e| match e {
        // not a contract: the client's mistake, not the RPC's
        alloy::contract::Error::ZeroData(..) => (StatusCode::BAD_REQUEST, e.to_string()),
        e => rpc_error(e),
    })?;
    // the fee now: the address fixes it, so a later change leaves this registration be
    let fee = app.fees.get(token_id).ok_or((
        StatusCode::BAD_REQUEST,
        format!("token {token_id} is not relayed"),
    ))?;
    let fee_recipient = app.fee_recipient;
    // predict reverts for an unregistered token, a zero address, both or neither of the refund address and signer, or a
    // referral over the cap
    let deposit = IDepositAddressFactory::new(app.factory, &app.provider)
        .predict(
            req.token,
            req.burn_address,
            req.refund_address,
            req.refund_signer,
            fee_recipient,
            fee,
            req.referrer,
            req.referral_bps,
        )
        .call()
        .await
        .map_err(rpc_error)?;
    let underlying = token.underlyingAsset().call().await.map_err(rpc_error)?;
    let reg = Reg {
        token: req.token,
        burn_address: req.burn_address,
        refund_address: req.refund_address,
        refund_signer: req.refund_signer,
        deposit_address: deposit,
        underlying,
        fee_recipient,
        fee,
        referrer: req.referrer,
        referral_bps: req.referral_bps,
        at: now(),
        reverted: false,
    };
    app.store
        .lock()
        .put(reg.clone())
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    Ok(answer(&reg))
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct RewatchReq {
    deposit_address: Address,
}

/// Watches a registered address for another window, at the fee it was registered with: a registration now would take
/// the fee of the moment, which makes another address. Anyone may ask, as anyone may flush; 404 for an address never
/// registered here.
async fn rewatch(
    State(app): State<Arc<App>>,
    Json(req): Json<RewatchReq>,
) -> Result<Json<serde_json::Value>, (StatusCode, String)> {
    let reg = app
        .store
        .lock()
        .rewatch(req.deposit_address, now())
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?
        .ok_or((
            StatusCode::NOT_FOUND,
            format!("{} is not registered here", req.deposit_address),
        ))?;
    Ok(answer(&reg))
}

/// The address, and the fee and recipient it fixes.
fn answer(r: &Reg) -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "depositAddress": r.deposit_address,
        "feeRecipient": r.fee_recipient,
        "fee": r.fee,
    }))
}
