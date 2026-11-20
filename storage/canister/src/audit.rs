//! The auditor: one principal, an Orbit station whose members approve each request, that may have
//! the key to any address's escrowed view key derived. Every request it makes is appended to a
//! public log before the key is derived.

use crate::registry::{derive_key, registration, vetkd_input, MIN_CYCLES};
use crate::{
    hex, rejected, to_array, AuditRecord, AuditRequest, Error, EvmAddress, AUDITOR, AUDITS,
    MAX_READ,
};
use candid::Principal;
use ic_stable_structures::storable::Bound;
use ic_stable_structures::Storable;
use std::borrow::Cow;

impl Storable for AuditRecord {
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.clone().into_bytes())
    }

    fn into_bytes(self) -> Vec<u8> {
        candid::encode_one(self)
            .unwrap_or_else(|e| ic_cdk::trap(format!("an audit record does not encode: {e}")))
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        candid::decode_one(&bytes)
            .unwrap_or_else(|e| ic_cdk::trap(format!("a stored audit record does not decode: {e}")))
    }

    const BOUND: Bound = Bound::Unbounded;
}

/// Traps on the anonymous principal, as which anyone can call, failing the install or upgrade.
pub(crate) fn set_auditor(auditor: Principal) {
    if auditor == Principal::anonymous() {
        ic_cdk::trap("auditor must not be the anonymous principal");
    }
    AUDITOR.with(|a| a.borrow_mut().set(auditor));
}

/// The target and notify key of the registration a request names, if it names one.
fn check_request(args: &AuditRequest) -> Result<(EvmAddress, [u8; 32]), Error> {
    let target: EvmAddress = to_array(&args.target, "target must be 20 bytes")?;
    let notify_key: [u8; 32] = to_array(&args.notify_key, "notify key must be 32 bytes")?;
    if args.transport_public_key.len() != 48 {
        return rejected("transport public key must be 48 bytes");
    }
    if registration(&target, &notify_key).is_none() {
        return rejected("no such registration");
    }
    Ok((target, notify_key))
}

/// What the station's approvers see of a request before they approve it: the registration it opens and the
/// transport key the opened key is encrypted to, or why `audit_escrow_key` would reject it.
pub(crate) fn validate(args: &AuditRequest) -> Result<String, String> {
    check_request(args).map_err(|e| format!("{e:?}"))?;
    Ok(format!(
        "zERC20 storage audit request\ntarget: 0x{}\nnotify_key: 0x{}\ntransport_public_key: 0x{}",
        hex(&args.target),
        hex(&args.notify_key),
        hex(&args.transport_public_key),
    ))
}

/// Everything `audit_escrow_key` checks (the caller, cycles, and that the target made the
/// registration), the record to log, and the vetKD input of the escrow the request opens. Requests
/// need no expiry or replay guard: only the auditor can make them, and the station executes each
/// approved request once.
pub(crate) fn authorize_audit(
    args: &AuditRequest,
    caller: Principal,
    now_ns: u64,
    cycles: u128,
) -> Result<(AuditRecord, Vec<u8>), Error> {
    let auditor = AUDITOR.with(|a| *a.borrow().get());
    if caller != auditor {
        return rejected("not the auditor");
    }
    if cycles < MIN_CYCLES {
        return rejected("canister is low on cycles");
    }
    let (target, notify_key) = check_request(args)?;
    let record = AuditRecord {
        auditor,
        target: args.target.clone(),
        notify_key: args.notify_key.clone(),
        transport_public_key: args.transport_public_key.clone(),
        at_ns: now_ns,
    };
    Ok((record, vetkd_input(&target, &notify_key)))
}

fn log(record: AuditRecord) {
    AUDITS.with(|a| {
        let mut a = a.borrow_mut();
        let next = a.len();
        a.insert(next, record);
    });
}

/// Logs the request, then derives. The log entry is committed before the `await`, so a key can never
/// be handed out unlogged.
pub(crate) async fn audit(args: AuditRequest) -> Result<Vec<u8>, Error> {
    let (record, input) = authorize_audit(
        &args,
        ic_cdk::api::msg_caller(),
        ic_cdk::api::time(),
        ic_cdk::api::canister_cycle_balance(),
    )?;
    log(record);
    derive_key(input, args.transport_public_key).await
}

pub(crate) fn audits(start: u64, limit: u32) -> Vec<AuditRecord> {
    let end = start.saturating_add(limit.min(MAX_READ as u32) as u64);
    AUDITS.with(|a| a.borrow().range(start..end).map(|e| e.value()).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::evm_address;
    use crate::registry::tests::{register_now, registration_by};
    use k256::ecdsa::SigningKey;

    #[test]
    fn audits_come_only_from_the_auditor_and_are_logged() {
        let auditor = Principal::from_slice(&[3; 10]);
        set_auditor(auditor);
        let owner = SigningKey::from_bytes(&[10; 32].into()).unwrap();
        let target = evm_address(owner.verifying_key());
        register_now(&registration_by(&owner, 1, 1)).unwrap();
        let request = |notify: u8| AuditRequest {
            target: target.to_vec(),
            notify_key: vec![notify; 32],
            transport_public_key: vec![4; 48],
        };
        let authorize = |args: &AuditRequest, caller| {
            authorize_audit(args, caller, 7, MIN_CYCLES).map(|(record, _)| record)
        };

        assert_eq!(
            authorize(&request(1), Principal::anonymous()),
            rejected("not the auditor")
        );
        assert_eq!(
            authorize(&request(2), auditor),
            rejected("no such registration")
        );
        assert!(validate(&request(2)).is_err());
        assert!(validate(&request(1)).unwrap().contains(&hex(&target)));

        let record = authorize(&request(1), auditor).unwrap();
        assert_eq!(
            (record.auditor, record.target.clone(), record.at_ns),
            (auditor, target.to_vec(), 7)
        );
        log(record.clone());
        assert_eq!(audits(0, 10), vec![record]);
    }
}
