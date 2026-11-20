//! The directory and the vetKD gateway: registrations, the escrow public key, and the vetKD derivation
//! that only audits use.

use crate::store::take_room;
use crate::{
    check_expiry, check_pow, eip191_signer, hex, rejected, tagged_hash, to_array, Error,
    EvmAddress, Registration, CURRENT, KEY_NAME, REGISTER_POW_BITS, REGISTRATIONS,
};
use candid::Principal;
use ic_cdk::management_canister::{
    vetkd_derive_key, vetkd_public_key, VetKDCurve, VetKDDeriveKeyArgs, VetKDKeyId,
    VetKDPublicKeyArgs,
};
use ic_stable_structures::storable::Bound;
use ic_stable_structures::Storable;
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::cell::RefCell;

pub(crate) const MIN_CYCLES: u128 = 1_000_000_000_000;
/// vetKD context of every escrow key. The address and notify key go in the input, so one escrow public
/// key covers all.
const ESCROW_CONTEXT: &[u8] = b"zerc20/storage/escrow/v1";
/// Tags a registration's proof-of-work digest and the text its owner signs.
const REGISTRATION_TAG: &str = "zerc20/storage/registration/v1";
/// An IBE ciphertext of a 32-byte seed, with room to spare.
pub(crate) const MAX_ESCROW: usize = 512;

thread_local! {
    /// Fixed for a given (canister, context, key name); refetched after an upgrade.
    static ESCROW_PUBLIC_KEY: RefCell<Option<Vec<u8>>> = RefCell::default();
}

impl Storable for Registration {
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.clone().into_bytes())
    }

    fn into_bytes(self) -> Vec<u8> {
        candid::encode_one(self)
            .unwrap_or_else(|e| ic_cdk::trap(format!("a registration does not encode: {e}")))
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        candid::decode_one(&bytes)
            .unwrap_or_else(|e| ic_cdk::trap(format!("a stored registration does not decode: {e}")))
    }

    const BOUND: Bound = Bound::Unbounded;
}

/// The vetKD input (= IBE identity) of the escrow key of a registration: `address(20) ‖ notify_key(32)`.
/// Every vetKD use goes through this so derivation, encryption and verification cannot drift apart.
pub fn vetkd_input(address: &EvmAddress, notify_key: &[u8; 32]) -> Vec<u8> {
    [&address[..], notify_key].concat()
}

pub(crate) fn current(address: &EvmAddress) -> Option<Registration> {
    let key = CURRENT.with(|c| c.borrow().get(address))?;
    registration(address, &key)
}

pub(crate) fn registration(address: &EvmAddress, notify_key: &[u8; 32]) -> Option<Registration> {
    REGISTRATIONS.with(|r| r.borrow().get(&(*address, *notify_key)))
}

/// The exact text the address owner signs (EIP-191) to register.
pub fn register_message(canister: &Principal, r: &Registration) -> String {
    format!(
        "zERC20 storage registration\ncanister: {canister}\naddress: 0x{}\npublic_key: 0x{}\n\
         notify_key: 0x{}\nescrow_sha256: 0x{}\nexpiry_ns: {}\ntag: {REGISTRATION_TAG}",
        hex(&r.address),
        hex(&r.public_key),
        hex(&r.notify_key),
        hex(&Sha256::digest(&r.escrow)),
        r.expiry_ns,
    )
}

/// Proof-of-work digest of a `register` call.
pub fn register_digest(r: &Registration) -> [u8; 32] {
    tagged_hash(
        REGISTRATION_TAG.as_bytes(),
        &[
            &r.address,
            &r.public_key,
            &r.notify_key,
            &r.escrow,
            &r.expiry_ns.to_be_bytes(),
        ],
    )
}

/// Traps on an empty name, which fails the install.
pub(crate) fn set_key_name(name: String) {
    if name.is_empty() {
        ic_cdk::trap("vetkd_key_name must be set");
    }
    KEY_NAME.with(|k| k.borrow_mut().set(name));
}

/// Traps on a name other than the installed one, which fails the upgrade.
pub(crate) fn keep_key_name(name: &str) {
    if KEY_NAME.with(|k| k.borrow().get() != name) {
        ic_cdk::trap("vetkd_key_name cannot change");
    }
}

fn key_id() -> VetKDKeyId {
    VetKDKeyId {
        curve: VetKDCurve::Bls12_381_G2,
        name: KEY_NAME.with(|k| k.borrow().get().clone()),
    }
}

/// Everything `register` checks, and the key to file the registration under: its address and notify
/// key. `Ok(None)`: the identical registration is already current (a retry), so there is nothing to
/// do. Otherwise a registration replaces the current one only if it expires later, so an old
/// signature cannot be replayed over a newer one.
fn authorize_register(
    r: &Registration,
    pow_nonce: u64,
    canister: Principal,
    now_ns: u64,
) -> Result<Option<(EvmAddress, [u8; 32])>, Error> {
    let address: EvmAddress = to_array(&r.address, "address must be 20 bytes")?;
    let current = current(&address);
    if current.as_ref() == Some(r) {
        return Ok(None);
    }
    check_pow(&register_digest(r), pow_nonce, REGISTER_POW_BITS)?;
    if current.is_some_and(|c| r.expiry_ns <= c.expiry_ns) {
        return rejected("a registration must expire later than the current one");
    }
    if r.public_key.len() != 32 {
        return rejected("public key must be 32 bytes");
    }
    let notify_key: [u8; 32] = to_array(&r.notify_key, "notify key must be 32 bytes")?;
    if r.escrow.is_empty() || r.escrow.len() > MAX_ESCROW {
        return rejected("escrow must be 1..=512 bytes");
    }
    check_expiry(r.expiry_ns, now_ns)?;
    if eip191_signer(&register_message(&canister, r), &r.signature) != Some(address) {
        return rejected("bad signature");
    }
    Ok(Some((address, notify_key)))
}

pub(crate) fn register(r: Registration, pow_nonce: u64) -> Result<(), Error> {
    register_at(
        r,
        pow_nonce,
        ic_cdk::api::canister_self(),
        ic_cdk::api::time(),
    )
}

/// Files `r` as its address's current registration, under the key `authorize_register` gives it, if there is room.
pub(crate) fn register_at(
    r: Registration,
    pow_nonce: u64,
    canister: Principal,
    now_ns: u64,
) -> Result<(), Error> {
    if let Some((address, notify_key)) = authorize_register(&r, pow_nonce, canister, now_ns)? {
        // at most two entries: the registration, and its address's first in CURRENT
        take_room(2, now_ns)?;
        CURRENT.with(|c| c.borrow_mut().insert(address, notify_key));
        REGISTRATIONS.with(|m| m.borrow_mut().insert((address, notify_key), r));
    }
    Ok(())
}

pub(crate) async fn escrow_public_key() -> Result<Vec<u8>, Error> {
    if let Some(key) = ESCROW_PUBLIC_KEY.with(|k| k.borrow().clone()) {
        return Ok(key);
    }
    let args = VetKDPublicKeyArgs {
        canister_id: None,
        context: ESCROW_CONTEXT.to_vec(),
        key_id: key_id(),
    };
    let key = vetkd_public_key(&args)
        .await
        .map_err(|e| Error::Rejected(format!("vetkd_public_key: {e}")))?
        .public_key;
    ESCROW_PUBLIC_KEY.with(|k| *k.borrow_mut() = Some(key.clone()));
    Ok(key)
}

/// The key to the escrow with vetKD `input`, encrypted to `transport_public_key`. `audit` authorizes
/// it first.
pub(crate) async fn derive_key(
    input: Vec<u8>,
    transport_public_key: Vec<u8>,
) -> Result<Vec<u8>, Error> {
    let args = VetKDDeriveKeyArgs {
        input,
        context: ESCROW_CONTEXT.to_vec(),
        transport_public_key,
        key_id: key_id(),
    };
    let result = vetkd_derive_key(&args)
        .await
        .map_err(|e| Error::Rejected(format!("vetkd_derive_key: {e}")))?;
    Ok(result.encrypted_key)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{evm_address, sign, solve, MAX_TTL_NS};
    use k256::ecdsa::SigningKey;

    const CANISTER: Principal = Principal::anonymous();

    pub(crate) fn registration_by(owner: &SigningKey, notify: u8, expiry_ns: u64) -> Registration {
        let mut r = Registration {
            address: evm_address(owner.verifying_key()).to_vec(),
            public_key: vec![3; 32],
            notify_key: vec![notify; 32],
            escrow: vec![9; 160],
            expiry_ns,
            signature: vec![],
        };
        r.signature = sign(owner, &register_message(&CANISTER, &r));
        r
    }

    /// Registers `r` at time 0, solving its proof of work.
    pub(crate) fn register_now(r: &Registration) -> Result<(), Error> {
        let nonce = solve(&register_digest(r), REGISTER_POW_BITS);
        register_at(r.clone(), nonce, CANISTER, 0)
    }

    #[test]
    fn registration_takes_the_owner_and_only_a_later_replacement() {
        let bob = SigningKey::from_bytes(&[5; 32].into()).unwrap();
        let mallory = SigningKey::from_bytes(&[6; 32].into()).unwrap();
        let addr = evm_address(bob.verifying_key());

        let forged = Registration {
            signature: sign(
                &mallory,
                &register_message(&CANISTER, &registration_by(&bob, 1, 1)),
            ),
            ..registration_by(&bob, 1, 1)
        };
        assert_eq!(register_now(&forged), rejected("bad signature"));
        let late = registration_by(&bob, 1, MAX_TTL_NS + 1);
        assert_eq!(
            register_now(&late),
            rejected("signature expired or TTL too long")
        );
        let first = registration_by(&bob, 1, 2);
        register_now(&first).unwrap();
        assert_eq!(current(&addr), Some(first.clone()));
        register_now(&first).unwrap(); // an identical retry, even past its expiry
        for expiry_ns in [1, 2] {
            assert_eq!(
                register_now(&registration_by(&bob, 2, expiry_ns)),
                rejected("a registration must expire later than the current one")
            );
        }
        let second = registration_by(&bob, 2, 3);
        register_now(&second).unwrap();
        assert_eq!(current(&addr), Some(second));
        // the replaced one stays, for audits
        assert_eq!(registration(&addr, &[1; 32]), Some(first.clone()));
        // and cannot come back
        assert_eq!(
            register_now(&first),
            rejected("a registration must expire later than the current one")
        );
    }
}
