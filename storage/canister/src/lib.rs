//! zerc20_storage: private note delivery for zERC20, in lanes of sealed slots (one sequence per chain):
//! channels, receive codes, points of sale, and each owner's own.
//!
//! Nothing here sees a secret. The client (the TypeScript SDK in `sdk/`) derives every id and
//! ciphertext. This canister is:
//! - a write-once ciphertext store with an append-only announcement list per inbox and a log of
//!   lane slot ids in write order (`store`);
//! - a directory (`registry`): each address registers, with one EIP-191 signature, its zERC20 public
//!   key, the key senders encrypt channel announcements to, and its view key escrowed to the auditor.
//!   A later registration replaces it;
//! - a gateway (`audit`) through which the auditor, an Orbit station whose members approve each
//!   request, has vetKD derive the key that opens an escrow, each request logged publicly first. vetKD
//!   serves nothing else: owners derive their view keys from their seed.
//!
//! Consequences:
//! - Senders are not authenticated: anyone can open a channel claiming to be anyone.
//! - Slot ids are pseudorandom and only key holders can compute them, so the canister cannot check
//!   index contiguity. Honest senders write sequentially and readers scan to the first empty slot.
//! - Whoever controls this canister's code, or a threshold of the vetKD subnet, can open every
//!   escrow, and so read every view key. It cannot forge a registration: senders check the owner's
//!   signature themselves.
//! - The canister cannot check that an escrow holds the right seed; audits rely on honest wallets.
//! - Reads are uncertified queries, so a single replica could omit records.

mod audit;
mod auth;
mod registry;
mod store;

use candid::{CandidType, Deserialize, Principal};
use ic_stable_structures::memory_manager::{MemoryId, MemoryManager, VirtualMemory};
use ic_stable_structures::{DefaultMemoryImpl, StableBTreeMap, StableCell};
use sha2::{Digest, Sha256};
use std::cell::RefCell;

pub use auth::{eip191_hash, eip191_signer, evm_address, EvmAddress};
pub use registry::{register_digest, register_message, vetkd_input};
pub use store::{actions_digest, required_pow_bits, BLOB_LEN, MAX_READ};

// Proof of work, sized for a five-year-old budget Android phone, whose browser does about 100k of these
// hashes a second: a plain write takes ~0.2 s on average, opening a channel ~1.3 s and registering
// ~2.6 s (three times as long one time in twenty). Spam costs that little too; the hourly entry and
// channel caps bound it.
const POW_BITS: u32 = 14;
/// Address inboxes are public, so opening a channel costs more work than a plain write.
const OPEN_POW_BITS: u32 = 17;
/// Registrations add state and happen once per address and root seed.
pub const REGISTER_POW_BITS: u32 = 18;
/// Longest a signed request stays valid, which bounds how long a leaked signature is usable.
pub const MAX_TTL_NS: u64 = 10 * 60 * 1_000_000_000;
const HOUR_NS: u64 = 3_600 * 1_000_000_000;

pub type Id = [u8; 32];

#[derive(CandidType, Deserialize)]
pub struct InitArgs {
    /// The auditor: the Orbit station whose members approve each request for an address's view key.
    pub auditor: Principal,
    /// vetKD key: "key_1" on mainnet, "test_key_1" for tests. Fixed at install.
    pub vetkd_key_name: String,
}

/// The auditor's request for the vetKey that opens the escrow of `target`'s registration with `notify_key`.
#[derive(CandidType, Deserialize, Clone)]
pub struct AuditRequest {
    pub target: Vec<u8>,
    /// Names the registration: the current one or any earlier one.
    pub notify_key: Vec<u8>,
    pub transport_public_key: Vec<u8>,
}

/// What `address` registers: its first registration, or one that replaces the current one and expires
/// later. The owner signs all of it at once (EIP-191 over `register_message(..)`).
#[derive(CandidType, Deserialize, Clone, Debug, PartialEq)]
pub struct Registration {
    pub address: Vec<u8>,
    /// The zERC20 public key (32 bytes) that payments to the address are owned by, on every chain and
    /// token.
    pub public_key: Vec<u8>,
    /// X25519 key (32 bytes) senders encrypt channel announcements to. It names the registration:
    /// another root seed has another one.
    pub notify_key: Vec<u8>,
    /// The view key, IBE-encrypted to identity `vetkd_input(address, notify_key)` under
    /// `escrow_public_key`. Only the auditor can have that vetKey derived.
    pub escrow: Vec<u8>,
    pub expiry_ns: u64,
    pub signature: Vec<u8>,
}

/// One audit, logged before the key is derived. It names the auditor that made it, so that records
/// stay attributed when the auditor is replaced.
#[derive(CandidType, Deserialize, Clone, Debug, PartialEq)]
pub struct AuditRecord {
    pub auditor: Principal,
    pub target: Vec<u8>,
    pub notify_key: Vec<u8>,
    pub transport_public_key: Vec<u8>,
    pub at_ns: u64,
}

/// The slot kinds. The numbers key stable memory: never reuse one.
/// Every record of a lane (notes, deposits, burn blocks, receipts) is a lane slot, so that the kind does
/// not tell what was written.
#[derive(CandidType, Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Outgoing = 0,
    Lane = 1,
}

/// A stored slot and the time it was first written (a retry keeps the first time).
#[derive(CandidType, Deserialize, Clone, Debug, PartialEq)]
pub struct Slot {
    pub data: Vec<u8>,
    pub at_ns: u64,
}

#[derive(CandidType, Deserialize, Clone, Debug)]
pub enum Action {
    /// First contact: append `enc_announcement` to the inbox's announcements and write the sender's
    /// own encrypted outgoing entry. Happens at most once per `outgoing_id`.
    OpenChannel {
        inbox: Vec<u8>,
        enc_announcement: Vec<u8>,
        outgoing_id: Vec<u8>,
        enc_outgoing: Vec<u8>,
    },
    /// Write-once slot. An `Outgoing` one records a payment to a receive code, which opens no channel.
    Put {
        kind: Kind,
        id: Vec<u8>,
        data: Vec<u8>,
    },
}

#[derive(CandidType, Deserialize, Debug, PartialEq)]
pub enum Error {
    /// The slot already holds different data; the sender should move to the next index.
    Occupied(Vec<u8>),
    Rejected(String),
}

fn rejected<T>(msg: &str) -> Result<T, Error> {
    Err(Error::Rejected(msg.into()))
}

fn to_array<const N: usize>(bytes: &[u8], msg: &str) -> Result<[u8; N], Error> {
    bytes.try_into().or_else(|_| rejected(msg))
}

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn len_prefixed(h: &mut Sha256, field: &[u8]) {
    h.update((field.len() as u32).to_be_bytes());
    h.update(field);
}

/// SHA-256 of `tag` and `parts`, each length-prefixed, so that fields can never run into each other.
fn tagged_hash(tag: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for part in [tag].iter().chain(parts) {
        len_prefixed(&mut h, part);
    }
    h.finalize().into()
}

/// Stateless: each endpoint makes replays harmless on its own (idempotent writes, registrations that
/// must expire later than the current one, audits only from the auditor).
/// ponytail: fixed difficulty per endpoint; raise it with the recent request rate if spammers
/// out-hash it.
pub fn pow_ok(digest: &[u8; 32], nonce: u64, bits: u32) -> bool {
    let h = Sha256::new()
        .chain_update(b"zerc20/storage/pow/v1")
        .chain_update(digest)
        .chain_update(nonce.to_be_bytes())
        .finalize();
    let zeros = h
        .iter()
        .position(|b| *b != 0)
        .map_or(256, |i| i as u32 * 8 + h[i].leading_zeros());
    zeros >= bits
}

fn check_pow(digest: &[u8; 32], nonce: u64, bits: u32) -> Result<(), Error> {
    if pow_ok(digest, nonce, bits) {
        Ok(())
    } else {
        rejected("insufficient proof of work")
    }
}

/// A signed request is valid until `expiry_ns`, which may be at most `MAX_TTL_NS` ahead.
fn check_expiry(expiry_ns: u64, now_ns: u64) -> Result<(), Error> {
    if expiry_ns < now_ns || expiry_ns - now_ns > MAX_TTL_NS {
        return rejected("signature expired or TTL too long");
    }
    Ok(())
}

/// The counters of the current hour of a fixed-window rate limit, reset when the hour changes.
/// ponytail: windows live on the heap, so an upgrade starts a fresh hour; move them to stable
/// memory if that matters.
fn this_hour<T: Default>(window: &mut (u64, T), hour: u64) -> &mut T {
    if window.0 != hour {
        *window = (hour, T::default());
    }
    &mut window.1
}

type Memory = VirtualMemory<DefaultMemoryImpl>;

// Stable memory layout, kept in one place: one MemoryId per structure. Never renumber or reuse an id.
thread_local! {
    static MM: RefCell<MemoryManager<DefaultMemoryImpl>> =
        RefCell::new(MemoryManager::init(DefaultMemoryImpl::default()));
    static ANNOUNCEMENTS: RefCell<StableBTreeMap<(Id, u32), Vec<u8>, Memory>> =
        RefCell::new(StableBTreeMap::init(mem(0)));
    static ANNOUNCEMENT_COUNT: RefCell<StableBTreeMap<Id, u32, Memory>> =
        RefCell::new(StableBTreeMap::init(mem(1)));
    static SLOTS: RefCell<StableBTreeMap<(u8, Id), Slot, Memory>> =
        RefCell::new(StableBTreeMap::init(mem(2)));
    /// The auditor. `init` always sets it, and never to the anonymous principal.
    static AUDITOR: RefCell<StableCell<Principal, Memory>> =
        RefCell::new(StableCell::init(mem(3), Principal::anonymous()));
    static KEY_NAME: RefCell<StableCell<String, Memory>> =
        RefCell::new(StableCell::init(mem(4), String::new()));
    /// Each address's current registration, by its notify key.
    static CURRENT: RefCell<StableBTreeMap<EvmAddress, [u8; 32], Memory>> =
        RefCell::new(StableBTreeMap::init(mem(5)));
    /// Public audit log, append only.
    static AUDITS: RefCell<StableBTreeMap<u64, AuditRecord, Memory>> =
        RefCell::new(StableBTreeMap::init(mem(6)));
    /// Every registration, current or replaced, by address and notify key: audits may name any.
    static REGISTRATIONS: RefCell<StableBTreeMap<(EvmAddress, [u8; 32]), Registration, Memory>> =
        RefCell::new(StableBTreeMap::init(mem(7)));
    /// Every lane slot's id, in the order they were first written: readers find their own news
    /// here instead of probing each of their sequences.
    static LOG: RefCell<StableBTreeMap<u64, Id, Memory>> =
        RefCell::new(StableBTreeMap::init(mem(8)));
}

fn mem(id: u8) -> Memory {
    MM.with(|m| m.borrow().get(MemoryId::new(id)))
}

#[ic_cdk::init]
fn init(args: InitArgs) {
    registry::set_key_name(args.vetkd_key_name);
    audit::set_auditor(args.auditor);
}

/// Pass `opt record { auditor; vetkd_key_name }` to replace the auditor. The key name cannot change:
/// a new key would change the escrow public key, and no escrow made under the old one would open.
#[ic_cdk::post_upgrade]
fn post_upgrade(args: Option<InitArgs>) {
    if let Some(args) = args {
        registry::keep_key_name(&args.vetkd_key_name);
        audit::set_auditor(args.auditor);
    }
}

/// The vetKD public key owners IBE-encrypt their escrows with. An update, not a query: a single
/// replica answering with its own key could open every escrow encrypted to it.
#[ic_cdk::update]
async fn escrow_public_key() -> Result<Vec<u8>, Error> {
    registry::escrow_public_key().await
}

#[ic_cdk::update]
fn register(registration: Registration, pow_nonce: u64) -> Result<(), Error> {
    registry::register(registration, pow_nonce)
}

/// The address's registration with `notify_key` (default: its current one). Senders call it as an
/// update, so that no single replica can answer with a replaced registration, and check its signature
/// themselves.
#[ic_cdk::query]
fn registration(address: Vec<u8>, notify_key: Option<Vec<u8>>) -> Option<Registration> {
    let address = EvmAddress::try_from(address.as_slice()).ok()?;
    match notify_key {
        Some(key) => registry::registration(&address, &key.try_into().ok()?),
        None => registry::current(&address),
    }
}

/// The vetKey that opens the escrow of one of the target's registrations, for the auditor alone. Every
/// request it makes is logged.
#[ic_cdk::update]
async fn audit_escrow_key(args: AuditRequest) -> Result<Vec<u8>, Error> {
    audit::audit(args).await
}

/// The Orbit station's validation method for `audit_escrow_key`: what its approvers see of a request, or
/// why the request would be rejected.
#[ic_cdk::query]
fn validate_audit_escrow_key(args: AuditRequest) -> Result<String, String> {
    audit::validate(&args)
}

/// The public audit log. Call it as an update to check that no replica left records out.
#[ic_cdk::query]
fn get_audits(start: u64, limit: u32) -> Vec<AuditRecord> {
    audit::audits(start, limit)
}

#[ic_cdk::update]
fn submit(actions: Vec<Action>, pow_nonce: u64) -> Result<(), Error> {
    store::submit_at(actions, pow_nonce, ic_cdk::api::time())
}

/// Lane slot ids from position `start`, in the order they were first written (at most 8192).
/// Readers compute the next id of each of their sequences and match them here, so a refresh costs
/// the same however many channels a reader has, and asks for no id that is not its own news.
#[ic_cdk::query]
fn get_log(start: u64, limit: u32) -> Vec<Vec<u8>> {
    store::log(start, limit)
}

/// How many lane slots have been written: where a reader that has just read everything starts.
#[ic_cdk::query]
fn log_length() -> u64 {
    LOG.with(|l| l.borrow().len())
}

#[ic_cdk::query]
fn get_announcements(inbox: Vec<u8>, start: u32, limit: u32) -> Vec<Vec<u8>> {
    store::announcements(&inbox, start, limit)
}

#[ic_cdk::query]
fn get_slots(kind: Kind, ids: Vec<Vec<u8>>) -> Vec<Option<Slot>> {
    if ids.len() > MAX_READ {
        ic_cdk::trap("at most 256 ids per call");
    }
    store::slots(kind, &ids)
}

/// Room for Candid's header, type table and length prefixes around an argument's fields: several times what a client
/// writes.
const CANDID_OVERHEAD: usize = 1024;

/// Whether an ingress message to `method` with an argument of `arg_len` bytes could be valid. Ingress takes the
/// updates and the queries a client calls as an update when a stale answer matters; `get_log` and `log_length` answer
/// as queries only, since a replica that leaves entries out only delays news, and `validate_audit_escrow_key` is called
/// by the auditor's station, a canister.
fn accepts(method: &str, arg_len: usize) -> bool {
    let fields = match method {
        // the largest action, OpenChannel, in a full batch
        "submit" => store::MAX_ACTIONS * (32 + BLOB_LEN + 32 + BLOB_LEN) + 8,
        "register" => 20 + 32 + 32 + registry::MAX_ESCROW + 8 + 65 + 8,
        "audit_escrow_key" => 20 + 32 + 48,
        "get_slots" => MAX_READ * 32,
        "registration" => 20 + 32,
        "get_announcements" => 32 + 4 + 4,
        "get_audits" => 8 + 4,
        "escrow_public_key" => 0,
        _ => return false,
    };
    arg_len <= fields + CANDID_OVERHEAD
}

/// Refuses ingress the canister has no use for, so that it never pays for it: to a method ingress does not take, or
/// with an argument larger than any valid one, up to the 2 MiB a message may carry. It runs on one replica, outside
/// consensus, and never for calls from canisters, so it guards nothing: each method still checks its own arguments.
#[ic_cdk::inspect_message]
fn inspect_message() {
    if accepts(
        &ic_cdk::api::msg_method_name(),
        ic_cdk::api::msg_arg_data().len(),
    ) {
        ic_cdk::api::accept_message();
    }
}

ic_cdk::export_candid!();

#[cfg(test)]
fn solve(digest: &[u8; 32], bits: u32) -> u64 {
    (0..).find(|n| pow_ok(digest, *n, bits)).unwrap()
}

/// EIP-191 signature in the wallet format `r ‖ s ‖ v` (v = 27/28).
#[cfg(test)]
fn sign(key: &k256::ecdsa::SigningKey, msg: &str) -> Vec<u8> {
    let (sig, rec) = key
        .sign_prehash_recoverable(&eip191_hash(msg.as_bytes()))
        .unwrap();
    [&sig.to_bytes()[..], &[27 + rec.to_byte()]].concat()
}

#[cfg(test)]
mod ingress {
    use super::*;
    use candid::{encode_args, encode_one};

    #[test]
    fn ingress_takes_the_largest_valid_arguments_and_nothing_larger() {
        let open = Action::OpenChannel {
            inbox: vec![0; 32],
            enc_announcement: vec![0; BLOB_LEN],
            outgoing_id: vec![0; 32],
            enc_outgoing: vec![0; BLOB_LEN],
        };
        let registration = Registration {
            address: vec![0; 20],
            public_key: vec![0; 32],
            notify_key: vec![0; 32],
            escrow: vec![0; registry::MAX_ESCROW],
            expiry_ns: u64::MAX,
            signature: vec![0; 65],
        };
        let audit = AuditRequest {
            target: vec![0; 20],
            notify_key: vec![0; 32],
            transport_public_key: vec![0; 48],
        };
        let largest = [
            (
                "submit",
                encode_args((vec![open; store::MAX_ACTIONS], u64::MAX)),
            ),
            ("register", encode_args((registration, u64::MAX))),
            ("audit_escrow_key", encode_one(audit)),
            (
                "get_slots",
                encode_args((Kind::Outgoing, vec![vec![0u8; 32]; MAX_READ])),
            ),
            (
                "registration",
                encode_args((vec![0u8; 20], Some(vec![0u8; 32]))),
            ),
            (
                "get_announcements",
                encode_args((vec![0u8; 32], u32::MAX, u32::MAX)),
            ),
            ("get_audits", encode_args((u64::MAX, u32::MAX))),
            ("escrow_public_key", encode_args(())),
        ];
        for (method, arg) in largest {
            let len = arg.unwrap().len();
            assert!(accepts(method, len), "{method}: {len} B");
            assert!(!accepts(method, 2 << 20), "{method} takes 2 MiB");
        }
        for method in [
            "get_log",
            "log_length",
            "validate_audit_escrow_key",
            "init",
            "",
        ] {
            assert!(!accepts(method, 0), "{method}");
        }
    }
}

/// The bytes clients must reproduce. `sdk/test/wire.test.ts` pins the same values.
#[cfg(test)]
mod wire_fixtures {
    use super::*;
    use candid::Principal;

    fn sha(bytes: impl AsRef<[u8]>) -> String {
        hex(&Sha256::digest(bytes))
    }

    fn fixture(expiry_ns: u64) -> Registration {
        Registration {
            address: vec![0x11; 20],
            public_key: vec![0x33; 32],
            notify_key: vec![0x44; 32],
            escrow: vec![0x55; 5],
            expiry_ns,
            signature: vec![],
        }
    }

    #[test]
    fn wire_fixtures() {
        let canister = Principal::from_text("rrkah-fqaaa-aaaaa-aaaaq-cai").unwrap();
        let (address, notify_key) = ([0x11; 20], [0x44; 32]);
        let expiry_ns = 1_760_000_000_123_456_792;
        let registration = fixture(expiry_ns);
        let actions = [
            Action::OpenChannel {
                inbox: vec![1; 32],
                enc_announcement: vec![2; 3],
                outgoing_id: vec![3; 32],
                enc_outgoing: vec![4; 5],
            },
            Action::Put {
                kind: Kind::Lane,
                id: vec![5; 32],
                data: vec![6; 7],
            },
        ];
        let pow_digest = register_digest(&registration);
        let got = [
            hex(&vetkd_input(&address, &notify_key)),
            sha(register_message(&canister, &registration)),
            hex(&pow_digest),
            hex(&actions_digest(&actions)),
        ];
        assert_eq!(
            got,
            [
                "11111111111111111111111111111111111111114444444444444444444444444444444444444444444444444444444444444444",
                "bfee87e253dcdf86a0c0de307c8c6963bf0b444f3e013f60f338ad774a843ebb",
                "1a20c636defbfa95a28b75ffd3fdbbd0f751382619c202ddea752e2f77be6050",
                "b1042d9cf44b92781350c9175b5abfd916b1744a051ee78905a272d8b0d92f1b",
            ]
        );
        // This nonce's PoW hash has exactly one leading zero bit.
        let pow_nonce = 0;
        assert!(pow_ok(&pow_digest, pow_nonce, 1) && !pow_ok(&pow_digest, pow_nonce, 2));
    }
}
