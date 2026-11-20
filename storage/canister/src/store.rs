//! Write-once slots and append-only announcement lists: everything `submit` writes and the queries read.
//! Each slot is stamped with the time it was first written.

use crate::{
    check_pow, len_prefixed, rejected, this_hour, to_array, Action, Error, Id, Kind, Slot,
    ANNOUNCEMENTS, ANNOUNCEMENT_COUNT, CURRENT, HOUR_NS, LOG, OPEN_POW_BITS, POW_BITS,
    REGISTRATIONS, SLOTS,
};
use ic_stable_structures::storable::Bound;
use ic_stable_structures::Storable;
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::BTreeMap;

/// Every blob is exactly this long, so its length tells nothing of what it holds.
pub const BLOB_LEN: usize = 256;
pub(crate) const MAX_ACTIONS: usize = 16;
pub const MAX_READ: usize = 256;
/// Log entries per `get_log` call: 32-byte ids, so a reply stays well under the query size limit.
pub const MAX_LOG_READ: u32 = 8192;
/// Entries `submit` and `register` may hold in all (`total_entries`), sized from stable memory. The memory manager
/// addresses at most 256 GiB (32768 buckets of 8 MiB), and the largest entry, a registration that replaces another, takes
/// ~858 B there (`entries_fit_in_stable_memory`). 250M of those is ~200 GiB, leaving room for the audit log and for
/// structures a later upgrade adds.
pub(crate) const MAX_ENTRIES: u64 = 250_000_000;
/// Entries `submit` and `register` may add in an hour, in all. Callers may be anonymous and principals are free, so no
/// cap per caller holds, and proof of work sized for a phone costs a GPU next to nothing: only a rate slows spam that
/// fills `MAX_ENTRIES` for good. At this one filling it takes a year, time enough to respond. One ordinary computer can
/// use up every hour, but new writes are then refused only until it stops.
pub(crate) const MAX_ENTRIES_PER_HOUR: u64 = MAX_ENTRIES / (365 * 24);
const MAX_NEW_CHANNELS_PER_HOUR: u32 = 32;

thread_local! {
    /// New channels per inbox in the current hour.
    static CHANNEL_RATE: RefCell<(u64, BTreeMap<Id, u32>)> = RefCell::default();
    /// Entries added in the current hour.
    static ENTRY_RATE: RefCell<(u64, u64)> = RefCell::default();
}

/// Proof-of-work digest of a `submit` batch.
pub fn actions_digest(actions: &[Action]) -> [u8; 32] {
    let mut h = Sha256::new();
    for action in actions {
        match action {
            Action::OpenChannel {
                inbox,
                enc_announcement,
                outgoing_id,
                enc_outgoing,
            } => {
                h.update([0]);
                for field in [inbox, enc_announcement, outgoing_id, enc_outgoing] {
                    len_prefixed(&mut h, field);
                }
            }
            Action::Put { kind, id, data } => {
                h.update([1, *kind as u8]);
                len_prefixed(&mut h, id);
                len_prefixed(&mut h, data);
            }
        }
    }
    h.finalize().into()
}

pub fn required_pow_bits(actions: &[Action]) -> u32 {
    if actions
        .iter()
        .any(|a| matches!(a, Action::OpenChannel { .. }))
    {
        OPEN_POW_BITS
    } else {
        POW_BITS
    }
}

fn check_blob(blob: &[u8]) -> Result<(), Error> {
    if blob.len() != BLOB_LEN {
        return rejected("blob must be 256 bytes");
    }
    Ok(())
}

/// The writes a batch makes, validated against storage and against itself.
#[derive(Default)]
struct Batch {
    slots: BTreeMap<(u8, Id), Vec<u8>>,
    announcements: Vec<(Id, Vec<u8>)>,
    new_channels: BTreeMap<Id, u32>,
}

impl Batch {
    /// Write-once check. `Ok(true)`: new slot (queued). `Ok(false)`: identical retry, nothing to do.
    fn claim(&mut self, kind: Kind, id: &[u8], data: &[u8]) -> Result<bool, Error> {
        let id: Id = to_array(id, "id must be 32 bytes")?;
        check_blob(data)?;
        let key = (kind as u8, id);
        let stored = || SLOTS.with(|s| s.borrow().get(&key)).map(|slot| slot.data);
        let existing = self.slots.get(&key).cloned().or_else(stored);
        match existing {
            Some(v) if v == data => Ok(false),
            Some(_) => Err(Error::Occupied(id.to_vec())),
            None => {
                self.slots.insert(key, data.to_vec());
                Ok(true)
            }
        }
    }

    fn add(&mut self, action: Action) -> Result<(), Error> {
        match action {
            Action::OpenChannel {
                inbox,
                enc_announcement,
                outgoing_id,
                enc_outgoing,
            } => {
                let inbox: Id = to_array(&inbox, "inbox must be 32 bytes")?;
                check_blob(&enc_announcement)?;
                if self.claim(Kind::Outgoing, &outgoing_id, &enc_outgoing)? {
                    *self.new_channels.entry(inbox).or_default() += 1;
                    self.announcements.push((inbox, enc_announcement));
                }
            }
            Action::Put { kind, id, data } => {
                self.claim(kind, &id, &data)?;
            }
        }
        Ok(())
    }

    fn entries(&self) -> u64 {
        (self.slots.len() + self.announcements.len()) as u64
    }

    fn apply(self, now_ns: u64) {
        SLOTS.with(|s| {
            let mut s = s.borrow_mut();
            for (key, data) in self.slots {
                s.insert(
                    key,
                    Slot {
                        data,
                        at_ns: now_ns,
                    },
                );
                if key.0 == Kind::Lane as u8 {
                    LOG.with(|l| {
                        let mut l = l.borrow_mut();
                        let next = l.len();
                        l.insert(next, key.1);
                    });
                }
            }
        });
        for (inbox, data) in self.announcements {
            let index = ANNOUNCEMENT_COUNT.with(|c| c.borrow().get(&inbox).unwrap_or(0));
            ANNOUNCEMENTS.with(|c| c.borrow_mut().insert((inbox, index), data));
            ANNOUNCEMENT_COUNT.with(|c| c.borrow_mut().insert(inbox, index + 1));
        }
        CHANNEL_RATE.with(|r| {
            let mut r = r.borrow_mut();
            let used = this_hour(&mut r, now_ns / HOUR_NS);
            for (inbox, n) in self.new_channels {
                *used.entry(inbox).or_default() += n;
            }
        });
    }
}

/// Everything that counts toward `MAX_ENTRIES`.
fn total_entries() -> u64 {
    ANNOUNCEMENTS.with(|m| m.borrow().len())
        + SLOTS.with(|m| m.borrow().len())
        + CURRENT.with(|m| m.borrow().len())
        + REGISTRATIONS.with(|m| m.borrow().len())
}

/// Takes room for `n` new entries at `now_ns`, or refuses them: the canister holds at most `MAX_ENTRIES`, and adds at
/// most `MAX_ENTRIES_PER_HOUR` in an hour. Called right before the entries are added, which then cannot fail.
pub(crate) fn take_room(n: u64, now_ns: u64) -> Result<(), Error> {
    if total_entries() + n > MAX_ENTRIES {
        return rejected("storage full");
    }
    ENTRY_RATE.with(|r| {
        let mut r = r.borrow_mut();
        let used = this_hour(&mut r, now_ns / HOUR_NS);
        if *used + n > MAX_ENTRIES_PER_HOUR {
            return rejected("hourly entry limit");
        }
        *used += n;
        Ok(())
    })
}

/// Validates the whole batch, then applies it: an Err leaves state untouched.
pub(crate) fn submit_at(actions: Vec<Action>, pow_nonce: u64, now_ns: u64) -> Result<(), Error> {
    if actions.is_empty() || actions.len() > MAX_ACTIONS {
        return rejected("1..=16 actions per batch");
    }
    check_pow(
        &actions_digest(&actions),
        pow_nonce,
        required_pow_bits(&actions),
    )?;
    let mut batch = Batch::default();
    for action in actions {
        batch.add(action)?;
    }
    let over_rate = CHANNEL_RATE.with(|r| {
        let mut r = r.borrow_mut();
        let used = this_hour(&mut r, now_ns / HOUR_NS);
        batch
            .new_channels
            .iter()
            .any(|(inbox, n)| used.get(inbox).unwrap_or(&0) + n > MAX_NEW_CHANNELS_PER_HOUR)
    });
    if over_rate {
        return rejected("inbox channel rate limit");
    }
    take_room(batch.entries(), now_ns)?;
    batch.apply(now_ns);
    Ok(())
}

pub(crate) fn announcements(inbox: &[u8], start: u32, limit: u32) -> Vec<Vec<u8>> {
    let Ok(inbox) = Id::try_from(inbox) else {
        return vec![];
    };
    let end = start.saturating_add(limit.min(MAX_READ as u32));
    ANNOUNCEMENTS.with(|c| {
        c.borrow()
            .range((inbox, start)..(inbox, end))
            .map(|e| e.value())
            .collect()
    })
}

pub(crate) fn log(start: u64, limit: u32) -> Vec<Vec<u8>> {
    let end = start.saturating_add(limit.min(MAX_LOG_READ) as u64);
    LOG.with(|l| {
        l.borrow()
            .range(start..end)
            .map(|e| e.value().to_vec())
            .collect()
    })
}

pub(crate) fn slots(kind: Kind, ids: &[Vec<u8>]) -> Vec<Option<Slot>> {
    SLOTS.with(|s| {
        let s = s.borrow();
        let get = |id: &Vec<u8>| s.get(&(kind as u8, Id::try_from(id.as_slice()).ok()?));
        ids.iter().map(get).collect()
    })
}

/// Stored as `at_ns(8) ‖ data`.
impl Storable for Slot {
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned([&self.at_ns.to_be_bytes()[..], &self.data].concat())
    }

    fn into_bytes(self) -> Vec<u8> {
        self.to_bytes().into_owned()
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        let Some((at_ns, data)) = bytes.split_first_chunk() else {
            ic_cdk::trap("a stored slot has no timestamp");
        };
        Slot {
            data: data.to_vec(),
            at_ns: u64::from_be_bytes(*at_ns),
        }
    }

    const BOUND: Bound = Bound::Unbounded;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solve;

    fn submit(actions: Vec<Action>, now_ns: u64) -> Result<(), Error> {
        let nonce = solve(&actions_digest(&actions), required_pow_bits(&actions));
        submit_at(actions, nonce, now_ns)
    }

    fn id(n: u32) -> Vec<u8> {
        [n.to_be_bytes().to_vec(), vec![0; 28]].concat()
    }

    #[test]
    fn submit_is_atomic_idempotent_and_rate_limited() {
        let inbox = [5; 32];
        let blob = |b: u8| vec![b; BLOB_LEN];
        let put = |n: u32, data: u8| Action::Put {
            kind: Kind::Lane,
            id: id(n),
            data: blob(data),
        };
        let open = |n: u32| Action::OpenChannel {
            inbox: inbox.to_vec(),
            enc_announcement: blob(1),
            outgoing_id: id(n),
            enc_outgoing: blob(2),
        };
        let channel_count = || ANNOUNCEMENT_COUNT.with(|c| c.borrow().get(&inbox).unwrap_or(0));
        assert_eq!(
            (
                required_pow_bits(&[put(1, 1)]),
                required_pow_bits(&[put(1, 1), open(1)])
            ),
            (POW_BITS, OPEN_POW_BITS)
        );

        let short = Action::Put {
            kind: Kind::Lane,
            id: id(1),
            data: vec![1; BLOB_LEN - 1],
        };
        assert_eq!(submit(vec![short], 5), rejected("blob must be 256 bytes"));
        submit(vec![put(1, 1)], 5).unwrap();
        submit(vec![put(1, 1), put(1, 1)], 9).unwrap(); // identical retries are no-ops
        assert_eq!(log(0, 10), vec![id(1)]); // a lane slot is logged once, when first written
        assert_eq!(
            submit(vec![put(2, 1), put(1, 9)], 9),
            Err(Error::Occupied(id(1)))
        );
        let first_write = Slot {
            data: blob(1),
            at_ns: 5,
        };
        assert_eq!(
            slots(Kind::Lane, &[id(1), id(2)]),
            vec![Some(first_write), None]
        );
        // an outgoing record for a code payment, which opens no channel; it is not logged
        submit(
            vec![Action::Put {
                kind: Kind::Outgoing,
                id: id(3),
                data: blob(1),
            }],
            0,
        )
        .unwrap();
        assert_eq!(
            slots(Kind::Outgoing, &[id(3)])[0].as_ref().unwrap().data,
            blob(1)
        );

        let actions = vec![put(5, 1)];
        let bad_nonce = (0..)
            .find(|n| !crate::pow_ok(&actions_digest(&actions), *n, POW_BITS))
            .unwrap();
        assert_eq!(
            submit_at(actions, bad_nonce, 0),
            rejected("insufficient proof of work")
        );

        assert_eq!(log(0, 10), vec![id(1)]); // the rejected batch logged nothing

        submit((100..116).map(open).collect(), 0).unwrap();
        submit((116..132).map(open).collect(), 0).unwrap();
        submit(vec![open(100)], 0).unwrap(); // retry of an existing channel is not a new channel
        assert_eq!(
            submit(vec![open(132)], 0),
            rejected("inbox channel rate limit")
        );
        assert_eq!(channel_count(), 32);
        submit(vec![open(132)], HOUR_NS).unwrap();
        assert_eq!(
            CHANNEL_RATE.with(|r| r.borrow().clone()),
            (1, BTreeMap::from([(inbox, 1)]))
        );
        assert_eq!(channel_count(), 33);
        assert_eq!(announcements(&inbox, 30, 10).len(), 3);
    }

    #[test]
    fn writes_and_registrations_share_an_hourly_room_that_retries_and_refused_calls_take_none_of() {
        use crate::registry::tests::{register_now, registration_by};
        let put = |n: u32| Action::Put {
            kind: Kind::Lane,
            id: id(n),
            data: vec![1; BLOB_LEN],
        };
        let used = |n: u64| ENTRY_RATE.with(|r| *r.borrow_mut() = (0, n));
        used(MAX_ENTRIES_PER_HOUR - 1);
        assert_eq!(
            submit(vec![put(1), put(2)], 0),
            rejected("hourly entry limit")
        );
        submit(vec![put(1)], 0).unwrap();
        submit(vec![put(1)], 0).unwrap(); // a retry adds nothing
        assert_eq!(submit(vec![put(2)], 0), rejected("hourly entry limit"));
        submit(vec![put(2)], HOUR_NS).unwrap();

        // a registration takes two
        let owner = k256::ecdsa::SigningKey::from_bytes(&[5; 32].into()).unwrap();
        used(MAX_ENTRIES_PER_HOUR - 1);
        assert_eq!(
            register_now(&registration_by(&owner, 1, 1)),
            rejected("hourly entry limit")
        );
        used(MAX_ENTRIES_PER_HOUR - 2);
        register_now(&registration_by(&owner, 1, 1)).unwrap();
        used(MAX_ENTRIES_PER_HOUR);
        register_now(&registration_by(&owner, 1, 1)).unwrap(); // its retry, in a full hour

        // a call refused for another reason takes no room
        used(MAX_ENTRIES_PER_HOUR - 2);
        let mallory = k256::ecdsa::SigningKey::from_bytes(&[6; 32].into()).unwrap();
        let forged = crate::Registration {
            signature: registration_by(&mallory, 2, 2).signature,
            ..registration_by(&owner, 2, 2)
        };
        assert_eq!(register_now(&forged), rejected("bad signature"));
        let open = |n: u32| Action::OpenChannel {
            inbox: vec![5; 32],
            enc_announcement: vec![1; BLOB_LEN],
            outgoing_id: id(n),
            enc_outgoing: vec![2; BLOB_LEN],
        };
        CHANNEL_RATE.with(|r| *r.borrow_mut() = (0, BTreeMap::from([([5; 32], 32)])));
        assert_eq!(
            submit(vec![open(200)], 0),
            rejected("inbox channel rate limit")
        );
        register_now(&registration_by(&owner, 2, 2)).unwrap();
    }

    /// `MAX_ENTRIES` of the largest entry, as stable memory holds it, fit 200 GiB of the memory manager's 256.
    #[test]
    fn entries_fit_in_stable_memory() {
        use crate::{mem, Registration};
        use ic_stable_structures::Memory;
        const N: u32 = 20_000;
        // pseudorandom keys, like the slot ids and inboxes clients derive
        let key = |tag: u8, i: u32| -> Id {
            Sha256::new()
                .chain_update([tag])
                .chain_update(i.to_be_bytes())
                .finalize()
                .into()
        };
        let used = |ids: &[u8]| -> u64 { ids.iter().map(|id| mem(*id).size() * 65_536).sum() };
        let per_entry = |ids: &[u8], entries: u32, write: &dyn Fn(u32)| {
            let before = used(ids);
            (0..N).for_each(write);
            (used(ids) - before) / (N * entries) as u64
        };
        let slot = |tag: u8, i: u32| {
            SLOTS.with(|s| {
                s.borrow_mut().insert(
                    (tag, key(tag, i)),
                    Slot {
                        data: vec![7; BLOB_LEN],
                        at_ns: 7,
                    },
                )
            })
        };
        let reg = |address: [u8; 20], notify_key: Id| Registration {
            address: address.to_vec(),
            public_key: vec![2; 32],
            notify_key: notify_key.to_vec(),
            escrow: vec![4; 512],
            expiry_ns: u64::MAX,
            signature: vec![5; 65],
        };
        let footprints = [
            // a lane slot and its log entry
            per_entry(&[2, 8], 1, &|i| {
                slot(Kind::Lane as u8, i);
                LOG.with(|l| l.borrow_mut().insert(i as u64, key(Kind::Lane as u8, i)));
            }),
            // a channel to a fresh inbox: its announcement, the inbox's count and the outgoing slot, two entries
            per_entry(&[0, 1, 2], 2, &|i| {
                ANNOUNCEMENTS.with(|c| c.borrow_mut().insert((key(9, i), 0), vec![7; BLOB_LEN]));
                ANNOUNCEMENT_COUNT.with(|c| c.borrow_mut().insert(key(9, i), 1));
                slot(Kind::Outgoing as u8, i);
            }),
            // a first registration and its current entry, two entries
            per_entry(&[5, 7], 2, &|i| {
                let address: [u8; 20] = key(5, i)[..20].try_into().unwrap();
                let notify_key = key(6, i);
                let r = reg(address, notify_key);
                REGISTRATIONS.with(|m| m.borrow_mut().insert((address, notify_key), r));
                CURRENT.with(|c| c.borrow_mut().insert(address, notify_key));
            }),
            // a replacement: one more registration, with the current entry overwritten
            per_entry(&[5, 7], 1, &|i| {
                let notify_key = key(7, i);
                let r = reg([1; 20], notify_key);
                REGISTRATIONS.with(|m| m.borrow_mut().insert(([1; 20], notify_key), r));
                CURRENT.with(|c| c.borrow_mut().insert([1; 20], notify_key));
            }),
        ];
        let largest = *footprints.iter().max().unwrap();
        assert!(
            MAX_ENTRIES * largest <= 200 << 30,
            "{footprints:?} B per entry"
        );
    }
}
