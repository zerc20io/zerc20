//! Registrations, keyed by deposit address, in an append-only JSONL file (latest line wins).
use alloy::primitives::{Address, U256};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use zerc20_common::{AppendFile, whole_lines};

/// A registration is watched this long; registering it again, or `rewatch`, restarts it.
pub const WATCH_SECS: u64 = 7 * 24 * 3600;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Reg {
    pub token: Address,
    pub burn_address: Address,
    /// One of the two is zero: part of the deposit address, as the factory takes them.
    pub refund_address: Address,
    pub refund_signer: Address,
    pub deposit_address: Address,
    pub underlying: Address,
    /// Part of the deposit address, so flushing it needs them; a later change of `FEES` leaves them be.
    pub fee_recipient: Address,
    pub fee: U256,
    pub referrer: Address,
    pub referral_bps: u16,
    /// Unix seconds of the latest registration.
    pub at: u64,
    /// A flush of it reverted on chain and left its funds there, so it is flushed no more.
    #[serde(default)]
    pub reverted: bool,
}

/// ponytail: the file only grows; compact out expired lines if it ever gets large.
pub struct Store {
    file: AppendFile,
    regs: HashMap<Address, Reg>,
}

impl Store {
    pub fn open(path: &str) -> anyhow::Result<Self> {
        // a line torn by a crash was never acknowledged, so it is safe to drop
        let (file, data) = AppendFile::open(path, whole_lines)?;
        let mut regs = HashMap::new();
        for line in data.split(|&b| b == b'\n').filter(|l| !l.is_empty()) {
            match serde_json::from_slice::<Reg>(line) {
                Ok(r) => drop(regs.insert(r.deposit_address, r)),
                Err(e) => tracing::warn!("skipping a bad line in {path}: {e}"),
            }
        }
        Ok(Self { file, regs })
    }

    /// Durable before it returns. An address whose flush reverted stays unflushed, however it is registered again.
    pub fn put(&mut self, mut r: Reg) -> anyhow::Result<()> {
        r.reverted |= self
            .regs
            .get(&r.deposit_address)
            .is_some_and(|o| o.reverted);
        let mut line = serde_json::to_vec(&r)?;
        line.push(b'\n');
        self.file.append(&line)?;
        self.regs.insert(r.deposit_address, r);
        Ok(())
    }

    /// Watches the registration of `deposit` again from `at`, with the fee and recipient it was registered with, which
    /// the address fixes; None if it was never registered here.
    pub fn rewatch(&mut self, deposit: Address, at: u64) -> anyhow::Result<Option<Reg>> {
        let Some(r) = self.regs.get(&deposit) else {
            return Ok(None);
        };
        let r = Reg { at, ..r.clone() };
        self.put(r.clone())?;
        Ok(Some(r))
    }

    /// Stops flushing `deposit`, for good: a flush of it reverted on chain and left its funds there.
    pub fn reverted(&mut self, deposit: Address) -> anyhow::Result<()> {
        match self.regs.get(&deposit) {
            Some(r) => self.put(Reg {
                reverted: true,
                ..r.clone()
            }),
            None => Ok(()),
        }
    }

    /// Registrations still inside their watch window at `now`, and still flushed.
    pub fn watched(&self, now: u64) -> Vec<Reg> {
        let since = now.saturating_sub(WATCH_SECS);
        self.regs
            .values()
            .filter(|r| r.at > since && !r.reverted)
            .cloned()
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use zerc20_common::contracts::NATIVE;

    fn reg(deposit: u8, at: u64) -> Reg {
        Reg {
            token: Address::repeat_byte(1),
            burn_address: Address::repeat_byte(2),
            refund_address: Address::repeat_byte(3),
            refund_signer: Address::ZERO,
            deposit_address: Address::repeat_byte(deposit),
            underlying: NATIVE,
            fee_recipient: Address::repeat_byte(4),
            fee: U256::from(5),
            referrer: Address::repeat_byte(6),
            referral_bps: 30,
            at,
            reverted: false,
        }
    }

    #[test]
    fn round_trip() {
        let path =
            std::env::temp_dir().join(format!("deposit-relayer-{}.jsonl", std::process::id()));
        let path = path.to_str().unwrap();
        let _ = std::fs::remove_file(path);
        let mut s = Store::open(path).unwrap();
        s.put(reg(10, 1)).unwrap();
        s.put(reg(11, 2)).unwrap();
        s.put(reg(10, 3)).unwrap(); // re-registration: latest wins
        drop(s);
        std::fs::OpenOptions::new()
            .append(true)
            .open(path)
            .unwrap()
            .write_all(b"{\"token\":\"0x01")
            .unwrap(); // torn

        let mut s = Store::open(path).unwrap();
        assert_eq!(s.regs.len(), 2);
        assert_eq!(s.regs[&Address::repeat_byte(10)], reg(10, 3));
        assert_eq!(
            s.watched(WATCH_SECS + 2),
            vec![reg(10, 3)],
            "the window drops the older one"
        );
        assert_eq!(
            s.rewatch(Address::repeat_byte(11), WATCH_SECS + 3).unwrap(),
            Some(reg(11, WATCH_SECS + 3)),
            "rewatched with what it was registered with"
        );
        assert_eq!(
            s.watched(WATCH_SECS + 3),
            vec![reg(11, WATCH_SECS + 3)],
            "its window restarts"
        );
        assert_eq!(s.rewatch(Address::repeat_byte(13), 0).unwrap(), None);
        s.put(reg(12, 4)).unwrap();
        drop(s);
        assert_eq!(
            Store::open(path).unwrap().regs[&Address::repeat_byte(12)],
            reg(12, 4),
            "lost after a torn line"
        );
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn an_address_whose_flush_reverted_stays_unflushed_however_it_is_registered_again() {
        let path = std::env::temp_dir().join(format!(
            "deposit-relayer-reverted-{}.jsonl",
            std::process::id()
        ));
        let path = path.to_str().unwrap();
        // a line without the field reads as still flushed
        let mut line = serde_json::to_value(reg(10, 1)).unwrap();
        line.as_object_mut().unwrap().remove("reverted");
        std::fs::write(path, format!("{line}\n")).unwrap();
        let mut s = Store::open(path).unwrap();
        assert_eq!(s.watched(2), vec![reg(10, 1)]);

        s.reverted(Address::repeat_byte(10)).unwrap();
        assert_eq!(s.watched(2), vec![]);
        s.put(reg(10, 3)).unwrap();
        s.rewatch(Address::repeat_byte(10), 4).unwrap();
        s.reverted(Address::repeat_byte(11)).unwrap(); // never registered: nothing to stop
        drop(s);
        let s = Store::open(path).unwrap();
        assert_eq!(s.watched(5), vec![]);
        assert!(s.regs[&Address::repeat_byte(10)].reverted);
        std::fs::remove_file(path).unwrap();
    }
}
