//! The ASP's decisions, one per commitment position in index order, and the tree over them, keyed and grouped like the
//! commitment tree (see `zerc20_zkp::tree`). Both files only grow: a decision is final, so every root published
//! approves a superset of the ones before it.
use alloy::primitives::U256;
use anyhow::Result;
use zerc20_common::AppendFile;
use zerc20_common::fields::u256;
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::commitments::asp_leaf;
use zerc20_zkp::tree::{self as t, CHUNK, CHUNK_BITS, PAGE_BITS};

/// Bytes per entry of the `.roots` file and of `/roots/{p}`.
pub const RECORD: usize = 104;

/// A root as recorded before it is published: the size it covers and the roots of the partial chunk and page at that
/// size (zero where the size ends on a boundary), which is what a wallet needs besides its own chunk to build a path.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Record {
    pub size: u64,
    pub root: U256,
    pub partial_chunk: U256,
    pub partial_page: U256,
}

impl Record {
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = self.size.to_be_bytes().to_vec();
        for w in [self.root, self.partial_chunk, self.partial_page] {
            b.extend(w.to_be_bytes::<32>());
        }
        b
    }
    fn parse(b: &[u8; RECORD]) -> Self {
        let w = |i: usize| U256::from_be_slice(&b[8 + 32 * i..8 + 32 * (i + 1)]);
        Self {
            size: u64::from_be_bytes(std::array::from_fn(|i| b[i])),
            root: w(0),
            partial_chunk: w(1),
            partial_page: w(2),
        }
    }
}

pub struct Tree {
    bits: Vec<bool>,
    /// roots of the full chunks and of the full pages
    chunk_roots: Vec<Fr>,
    page_roots: Vec<Fr>,
    records: Vec<Record>,
    /// one ASCII byte per position, `1` approved and `0` not
    decisions: AppendFile,
    roots: AppendFile,
}

impl Tree {
    /// ponytail: rebuilds every full chunk's root (about 8k hashes each); persist them if startup gets slow.
    pub fn open(prefix: &str) -> Result<Self> {
        let (decisions, d) = AppendFile::open(&format!("{prefix}.decisions"), |d| {
            d.iter()
                .position(|b| !matches!(b, b'0' | b'1'))
                .unwrap_or(d.len())
        })?;
        let (roots, r) =
            AppendFile::open(&format!("{prefix}.roots"), |d| d.len() / RECORD * RECORD)?;
        let mut tree = Self {
            bits: Vec::new(),
            chunk_roots: Vec::new(),
            page_roots: Vec::new(),
            records: r.as_chunks().0.iter().map(Record::parse).collect(),
            decisions,
            roots,
        };
        tree.extend(d.iter().map(|&b| b == b'1'));
        if let Some(r) = tree.records.iter().find(|r| r.size > tree.decided()) {
            anyhow::bail!(
                "{prefix}.roots holds a root over {} positions, but only {} are decided: decisions were lost, and \
                 screening them again could withdraw approvals that root made. Replace the publisher \
                 (Verifier.setAspPublisher) and start from an empty DATA_DIR.",
                r.size,
                tree.decided()
            );
        }
        Ok(tree)
    }

    pub fn decided(&self) -> u64 {
        self.bits.len() as u64
    }
    pub fn bits(&self) -> &[bool] {
        &self.bits
    }
    pub fn chunk_roots(&self) -> &[Fr] {
        &self.chunk_roots
    }
    pub fn page_roots(&self) -> &[Fr] {
        &self.page_roots
    }
    pub fn records(&self) -> &[Record] {
        &self.records
    }

    /// Decides the next `bits.len()` positions, durably.
    pub fn append(&mut self, bits: &[bool]) -> Result<()> {
        let bytes: Vec<u8> = bits.iter().map(|&b| if b { b'1' } else { b'0' }).collect();
        self.decisions.append(&bytes)?;
        self.extend(bits.iter().copied());
        Ok(())
    }

    fn extend(&mut self, bits: impl IntoIterator<Item = bool>) {
        for b in bits {
            self.bits.push(b);
            let n = self.decided();
            if n.is_multiple_of(CHUNK) {
                let lo = n - CHUNK;
                let leaves = leaves(lo, &self.bits[lo as usize..]);
                self.chunk_roots.push(t::chunk_root(leaves));
            }
            if n.is_multiple_of(1 << PAGE_BITS) {
                let c = self.chunk_roots.len() - CHUNK as usize;
                self.page_roots
                    .push(t::page_root(self.chunk_roots[c..].to_vec()));
            }
        }
    }

    /// The tree over every position decided so far.
    pub fn current(&self) -> Record {
        let n = self.decided();
        let lo = n >> CHUNK_BITS << CHUNK_BITS;
        let page_lo = (n >> PAGE_BITS << CHUNK_BITS) as usize;
        let s = t::sized(
            n,
            &self.page_roots,
            &self.chunk_roots[page_lo..],
            leaves(lo, &self.bits[lo as usize..]),
        );
        Record {
            size: n,
            root: u256(s.root),
            partial_chunk: s.partial_chunk.map(u256).unwrap_or_default(),
            partial_page: s.partial_page.map(u256).unwrap_or_default(),
        }
    }

    /// Records `r` durably unless it is the latest record already. Done before publishing, so a wallet that reads a
    /// root on chain always finds its size here.
    pub fn record(&mut self, r: Record) -> Result<()> {
        if self.records.last().is_some_and(|l| l.root == r.root) {
            return Ok(());
        }
        self.roots.append(&r.bytes())?;
        self.records.push(r);
        Ok(())
    }

    pub fn knows(&self, root: U256) -> bool {
        self.records.iter().any(|r| r.root == root)
    }
}

/// Leaves of positions `lo..lo + bits.len()`: the global position's `asp_leaf` where approved, else 0.
fn leaves(lo: u64, bits: &[bool]) -> Vec<Fr> {
    bits.iter()
        .zip(lo..)
        .map(|(&b, i)| {
            if b {
                asp_leaf(Fr::from(i))
            } else {
                Fr::from(0u64)
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::OpenOptions;
    use std::io::Write;
    use zerc20_zkp::tree::merkle_path;

    fn temp(name: &str) -> String {
        let p = std::env::temp_dir().join(format!("asp-{name}-{}", std::process::id()));
        let p = p.to_str().unwrap().to_string();
        for ext in ["decisions", "roots"] {
            let _ = std::fs::remove_file(format!("{p}.{ext}"));
        }
        p
    }

    #[test]
    fn root_matches_the_reference_tree() {
        assert_eq!(
            u256(asp_leaf(Fr::from(1u64))).to_string(),
            "11421855863859206043844312539642350555737086245092967861255959580848089452617",
            "deposit_asp_leaf in zkp/test-vectors/circuit-vectors.json"
        );
        let bits: Vec<bool> = (0..CHUNK + 3).map(|i| i % 3 != 1).collect();
        let p = temp("root");
        let mut tree = Tree::open(&p).unwrap();
        let mut n = 0;
        for upto in [0, 1, 2, CHUNK - 1, CHUNK, CHUNK + 3] {
            tree.append(&bits[n as usize..upto as usize]).unwrap();
            n = upto;
            let r = tree.current();
            let reference = leaves(0, &bits[..n as usize]);
            assert_eq!(r.size, n);
            assert_eq!(r.root, u256(merkle_path(&reference, 0).0), "n = {n}");
            assert_eq!(r.partial_chunk.is_zero(), n % CHUNK == 0, "n = {n}");
        }
        // reopening rebuilds the same tree, and the full chunk's root at its global positions
        let again = Tree::open(&p).unwrap();
        assert_eq!(again.current(), tree.current());
        assert_eq!(again.chunk_roots().len(), 1);
    }

    #[test]
    fn torn_files_are_cut_and_appending_resumes() {
        let p = temp("torn");
        let mut tree = Tree::open(&p).unwrap();
        tree.append(&[true, false, true]).unwrap();
        let r = tree.current();
        tree.record(r).unwrap();
        tree.record(r).unwrap(); // the same root twice is recorded once
        drop(tree);
        let raw = |ext: &str, b: &[u8]| {
            OpenOptions::new()
                .append(true)
                .open(format!("{p}.{ext}"))
                .unwrap()
                .write_all(b)
                .unwrap()
        };
        raw("decisions", b"1\0\0x"); // the 1 made it to disk, then garbage
        raw("roots", &[7; 50]);

        let mut tree = Tree::open(&p).unwrap();
        assert_eq!(tree.bits(), [true, false, true, true]);
        assert_eq!(tree.records(), [r]);
        assert!(tree.knows(r.root));
        tree.append(&[false]).unwrap();
        tree.record(tree.current()).unwrap();
        drop(tree);
        let tree = Tree::open(&p).unwrap();
        assert_eq!(tree.bits(), [true, false, true, true, false]);
        assert_eq!(tree.records().len(), 2);
        assert_eq!(Record::parse(&r.bytes().try_into().unwrap()), r);
    }

    #[test]
    fn a_root_beyond_the_decisions_refuses_to_start() {
        let p = temp("lost");
        let mut tree = Tree::open(&p).unwrap();
        tree.append(&[true, true]).unwrap();
        tree.record(tree.current()).unwrap();
        drop(tree);
        std::fs::write(format!("{p}.decisions"), b"1").unwrap();
        assert!(Tree::open(&p).is_err());
    }
}
