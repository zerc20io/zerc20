//! The commitment tree: an append-only Merkle tree over circomlib `Poseidon(2)`
//! with empty leaves equal to zero. The ASP tree has the same shape.
//!
//! Servers hold it without a node table. Its 32 levels split into two strata of
//! 12 and a top of 8:
//! - a chunk is 2^12 leaves; a full chunk's root is computed once and stored;
//! - a page is 2^12 chunk roots (2^24 leaves); a full page's root is computed
//!   once and stored;
//! - at most 2^8 page roots lie under the tree root.
//!
//! So nothing a reader or a server touches to get a root or a path grows with
//! the tree beyond 4096 entries per stratum.

use ark_bn254::Fr;
use ark_r1cs_std::{boolean::Boolean, fields::fp::FpVar};
use ark_relations::gr1cs::SynthesisError;
use std::sync::LazyLock;

use crate::poseidon::{self, POSEIDON2};

pub const TREE_HEIGHT: usize = 32;

/// Host-side incremental tree producing the sibling paths the step circuit
/// consumes.
pub struct IncrementalTree {
    /// `zeros[level]` is the root of an empty subtree of height `level`.
    zeros: [Fr; TREE_HEIGHT],
    /// The latest left child seen at each level.
    filled: [Fr; TREE_HEIGHT],
    next_index: u64,
    pub root: Fr,
}

impl Default for IncrementalTree {
    fn default() -> Self {
        let mut zeros = [Fr::from(0u64); TREE_HEIGHT];
        for level in 1..TREE_HEIGHT {
            zeros[level] = poseidon::hash(&POSEIDON2, &[zeros[level - 1]; 2]);
        }
        let root = poseidon::hash(&POSEIDON2, &[zeros[TREE_HEIGHT - 1]; 2]);
        Self {
            zeros,
            filled: zeros,
            next_index: 0,
            root,
        }
    }
}

impl IncrementalTree {
    /// The tree at `next_index` leaves, from its frontier: `filled[level]` is
    /// the root of the full subtree left of position `next_index` at `level`,
    /// read only where bit `level` of `next_index` is 1.
    fn from_frontier(next_index: u64, filled: [Fr; TREE_HEIGHT]) -> Self {
        let zeros = Self::default().zeros;
        // the path of position `next_index`, which is empty
        let root = (0..TREE_HEIGHT).fold(Fr::from(0u64), |current, level| {
            let pair = if next_index >> level & 1 == 0 {
                [current, zeros[level]]
            } else {
                [filled[level], current]
            };
            poseidon::hash(&POSEIDON2, &pair)
        });
        Self {
            zeros,
            filled,
            next_index,
            root,
        }
    }

    /// Appends `leaf` and returns the sibling path of its position, which is
    /// unchanged by the append.
    pub fn append(&mut self, leaf: Fr) -> [Fr; TREE_HEIGHT] {
        let mut index = self.next_index;
        let mut current = leaf;
        let mut siblings = self.zeros;
        for (level, sibling) in siblings.iter_mut().enumerate() {
            current = if index & 1 == 0 {
                self.filled[level] = current;
                poseidon::hash(&POSEIDON2, &[current, *sibling])
            } else {
                *sibling = self.filled[level];
                poseidon::hash(&POSEIDON2, &[*sibling, current])
            };
            index >>= 1;
        }
        self.root = current;
        self.next_index += 1;
        siblings
    }
}

/// Root of the tree holding `leaves` from position 0, and the sibling path of
/// `leaves[index]` against it. Unlike [`IncrementalTree::append`], the path
/// stays valid after later leaves are added.
pub fn merkle_path(leaves: &[Fr], mut index: usize) -> (Fr, [Fr; TREE_HEIGHT]) {
    let mut layer = leaves.to_vec();
    let mut zero = Fr::from(0u64);
    let mut siblings = [zero; TREE_HEIGHT];
    for sibling in &mut siblings {
        *sibling = layer.get(index ^ 1).copied().unwrap_or(zero);
        layer = layer
            .chunks(2)
            .map(|pair| poseidon::hash(&POSEIDON2, &[pair[0], *pair.get(1).unwrap_or(&zero)]))
            .collect();
        zero = poseidon::hash(&POSEIDON2, &[zero; 2]);
        index >>= 1;
    }
    (layer.first().copied().unwrap_or(zero), siblings)
}

/// Root of the tree holding `leaf` at the position given by `index_bits`
/// (little-endian, one per level) with sibling path `siblings`.
pub fn merkle_root_var(
    leaf: &FpVar<Fr>,
    index_bits: &[Boolean<Fr>],
    siblings: &[FpVar<Fr>],
) -> Result<FpVar<Fr>, SynthesisError> {
    assert_eq!(index_bits.len(), siblings.len());
    index_bits
        .iter()
        .zip(siblings)
        .try_fold(leaf.clone(), |current, (is_right, sibling)| {
            let left = is_right.select(sibling, &current)?;
            let right = is_right.select(&current, sibling)?;
            poseidon::hash_var(&POSEIDON2, &[left, right])
        })
}

pub const CHUNK_BITS: usize = 12;
pub const CHUNK: u64 = 1 << CHUNK_BITS;
/// A page holds the roots of 2^12 chunks: a subtree of 2^24 leaves.
pub const PAGE_BITS: usize = 2 * CHUNK_BITS;

/// `ZEROS[level]` is the root of an empty subtree of height `level`.
static ZEROS: LazyLock<[Fr; TREE_HEIGHT + 1]> = LazyLock::new(|| {
    let mut z = [Fr::from(0u64); TREE_HEIGHT + 1];
    for l in 1..=TREE_HEIGHT {
        z[l] = poseidon::hash(&POSEIDON2, &[z[l - 1]; 2]);
    }
    z
});

/// Root of the subtree spanning levels `from..to` whose level-`from` nodes are `layer`, then empty subtrees.
fn fold(mut layer: Vec<Fr>, from: usize, to: usize) -> Fr {
    for z in &ZEROS[from..to] {
        layer = layer
            .chunks(2)
            .map(|p| poseidon::hash(&POSEIDON2, &[p[0], *p.get(1).unwrap_or(z)]))
            .collect();
    }
    layer.first().copied().unwrap_or(ZEROS[to])
}

/// Root of one chunk holding `leaves` (up to 2^12) from its first position.
pub fn chunk_root(leaves: Vec<Fr>) -> Fr {
    fold(leaves, 0, CHUNK_BITS)
}

/// Root of one page holding `chunk_roots` (up to 2^12) from its first chunk.
pub fn page_root(chunk_roots: Vec<Fr>) -> Fr {
    fold(chunk_roots, CHUNK_BITS, PAGE_BITS)
}

/// The tree at `n` leaves, with the roots of its last, partial chunk and page (None where `n` ends on a boundary).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Sized {
    pub root: Fr,
    pub partial_chunk: Option<Fr>,
    pub partial_page: Option<Fr>,
}

/// The tree at `n` leaves. It takes what a wallet holds to build a path, which is bounded however large the tree
/// grows:
/// - the full pages' roots (at least `n >> 24` of them);
/// - the roots of the full chunks in the page containing `n` (chunks `n >> 24 << 12 .. n >> 12`);
/// - the leaves of the partial chunk (positions `n >> 12 << 12 .. n`).
pub fn sized(n: u64, page_roots: &[Fr], page_chunks: &[Fr], partial_leaves: Vec<Fr>) -> Sized {
    let pages = (n >> PAGE_BITS) as usize;
    debug_assert_eq!(page_chunks.len() as u64, (n >> CHUNK_BITS) % CHUNK);
    let partial_chunk = (!n.is_multiple_of(CHUNK)).then(|| chunk_root(partial_leaves));
    let partial_page = (!page_chunks.is_empty() || partial_chunk.is_some())
        .then(|| page_root(page_chunks.iter().copied().chain(partial_chunk).collect()));
    let top = page_roots[..pages]
        .iter()
        .copied()
        .chain(partial_page)
        .collect();
    Sized {
        root: fold(top, PAGE_BITS, TREE_HEIGHT),
        partial_chunk,
        partial_page,
    }
}

/// The tree at `n` leaves as an [`IncrementalTree`] to append to, from what [`sized`] takes.
pub fn frontier(
    n: u64,
    page_roots: &[Fr],
    page_chunks: &[Fr],
    partial_leaves: &[Fr],
) -> IncrementalTree {
    let mut filled = [Fr::from(0u64); TREE_HEIGHT];
    // each stratum: its nodes from its first position, the position of `n` among them, and their level
    for (nodes, pos, base) in [
        (partial_leaves, n % CHUNK, 0),
        (page_chunks, (n >> CHUNK_BITS) % CHUNK, CHUNK_BITS),
        (page_roots, n >> PAGE_BITS, PAGE_BITS),
    ] {
        for k in 0..(TREE_HEIGHT - base).min(CHUNK_BITS) {
            let i = (pos >> k) as usize;
            if i & 1 == 1 {
                filled[base + k] = fold(nodes[(i - 1) << k..i << k].to_vec(), base, base + k);
            }
        }
    }
    IncrementalTree::from_frontier(n, filled)
}

/// Fills `out` with the siblings of `layer[index]` at levels `from..from + out.len()`, where `layer` holds the
/// level-`from` nodes from the subtree's first position and empty subtrees follow.
fn siblings_in(mut layer: Vec<Fr>, mut index: usize, from: usize, out: &mut [Fr]) {
    for (sibling, z) in out.iter_mut().zip(&ZEROS[from..]) {
        *sibling = layer.get(index ^ 1).copied().unwrap_or(*z);
        layer = layer
            .chunks(2)
            .map(|p| poseidon::hash(&POSEIDON2, &[p[0], *p.get(1).unwrap_or(z)]))
            .collect();
        index >>= 1;
    }
}

/// The sibling path of position `i` in the tree at `n` leaves (`i < n`), from what a wallet holds, which is bounded
/// however large the tree grows:
/// - `chunk_leaves`: the leaves of `i`'s chunk from its first position (any past `n` are ignored, missing ones read
///   as empty);
/// - `page_chunks`: the roots of the full chunks in `i`'s page (any past `n` are ignored);
/// - `page_roots`: the full pages' roots (any past `n` are ignored);
/// - `at`: the partial chunk and page roots of the tree at `n`, as the indexer and ASP publish them with each root.
///
/// Every list keeps growing after the root it is used against, hence the truncation to `n`. Check the result with
/// [`path_root`] against a root the chain accepts: that authenticates every input.
pub fn path(
    i: u64,
    n: u64,
    chunk_leaves: &[Fr],
    page_chunks: &[Fr],
    page_roots: &[Fr],
    at: &Sized,
) -> [Fr; TREE_HEIGHT] {
    assert!(i < n, "position {i} is not in a tree of {n} leaves");
    let (chunk, page) = (i >> CHUNK_BITS, i >> PAGE_BITS);
    let in_chunk = (n - (chunk << CHUNK_BITS)).min(CHUNK) as usize;
    let mut out = [Fr::from(0u64); TREE_HEIGHT];
    siblings_in(
        chunk_leaves.iter().copied().take(in_chunk).collect(),
        (i % CHUNK) as usize,
        0,
        &mut out[..CHUNK_BITS],
    );
    // the chunk roots of i's page at n: its full chunks, then the partial chunk if the page holds it
    let full_chunks = ((n >> CHUNK_BITS) - (page << CHUNK_BITS)).min(CHUNK) as usize;
    let partial_chunk = (n >> PAGE_BITS == page)
        .then_some(at.partial_chunk)
        .flatten();
    let chunks = page_chunks
        .iter()
        .copied()
        .take(full_chunks)
        .chain(partial_chunk)
        .collect();
    siblings_in(
        chunks,
        (chunk % CHUNK) as usize,
        CHUNK_BITS,
        &mut out[CHUNK_BITS..PAGE_BITS],
    );
    let pages = page_roots
        .iter()
        .copied()
        .take((n >> PAGE_BITS) as usize)
        .chain(at.partial_page)
        .collect();
    siblings_in(pages, page as usize, PAGE_BITS, &mut out[PAGE_BITS..]);
    out
}

/// Root of the tree holding `leaf` at position `i` with sibling path `siblings`.
pub fn path_root(leaf: Fr, i: u64, siblings: &[Fr; TREE_HEIGHT]) -> Fr {
    siblings
        .iter()
        .enumerate()
        .fold(leaf, |current, (level, sibling)| {
            let pair = if i >> level & 1 == 0 {
                [current, *sibling]
            } else {
                [*sibling, current]
            };
            poseidon::hash(&POSEIDON2, &pair)
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frontier_matches_sized() {
        let seq = |from: u64, k: u64| (from..from + k).map(Fr::from).collect::<Vec<_>>();
        // set and unset bits in all three strata
        let n = (3 << PAGE_BITS) + (5 << CHUNK_BITS) + 7;
        let (pages, chunks, mut leaves) = (seq(100, 3), seq(200, 5), seq(300, 7));
        let mut tree = frontier(n, &pages, &chunks, &leaves);
        assert_eq!(tree.root, sized(n, &pages, &chunks, leaves.clone()).root);
        // the root after an append is folded from the siblings it returns
        tree.append(Fr::from(400u64));
        leaves.push(Fr::from(400u64));
        assert_eq!(tree.root, sized(n + 1, &pages, &chunks, leaves).root);
    }

    #[test]
    fn path_matches_merkle_path() {
        let leaves: Vec<Fr> = (1..=2 * CHUNK + 3).map(Fr::from).collect();
        // a partial first chunk, a full one, and a partial chunk after full ones
        for n in [2, CHUNK, 2 * CHUNK + 3] {
            let full = (n / CHUNK) as usize * CHUNK as usize;
            let roots: Vec<Fr> = leaves[..full]
                .chunks(CHUNK as usize)
                .map(|c| chunk_root(c.to_vec()))
                .collect();
            let at = sized(n, &[], &roots, leaves[full..n as usize].to_vec());
            for i in [1, CHUNK - 1, CHUNK + 2, 2 * CHUNK + 2] {
                if i >= n {
                    continue;
                }
                let start = (i / CHUNK * CHUNK) as usize;
                // the lists run past n, as a wallet's later download would
                let got = path(i, n, &leaves[start..], &roots, &[], &at);
                let (root, want) = merkle_path(&leaves[..n as usize], i as usize);
                assert_eq!(got, want, "i = {i}, n = {n}");
                assert_eq!(path_root(leaves[i as usize], i, &got), root);
            }
        }
    }

    /// Across a page boundary, with chunk roots standing in for every chunk but the one holding the leaf.
    #[test]
    fn path_spans_pages() {
        let leaves: Vec<Fr> = (1..=3u64).map(|v| Fr::from(v * 11)).collect();
        let mut chunk_roots: Vec<Fr> = (1..=CHUNK + 3).map(|v| Fr::from(v * 7)).collect();
        // i in a full chunk of the full first page, and in the partial chunk of the second page
        for (chunk, n) in [
            (3, (CHUNK + 2) << CHUNK_BITS),
            (CHUNK + 2, ((CHUNK + 2) << CHUNK_BITS) + 3),
        ] {
            let full = chunk < n >> CHUNK_BITS;
            if full {
                let mut chunk_leaves = leaves.clone();
                chunk_leaves.resize(CHUNK as usize, Fr::from(0u64));
                chunk_roots[chunk as usize] = chunk_root(chunk_leaves);
            }
            let pages = [page_root(chunk_roots[..CHUNK as usize].to_vec())];
            let page_chunks = &chunk_roots[CHUNK as usize..(n >> CHUNK_BITS) as usize];
            let partial = if full { vec![] } else { leaves.clone() };
            let at = sized(n, &pages, page_chunks, partial);
            let i = (chunk << CHUNK_BITS) + 1;
            let own_page = if chunk < CHUNK {
                &chunk_roots[..CHUNK as usize]
            } else {
                page_chunks
            };
            let got = path(i, n, &leaves, own_page, &pages, &at);
            assert_eq!(path_root(leaves[1], i, &got), at.root, "chunk {chunk}");
        }
    }

    #[test]
    fn merkle_path_matches_incremental_tree() {
        let leaves: Vec<Fr> = (1..=5u64).map(Fr::from).collect();
        let mut tree = IncrementalTree::default();
        assert_eq!(merkle_path(&[], 0).0, tree.root);
        let siblings: Vec<_> = leaves.iter().map(|&leaf| tree.append(leaf)).collect();
        assert_eq!(merkle_path(&leaves, 4), (tree.root, siblings[4]));
        // An earlier leaf's path is re-derived against the final root.
        let (root, path) = merkle_path(&leaves, 1);
        assert_eq!(root, tree.root);
        assert_eq!(path[1], poseidon::hash(&POSEIDON2, &[leaves[2], leaves[3]]));
    }

    #[test]
    fn chunked_root_matches_the_reference_tree() {
        let leaves: Vec<Fr> = (1..=2 * CHUNK + 3).map(Fr::from).collect();
        for n in [
            0,
            1,
            2,
            3,
            CHUNK - 1,
            CHUNK,
            CHUNK + 1,
            2 * CHUNK,
            2 * CHUNK + 3,
        ] {
            let full = (n / CHUNK) as usize * CHUNK as usize;
            let roots: Vec<Fr> = leaves[..full]
                .chunks(CHUNK as usize)
                .map(|c| chunk_root(c.to_vec()))
                .collect();
            let tree = sized(n, &[], &roots, leaves[full..n as usize].to_vec());
            assert_eq!(
                tree.root,
                merkle_path(&leaves[..n as usize], 0).0,
                "n = {n}"
            );
            assert_eq!(tree.partial_chunk.is_some(), n % CHUNK != 0);
        }
    }

    /// Pages only regroup the chunk roots: the root must equal folding every chunk root straight up, across a page
    /// boundary too (a full page is 2^24 leaves, so chunk roots stand in for real chunks here).
    #[test]
    fn pages_regroup_chunk_roots() {
        let chunk_roots: Vec<Fr> = (1..=CHUNK + 3).map(|i| Fr::from(i * 7)).collect();
        let pages = [page_root(chunk_roots[..CHUNK as usize].to_vec())];
        for chunks in [1, CHUNK - 1, CHUNK, CHUNK + 3] {
            let n = chunks << CHUNK_BITS;
            let flat = fold(
                chunk_roots[..chunks as usize].to_vec(),
                CHUNK_BITS,
                TREE_HEIGHT,
            );
            let page_chunks = &chunk_roots[(chunks / CHUNK * CHUNK) as usize..chunks as usize];
            let tree = sized(n, &pages[..(chunks / CHUNK) as usize], page_chunks, vec![]);
            assert_eq!(tree.root, flat, "{chunks} chunks");
            assert_eq!(tree.partial_page.is_some(), chunks % CHUNK != 0);
        }
        // a partial chunk on top of a full page: its root goes into the next page
        let leaf = Fr::from(5u64);
        let n = (CHUNK << CHUNK_BITS) + 1;
        let tail = chunk_root(vec![leaf]);
        let mut flat = chunk_roots[..CHUNK as usize].to_vec();
        flat.push(tail);
        let tree = sized(n, &pages, &[], vec![leaf]);
        assert_eq!(tree.root, fold(flat, CHUNK_BITS, TREE_HEIGHT));
        assert_eq!(
            (tree.partial_chunk, tree.partial_page),
            (Some(tail), Some(page_root(vec![tail])))
        );
    }
}
