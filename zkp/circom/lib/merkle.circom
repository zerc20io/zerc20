pragma circom 2.0.0;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "./poseidon.circom";

// Recomputes a Merkle root from a leaf and its sibling path.
//
// `index` is the leaf's position, decomposed little-endian into `depth` bits:
// bit 0 chooses the side at the leaf level and bit (depth-1) at the level just
// below the root. At each level the index bit selects whether the running hash
// is the left or right child (the sibling takes the other side). The caller
// compares the returned `root` against a trusted root to prove membership.
//
// This index/orientation convention must match the off-chain indexer exactly,
// otherwise valid paths will compute the wrong root. Num2Bits also bounds
// `index` to [0, 2^depth), the number of leaves in the tree.
template MerkleRoot(depth) {
    signal input leaf;
    signal input index;
    signal input siblings[depth];
    signal output root;

    signal current[depth + 1];
    signal left[depth];
    signal right[depth];

    component index_bits = Num2Bits(depth);
    component hashers[depth];

    index_bits.in <== index;
    current[0] <== leaf;

    for (var level = 0; level < depth; level++) {
        // A set index bit means the running hash is the right child, so the
        // sibling is placed on the left. An unset bit keeps (current, sibling).
        // The selection is expressed as branch-free linear interpolation.
        left[level] <== current[level] + index_bits.out[level] * (siblings[level] - current[level]);
        right[level] <== siblings[level] + index_bits.out[level] * (current[level] - siblings[level]);

        hashers[level] = Hash2();
        hashers[level].left <== left[level];
        hashers[level].right <== right[level];

        current[level + 1] <== hashers[level].out;
    }

    root <== current[depth];
}
