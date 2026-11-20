pragma circom 2.0.0;

include "./constants.circom";
include "./poseidon.circom";

// Leaf encodings for the commitment tree.
//
// Every leaf is a 4-field Poseidon hash. `field0` always carries a type tag in
// its high bits (see *_FIELD0_BASE in constants) plus the token id in its low
// bits, so notes and transfers occupy disjoint encodings and cannot be confused
// for one another even before the remaining fields are considered. All of this
// must stay byte-for-byte in lockstep with the off-chain indexer; changing any
// encoding invalidates every previously computed commitment root.

// Canonical 4-field commitment leaf: leaf = Poseidon4(field0..field3).
template CommitmentLeaf() {
    signal input field0;
    signal input field1;
    signal input field2;
    signal input field3;
    signal output leaf;

    component leaf_hash = Hash4();

    leaf_hash.values[0] <== field0;
    leaf_hash.values[1] <== field1;
    leaf_hash.values[2] <== field2;
    leaf_hash.values[3] <== field3;

    leaf <== leaf_hash.out;
}

// Leaf for an on-chain ERC20 transfer to a burn address. It has no salt: two
// identical transfers legitimately produce identical leaves, and they are kept
// distinct (and independently spendable) by their tree positions, since the
// nullifier is keyed by position rather than by leaf contents.
template TransferLeaf() {
    signal input token_id;
    signal input from;
    signal input to;
    signal input value;
    signal output leaf;

    signal field0;

    field0 <== TRANSFER_FIELD0_BASE() + token_id;

    component commitment_leaf = CommitmentLeaf();
    commitment_leaf.field0 <== field0;
    commitment_leaf.field1 <== from;
    commitment_leaf.field2 <== to;
    commitment_leaf.field3 <== value;

    leaf <== commitment_leaf.leaf;
}

// Leaf for a private note commitment. The note hash already binds every note
// field, so the unused leaf fields are zero-padded.
template NoteLeaf() {
    signal input token_id;
    signal input note_hash;
    signal output leaf;

    signal field0;

    field0 <== NOTE_FIELD0_BASE() + token_id;

    component commitment_leaf = CommitmentLeaf();
    commitment_leaf.field0 <== field0;
    commitment_leaf.field1 <== note_hash;
    commitment_leaf.field2 <== 0;
    commitment_leaf.field3 <== 0;

    leaf <== commitment_leaf.leaf;
}

// Leaf for the Association Set Provider (ASP) tree: one deposit the ASP has
// approved, named by its commitment index on this chain. The tree is keyed like
// the commitment tree: the leaf sits at position `commitment_index`, and positions
// the ASP has not approved are 0. Membership is what gates burn-address intake.
// The leaf can only exist once the deposit does, so the screening it records
// always happened after the deposit. Interior nodes of the
// same tree are Hash2 (see merkle.circom) with the same arity, so the leaf carries
// its own domain tag: opening a node as a leaf would need a child equal to the tag.
// The commitment tree gets that separation for free from its Poseidon(4) leaves.
template AspLeaf() {
    signal input commitment_index;
    signal output leaf;

    component hash = DomainHash1(DOMAIN_ASP_LEAF());
    hash.value <== commitment_index;
    leaf <== hash.out;
}
