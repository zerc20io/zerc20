pragma circom 2.0.0;

include "../../node_modules/circomlib/circuits/comparators.circom";
include "./constants.circom";
include "./primitives.circom";
include "./commitments.circom";
include "./merkle.circom";
include "./range.circom";

// Per-input spend logic for the JoinSplit circuit.
//
// The main circuit feeds two slots. in0 is always real and is either a private
// note (NoteSpend) or an on-chain transfer to a burn address (BurnIntake); in1
// is a private note or a zero-value padding input (NoteSpend with enabled = 0).
// Each template bundles everything specific to one branch: ownership, the
// commitment leaf, the derived value, and (for notes) the nullifier. JoinSplit
// supplies a boolean-constrained `enabled` selector for each branch. When
// disabled, the branch's witness fields are pinned to their canonical zero
// opening so every inactive path has one valid representation. Merkle membership
// of the produced leaf is intentionally left to the caller, because the two slots
// check membership differently (in0 always; in1 only when real).

// Validates one private-note input.
//
// Produces the note's commitment leaf, note hash, value and nullifier. When
// `enabled` is 1 the committed owner public key must equal `owner_public_key`
// (knowledge of the private key). When `enabled` is 0 the note opening is forced
// to zero, so a disabled slot contributes a deterministic empty note. The
// nullifier is always derived from `commitment_index` and `nullifying_key`, giving
// the caller a defined value even for disabled slots. The in0 burn case reuses
// that value because protocol nullifiers are keyed by tree position, not by note
// contents.
template NoteSpend() {
    signal input enabled;
    signal input chain_id;
    signal input token_id;
    signal input note_public_key;
    signal input note_value;
    signal input note_salt;
    signal input owner_public_key;
    signal input commitment_index;
    signal input nullifying_key;

    signal output leaf;
    signal output value;
    signal output nullifier;

    // `enabled` is boolean-constrained by JoinSplit, so this is its complement.
    signal disabled;
    disabled <== 1 - enabled;

    // Ownership: the committed owner must match the derived key while active.
    component owner_check = ForceEqualIfEnabled();
    owner_check.enabled <== enabled;
    owner_check.in[0] <== note_public_key;
    owner_check.in[1] <== owner_public_key;

    // Canonical disabled witness: a disabled note carries the zero opening.
    component zero_public_key = ForceEqualIfEnabled();
    zero_public_key.enabled <== disabled;
    zero_public_key.in[0] <== note_public_key;
    zero_public_key.in[1] <== 0;
    component zero_value = ForceEqualIfEnabled();
    zero_value.enabled <== disabled;
    zero_value.in[0] <== note_value;
    zero_value.in[1] <== 0;
    component zero_salt = ForceEqualIfEnabled();
    zero_salt.enabled <== disabled;
    zero_salt.in[0] <== note_salt;
    zero_salt.in[1] <== 0;

    component hash = NoteHash();
    hash.chain_id <== chain_id;
    hash.public_key <== note_public_key;
    hash.value <== note_value;
    hash.token_id <== token_id;
    hash.note_salt <== note_salt;

    component note_leaf = NoteLeaf();
    note_leaf.token_id <== token_id;
    note_leaf.note_hash <== hash.note_hash;
    leaf <== note_leaf.leaf;

    component nf = Nullifier();
    nf.chain_id <== chain_id;
    nf.commitment_index <== commitment_index;
    nf.nullifying_key <== nullifying_key;
    nullifier <== nf.nullifier;

    value <== note_value;
}

// Validates the burn-address intake branch of in0.
//
// Checks burn-witness ownership, derives the proof-of-work-bound burn address,
// builds the transfer commitment leaf, and proves that the ASP approved the
// deposit at `commitment_index`: its ASP leaf sits at that same position of the
// ASP tree. Every branch-specific check is gated by
// `enabled`; when disabled, the burn witness fields are pinned to zero and the
// PoW/ASP checks do not constrain the proof. Merkle membership of the returned
// `leaf` at `commitment_index` against the commitment root is left to the caller,
// which must use the same index so the approval names this deposit.
template BurnIntake(depth, address_bits, pow_bits) {
    signal input enabled;
    signal input chain_id;
    signal input token_id;
    signal input owner_public_key;
    signal input burn_public_key;
    signal input burn_salt;
    signal input burn_transfer_from;
    signal input burn_transfer_value;
    signal input commitment_index;
    signal input asp_root;
    signal input asp_siblings[depth];

    signal output leaf;
    signal output value;

    signal disabled;
    disabled <== 1 - enabled;

    // Ownership: the burn witness public key must match the derived key.
    component owner_check = ForceEqualIfEnabled();
    owner_check.enabled <== enabled;
    owner_check.in[0] <== burn_public_key;
    owner_check.in[1] <== owner_public_key;

    // Canonical disabled witness: a disabled burn branch carries zero fields.
    component zero_public_key = ForceEqualIfEnabled();
    zero_public_key.enabled <== disabled;
    zero_public_key.in[0] <== burn_public_key;
    zero_public_key.in[1] <== 0;
    component zero_salt = ForceEqualIfEnabled();
    zero_salt.enabled <== disabled;
    zero_salt.in[0] <== burn_salt;
    zero_salt.in[1] <== 0;
    component zero_from = ForceEqualIfEnabled();
    zero_from.enabled <== disabled;
    zero_from.in[0] <== burn_transfer_from;
    zero_from.in[1] <== 0;
    component zero_value = ForceEqualIfEnabled();
    zero_value.enabled <== disabled;
    zero_value.in[0] <== burn_transfer_value;
    zero_value.in[1] <== 0;

    // A real burn intake must carry economic value. The disabled branch remains
    // the canonical zero witness pinned above.
    component transfer_value_is_zero = IsZero();
    transfer_value_is_zero.in <== burn_transfer_value;
    component positive_transfer_value = ForceEqualIfEnabled();
    positive_transfer_value.enabled <== enabled;
    positive_transfer_value.in[0] <== transfer_value_is_zero.out;
    positive_transfer_value.in[1] <== 0;

    // Burn address derivation with the PoW window, gated by `enabled`.
    component digest = BurnDigest();
    digest.chain_id <== chain_id;
    digest.public_key <== burn_public_key;
    digest.burn_salt <== burn_salt;
    component address = AddressFromDigest(address_bits, pow_bits);
    address.enabled <== enabled;
    address.digest <== digest.digest;

    // Transfer commitment leaf for the on-chain burn transfer.
    component transfer_leaf = TransferLeaf();
    transfer_leaf.token_id <== token_id;
    transfer_leaf.from <== burn_transfer_from;
    transfer_leaf.to <== address.address;
    transfer_leaf.value <== burn_transfer_value;
    leaf <== transfer_leaf.leaf;

    // The ASP approves this deposit, not its sender: an address screened once
    // cannot carry a later deposit. Gated by `enabled`.
    component asp_leaf = AspLeaf();
    asp_leaf.commitment_index <== commitment_index;

    component asp_root_calc = MerkleRoot(depth);
    asp_root_calc.leaf <== asp_leaf.leaf;
    asp_root_calc.index <== commitment_index;
    for (var i = 0; i < depth; i++) {
        asp_root_calc.siblings[i] <== asp_siblings[i];
    }

    component asp_root_check = ForceEqualIfEnabled();
    asp_root_check.enabled <== enabled;
    asp_root_check.in[0] <== asp_root_calc.root;
    asp_root_check.in[1] <== asp_root;

    value <== burn_transfer_value;
}
