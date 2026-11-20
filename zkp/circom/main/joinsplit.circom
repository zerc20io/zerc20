pragma circom 2.0.0;

include "../../node_modules/circomlib/circuits/comparators.circom";
include "../lib/constants.circom";
include "../lib/range.circom";
include "../lib/primitives.circom";
include "../lib/merkle.circom";
include "../lib/inputs.circom";

// Main zERC20 private state transition. The circuit has two input slots, two
// private output-note slots, and one optional public withdrawal. It proves value
// conservation without revealing the spent notes. A zero `withdraw_amount` makes
// the transition a pure private transfer, with all value assigned to output notes.
// `withdraw_intent` says how the withdrawal is paid out (e.g. as the underlying
// asset); the circuit only binds it and leaves its meaning to the contract.
//
// Inputs:
//   - in0 (always real): either an on-chain transfer to a burn address
//     (`in0_is_burn = 1`) or an existing private note (`in0_is_burn = 0`).
//   - in1: either an existing private note (`in1_is_dummy = 0`) or a zero-value
//     padding input (`in1_is_dummy = 1`).
//
// Circuit-enforced invariants:
//   - Ownership: each real input requires knowledge of the spending private key,
//     which derives the nullifying key that the owner's public key commits to.
//   - Membership: each real input is a leaf of `commitment_root`; a burn input must
//     also be a deposit the ASP approved in `asp_root`.
//   - Conservation: range-bounded input value equals withdrawal + output notes.
//   - Replay safety: a distinct nullifier is emitted per input.
//
// Per-input validation lives in lib/inputs.circom (NoteSpend / BurnIntake); this
// template wires the slots together and enforces the cross-input invariants
// (leaf selection, Merkle membership, distinct nullifiers, conservation).
//
// Public signal model:
//   - The `component main { public [...] }` list contains the explicit public
//     inputs accepted by the circuit.
//   - `signal output` values (nullifiers, withdrawal data, output note hashes)
//     are also proof public signals. This binds them to the proof, exposes them
//     to the verifier contract, and gives Picus deterministic outputs to check.
template JoinSplit(depth, amount_bits, address_bits, pow_bits) {
    signal input token_id;
    signal input chain_id;
    signal input commitment_root;
    signal input asp_root;

    signal input entropy;

    signal input in0_is_burn;
    signal input in1_is_dummy;

    signal input in_note0_public_key;
    signal input in_note0_value;
    signal input in_note0_salt;
    signal input in_note1_public_key;
    signal input in_note1_value;
    signal input in_note1_salt;

    // BurnWitness is flattened into named fields to keep JSON witness generation
    // stable and unambiguous.
    signal input burn_public_key;
    signal input burn_salt;
    signal input burn_transfer_from;
    signal input burn_transfer_value;

    signal input withdraw_recipient_private;
    signal input withdraw_amount_private;
    signal input withdraw_intent_private;

    signal input out_note1_public_key;
    signal input out_note1_value;
    signal input out_note1_salt;
    signal input out_note2_public_key;
    signal input out_note2_value;
    signal input out_note2_salt;

    signal input private_key0;
    signal input private_key1;
    signal input auth_key_hash0;
    signal input auth_key_hash1;
    signal input commitment_index0;
    signal input commitment_index1;
    signal input in0_merkle_siblings[depth];
    signal input in1_merkle_siblings[depth];
    signal input in0_asp_siblings[depth];

    signal output nullifier0;
    signal output nullifier1;
    signal output withdraw_recipient;
    signal output withdraw_amount;
    signal output withdraw_intent;
    signal output note_hash1;
    signal output note_hash2;

    signal in0_is_note;
    signal in1_is_real;
    signal input0_value;
    signal input1_value;
    signal selected_in0_leaf;
    signal selected_nullifier1;
    signal amount_values[6];
    signal address_values[2];

    // Mode flags must be boolean before they feed branch selectors. Otherwise a
    // prover could blend both branches through the linear interpolation muxes.
    // The complements are derived once and reused.
    component in0_is_burn_bool = Boolean();
    component in1_is_dummy_bool = Boolean();
    in0_is_burn_bool.in <== in0_is_burn;
    in1_is_dummy_bool.in <== in1_is_dummy;

    in0_is_note <== 1 - in0_is_burn;
    in1_is_real <== 1 - in1_is_dummy;

    // Range checks. Every value that participates in protocol arithmetic is
    // bounded to its external domain. This prevents conservation from being
    // satisfied by field wraparound and keeps Ethereum-sized fields canonical.
    // RangeCheck(n) constrains its input to [0, 2^n) (see lib/range.circom).
    component token_id_range = RangeCheck(TOKEN_ID_BITS());
    component chain_id_range = RangeCheck(CHAIN_ID_BITS());
    token_id_range.in <== token_id;
    chain_id_range.in <== chain_id;

    // Every amount that enters value conservation, on either side of the equation.
    amount_values[0] <== withdraw_amount_private;
    amount_values[1] <== burn_transfer_value;
    amount_values[2] <== in_note0_value;
    amount_values[3] <== in_note1_value;
    amount_values[4] <== out_note1_value;
    amount_values[5] <== out_note2_value;

    component amount_range[6];
    for (var amount_i = 0; amount_i < 6; amount_i++) {
        amount_range[amount_i] = RangeCheck(amount_bits);
        amount_range[amount_i].in <== amount_values[amount_i];
    }

    address_values[0] <== withdraw_recipient_private;
    address_values[1] <== burn_transfer_from;

    component address_range[2];
    for (var address_i = 0; address_i < 2; address_i++) {
        address_range[address_i] = RangeCheck(address_bits);
        address_range[address_i].in <== address_values[address_i];
    }

    // Nullifier indexes are explicit protocol operands, so bound them at this
    // layer instead of relying only on the current unconditional MerkleRoot
    // wiring. The Merkle templates retain their own defense-in-depth bounds.
    component commitment_index_range[2];
    commitment_index_range[0] = RangeCheck(depth);
    commitment_index_range[0].in <== commitment_index0;
    commitment_index_range[1] = RangeCheck(depth);
    commitment_index_range[1].in <== commitment_index1;

    // Ownership keys are derived from the supplied secrets and signing key
    // hashes. The per-input templates below compare them against the committed
    // owner of each branch.
    component public_key0 = PublicKey();
    component public_key1 = PublicKey();
    component nullifying_key0 = NullifyingKey();
    component nullifying_key1 = NullifyingKey();

    nullifying_key0.private_key <== private_key0;
    nullifying_key1.private_key <== private_key1;
    public_key0.auth_key_hash <== auth_key_hash0;
    public_key0.nullifying_key <== nullifying_key0.nullifying_key;
    public_key1.auth_key_hash <== auth_key_hash1;
    public_key1.nullifying_key <== nullifying_key1.nullifying_key;

    // in0 is always a real input, validated as a private note or a burn transfer.
    // The two branches are mutually exclusive; the inactive one is gated off and
    // its witness fields are pinned to zero inside the sub-template.
    component in0_note = NoteSpend();
    in0_note.enabled <== in0_is_note;
    in0_note.chain_id <== chain_id;
    in0_note.token_id <== token_id;
    in0_note.note_public_key <== in_note0_public_key;
    in0_note.note_value <== in_note0_value;
    in0_note.note_salt <== in_note0_salt;
    in0_note.owner_public_key <== public_key0.public_key;
    in0_note.commitment_index <== commitment_index0;
    in0_note.nullifying_key <== nullifying_key0.nullifying_key;

    component in0_burn = BurnIntake(depth, address_bits, pow_bits);
    in0_burn.enabled <== in0_is_burn;
    in0_burn.chain_id <== chain_id;
    in0_burn.token_id <== token_id;
    in0_burn.owner_public_key <== public_key0.public_key;
    in0_burn.burn_public_key <== burn_public_key;
    in0_burn.burn_salt <== burn_salt;
    in0_burn.burn_transfer_from <== burn_transfer_from;
    in0_burn.burn_transfer_value <== burn_transfer_value;
    in0_burn.commitment_index <== commitment_index0;
    in0_burn.asp_root <== asp_root;
    for (var asp_i = 0; asp_i < depth; asp_i++) {
        in0_burn.asp_siblings[asp_i] <== in0_asp_siblings[asp_i];
    }

    // in1 is a private note, or a zero-value dummy when `in1_is_dummy`.
    component in1_note = NoteSpend();
    in1_note.enabled <== in1_is_real;
    in1_note.chain_id <== chain_id;
    in1_note.token_id <== token_id;
    in1_note.note_public_key <== in_note1_public_key;
    in1_note.note_value <== in_note1_value;
    in1_note.note_salt <== in_note1_salt;
    in1_note.owner_public_key <== public_key1.public_key;
    in1_note.commitment_index <== commitment_index1;
    in1_note.nullifying_key <== nullifying_key1.nullifying_key;

    // A disabled input has one canonical witness, including the path metadata
    // that NoteSpend itself does not own. This removes free dummy index/sibling
    // fields while preserving the public signal ABI.
    commitment_index1 * in1_is_dummy === 0;
    for (var dummy_i = 0; dummy_i < depth; dummy_i++) {
        in1_merkle_siblings[dummy_i] * in1_is_dummy === 0;
    }

    // in0 always proves membership; the leaf switches between the burn transfer
    // commitment and the note commitment based on `in0_is_burn`.
    selected_in0_leaf <== in0_note.leaf + in0_is_burn * (in0_burn.leaf - in0_note.leaf);

    component in0_root = MerkleRoot(depth);
    component in1_root = MerkleRoot(depth);
    in0_root.leaf <== selected_in0_leaf;
    in0_root.index <== commitment_index0;
    in1_root.leaf <== in1_note.leaf;
    in1_root.index <== commitment_index1;

    for (var i = 0; i < depth; i++) {
        in0_root.siblings[i] <== in0_merkle_siblings[i];
        in1_root.siblings[i] <== in1_merkle_siblings[i];
    }

    in0_root.root === commitment_root;

    // in1 proves membership only when it is a real note. For a dummy input,
    // NoteSpend pins the note opening to zero and this computed root is ignored.
    component in1_root_check = ForceEqualIfEnabled();
    in1_root_check.enabled <== in1_is_real;
    in1_root_check.in[0] <== in1_root.root;
    in1_root_check.in[1] <== commitment_root;

    // Nullifiers. in0 always emits its index-keyed nullifier, which is valid for
    // both the note and burn branches because nullifiers are keyed by tree
    // position. in1 emits its real nullifier, or a domain-separated dummy
    // nullifier when padding so dummy and real nullifiers are structurally
    // separated. Dummy-nullifier freshness is an external requirement: the
    // witness generator must use fresh entropy and the verifier must reject any
    // public nullifier that already appears in the on-chain nullifier set.
    component dummy_nullifier1 = DummyNullifier(1);
    dummy_nullifier1.chain_id <== chain_id;
    dummy_nullifier1.entropy <== entropy;

    nullifier0 <== in0_note.nullifier;
    selected_nullifier1 <== in1_note.nullifier + in1_is_dummy * (dummy_nullifier1.nullifier - in1_note.nullifier);
    nullifier1 <== selected_nullifier1;

    // The two nullifiers must differ. This rejects spending the same input in both
    // slots (which would otherwise pass every other check) within a single proof;
    // cross-transaction double spends are caught on-chain by the nullifier set.
    component distinct_nullifiers = IsZero();
    distinct_nullifiers.in <== nullifier0 - nullifier1;
    distinct_nullifiers.out === 0;

    // Output note commitments. Their openings are chosen by the prover; a
    // zero-value opening represents an unused output. Values are range checked
    // above, while public keys and salts are field elements. The hashes are
    // published so the contract can insert them into the commitment tree.
    component out_note_hash1 = NoteHash();
    component out_note_hash2 = NoteHash();
    out_note_hash1.chain_id <== chain_id;
    out_note_hash1.public_key <== out_note1_public_key;
    out_note_hash1.value <== out_note1_value;
    out_note_hash1.token_id <== token_id;
    out_note_hash1.note_salt <== out_note1_salt;
    out_note_hash2.chain_id <== chain_id;
    out_note_hash2.public_key <== out_note2_public_key;
    out_note_hash2.value <== out_note2_value;
    out_note_hash2.token_id <== token_id;
    out_note_hash2.note_salt <== out_note2_salt;

    // Conservation over range-limited amounts (cannot wrap the field modulus).
    // Each input contributes its branch value: in0 switches between note and burn,
    // in1 is zero when it is a dummy.
    input0_value <== in0_note.value + in0_is_burn * (in0_burn.value - in0_note.value);
    input1_value <== in1_note.value * in1_is_real;

    input0_value + input1_value === withdraw_amount_private + out_note1_value + out_note2_value;

    // Canonical inactive withdrawal leg. `withdraw_recipient` and `withdraw_intent` are public
    // signals on every transition, but the recipient's range check above is their only other
    // constraint. Without these pins a pure private transfer has 2^160 (and p) valid public-signal
    // rows for one private state transition, which is both a linkable stamp and a covert channel
    // per proof. Pinned to zero, it opens canonically, as every other inactive branch (NoteSpend /
    // BurnIntake `disabled`) does.
    component withdraw_inactive = IsZero();
    withdraw_inactive.in <== withdraw_amount_private;
    component zero_withdraw_recipient = ForceEqualIfEnabled();
    zero_withdraw_recipient.enabled <== withdraw_inactive.out;
    zero_withdraw_recipient.in[0] <== withdraw_recipient_private;
    zero_withdraw_recipient.in[1] <== 0;
    component zero_withdraw_intent = ForceEqualIfEnabled();
    zero_withdraw_intent.enabled <== withdraw_inactive.out;
    zero_withdraw_intent.in[0] <== withdraw_intent_private;
    zero_withdraw_intent.in[1] <== 0;

    withdraw_recipient <== withdraw_recipient_private;
    withdraw_amount <== withdraw_amount_private;
    withdraw_intent <== withdraw_intent_private;
    note_hash1 <== out_note_hash1.note_hash;
    note_hash2 <== out_note_hash2.note_hash;
}

component main {
    public [
        token_id,
        chain_id,
        commitment_root,
        asp_root
    ]
} = JoinSplit(
    MERKLE_DEPTH(),
    AMOUNT_BITS(),
    ADDRESS_BITS(),
    BURN_POW_BITS()
);
