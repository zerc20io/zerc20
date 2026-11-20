pragma circom 2.0.0;

// Protocol-level circuit parameters.
//
// These are declared as functions (not `var`s) so they can be used both as
// compile-time template parameters / array sizes and as plain values inside
// templates. Every value here is part of the protocol's wire format: changing
// one is a breaking change that invalidates existing commitments, roots, and
// previously generated proofs.

// Height of the commitment and ASP Merkle trees (2^32 leaves).
function MERKLE_DEPTH() {
    return 32;
}

// Bit width of every token amount. Bounded so the value-conservation sum cannot
// overflow the field: even six 248-bit terms stay below the ~254-bit modulus.
function AMOUNT_BITS() {
    return 248;
}

// Bit width of an Ethereum address (20 bytes).
function ADDRESS_BITS() {
    return 160;
}

// Bit width of a token identifier.
function TOKEN_ID_BITS() {
    return 32;
}

// Bit width of an EVM chain identifier.
function CHAIN_ID_BITS() {
    return 64;
}

// Proof-of-work difficulty for burn addresses: the top 16 bits of the canonical
// burn digest must be zero, costing the sender ~2^16 salt-grinding attempts.
function BURN_POW_BITS() {
    return 16;
}

// Number of bits in the canonical representation of an Fr element (BN254 scalar
// field is 254 bits). Used by the alias-safe digest decomposition.
function FIELD_BIT_LENGTH() {
    return 254;
}

function TRANSFER_FIELD0_BASE() {
    // Matches CommitmentLedger.TRANSFER_TAG shifted into the field0 tag slot.
    // field0 = (uint32(bytes4(keccak256("Transfer(address,address,uint256)"))) << 32) | token_id
    return 15992936129728872448;
}

function NOTE_FIELD0_BASE() {
    // Matches CommitmentLedger.NOTE_HASH_TAG shifted into the field0 tag slot.
    // field0 = (uint32(bytes4(keccak256("NoteHash(uint256)"))) << 32) | token_id
    return 8691708596607516672;
}

// Domain-separation tags for Poseidon hashing.
//
// Each tag is the first input to a domain-specific hash so that, for example, a
// note hash can never be reinterpreted as a nullifier or a public key. The
// values are `sha256(label) mod Fr`. Every client that generates witnesses must
// reproduce this exact encoding, otherwise the public outputs (nullifiers, note
// hashes) will not match what the contract expects.
function DOMAIN_NOTE() {
    return 12890024175661825764581542883111592339070511154523346722771315793398079606973;
}

function DOMAIN_PUBLIC_KEY() {
    return 12748143626193170683619257575461114475162050184551511165632901980951779591788;
}

function DOMAIN_NULLIFYING_KEY() {
    return 17471194487513808174444331798961284844045019683771872456746961298409210755086;
}

function DOMAIN_NULLIFIER() {
    return 21656625071485835455144987912439041855442440977080724417184138235324194035747;
}

function DOMAIN_DUMMY_NULLIFIER() {
    return 7044432322484129783600934309074221576946257299516531409248588859126398254720;
}

function DOMAIN_BURN() {
    return 7812678369084671832725575743163273348609229243038681297431930412876960276650;
}

// Separates an ASP leaf preimage from an ASP interior node. The ASP tree hashes
// both roles with Poseidon(2), unlike the commitment tree where leaves are
// Poseidon(4) and are disjoint from nodes by arity. Without this tag, nothing in
// AspLeaf or MerkleRoot stops an interior node from being opened as a leaf; the
// only barriers would be the fixed path length and the caller's range check on
// `commitment_index`, neither of which lives in the templates that rely on it.
function DOMAIN_ASP_LEAF() {
    return 20989222074995585771835793404421254795991252548608321040973959344582939809523;
}

// Spend authorization (zkp/src/auth.rs). The circom circuits take the signing
// key's hash as a witness and never check a signature; the merge step and the
// attester do. Kept here so every domain tag is in one place.
function DOMAIN_AUTH_KEY() {
    return 10225447400557743590985446737842398671604622534850121808755795315749324473275;
}

function DOMAIN_SPEND_AUTH() {
    return 8230886534581055996046092392097874170742872724656370212214393322619803652446;
}

function DOMAIN_TRANSACT_AUTH() {
    return 13562453510417820550960573109771867520359186262900151110365996214945948233794;
}

function DOMAIN_MERGE_AUTH() {
    return 16474997453874937243622623791033663138618536810477243309426195930856928586225;
}
