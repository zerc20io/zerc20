pragma circom 2.0.0;

include "./constants.circom";
include "./poseidon.circom";

// Protocol cryptographic primitives.
//
// One template per hashed protocol object (keys, nullifiers, note and burn
// commitments), each a thin domain-separated wrapper over the generic Poseidon
// helpers in poseidon.circom. Keeping a single named definition per object makes
// the wire format auditable and easy to keep in lockstep with the off-chain
// indexer and the on-chain verifier.

// Key derivation. The nullifying key is a domain-separated hash of the private
// key, and the public key hashes it together with the hash of the owner's
// signing key (zkp/src/auth.rs). Spending a note here requires knowing the
// private key: the nullifying key is derived from it, and the public key must
// match. The merge step instead takes the nullifying key and a signature, so its
// prover never holds the private key. The nullifier is derived from the
// nullifying key, so the on-chain nullifier never reveals the public key or
// either secret.
template PublicKey() {
    signal input auth_key_hash;
    signal input nullifying_key;
    signal output public_key;

    component hash = DomainHash2(DOMAIN_PUBLIC_KEY());
    hash.values[0] <== auth_key_hash;
    hash.values[1] <== nullifying_key;
    public_key <== hash.out;
}

template NullifyingKey() {
    signal input private_key;
    signal output nullifying_key;

    component hash = DomainHash1(DOMAIN_NULLIFYING_KEY());
    hash.value <== private_key;
    nullifying_key <== hash.out;
}

// Nullifier for a real input. It is keyed by the leaf's position in the
// commitment tree (`commitment_index`) rather than by the note contents, so each
// tree position can be spent exactly once. The chain id binds it to a single
// chain. Uniqueness across the whole protocol is enforced on-chain by recording
// spent nullifiers; this circuit only guarantees the value is computed correctly.
template Nullifier() {
    signal input chain_id;
    signal input commitment_index;
    signal input nullifying_key;
    signal output nullifier;

    component hash = DomainHash4(DOMAIN_NULLIFIER());
    hash.values[0] <== chain_id;
    hash.values[1] <== commitment_index;
    hash.values[2] <== nullifying_key;
    hash.values[3] <== 0;
    nullifier <== hash.out;
}

// Nullifier for a dummy (padding) input. A transaction may have fewer real
// inputs than slots; the unused slot still emits a nullifier so the public
// interface is uniform. Its own domain tag separates it from real nullifiers.
// Global freshness cannot be proven inside one circuit invocation, so the witness
// generator must supply fresh entropy and the verifier must reject reused public
// nullifiers.
//
// `entropy` carries no constraint and fully determines the emitted nullifier, so
// a low-entropy default is not only a self-DoS: a deployment-wide constant (say
// `entropy = 0`) can be spent once by anyone and then blocks every client that
// shares that default. Clients must draw it from a CSPRNG.
//
// Slot separation is an additive offset, which only works while there is exactly
// one dummy slot. With two slots, `entropy` values differing by 1 make adjacent
// slots translates of each other and they collide; a second slot must move
// `dummy_index` into its own Poseidon input rather than adding it to `entropy`.
template DummyNullifier(dummy_index) {
    signal input chain_id;
    signal input entropy;
    signal output nullifier;

    signal indexed_entropy;

    indexed_entropy <== entropy + dummy_index;

    component hash = DomainHash2(DOMAIN_DUMMY_NULLIFIER());
    hash.values[0] <== chain_id;
    hash.values[1] <== indexed_entropy;
    nullifier <== hash.out;
}

// Commitment to a private note. The salt makes the hash hiding (two notes with
// the same owner, token and value still differ) and the bundled chain id, owner
// public key, value and token id bind every field the protocol cares about.
template NoteHash() {
    signal input chain_id;
    signal input public_key;
    signal input value;
    signal input token_id;
    signal input note_salt;
    signal output note_hash;

    component hash = DomainHash5(DOMAIN_NOTE());
    hash.values[0] <== chain_id;
    hash.values[1] <== public_key;
    hash.values[2] <== value;
    hash.values[3] <== token_id;
    hash.values[4] <== note_salt;
    note_hash <== hash.out;
}

// Digest that a burn address is derived from (see AddressFromDigest). Binding the
// chain id and owner public key means a burn address is controllable only by the
// holder of the corresponding private key, and the salt is what the sender grinds
// to satisfy the proof-of-work window.
template BurnDigest() {
    signal input chain_id;
    signal input public_key;
    signal input burn_salt;
    signal output digest;

    component hash = DomainHash4(DOMAIN_BURN());
    hash.values[0] <== chain_id;
    hash.values[1] <== public_key;
    hash.values[2] <== burn_salt;
    hash.values[3] <== 0;
    digest <== hash.out;
}
