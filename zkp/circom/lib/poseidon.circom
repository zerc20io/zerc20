pragma circom 2.0.0;

include "../../node_modules/circomlib/circuits/poseidon.circom";

// Generic Poseidon wrappers.
//
// This is the low-level hashing layer: thin, protocol-agnostic helpers over
// circomlib's Poseidon. Each wrapper fixes a specific arity (and, for the
// DomainHash* family, a compile-time domain-separation tag) so every call site
// reads explicitly instead of packing values into an anonymous Poseidon
// component. Protocol-specific hashes (notes, nullifiers, keys, ...) build on
// these in primitives.circom.

// Plain 2-input Poseidon. Used only for Merkle interior-node hashing; ASP leaves use
// DomainHash1(DOMAIN_ASP_LEAF) to separate their image from interior nodes.
template Hash2() {
    signal input left;
    signal input right;
    signal output out;

    component poseidon = Poseidon(2);
    poseidon.inputs[0] <== left;
    poseidon.inputs[1] <== right;
    out <== poseidon.out;
}

// Plain 4-input Poseidon, used for the canonical commitment leaf.
template Hash4() {
    signal input values[4];
    signal output out;

    component poseidon = Poseidon(4);
    poseidon.inputs[0] <== values[0];
    poseidon.inputs[1] <== values[1];
    poseidon.inputs[2] <== values[2];
    poseidon.inputs[3] <== values[3];
    out <== poseidon.out;
}

// Domain-separated hashes. `domain` is a compile-time tag bound as the first
// Poseidon input, so two structures with identical payloads but different domains
// always produce different digests. DomainHashN hashes N payload fields.
template DomainHash1(domain) {
    signal input value;
    signal output out;

    component poseidon = Poseidon(2);
    poseidon.inputs[0] <== domain;
    poseidon.inputs[1] <== value;
    out <== poseidon.out;
}

template DomainHash2(domain) {
    signal input values[2];
    signal output out;

    component poseidon = Poseidon(3);
    poseidon.inputs[0] <== domain;
    poseidon.inputs[1] <== values[0];
    poseidon.inputs[2] <== values[1];
    out <== poseidon.out;
}

template DomainHash4(domain) {
    signal input values[4];
    signal output out;

    component poseidon = Poseidon(5);
    poseidon.inputs[0] <== domain;
    poseidon.inputs[1] <== values[0];
    poseidon.inputs[2] <== values[1];
    poseidon.inputs[3] <== values[2];
    poseidon.inputs[4] <== values[3];
    out <== poseidon.out;
}

template DomainHash5(domain) {
    signal input values[5];
    signal output out;

    component poseidon = Poseidon(6);
    poseidon.inputs[0] <== domain;
    poseidon.inputs[1] <== values[0];
    poseidon.inputs[2] <== values[1];
    poseidon.inputs[3] <== values[2];
    poseidon.inputs[4] <== values[3];
    poseidon.inputs[5] <== values[4];
    out <== poseidon.out;
}
