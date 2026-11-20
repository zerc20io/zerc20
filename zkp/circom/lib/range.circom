pragma circom 2.0.0;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "./constants.circom";

// Constrains `in` to a single bit, i.e. `in` is either 0 or 1.
//
// Used for every mode flag in the protocol. Booleanity is a hard requirement:
// flags drive linear-interpolation muxes (`a + flag * (b - a)`), and a non-boolean
// flag would let a prover blend the two branches and forge an out-of-domain value.
template Boolean() {
    signal input in;

    in * (in - 1) === 0;
}

// Constrains `in` to the unsigned integer range [0, 2^bits).
//
// `Num2Bits(bits)` enforces the bound by requiring `in` to equal the sum of
// `bits` boolean signals. The extra `Bits2Num` recomposition consumes those bit
// signals inside this template so `circom --inspect` does not flag unused
// subcomponent outputs. Range-bounding inputs keeps the value-conservation
// equation exact: it cannot be satisfied by wrapping around the field modulus.
//
// The width bound is structural rather than a caller convention: at `bits = 254`
// `Num2Bits` admits aliased decompositions of the same field element, and
// `recompose.out === in` is the identical linear constraint `Num2Bits` already
// emits, so the template would silently stop bounding anything. `assert` on a
// template parameter is evaluated at compile time and emits no constraint.
template RangeCheck(bits) {
    assert(bits > 0);
    assert(bits < 254);

    signal input in;

    component decompose = Num2Bits(bits);
    component recompose = Bits2Num(bits);

    decompose.in <== in;
    for (var i = 0; i < bits; i++) {
        recompose.in[i] <== decompose.out[i];
    }
    recompose.out === in;
}

// Derives an `address_bits`-wide burn address from a field-element digest and
// enforces the burn proof-of-work window.
//
// `address` is the low `address_bits` bits of `digest`. JoinSplit supplies a
// boolean-constrained `enabled` selector. When `enabled` is 1 (burn mode), the
// top `pow_bits` bits of the canonical 254-bit digest are forced to zero; this
// is the proof-of-work cost the sender pays off-chain by grinding the burn salt.
// The window is intentionally outside the returned low-160 address, so a valid
// burn address remains indistinguishable from an ordinary EVM address by shape.
// When `enabled` is 0, the PoW window is unconstrained and `address` is ignored
// by the caller.
//
// The address width is a parameter rather than a direct read of the global
// `ADDRESS_BITS()`, so callers that range-check burn operands with their own
// `address_bits` parameter cannot drift from the width this template splits. The
// asserts are compile-time only and emit no constraint: `pow_bits` carves the PoW
// window out of the top of the canonical field representation.
template AddressFromDigest(address_bits, pow_bits) {
    assert(address_bits <= FIELD_BIT_LENGTH());
    assert(pow_bits <= FIELD_BIT_LENGTH());

    signal input enabled;
    signal input digest;
    signal output address;

    // Num2Bits_strict is circomlib's alias-safe decomposition: it additionally
    // proves the bits are the canonical representative of `digest` in Fr, so a
    // prover cannot pick an aliased bit pattern. Bits2Num recomposes the full
    // 254-bit value here to consume every bit and keep `--inspect` clean.
    component digest_bits = Num2Bits_strict();
    component digest_num = Bits2Num(FIELD_BIT_LENGTH());
    digest_bits.in <== digest;

    var coefficient = 1;
    var address_lc = 0;

    for (var k = 0; k < FIELD_BIT_LENGTH(); k++) {
        digest_num.in[k] <== digest_bits.out[k];
    }

    for (var i = 0; i < address_bits; i++) {
        address_lc += digest_bits.out[i] * coefficient;
        coefficient = coefficient + coefficient;
    }

    digest_num.out === digest;
    address <== address_lc;

    // Proof-of-work: the high `pow_bits` bits of the canonical digest must be
    // zero while burn mode is active. Multiplying by `enabled` gates the
    // constraint for non-burn inputs without branching.
    for (var j = FIELD_BIT_LENGTH() - pow_bits; j < FIELD_BIT_LENGTH(); j++) {
        digest_bits.out[j] * enabled === 0;
    }
}
