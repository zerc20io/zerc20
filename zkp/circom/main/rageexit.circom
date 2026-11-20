pragma circom 2.0.0;

include "../lib/constants.circom";
include "../lib/range.circom";
include "../lib/primitives.circom";

// Emergency exit circuit for burn-address deposits.
//
// RageExit is intentionally narrower than JoinSplit's burn intake path:
// it does not consult ASP roots and it cannot create private notes. It proves
// ownership of the burn address a deposit was sent to and derives the
// deposit's nullifier, so the contract can refund the transfer sender.
//
// Membership is not proven here. The contract authenticates the deposit
// commitment (token, from, burn address, value) and its ledger index by walking
// the SHA-256 commitment hash chain to a recorded checkpoint, so an exit needs
// no proved commitment root and keeps working when root transitions stop.
//
// Public signal model:
//   - chain_id, commitment_index and burn_address are explicit public inputs,
//     supplied by the contract from the authenticated commitment.
//   - nullifier is a public output bound to the proof.
//
// Safety invariants:
//   - Ownership: private_key derives the nullifying_key, which with
//     auth_key_hash derives the burn public key, and the burn digest of
//     (chain_id, public key, burn_salt) passes the PoW window and has
//     burn_address as its low address_bits.
//   - Replay safety: nullifier uses the same index-keyed construction as
//     JoinSplit, so the normal nullifier set prevents spending the commitment
//     through both the ASP path and the emergency path.
template RageExit(depth, address_bits, pow_bits) {
    signal input chain_id;
    signal input commitment_index;
    signal input burn_address;

    signal input private_key;
    signal input auth_key_hash;
    signal input burn_salt;

    signal output nullifier;

    component chain_id_range = RangeCheck(CHAIN_ID_BITS());
    component index_range = RangeCheck(depth);

    chain_id_range.in <== chain_id;
    index_range.in <== commitment_index;

    component nullifying_key = NullifyingKey();
    component public_key = PublicKey();

    nullifying_key.private_key <== private_key;
    public_key.auth_key_hash <== auth_key_hash;
    public_key.nullifying_key <== nullifying_key.nullifying_key;

    component digest = BurnDigest();
    digest.chain_id <== chain_id;
    digest.public_key <== public_key.public_key;
    digest.burn_salt <== burn_salt;

    component derived_burn_address = AddressFromDigest(address_bits, pow_bits);
    derived_burn_address.enabled <== 1;
    derived_burn_address.digest <== digest.digest;

    derived_burn_address.address === burn_address;

    component nf = Nullifier();
    nf.chain_id <== chain_id;
    nf.commitment_index <== commitment_index;
    nf.nullifying_key <== nullifying_key.nullifying_key;

    nullifier <== nf.nullifier;
}

component main {
    public [
        chain_id,
        commitment_index,
        burn_address
    ]
} = RageExit(
    MERKLE_DEPTH(),
    ADDRESS_BITS(),
    BURN_POW_BITS()
);
