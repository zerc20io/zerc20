// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

/// @notice Cross-boundary consensus constants shared with the ZKP circuits, plus the field-0 packing.
library Protocol {
    uint256 internal constant FIELD_MODULUS =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 internal constant HASH_CHAIN_BOUND = uint256(1) << 248;
    uint256 internal constant HASH_CHAIN_MASK = HASH_CHAIN_BOUND - 1;
    /// @dev Exclusive upper bound for every amount.
    uint256 internal constant AMOUNT_BOUND = HASH_CHAIN_BOUND;
    /// @dev Depth-32 commitment tree.
    uint256 internal constant TREE_SIZE = uint256(1) << 32;
    /// @dev Empty depth-32 Poseidon commitment root.
    uint256 internal constant EMPTY_ROOT =
        21443572485391568159800782191812935835534334817699172242223315142338162256601;

    /// @dev Conventional sentinel for the chain's native asset (1inch, Curve, ERC-7528).
    address internal constant NATIVE = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    uint32 internal constant TRANSFER_TAG = uint32(bytes4(keccak256("Transfer(address,address,uint256)")));
    uint32 internal constant NOTE_HASH_TAG = uint32(bytes4(keccak256("NoteHash(uint256)")));

    /// @dev A JoinSplit's `withdrawIntent` says how its withdrawal is paid out: the EIP-712 struct hash of the
    ///      instruction, reduced into the field. 0 mints zERC20; `Unwrap()` pays the underlying asset instead.
    uint256 internal constant UNWRAP_INTENT = uint256(keccak256(abi.encode(keccak256("Unwrap()")))) % FIELD_MODULUS;

    /// @dev field0 = tag << 32 | tokenId; bits >= 64 must be zero.
    function encode(uint32 tag, uint32 tokenId) internal pure returns (uint256) {
        return (uint256(tag) << 32) | tokenId;
    }

    function decode(uint256 field0) internal pure returns (uint32 tag, uint32 tokenId) {
        // forge-lint: disable-next-line(unsafe-typecast)
        tag = uint32(field0 >> 32);
        // forge-lint: disable-next-line(unsafe-typecast)
        tokenId = uint32(field0);
    }
}
