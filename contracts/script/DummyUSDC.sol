// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";

/// @dev A worthless USDC for testnets (Deploy.s.sol with DUMMY_USDC): 6 decimals, and anyone may mint.
contract DummyUSDC is ERC20 {
    constructor() ERC20("Dummy USD Coin", "USDC") {}

    function decimals() public pure override returns (uint8) {
        return 6;
    }

    function mint(address to, uint256 amount) external {
        _mint(to, amount);
    }
}
