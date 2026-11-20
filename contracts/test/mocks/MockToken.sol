// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract MockToken is ERC20 {
    uint8 private immutable DECIMALS;

    constructor(uint8 decimals_) ERC20("Mock", "MCK") {
        DECIMALS = decimals_;
    }

    function decimals() public view override returns (uint8) {
        return DECIMALS;
    }
}
