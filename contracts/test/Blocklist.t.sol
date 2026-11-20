// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Vm} from "forge-std/Vm.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import {Blocklist} from "../src/Blocklist.sol";
import {ProtocolTest} from "./utils/ProtocolTest.sol";

contract BlocklistTest is ProtocolTest {
    function _pair() internal view returns (address[] memory list) {
        list = new address[](2);
        list[0] = alice;
        list[1] = bob;
    }

    function test_setBlockedMarksAndClearsEveryAccountInTheBatch() public {
        assertFalse(blocklist.isBlocked(alice));
        vm.expectEmit(address(blocklist));
        emit Blocklist.BlocklistUpdated(alice, true);
        vm.expectEmit(address(blocklist));
        emit Blocklist.BlocklistUpdated(bob, true);
        blocklist.setBlocked(_pair(), true);
        assertTrue(blocklist.isBlocked(alice));
        assertTrue(blocklist.isBlocked(bob));

        blocklist.setBlocked(_pair(), false);
        assertFalse(blocklist.isBlocked(alice));
        assertFalse(blocklist.isBlocked(bob));
    }

    function test_anUnchangedWriteStillEmitsSoTheLogReplays() public {
        _setBlocked(alice, true);
        vm.recordLogs();
        _setBlocked(alice, true);
        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics[0], Blocklist.BlocklistUpdated.selector);
        assertTrue(blocklist.isBlocked(alice));
    }

    function test_aZeroAddressRevertsTheWholeBatch() public {
        address[] memory list = new address[](2);
        list[0] = alice;
        vm.expectRevert(Blocklist.ZeroAddress.selector);
        blocklist.setBlocked(list, true);
        assertFalse(blocklist.isBlocked(alice));
    }

    function test_onlyTheOwnerEditsTheList() public {
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        blocklist.setBlocked(_pair(), true);
    }
}
