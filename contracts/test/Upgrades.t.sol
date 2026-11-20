// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Initializable} from "@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import {UUPSUpgradeable} from "@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol";
import {Blocklist} from "../src/Blocklist.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {DepositAddressFactory} from "../src/DepositAddress.sol";
import {Verifier} from "../src/Verifier.sol";
import {ZERC20} from "../src/ZERC20.sol";
import {ZERC20Factory} from "../src/ZERC20Factory.sol";
import {IMergeDeciderVerifier, IRootDeciderVerifier} from "../src/interfaces/INovaDeciderVerifier.sol";
import {ITokenRegistry} from "../src/interfaces/ITokenRegistry.sol";
import {IJoinSplitVerifier, IRageExitVerifier} from "../src/interfaces/IPrivateProofVerifier.sol";
import {Protocol} from "../src/libs/Protocol.sol";
import {ProtocolTest} from "./utils/ProtocolTest.sol";

contract UpgradesTest is ProtocolTest {
    function _proxies() internal view returns (address[5] memory) {
        return [address(blocklist), address(ledger), address(verifier), address(factory), address(deposits)];
    }

    // Arguments are read before `expectRevert`, which applies to the very next call.

    function test_implementationsCannotBeInitialized() public {
        bytes4 refused = Initializable.InvalidInitialization.selector;
        IRootDeciderVerifier root = ledger.rootVerifier();
        vm.expectRevert(refused);
        Blocklist(_implementation(address(blocklist))).initialize(alice);
        vm.expectRevert(refused);
        CommitmentLedger(_implementation(address(ledger))).initialize(alice, factory, root);
        vm.expectRevert(refused);
        Verifier(_implementation(address(verifier)))
            .initialize(
                alice,
                factory,
                ledger,
                IJoinSplitVerifier(address(1)),
                IRageExitVerifier(address(1)),
                IMergeDeciderVerifier(address(1)),
                alice
            );
        vm.expectRevert(refused);
        ZERC20Factory(_implementation(address(factory)))
            .initialize(alice, ledger, address(verifier), blocklist, tokenImpl);
        vm.expectRevert(refused);
        DepositAddressFactory(_implementation(address(deposits))).initialize(alice, factory);
        vm.expectRevert(refused);
        ZERC20(payable(tokenImpl)).initialize("x", "x", 18, 1, address(1), ledger, address(1), blocklist);
    }

    function test_proxiesCannotBeInitializedASecondTime() public {
        bytes4 refused = Initializable.InvalidInitialization.selector;
        IRootDeciderVerifier root = ledger.rootVerifier();
        IJoinSplitVerifier joinSplit = verifier.joinSplitVerifier();
        IRageExitVerifier rageExit = verifier.rageExitVerifier();
        IMergeDeciderVerifier merge = verifier.mergeVerifier();
        vm.expectRevert(refused);
        blocklist.initialize(alice);
        vm.expectRevert(refused);
        ledger.initialize(alice, factory, root);
        vm.expectRevert(refused);
        verifier.initialize(alice, factory, ledger, joinSplit, rageExit, merge, alice);
        vm.expectRevert(refused);
        factory.initialize(alice, ledger, address(verifier), blocklist, tokenImpl);
        vm.expectRevert(refused);
        deposits.initialize(alice, ITokenRegistry(address(factory)));
        vm.expectRevert(refused);
        token.initialize("x", "x", 18, 1, address(1), ledger, address(1), blocklist);
    }

    function test_storageLivesInTheErc7201Namespace() public view {
        // The first struct field sits at the namespace slot; the default slot 0 stays empty.
        assertEq(
            vm.load(address(factory), _erc7201("zerc20.storage.ZERC20Factory")),
            bytes32(uint256(uint160(address(ledger))))
        );
        assertEq(
            vm.load(address(verifier), _erc7201("zerc20.storage.Verifier")), bytes32(uint256(uint160(address(factory))))
        );
        assertEq(
            vm.load(address(ledger), _erc7201("zerc20.storage.CommitmentLedger")),
            bytes32(uint256(uint160(address(factory))))
        );
        assertEq(
            vm.load(address(deposits), _erc7201("zerc20.storage.DepositAddressFactory")),
            bytes32(uint256(uint160(address(factory))))
        );
        // underlyingAsset, tokenId (1) and decimals (18) are packed into the first slot
        assertEq(
            vm.load(address(token), _erc7201("zerc20.storage.ZERC20")),
            bytes32(uint256(uint160(Protocol.NATIVE)) | (uint256(1) << 160) | (uint256(18) << 192))
        );
        address[5] memory proxies = _proxies();
        for (uint256 i; i < proxies.length; ++i) {
            assertEq(vm.load(proxies[i], bytes32(0)), bytes32(0));
        }
        assertEq(vm.load(address(token), bytes32(0)), bytes32(0));
    }

    function test_proxiesUpgradeOnlyByTheOwnerAndKeepTheirState() public {
        _setBlocked(carol, true);
        _wrap(alice, 1 ether, bob); // ledger index 1, bob balance 1 ether
        address deposit = deposits.predict(token, address(0xB0E), alice, address(0), address(0xFEE), 1, address(0), 0);

        address[5] memory proxies = _proxies();
        address[5] memory newImpls = [
            address(new Blocklist()),
            address(new CommitmentLedger()),
            address(new Verifier()),
            address(new ZERC20Factory()),
            address(new DepositAddressFactory())
        ];
        for (uint256 i; i < proxies.length; ++i) {
            vm.prank(alice);
            vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
            UUPSUpgradeable(proxies[i]).upgradeToAndCall(newImpls[i], "");

            UUPSUpgradeable(proxies[i]).upgradeToAndCall(newImpls[i], "");
            assertEq(_implementation(proxies[i]), newImpls[i]);
        }
        // state written before the upgrades is intact and the system still works
        assertTrue(blocklist.isBlocked(carol));
        assertEq(ledger.nextIndex(), 1);
        assertEq(factory.tokenById(1), address(token));
        assertTrue(verifier.aspRootAccepted(1));
        // a deposit address derives from the clone implementation, which an upgrade leaves in place
        assertEq(deposits.predict(token, address(0xB0E), alice, address(0), address(0xFEE), 1, address(0), 0), deposit);
        verifier.transact(_signals(1 ether, bob, 80));
        assertEq(token.balanceOf(bob), 2 ether);
    }
}
