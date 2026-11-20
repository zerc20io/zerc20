//! The contract calls the relayer makes, declared inline so it needs no forge build.
// sol! gives `predict` and `flush` a method taking each of their eight arguments
#![allow(clippy::too_many_arguments)]
use alloy::sol;

sol! {
    #[sol(rpc)]
    interface IDepositAddressFactory {
        function registry() external view returns (address);
        function predict(address token, address burnAddress, address refundAddress, address refundSigner, address feeRecipient, uint256 fee, address referrer, uint16 referralBps) external view returns (address);
        function flush(address token, address burnAddress, address refundAddress, address refundSigner, address feeRecipient, uint256 fee, address referrer, uint16 referralBps) external returns (address);
    }
    interface IERC20 {
        function balanceOf(address account) external view returns (uint256);
    }
    interface IMulticall3 {
        function getEthBalance(address addr) external view returns (uint256);
    }
}
