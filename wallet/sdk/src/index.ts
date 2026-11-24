// @zerc20/wallet-sdk: a zERC20 wallet for browsers and Node.
//
//   const wallet = await Wallet.open({ network, walletClient, seed, persist });
//   await wallet.sync();                     // or wallet.autoSync(render)
//   wallet.balances();                       // spendable, and what is pending and why
//   await (await wallet.deposit({ token, amount })).wait();
//   const q = await wallet.fees({ kind: 'send', token, amount });
//   await (await wallet.send({ to: 'zerc20id1…', token, amount, maxFee: q.fee })).wait();
//   const watching = await Wallet.watch({ network, viewKey: wallet.viewKey(), persist }); // elsewhere, spends nothing
//
// Nothing secret leaves the device unencrypted: JoinSplit proofs are made here, a merge's by the merge prover, and the
// attester and the prover get the witness sealed to an enclave whose measurement the wallet checks. Servers are only
// ever asked for what every wallet downloads.

export { accountId, idAccount } from './accountId.js';
export {
  Chain,
  type Reach,
  type Referrer,
  type Refund,
  type Token,
  MAX_REFERRAL_BPS,
  NATIVE,
  UNWRAP_INTENT,
  rpcTransport,
} from './chain.js';
export { type Burn, type BurnCall, type BurnRunner, runBurnsOn } from './core.js';
export { type ErrorCode, WalletError } from './errors.js';
export {
  type AttesterTrust,
  type ChainConfig,
  type Circuit,
  type Network,
  type ProverTrust,
  NITRO_ROOT_SHA256,
  checkNetwork,
  networkFromJson,
} from './network.js';
export { type Payment, PointOfSale, type PosToken, type Sale, type SaleStatus } from './pos.js';
export { accountKey, seedFromSignature } from './seed.js';
export { viewKeyAccount } from './viewKey.js';
export {
  type Activity,
  type Balance,
  type CoinInfo,
  type CoinState,
  type DepositAddressInfo,
  type DepositInfo,
  type DepositStep,
  type FeeQuote,
  type MaxAmount,
  type OpenOptions,
  type Operation,
  type OperationKind,
  type OperationStatus,
  type PendingReason,
  Wallet,
  type WatchOptions,
} from './wallet.js';
