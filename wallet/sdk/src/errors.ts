// What can go wrong, by code, so that an app can tell the user what to do.

import { BaseError, UserRejectedRequestError } from 'viem';
import type { CoinInfo } from './wallet.js';

export type ErrorCode =
  /** Not enough value for the amount and its fees, even counting what is still settling. */
  | 'insufficient-funds'
  /** No single JoinSplit pays it, but merging the spendable notes and deposits first would: `consolidate`, then pay.
   * `fees({ kind: 'consolidate' })` tells how many rounds that takes. */
  | 'needs-consolidation'
  /** What is spendable now does not pay it, but notes or deposits are still settling (screening, awaiting
   * a root, or the change of an operation in flight): pay again once `balances()` shows them spendable. The error's
   * `waitsOn` tells which coin, where that is known. */
  | 'funds-settling'
  /** The fees are above the `maxFee` the caller allowed. */
  | 'fee-too-high'
  /** Another device of this wallet spent a note or deposit the operation was spending, first: each device locks its
   * inputs in its own state. The operation cannot land and paid nothing: pay again. */
  | 'spent-elsewhere'
  /** The address never registered for private payments: pay it publicly or ask for a receive code. */
  | 'recipient-not-registered'
  /** The withdrawal's recipient (or a merge's fee recipient) fails the attester's AML screening: withdraw elsewhere. */
  | 'recipient-refused'
  /** A contract account: it cannot sign the messages a wallet needs. */
  | 'unsupported-account'
  /** The user declined a signature or a transaction in their wallet. */
  | 'user-rejected'
  /** The operation was cancelled (`cancel()`) before anything went to the relayer: it paid nothing. */
  | 'cancelled'
  /** The wallet is open in another tab or window: close it there (`close()`), or open it here with `take`. */
  | 'wallet-in-use'
  /** Another tab or window took this wallet (`taken`): open it again with `take` to take it back. */
  | 'wallet-taken'
  /** This wallet watches its account by its view key (`Wallet.watch`): it spends and writes nothing. */
  | 'read-only'
  /** This wallet object was closed (`close()`): open the wallet again to go on. */
  | 'wallet-closed'
  /** A server answered something that does not match the chain. */
  | 'indexer-mismatch'
  /** The attester's (or the merge prover's) enclave did not prove it is the published release. */
  | 'attester-unverified'
  /** A service did not answer, or refused. The operation can be resumed. */
  | 'unavailable'
  /** Bad input from the caller. */
  | 'invalid';

export class WalletError extends Error {
  constructor(
    readonly code: ErrorCode,
    message: string,
    /** For `funds-settling`, the coin on its way whose turning spendable should let it pay: when, by its `readyBy`,
     * and why, by its `state`. Null where it may wait on something with no estimate (a halted root, a note not
     * confirmed yet, an operation in flight), or where what is on its way does not pay it either. */
    readonly waitsOn: CoinInfo | null = null,
  ) {
    super(message);
    this.name = 'WalletError';
  }
}

export const fail = (code: ErrorCode, message: string): never => {
  throw new WalletError(code, message);
};

/** Whether `e` fails the operation it stops: only what trying again cannot change does. A server or an RPC that does
 * not answer (any error that is not the wallet's own), or answers what the chain does not show yet, is tried again. */
export const failsOperation = (e: unknown): e is WalletError =>
  e instanceof WalletError && e.code !== 'unavailable' && e.code !== 'indexer-mismatch';

const declined = (e: unknown) =>
  e instanceof UserRejectedRequestError || (e as { code?: number } | null)?.code === 4001;

/** Maps a declined wallet prompt to `user-rejected`, also where viem wraps it (a transaction's, in an execution error). */
export async function guard<T>(p: Promise<T>): Promise<T> {
  try {
    return await p;
  } catch (e) {
    if (declined(e) || (e instanceof BaseError && e.walk(declined)))
      throw new WalletError('user-rejected', 'declined in the wallet');
    throw e;
  }
}
