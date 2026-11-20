import { emptyState } from '@zerc20/storage-sdk';
import { expect, test } from 'vitest';
import type { Ctx } from '../src/context.js';
import { emptyWalletState } from '../src/state.js';
import { storageState } from '../src/sync.js';

test('a wallet saved before its network gained a chain watches that chain in storage too', () => {
  const view = { address: new Uint8Array(20), seed: new Uint8Array(32) };
  const chain = (chainId: bigint) => ({ config: { chainId } });
  const state = emptyWalletState(`0x${'11'.repeat(20)}`);
  state.storage = emptyState(view, [11155111n]);
  const ctx = { view, state, chains: [chain(11155111n), chain(84532n)] } as unknown as Ctx;

  expect(storageState(ctx).chains).toEqual([11155111n, 84532n]);
  expect(state.storage.chains).toEqual([11155111n, 84532n]);
});
