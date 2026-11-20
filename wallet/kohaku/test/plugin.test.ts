import { type Host, UnsupportedChainError } from '@kohaku-eth/plugins';
import type { Network } from '@zerc20/wallet-sdk';
import { expect, test } from 'vitest';
import { createZerc20Plugin } from '../src/index.js';

test('a host on a chain the network has no deployment on is refused before anything is read or derived', async () => {
  // only the chain id is there: the plugin would throw on anything else it touched first
  const host = { provider: { getChainId: async () => 999n } } as unknown as Host;
  const network = { chains: [{ chainId: 1n }] } as Network;
  await expect(createZerc20Plugin(host, { network, accountIndex: 0 })).rejects.toBeInstanceOf(UnsupportedChainError);
});
