import { expect, test } from 'vitest';
import { NITRO_ROOT_SHA256, type Network, checkNetwork } from '../src/index.js';

const circuit = { wasm: 'https://cdn.example/j.wasm', zkey: 'file:///keys/j.zkey', wasmSha256: '', zkeySha256: '' };
const network = (chain: Partial<Network['chains'][number]>, host = 'https://icp0.io'): Network => ({
  name: 'test',
  storage: { host, canisterId: 'aaaaa-aa' },
  circuits: { joinsplit: circuit, rageexit: circuit },
  chains: [
    {
      chainId: 1n,
      rpcUrls: ['https://rpc.example', 'https://rpc2.example'],
      verifier: '0x0000000000000000000000000000000000000001',
      depositAddressFactory: '0x0000000000000000000000000000000000000002',
      indexer: 'https://indexer.example',
      asp: 'https://asp.example',
      attester: 'https://attester.example',
      attesterTrust: { pcr0: 'ab'.repeat(48), rootSha256: NITRO_ROOT_SHA256 },
      transactRelayer: 'https://relayer.example',
      depositRelayer: 'https://deposits.example',
      ...chain,
    },
  ],
});
const code = (n: Network) => {
  try {
    checkNetwork(n);
  } catch (e) {
    return (e as { code?: string }).code;
  }
};

test('a network passes only with what production needs: https, a pinned Nitro root and a release enclave', () => {
  expect(code(network({}))).toBeUndefined();
  // the local stack: plain HTTP on this machine and a development attester, on the local chain
  const local = {
    chainId: 31337n,
    rpcUrls: ['http://127.0.0.1:8545'],
    indexer: 'http://localhost:3500',
    attesterTrust: { development: true as const },
  };
  expect(code(network(local, 'http://127.0.0.1:4943'))).toBeUndefined();
  expect(code(network({ indexer: 'http://indexer.example' }))).toBe('invalid');
  expect(code(network({ rpcUrls: [] }))).toBe('invalid');
  expect(code(network({ rpcUrls: ['https://rpc.example', 'http://rpc2.example'] }))).toBe('invalid');
  expect(code(network({}, 'http://icp0.io'))).toBe('invalid');
  expect(code(network({ attesterTrust: { development: true } }))).toBe('invalid');
  expect(code(network({ attesterTrust: { pcr0: '00'.repeat(48), rootSha256: NITRO_ROOT_SHA256 } }))).toBe('invalid');
  expect(code(network({ attesterTrust: { pcr0: 'ab'.repeat(48), rootSha256: '00'.repeat(32) } }))).toBe('invalid');
});
