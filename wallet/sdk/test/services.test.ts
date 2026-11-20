import { x25519 } from '@noble/curves/ed25519.js';
import { bytesToHex } from 'viem';
import { beforeAll, expect, test } from 'vitest';
import { Chain } from '../src/chain.js';
import { initCore } from '../src/core.js';
import { type ChainConfig, LOCAL_CHAIN_ID } from '../src/network.js';
import { attest, relay } from '../src/services.js';

const config = {
  chainId: LOCAL_CHAIN_ID,
  rpcUrls: ['https://rpc.example'],
  attester: 'https://attester.example',
  transactRelayer: 'https://relayer.example',
  attesterTrust: { development: true },
} as unknown as ChainConfig;
/** What the attester answers a statement with. */
let answer = new Response();
const publicKey = bytesToHex(x25519.getPublicKey(new Uint8Array(32).fill(9)));
/** The servers, asked through the app's fetch rather than the platform's. Like a platform's, it throws when called as
 * an object's method. */
const chain = new Chain(config, {
  fetch: async function (this: unknown, url) {
    if (this !== undefined) throw new TypeError('Illegal invocation');
    return String(url).endsWith('/attestation') ? Response.json({ publicKey, attestation: null }) : answer.clone();
  } as typeof fetch,
});

beforeAll(() => initCore());

test('a recipient that fails screening fails the attestation for good, a quota or an outage only for now', async () => {
  const cases = [
    [403, 'the withdrawal recipient fails screening', 'recipient-refused'],
    [429, 'screenings used up for now', 'unavailable'],
    [503, 'the enclave is unavailable', 'unavailable'],
    [400, 'commitmentRoot is not a root the indexer derived; retry once it has', 'unavailable'],
    [400, 'the witness does not prove the statement', 'invalid'],
  ] as const;
  for (const [status, body, code] of cases) {
    answer = new Response(body, { status });
    await expect(attest(chain, {}, '{}')).rejects.toMatchObject({ code });
  }
});

test('a relay refused for a nullifier spent already says so, whatever else the relayer refuses', async () => {
  const cases = [
    // as alloy words the verifier's revert in estimating it
    [
      'server returned an error response: error code 3: execution reverted: custom error 0xdc215c0a: 0dc3, data: "0xdc215c0a0dc3"',
      true,
    ],
    ['server returned an error response: error code 3: execution reverted, data: "0x799ab77c0001"', false],
    ['pays 1, the fee is 2', false],
  ] as const;
  for (const [body, spent] of cases) {
    answer = new Response(body, { status: 400 });
    expect(await relay(chain, {})).toEqual({ reverted: body, spent });
  }
});
