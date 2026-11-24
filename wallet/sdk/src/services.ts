// The attester, the merge prover and the relayers. Each sees only what it must: the attester's and the prover's hosts
// see the public statement and a witness sealed to their enclave, the transact-relayer a finished request, the
// deposit-relayer a burn address.

import { type Address, type Hex, bytesToHex, getAddress, hexToBytes, toFunctionSelector, zeroAddress } from 'viem';
import { type Chain, type Referrer, type Refund, factoryArgs } from './chain.js';
import { core } from './core.js';
import { WalletError, fail } from './errors.js';
import { LOCAL_CHAIN_ID, type Network, type ProverTrust, loopback } from './network.js';

/** A transact witness is sealed padded to this, and a merge's to `MERGE_PAD` per input, so its size does not leak the
 * amounts' digits (`backend/attester/README.md`). */
const WITNESS_PAD = 16 * 1024;
const MERGE_PAD = 8 * 1024;

const json = (v: unknown): string => JSON.stringify(v, (_, x: unknown) => (typeof x === 'bigint' ? x.toString() : x));

/** `url`'s answer, asked through `chain`'s fetch. */
async function call<T>(
  chain: Chain,
  url: string,
  init?: RequestInit & { timeoutMs?: number },
): Promise<{ status: number; body: T | string }> {
  let res: Response;
  try {
    res = await chain.fetch(url, { ...init, signal: AbortSignal.timeout(init?.timeoutMs ?? 30_000) });
  } catch (e) {
    return fail('unavailable', `${url}: ${(e as Error).message}`);
  }
  const text = await res.text();
  if (!res.ok) return { status: res.status, body: text };
  return { status: res.status, body: JSON.parse(text) as T };
}

const post = <T>(chain: Chain, url: string, body: unknown, timeoutMs?: number) =>
  call<T>(chain, url, { method: 'POST', headers: { 'content-type': 'application/json' }, body: json(body), timeoutMs });

const base64 = (s: string): Uint8Array => Uint8Array.from(atob(s), (c) => c.charCodeAt(0));

/** The key the attester's enclave opens witnesses with, once its attestation checks out. */
export const attesterKey = (chain: Chain): Promise<Uint8Array> =>
  enclaveKey(chain, `${chain.config.attester}/attestation`, chain.config.attesterTrust, 'attester');

/** The key an enclave (the attester's, the merge prover's) opens what is sealed to it with, from `url`, once its
 * attestation document checks out against `trust`; a local merge prover's, as it names it. */
export async function enclaveKey(chain: Chain, url: string, trust: ProverTrust, what: string): Promise<Uint8Array> {
  // before anything is asked of it: off this machine, a server with no document is a host that would read the witness,
  // whatever the flag says
  if ('local' in trust && (trust.local !== true || !loopback(url)))
    return fail('attester-unverified', `a local ${what} off this machine`);
  const r = await call<{ publicKey: Hex; attestation: string | null }>(chain, url);
  if (typeof r.body === 'string') return fail('unavailable', `${what}: ${r.body}`);
  if ('local' in trust) return hexToBytes(r.body.publicKey);
  if ('development' in trust) {
    // its host would read everything sealed to it, every input's opening included: a local chain only, whatever the
    // flag says
    if (trust.development !== true || chain.chainId !== LOCAL_CHAIN_ID)
      return fail('attester-unverified', `a development ${what} off the local chain`);
    return hexToBytes(r.body.publicKey);
  }
  if (!r.body.attestation) return fail('attester-unverified', `the ${what} sent no attestation document`);
  try {
    // from the document, never the `publicKey` beside it
    return core.verifyAttestation(
      base64(r.body.attestation),
      trust.rootSha256,
      trust.pcr0,
      BigInt(Math.floor(Date.now() / 1000)),
    );
  } catch (e) {
    return fail('attester-unverified', `the ${what}'s enclave does not check out: ${(e as Error).message}`);
  }
}

/** The attester's signature over `statement`, once its enclave has checked `witness` (JSON): a JoinSplit's, or with
 * `inputs`, a merge's of that many inputs. */
export async function attest(chain: Chain, statement: object, witness: string, inputs?: number): Promise<Hex> {
  const [path, pad] = inputs === undefined ? ['transact', WITNESS_PAD] : ['merge', MERGE_PAD * inputs];
  for (let attempt = 0; ; attempt++) {
    const sealed = bytesToHex(core.sealWitness(await attesterKey(chain), witness, pad));
    const r = await post<{ attestation: Hex }>(
      chain,
      `${chain.config.attester}/${path}`,
      { statement, witness: sealed },
      60_000,
    );
    if (typeof r.body !== 'string') return r.body.attestation;
    // the enclave restarted with a new key between the fetch and the request
    if (r.body.includes('fetch /attestation again') && attempt === 0) continue;
    // a screening's verdict: asking again gets the same, and spends the notes' screenings for nothing
    if (r.status === 403) return fail('recipient-refused', `attester: ${r.body}`);
    // a root its indexer has not derived yet is a 400 too, but one that passes
    const later = r.status !== 400 || r.body.includes('retry once');
    return fail(later ? 'unavailable' : 'invalid', `attester: ${r.body}`);
  }
}

export interface RelayerFees {
  relayer: Address;
  /** The relayer's note key, which owns its fee notes whatever their token. */
  publicKey: Hex;
  fees: Map<number, { fee: bigint }>;
}

export async function relayerFees(chain: Chain): Promise<RelayerFees> {
  const r = await call<{ relayer: Address; publicKey: Hex; fees: Record<string, { fee: Hex }> }>(
    chain,
    `${chain.config.transactRelayer}/fee`,
  );
  if (typeof r.body === 'string') return fail('unavailable', `transact-relayer: ${r.body}`);
  const fees = new Map(Object.entries(r.body.fees).map(([t, f]) => [Number(t), { fee: BigInt(f.fee) }]));
  return { relayer: r.body.relayer, publicKey: r.body.publicKey, fees };
}

export interface Relayed {
  txHash: Hex;
  /** The block it was mined in. */
  block: number;
  noteIndex1: number | null;
  noteIndex2: number | null;
}

/** What `relay` reports while the relayer is relaying a request with the same nullifiers: the request already there
 * gets the answer, and one after it finds the transaction landed. */
export class Relaying extends WalletError {}

/** A request the relayer refused, as the call reverts or by its own rules. `spent`: the verifier's revert says an input
 * is spent on chain already, which the indexer may not show yet. */
export interface Reverted {
  reverted: string;
  spent: boolean;
}

/** The revert data of the verifier's `NullifierAlreadyUsed`, which a relayer's answer quotes. */
const NULLIFIER_USED = toFunctionSelector('NullifierAlreadyUsed(uint256)');

/** Has the relayer submit `request`. A 400 means the call reverts, which includes "already landed". */
export const relay = (
  chain: Chain,
  request: object,
  feeNote?: { value: bigint; salt: Hex },
): Promise<Relayed | Reverted> =>
  relayed<Relayed>(chain, `${chain.config.transactRelayer}/transact`, { request, feeNote });

/** Has the relayer submit a merge's `request`, as `relay` does a JoinSplit's. Answers the merged note's index. */
export const relayMerge = (
  chain: Chain,
  request: object,
): Promise<{ txHash: Hex; block: number; noteIndex: number | null } | Reverted> =>
  relayed(chain, `${chain.config.transactRelayer}/merge`, { request });

async function relayed<T>(chain: Chain, url: string, body: object): Promise<T | Reverted> {
  // the relayer answers once mined, after fee bumping if need be. Without an answer it may have sent it all the same:
  // the same request goes again next sync, and lands at most once
  const r = await post<T>(chain, url, body, 15 * 60_000);
  if (typeof r.body !== 'string') return r.body;
  if (r.status === 400) return { reverted: r.body, spent: r.body.toLowerCase().includes(NULLIFIER_USED) };
  if (r.status === 409) throw new Relaying('unavailable', `transact-relayer: ${r.body}`);
  return fail('unavailable', `transact-relayer: HTTP ${r.status}: ${r.body}`);
}

export type MergeProver = NonNullable<Network['mergeProver']>;

/** Sends a merge's witness (JSON, of `inputs` inputs) sealed to the merge prover's enclave, to prove `statement` (the
 * attester's `Merge`). Proving takes minutes: `proofOf` tells when it is done. */
export async function requestProof(
  chain: Chain,
  p: MergeProver,
  statement: object,
  witness: string,
  inputs: number,
): Promise<void> {
  const key = await enclaveKey(chain, `${p.url}/enclave`, p.trust, 'merge prover');
  const sealed = bytesToHex(core.sealMergeWitness(key, witness, MERGE_PAD * inputs));
  const r = await post<{ status: string }>(chain, `${p.url}/proofs`, { statement, witness: sealed }, 60_000);
  if (typeof r.body === 'string') fail(r.status === 400 ? 'invalid' : 'unavailable', `merge prover: ${r.body}`);
}

/** Where the proof of the merge that outputs `noteHash` stands, asked through `chain`'s fetch: `null` when the prover
 * does not have it (it never did, or lost it in a restart), so it is to be sent again. `proof` is the ABI-encoded
 * `NovaDeciderProof`. */
export async function proofOf(
  chain: Chain,
  p: MergeProver,
  noteHash: Hex,
): Promise<{ status: 'queued' | 'proving' | 'done' | 'failed'; proof?: Hex; error?: string } | null> {
  const r = await call<{ status: 'queued' | 'proving' | 'done' | 'failed'; proof?: Hex; error?: string }>(
    chain,
    `${p.url}/proofs/${noteHash}`,
  );
  if (r.status === 404) return null;
  if (typeof r.body === 'string') return fail('unavailable', `merge prover: ${r.body}`);
  return r.body;
}

/** Has the deposit relayer watch `depositAddress` for another 7 days, at the fee it was registered with, which the
 * address fixes: the fee the relayer names. */
export async function rewatchDeposit(chain: Chain, depositAddress: Address): Promise<bigint> {
  const r = await post<{ fee: Hex }>(chain, `${chain.config.depositRelayer}/rewatch`, { depositAddress });
  if (typeof r.body === 'string') return fail('unavailable', `deposit-relayer: ${r.body}`);
  return BigInt(r.body.fee);
}

/** A deposit address that flushes whatever reaches it into `burnAddress`, less `fee` paid to `feeRecipient` and the
 * referrer's share of the rest each time; refunds go as `refund` says. What the relayer says is checked against the
 * factory: an address of its own would take the funds, and the fee it names is the one the address takes. The address
 * comes back checksummed, as every other address the SDK gives does: the relayer writes it in lower case. */
export async function registerDeposit(
  chain: Chain,
  token: Address,
  burnAddress: Hex,
  refund: Refund,
  referrer: Referrer = { address: zeroAddress, bps: 0 },
): Promise<{ depositAddress: Address; feeRecipient: Address; fee: bigint }> {
  const r = await post<{ depositAddress: Address; feeRecipient: Address; fee: Hex }>(
    chain,
    `${chain.config.depositRelayer}/register`,
    {
      token,
      burnAddress,
      ...('address' in refund ? { refundAddress: refund.address } : { refundSigner: refund.signer }),
      referrer: referrer.address,
      referralBps: referrer.bps,
    },
  );
  if (typeof r.body === 'string') return fail('unavailable', `deposit-relayer: ${r.body}`);
  const { depositAddress, feeRecipient } = r.body;
  const fee = BigInt(r.body.fee);
  // no balance exceeds such a fee, and storage holds values below 2^248 only
  if (fee >= 1n << 248n) fail('unavailable', `deposit-relayer: a fee of ${fee}`);
  const expected = await chain.predictDepositAddress(
    factoryArgs(token, burnAddress, refund, feeRecipient, fee, referrer.address, referrer.bps),
  );
  if (depositAddress.toLowerCase() !== expected.toLowerCase())
    fail('indexer-mismatch', `the deposit relayer gave ${depositAddress}, not the factory's ${expected}`);
  return { depositAddress: getAddress(depositAddress), feeRecipient, fee };
}
