// Where a wallet finds everything: per chain, its contracts, servers and artifacts. Apps pass one of these to
// `Wallet.open`; nothing here is secret.

import type { Address } from 'viem';
import { fail } from './errors.js';

/** A proving key set: the circuit's wasm and zkey, pinned by SHA-256 (from the setup's `setup.json`). */
export interface Circuit {
  wasm: string;
  zkey: string;
  wasmSha256: string;
  zkeySha256: string;
}

/** How to trust an enclave's key: the attester's, or the merge prover's. */
export type AttesterTrust =
  /** A Nitro Enclave: the document must chain to the root with this SHA-256 and measure this PCR0 (hex). */
  | { pcr0: string; rootSha256: string }
  /** A development attester, which has no document: its key is taken at its word. Never on a real network. */
  | { development: true };

/** How to trust the merge prover: its enclave's key, or a prover on this machine. */
export type ProverTrust =
  | AttesterTrust
  /** A prover at a loopback address, which has no document: its key is taken at its word, as the machine it runs on is
   * the one that holds the witness already. On any network. */
  | { local: true };

/** The AWS Nitro Enclaves root certificate (G1), SHA-256 over its DER. */
export const NITRO_ROOT_SHA256 = '641a0321a3e244efe456463195d606317ed7cdcc3c1756e09893f3c68f79bb5b';

export interface ChainConfig {
  chainId: bigint;
  /** The chain's RPCs, in order of preference, for every read and every wait on a receipt, never the wallet's own: a
   * call goes on to the next one when one fails it, and one that fails a call without answering is tried after the
   * others for five minutes, so one that a resolver, a firewall or an outage keeps from a device stops nothing. */
  rpcUrls: string[];
  verifier: Address;
  depositAddressFactory: Address;
  indexer: string;
  asp: string;
  attester: string;
  attesterTrust: AttesterTrust;
  transactRelayer: string;
  depositRelayer: string;
  /** The native currency, which its native zERC20 is named after; ETH if absent. For a chain an app does not know. */
  nativeCurrency?: { name: string; symbol: string };
}

export interface Network {
  name: string;
  chains: ChainConfig[];
  /** The note storage canister on the Internet Computer. */
  storage: { host: string; canisterId: string };
  circuits: { joinsplit: Circuit; rageexit: Circuit };
  /** The merge prover (`backend/merge-prover`), one shared by every chain, and how to trust it: it sees each merge's
   * witness while it proves it. Without it the wallet cannot consolidate. */
  mergeProver?: { url: string; trust: ProverTrust };
}

/** A `Network` from JSON, where chain ids are strings (JSON has no bigints), as scripts/dev-stack.sh writes it. */
export function networkFromJson(json: string): Network {
  const n = JSON.parse(json) as Network & { chains: (ChainConfig & { chainId: string })[] };
  return { ...n, chains: n.chains.map((c) => ({ ...c, chainId: BigInt(c.chainId) })) };
}

/** The local chain development settings are for. */
export const LOCAL_CHAIN_ID = 31337n;

/** Whether `url` is on this machine. */
export const loopback = (url: string) => ['localhost', '127.0.0.1', '[::1]'].includes(new URL(url).hostname);

/** Throws on settings that only a local development network may have: servers over plain HTTP (anyone on the path
 * could swap a deposit address or a fee), a development attester or merge prover (its host would read every witness,
 * the openings of what it spends included), or a Nitro trust that does not pin the AWS root and a real enclave. A
 * local merge prover passes on any network, at a loopback address only: off this machine it is a host like any other. */
export function checkNetwork(n: Network): void {
  const bad = (what: string) => fail('invalid', `network ${n.name}: ${what}`);
  const servers = (urls: string[]) => {
    for (const u of urls) if (new URL(u).protocol !== 'https:' && !loopback(u)) bad(`${u} is not https`);
  };
  servers([n.storage.host]);
  // artifacts are pinned by SHA-256, and Node reads them from disk
  for (const c of [n.circuits.joinsplit, n.circuits.rageexit]) {
    for (const u of [c.wasm, c.zkey]) if (!u.startsWith('file:')) servers([u]);
  }
  const trusted = (chains: ChainConfig[], what: string, t: AttesterTrust) => {
    if ('development' in t) {
      for (const c of chains) if (c.chainId !== LOCAL_CHAIN_ID) bad(`a development ${what} on chain ${c.chainId}`);
    } else if ('pcr0' in t) {
      if (t.rootSha256.toLowerCase() !== NITRO_ROOT_SHA256) bad(`the ${what} trust does not pin the AWS Nitro root`);
      // a debug enclave measures all zeros
      const pcr0 = t.pcr0.replace(/^0x/i, '');
      if (!/^[0-9a-f]{96}$/i.test(pcr0) || /^0+$/.test(pcr0)) bad(`PCR0 ${t.pcr0} is not a release enclave's`);
    } else {
      // JSON may say anything: an attester marked local is not one this check passes
      bad(`the ${what} trust names no enclave`);
    }
  };
  for (const c of n.chains) {
    if (!c.rpcUrls.length) bad(`chain ${c.chainId} names no RPC`);
    servers([...c.rpcUrls, c.indexer, c.asp, c.attester, c.transactRelayer, c.depositRelayer]);
    trusted([c], 'attester', c.attesterTrust);
  }
  if (n.mergeProver) {
    const { url, trust } = n.mergeProver;
    servers([url]);
    if (!('local' in trust)) trusted(n.chains, 'merge prover', trust);
    else if (!loopback(url)) bad(`a local merge prover at ${url}, off this machine`);
  }
}
