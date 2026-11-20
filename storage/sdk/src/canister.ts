// A zerc20_storage canister, called anonymously.

import { Actor, type ActorSubclass, type Agent, HttpAgent } from '@icp-sdk/core/agent';
import { Principal } from '@icp-sdk/core/principal';
import { DerivedPublicKey } from '@dfinity/vetkeys';
import { idlFactory, type Action, type CanisterError, type Registration, type Result, type Service } from './candid.js';
import { hex } from './crypto.js';
import { REGISTER_POW_BITS, actionsDigest, registerDigest, requiredPowBits, solvePow } from './wire.js';

/** A definite answer from the canister: `Occupied` (the slot holds other data) or `Rejected`. */
export class StorageError extends Error {
  constructor(readonly error: CanisterError) {
    super('Occupied' in error ? `occupied: 0x${hex(error.Occupied)}` : `rejected: ${error.Rejected}`);
  }

  get occupied(): boolean {
    return 'Occupied' in this.error;
  }
}

/** Each request gives up after this, so that one that hangs does not hold its caller forever. A call cut off may still
 * have landed, as one whose connection drops may. */
const TIMEOUT_MS = 30_000;

const withTimeout =
  (f: typeof fetch): typeof fetch =>
  (input, init) => {
    const timeout = AbortSignal.timeout(TIMEOUT_MS);
    return f(input, { ...init, signal: init?.signal ? AbortSignal.any([init.signal, timeout]) : timeout });
  };

export function unwrap<T>(result: Result<T>): T {
  if ('Err' in result) throw new StorageError(result.Err);
  return result.Ok;
}

export class CanisterClient {
  readonly canisterId: Principal;
  /** Queries answered by a single replica: cheap, but only good for spotting news. */
  readonly actor: ActorSubclass<Service>;
  /** Every method as an update call, so the subnet agrees on the answer. */
  readonly replicated: ActorSubclass<Service>;
  #escrowPublicKey?: Promise<DerivedPublicKey>;

  /** A client over HTTP, through `fetch` (the platform's, or an app's that goes through a proxy or Tor). A local replica
   * (an `http://` host on this machine) has its root key fetched; the IC's is built in. A root key fetched from
   * anywhere else would let whoever is on the path forge every certified answer. */
  static async connect(
    host: string,
    canisterId: Principal | string,
    fetch: typeof globalThis.fetch = (input, init) => globalThis.fetch(input, init),
  ): Promise<CanisterClient> {
    const url = new URL(host);
    const local = url.protocol === 'http:' && ['localhost', '127.0.0.1', '[::1]'].includes(url.hostname);
    const agent = await HttpAgent.create({ host, shouldFetchRootKey: local, fetch: withTimeout(fetch) });
    return new CanisterClient(agent, canisterId);
  }

  constructor(agent: Agent, canisterId: Principal | string) {
    this.canisterId = Principal.from(canisterId);
    const config = { agent, canisterId: this.canisterId };
    this.actor = Actor.createActor<Service>(idlFactory, config);
    this.replicated = Actor.createActor<Service>(idlFactory, { ...config, queryStrategy: 'update' });
  }

  /** The key owners IBE-encrypt their escrows with. Fixed for the canister's lifetime. */
  escrowPublicKey(): Promise<DerivedPublicKey> {
    this.#escrowPublicKey ??= this.actor.escrow_public_key().then((r) => DerivedPublicKey.deserialize(unwrap(r)));
    this.#escrowPublicKey.catch(() => (this.#escrowPublicKey = undefined));
    return this.#escrowPublicKey;
  }

  /** `address`'s registration with `notifyKey`, by default its current one: a query, which one replica answers.
   * Unverified: check it with `verifyRegistration`. Call `replicated.registration` where a stale answer matters. */
  async registration(address: Uint8Array, notifyKey?: Uint8Array): Promise<Registration | null> {
    const r = await this.actor.registration(address, notifyKey ? [notifyKey] : []);
    return r[0] ?? null;
  }

  /** Solves the proof of work and registers. An identical registration that is already stored is a
   * no-op, so a call whose outcome is unknown can be repeated. */
  async register(registration: Registration): Promise<void> {
    const nonce = await solvePow(registerDigest(registration), REGISTER_POW_BITS);
    unwrap(await this.actor.register(registration, nonce));
  }

  /** Solves the proof of work and submits the batch. Throws `StorageError` on a definite failure. */
  async submit(actions: Action[]): Promise<void> {
    const nonce = await solvePow(actionsDigest(actions), requiredPowBits(actions));
    unwrap(await this.actor.submit(actions, nonce));
  }
}
