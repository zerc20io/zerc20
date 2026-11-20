// @zerc20/kohaku-plugin: zERC20 as a Kohaku privacy plugin. A wallet built on @kohaku-eth/plugins shields into zERC20,
// pays privately and unshields through the host it already has, as it does with the other protocols.
//
//   const plugin = await createZerc20Plugin(host, { network: networkFromJson(json), accountIndex: 0 });
//   const { txns } = await plugin.prepareShield({ asset: { __type: 'erc20', contract: usdc }, amount }); // the host signs
//   const op = await plugin.prepareTransfer({ asset, amount }, 'zerc20id1…');
//   await createZerc20Broadcaster(plugin).broadcast(op);
//
// One plugin is one zERC20 account on the chain of the host's provider: Kohaku gives a plugin one provider, and the
// account's wallet on each chain keeps a state of its own, so a host opens one plugin per chain, side by side. Every
// chain read goes through that provider and every server request through the host's `network.fetch`, so a host's proxy
// or Tor covers the relayer, the attester and the storage canister too.

import {
  type AssetAmount,
  type ERC20AssetId,
  type Host,
  InsufficientBalanceError,
  InvalidAddressError,
  PluginError,
  type PluginInstance,
  type PrivateOperation,
  type PublicOperation,
  type UnshieldOptions,
  UnsupportedAssetError,
  UnsupportedChainError,
  scopeKeystore,
} from '@kohaku-eth/plugins';
import type { Broadcaster } from '@kohaku-eth/plugins/broadcaster';
import { base64 } from '@scure/base';
import { type Network, type Token, Wallet, WalletError, accountId, accountKey } from '@zerc20/wallet-sdk';
import { type Address, type EIP1193RequestFn, type Hex, custom, hexToBytes, isAddress, isAddressEqual } from 'viem';
import { privateKeyToAccount } from 'viem/accounts';

/** The keystore subtree zERC20 keys come from ("ze" in ASCII as the purpose, as Kohaku's own plugins name theirs): the
 * plugin derives nothing outside it. */
export const ZERC20_KEYSTORE_PREFIX = "m/31333'/1'";

export interface Zerc20PluginParameters {
  /** The zERC20 deployment, as `networkFromJson` reads its network.json. */
  network: Network;
  /** Which account of the keystore's: each index is an account of its own. */
  accountIndex: number;
  /** Where an account with no saved state starts looking on chain: the block its key was first used at, or roughly
   * when. Without it, an account that registered before is looked for from the chain's start, and a new one from now. */
  birthday?: bigint | Date;
}

/** An amount of a token of the plugin's chain, named by its underlying ERC20 (ETH as `0xeeee…eeee`, as Kohaku's other
 * plugins name it), which a shield wraps and an unshield pays out, or by the zERC20 itself, which moves as it is. */
export type Zerc20AssetAmount<Tag extends string | undefined = undefined> = AssetAmount<ERC20AssetId, bigint, Tag>;

/** The transactions a shield takes, for the host to sign and send in order before it prepares another shield of the same
 * asset: an ERC20's approval of the amount first, which a later one would replace, then the wrap. */
export interface Zerc20PublicOperation extends PublicOperation {
  txns: { to: Address; data: Hex; value: bigint }[];
}

/** A payment or a withdrawal as quoted: nothing is spent until a broadcaster sends it. */
export interface Zerc20PrivateOperation extends PrivateOperation {
  kind: 'send' | 'withdraw';
  token: Token;
  /** A send's recipient: a zERC20 ID, an address that opened a zERC20 wallet, or a receive code. A withdrawal's: any
   * address. */
  to: string;
  amount: bigint;
  /** The fee quoted, the most the payment may cost on top of `amount`. */
  maxFee: bigint;
  /** A withdrawal's payout in the underlying asset rather than the zERC20. */
  unwrap: boolean;
}

export type Zerc20Instance = PluginInstance<
  string,
  {
    features: { prepareShield: true; prepareTransfer: true; prepareUnshield: true };
    assetAmounts: {
      input: Zerc20AssetAmount;
      internal: Zerc20AssetAmount;
      output: Zerc20AssetAmount;
      /** Each asset's spendable amount, then what is on its way (screening, or awaiting a root) tagged `pending`. */
      read: Zerc20AssetAmount<'pending'>;
    };
    publicOp: Zerc20PublicOperation;
    privateOp: Zerc20PrivateOperation;
    extras: {
      /** Brings the account up to date with the chain and the servers, and moves operations under way along. Every call
       * that reads the account does it first. */
      sync(): Promise<void>;
      /** The zERC20 wallet underneath, for what Kohaku has no call for: receive codes, consolidation, rage exits,
       * history, a view key. `close()` lets the account go, for another plugin on the same chain. */
      wallet: Wallet;
    };
  }
>;

/** What a broadcast did: the operation's id in the wallet, and the transactions it sent. */
export interface Zerc20BroadcastResult {
  id: string;
  txHashes: Hex[];
}

export type Zerc20Broadcaster = Broadcaster<Zerc20PrivateOperation, Zerc20BroadcastResult>;

/** Opens account `accountIndex` of the host's keystore on the chain of its provider; the first time, it registers the
 * account for payments. Its state lives in the host's storage, encrypted by the wallet, under the deployment's storage
 * canister and verifier as well: the same keys on another deployment of the chain have a state of their own. An earlier
 * plugin of the same account and chain, here or in another tab, stops: Kohaku has no call to close one, and the two
 * would spend the same notes. */
export async function createZerc20Plugin(host: Host, params: Zerc20PluginParameters): Promise<Zerc20Instance> {
  const chainId = await host.provider.getChainId();
  const config = params.network.chains.find((c) => c.chainId === chainId);
  if (!config) throw new UnsupportedChainError(chainId);
  const keystore = scopeKeystore(host.keystore, { prefixes: [ZERC20_KEYSTORE_PREFIX] });
  // the key is the seed of every zERC20 key of the account: asked for whenever the wallet spends, and let go after
  const seed = async () => hexToBytes(await keystore.deriveAt(`${ZERC20_KEYSTORE_PREFIX}/${params.accountIndex}'`));
  const key = `zerc20-state:${params.network.storage.canisterId}:${chainId}:${config.verifier}:${params.accountIndex}`;
  const request = (({ method, params }) => host.provider.request({ method, params })) as EIP1193RequestFn;
  const wallet = await Wallet.open({
    network: { ...params.network, chains: [config] },
    account: privateKeyToAccount(accountKey(await seed())),
    seed,
    persist: {
      load: async () => {
        const saved = await host.storage.get(key);
        return saved === null ? null : base64.decode(saved);
      },
      save: (bytes) => host.storage.set(key, base64.encode(bytes)),
    },
    birthday: params.birthday,
    take: true,
    transport: () => custom({ request }),
    fetch: (input, init) => host.network.fetch(input, init),
  });

  const tokenOf = (asset: ERC20AssetId): { token: Token; wrapped: boolean } => {
    for (const token of wallet.tokens()) {
      if (isAddressEqual(token.underlying, asset.contract)) return { token, wrapped: false };
      if (isAddressEqual(token.address, asset.contract)) return { token, wrapped: true };
    }
    throw new UnsupportedAssetError(asset);
  };

  /** A payment's fee now, which also checks that one JoinSplit pays it from what is spendable. */
  const quote = async (
    kind: 'send' | 'withdraw',
    { asset, amount }: Zerc20AssetAmount,
    to: string,
  ): Promise<Zerc20PrivateOperation> => {
    await wallet.sync();
    const { token, wrapped } = tokenOf(asset);
    try {
      const { fee } = await wallet.fees({ kind, token, amount });
      return { __type: 'privateOperation', kind, token, to, amount, maxFee: fee, unwrap: !wrapped };
    } catch (e) {
      // as Kohaku's other plugins report it; settling funds and fragmented notes keep the wallet's own codes
      if (!(e instanceof WalletError) || e.code !== 'insufficient-funds') throw e;
      throw new InsufficientBalanceError(asset, amount, (await wallet.maxAmount({ kind, token })).amount);
    }
  };

  return {
    wallet,
    sync: () => wallet.sync(),
    instanceId: async () => accountId(wallet.address),

    async balance(assets) {
      await wallet.sync();
      const balances = wallet.balances();
      const rows = assets
        ? assets.map((asset) => ({ asset, token: tokenOf(asset).token }))
        : balances.map((b) => ({ asset: { __type: 'erc20', contract: b.token.underlying } as const, token: b.token }));
      return rows.flatMap(({ asset, token }) => {
        const b = balances.find((b) => b.token.tokenId === token.tokenId);
        const pending = b?.pending.reduce((sum, p) => sum + p.amount, 0n) ?? 0n;
        return [
          { asset, amount: b?.spendable ?? 0n },
          { asset, amount: pending, tag: 'pending' as const },
        ];
      });
    },

    async prepareShield({ asset, amount }, to) {
      await wallet.sync();
      const { token, wrapped } = tokenOf(asset);
      return { __type: 'publicOperation', txns: await wallet.depositTransactions({ token, amount, to, wrapped }) };
    },

    prepareTransfer: (asset, to) => quote('send', asset, to),

    async prepareUnshield(asset, to, options?: UnshieldOptions) {
      // a withdrawal pays one address and calls nothing after
      if (options?.tailCalls) throw new PluginError('a zERC20 withdrawal takes no tail calls');
      if (!isAddress(to)) throw new InvalidAddressError(to);
      return quote('withdraw', asset, to);
    },
  };
}

/** Sends what `plugin` prepared: proves the JoinSplit here, has the relayer submit it, and returns once it is mined,
 * as a wallet shows a public transaction, not the minutes later it is final. The plugin's syncs see it through to
 * final, and send it again should a reorg drop it; an interrupted broadcast resumes at the next sync too. */
export function createZerc20Broadcaster(plugin: Zerc20Instance): Zerc20Broadcaster {
  return {
    async broadcast(op) {
      const { wallet } = plugin;
      const { token, amount, maxFee } = op;
      const sent =
        op.kind === 'send'
          ? await wallet.send({ to: op.to, token, amount, maxFee })
          : await wallet.withdraw({ to: op.to as Address, token, amount, maxFee, unwrap: op.unwrap });
      await sent.wait({ until: 'mined' });
      return { id: sent.id, txHashes: [...sent.txHashes] };
    },
  };
}
