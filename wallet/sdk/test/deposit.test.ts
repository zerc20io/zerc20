import { expect, test } from 'vitest';
import type { Ctx } from '../src/context.js';
import type { DepositOperation } from '../src/state.js';
import { settleDeposit } from '../src/wallet.js';

const PAYER = '0x00000000000000000000000000000000000000b0' as const;
const sent = { from: PAYER, nonce: 7 };

interface Seen {
  /** Its receipt at each read, the last one repeated: none until it is mined. */
  receipts?: ('success' | 'reverted' | null)[];
  /** A node holds it, at nonce 7. */
  waiting?: true;
  /** How many of the payer's transactions are mined. */
  mined?: number;
  /** What the burn address holds; it held 20 before. */
  holds?: bigint;
  /** The node does not answer reads by block. */
  down?: true;
}

/** A chain where the deposit's transaction stands as `seen` says. */
function chainWith(seen: Seen): Ctx {
  const receipts = [...(seen.receipts ?? [null])];
  const answer = async <T>(v: T) => {
    if (seen.down) throw new Error('the node does not answer');
    return v;
  };
  const client = {
    getTransactionReceipt: async () => {
      const status = receipts.length > 1 ? receipts.shift() : receipts[0];
      if (!status) throw new Error('not mined');
      return { status };
    },
    getTransaction: async () => {
      if (!seen.waiting) throw new Error('not found');
      return { from: PAYER, nonce: 7 };
    },
    getBlockNumber: () => answer(100n),
    getTransactionCount: () => answer(seen.mined ?? 7),
    readContract: () => answer(seen.holds ?? 20n),
  };
  const chain = { client, tokens: async () => [{ tokenId: 1, address: '0x00000000000000000000000000000000000000c0' }] };
  return { chains: [{ config: { chainId: 1n }, chain }], save: async () => {} } as unknown as Ctx;
}

const deposit = (data: Partial<DepositOperation['data']> = {}): DepositOperation => ({
  id: '0x01',
  kind: 'deposit',
  chainId: 1n,
  tokenId: 1,
  amount: 50n,
  createdMs: 0,
  status: 'pending',
  data: { burnAddress: '0x00000000000000000000000000000000000000d0', txHash: '0xaa', held: 20n, ...data },
});

const settle = async (seen: Seen, data?: Partial<DepositOperation['data']>) => {
  const op = deposit(data);
  await settleDeposit(chainWith(seen), op);
  return op;
};

test('a deposit settles by its receipt, and waits while a node holds it, noting its nonce', async () => {
  expect((await settle({ receipts: ['success'] })).status).toBe('done');
  const reverted = await settle({ receipts: ['reverted'] });
  expect([reverted.status, reverted.error]).toEqual(['failed', 'the deposit transaction reverted']);
  const waiting = await settle({ waiting: true });
  expect([waiting.status, waiting.data.sent]).toEqual(['pending', sent]);
});

test('a deposit another transaction took the nonce of is done if the burn address got the amount, failed if not', async () => {
  // a speed-up: another hash paid it, on top of what a receive code's address held already
  expect((await settle({ mined: 8, holds: 70n }, { sent, code: 'zerc20code1…' })).status).toBe('done');
  // a cancel: the nonce went to a transaction that paid nothing
  expect((await settle({ mined: 8 }, { sent })).status).toBe('failed');
  // mined after all, between the first look and the last
  const late = await settle({ receipts: [null, 'reverted'], mined: 8 }, { sent });
  expect([late.status, late.error]).toEqual(['failed', 'the deposit transaction reverted']);
  // gone from the node's pool with its nonce still free: it may still be mined
  expect((await settle({ mined: 7 }, { sent })).status).toBe('pending');
});

test("a deposit's own burn address paid is done though no node showed it waiting; a receive code's is not", async () => {
  expect((await settle({ holds: 70n })).status).toBe('done');
  expect((await settle({ holds: 70n }, { code: 'zerc20code1…' })).status).toBe('pending');
  expect((await settle({ mined: 8 })).status).toBe('pending');
});

test('a deposit whose node does not answer waits for the next sync', async () => {
  expect((await settle({ down: true, mined: 8 }, { sent })).status).toBe('pending');
});
