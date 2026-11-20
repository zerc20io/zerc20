import { expect, test } from 'vitest';
import type { Ctx } from '../src/context.js';
import { WalletError } from '../src/errors.js';
import {
  type Coin,
  type MergeStep,
  type Step,
  advanceConsolidation,
  bpsOf,
  cancellable,
  chosenSettling,
  coins,
  feeOf,
  feesOf,
  grossed,
  inputsOf,
  landed,
  maxPayment,
  mergePool,
  mergeRound,
  minedInputsOf,
  nullifiersPast,
  payWith,
  pick,
  relayedState,
  roundsToMerge,
  settling,
  withdrawalOf,
} from '../src/spend.js';
import type { IndexerStatus } from '../src/servers.js';
import type { DepositRecord, NoteRecord, OperationRecord, SpendOperation } from '../src/state.js';
import { applyHits, dropReorged } from '../src/sync.js';

const note = (index: number, value: bigint): Coin => ({ kind: 'note', index, value, salt: '0x01' });
const burn = (index: number, value: bigint): Coin => ({ kind: 'burn', index, value, burnSalt: '0x02', sender: '0x03' });
const at = (index: number, more: object = {}) => ({ index, tentative: false, spent: false, confirmed: true, ...more });
/** The error code `f` throws. */
const code = (f: () => unknown) => {
  try {
    f();
  } catch (e) {
    return (e as { code?: string }).code;
  }
};

test('one JoinSplit: the smallest single input, else the smallest pair with a note second', () => {
  const coins = [note(1, 50n), burn(2, 70n), note(3, 30n), note(4, 120n)];
  expect(pick(coins, 60n)?.map((c) => c.index)).toEqual([2]);
  expect(pick(coins, 100n)?.map((c) => c.index)).toEqual([2, 3]);
  expect(pick(coins, 200n)).toBeNull();
  // two deposits never pair: one of them must become a note first
  expect(pick([burn(1, 50n), burn(2, 50n)], 90n)).toBeNull();
});

test('a merge spends up to 100 coins, the largest first, if they are worth more than its fee', () => {
  expect(mergeRound([note(1, 5n), burn(2, 70n), note(3, 30n)], 10n)?.map((c) => c.index)).toEqual([2, 3, 1]);
  // deposits merge together, and dust along with the rest
  expect(mergeRound([burn(1, 50n), burn(2, 60n), note(3, 1n)], 10n)?.map((c) => c.index)).toEqual([2, 1, 3]);
  // but not on its own
  expect(mergeRound([note(1, 5n), note(2, 4n)], 10n)).toBeNull();
  // a lone deposit becomes a note; a lone note is done
  expect(mergeRound([burn(1, 50n)], 10n)?.map((c) => c.index)).toEqual([1]);
  expect(mergeRound([note(1, 50n)], 10n)).toBeNull();
  const many = Array.from({ length: 150 }, (_, i) => note(i, BigInt(i + 1)));
  expect(
    mergeRound(many, 10n)
      ?.map((c) => c.index)
      .slice(0, 2),
  ).toEqual([149, 148]);
  expect(mergeRound(many, 10n)).toHaveLength(100);
});

test('merges to consolidate, and a consolidation of chosen coins only', () => {
  expect(
    [[], [note(1, 50n)], [burn(1, 50n)], [burn(1, 50n), burn(2, 60n)], [note(1, 50n), burn(2, 60n)]].map((c) =>
      roundsToMerge(c),
    ),
  ).toEqual([0, 0, 1, 1, 1]);
  // 100 in the first merge, then 99 more a merge with the one before's note
  expect([100, 101, 199, 200].map((n) => roundsToMerge(Array.from({ length: n }, (_, i) => note(i, 1n))))).toEqual([
    1, 2, 2, 3,
  ]);
  const all = [note(1, 50n), burn(2, 60n), burn(3, 70n), { ...note(4, 120n), salt: '0x09' as const }];
  expect(mergePool(all, undefined)).toBe(all);
  // the chosen coins, and the notes earlier rounds made of them; nothing else
  expect(mergePool(all, [3]).map((c) => c.index)).toEqual([3]);
  expect(mergePool(all, [2, 3], ['0x09']).map((c) => c.index)).toEqual([2, 3, 4]);
  expect(roundsToMerge(mergePool(all, [2, 3]))).toBe(1);
  expect(mergePool(all, [1, 3]).map((c) => c.index)).toEqual([1, 3]);
  expect(mergeRound(mergePool(all, [1, 3]), 10n)?.map((c) => c.index)).toEqual([3, 1]);
});

test('a payment is one JoinSplit, or fails with what to do instead', () => {
  const notes = [note(1, 50n), note(2, 50n), note(3, 50n)];
  expect(payWith(notes, 100n, 10n, false).map((c) => c.index)).toEqual(pick(notes, 100n)!.map((c) => c.index));
  // no pair pays 120, the three merged (150 less one merge's fee) would
  expect(code(() => payWith(notes, 120n, 10n, false))).toBe('needs-consolidation');
  expect(code(() => payWith(notes, 141n, 10n, true))).toBe('funds-settling');
  expect(code(() => payWith(notes, 141n, 10n, false))).toBe('insufficient-funds');
  // two deposits never share a JoinSplit: the first becomes a note, then pays with the second
  expect(code(() => payWith([burn(1, 60n), burn(2, 60n)], 100n, 10n, false))).toBe('needs-consolidation');
});

test('a payment pays the protocol on top: its recipient, or the relayer, gets all of theirs', async () => {
  // a 1% cut, rounded down
  const ctx = {
    chains: [{ config: { chainId: 1n }, chain: { withdrawFee: async (_: number, x: bigint) => x / 100n } }],
  } as unknown as Ctx;
  const step = (outputs: [bigint, bigint], withdrawn: bigint) =>
    ({
      inputs: [note(1, 1500n)],
      outputs: [
        { value: outputs[0], role: 'x' },
        { value: outputs[1], role: 'change' },
      ],
      withdraw: { amount: withdrawn },
    }) as unknown as Step;
  const op = (kind: string) => ({ amount: 1000n, data: { to: { kind } } }) as unknown as SpendOperation;
  // a withdrawal of 1000 withdraws 1010, and pays the relayer 10 by a note
  expect(await withdrawalOf(ctx, 1n, 1, true, 1000n, 10n)).toEqual({ withdrawn: 1010n, protocol: 10n });
  expect(feeOf(op('public'), step([10n, 480n], 1010n))).toBe(20n);
  // a send of 1000 pays the relayer 100 by withdrawing 101
  expect(await withdrawalOf(ctx, 1n, 1, false, 1000n, 100n)).toEqual({ withdrawn: 101n, protocol: 1n });
  expect(feeOf(op('address'), step([1000n, 399n], 101n))).toBe(101n);
  // Max: the most whose fees on top the coins still pay, to the unit, and what the fees take
  expect(await maxPayment(ctx, 1n, 1, true, [note(1, 1020n)], 10n)).toEqual({ amount: 1000n, fee: 20n, merges: 0 });
  expect(await maxPayment(ctx, 1n, 1, false, [burn(1, 1001n), note(2, 100n)], 100n)).toEqual({
    amount: 1000n,
    fee: 101n,
    merges: 0,
  });
  // the fees take everything: what they would be
  expect(await maxPayment(ctx, 1n, 1, false, [note(1, 101n)], 100n)).toEqual({ amount: 0n, fee: 101n, merges: 0 });
  expect(await maxPayment(ctx, 1n, 1, false, [note(1, 40n)], 100n)).toEqual({ amount: 0n, fee: 101n, merges: 0 });
});

test("a cut's rate is the tier's, from a withdrawal of 10,000 base units up", () => {
  for (const bps of [1n, 35n, 100n, 300n]) {
    for (const gross of [10_000n, 10_001n, 123_457n, 10n ** 18n + 7n]) {
      expect(bpsOf((gross * bps) / 10_000n, gross)).toBe(Number(bps));
    }
  }
  expect(bpsOf(0n, 0n)).toBe(0);
});

test('a withdrawal is grossed up to the unit in a few reads, whatever its size and rate', async () => {
  for (const bps of [1n, 35n, 100n, 300n]) {
    let reads = 0;
    // the contract's cut: a rate of the whole withdrawal, rounded down
    const cut = (x: bigint) => (x * bps) / 10_000n;
    const ctx = {
      chains: [{ config: { chainId: 1n }, chain: { withdrawFee: async (_: number, x: bigint) => (reads++, cut(x)) } }],
    } as unknown as Ctx;
    for (const net of [0n, 1n, 999n, 10n ** 6n, 10n ** 18n, 100n * 10n ** 18n, 10n ** 30n, 2n ** 247n]) {
      reads = 0;
      const gross = await grossed(ctx, 1n, 1, net);
      expect(gross - cut(gross)).toBeGreaterThanOrEqual(net);
      if (gross > 0n) expect(gross - 1n - cut(gross - 1n)).toBeLessThan(net);
      expect(reads).toBeLessThanOrEqual(4);
    }
  }
});

test("Max of coins one JoinSplit cannot spend together takes out the merge's fee, and the payment then asks for it", async () => {
  const ctx = { chains: [{ config: { chainId: 1n }, chain: { withdrawFee: async () => 0n } }] } as unknown as Ctx;
  const all = [burn(1, 500n), burn(2, 300n), note(3, 220n)];
  const max = await maxPayment(ctx, 1n, 1, true, all, 10n);
  expect(max).toEqual({ amount: 1000n, fee: 20n, merges: 1 });
  expect(code(() => payWith(all, max.amount + 10n, 10n, false))).toBe('needs-consolidation');
  // merged into one note of 1010, the same Max pays at once
  expect(await maxPayment(ctx, 1n, 1, true, [note(4, 1010n)], 10n)).toEqual({ amount: 1000n, fee: 10n, merges: 0 });
});

test('coins still settling count as on their way, notes only announced do not', () => {
  const noteWith = (found: NoteRecord['found'], value = 5n) =>
    ({ chainId: 1n, tokenId: 1, value, found }) as NoteRecord;
  const depositWith = (asp: 'approved' | 'rejected' | null, index: number) =>
    ({
      chainId: 1n,
      found: [{ index, tentative: false, spent: false, tokenId: 1, sender: '0x03', amount: 5n, asp }],
    }) as unknown as DepositRecord;
  const ctx = (notes: NoteRecord[], deposits: DepositRecord[] = []) =>
    ({ state: { notes, deposits } }) as unknown as Ctx;
  const settles = (c: Ctx) => settling(c, 1n, 1, 10);
  expect(settles(ctx([noteWith([at(3)]), noteWith([])]))).toBe(false); // spendable, and announced only
  expect(settles(ctx([noteWith([at(12)])]))).toBe(true); // awaiting a root
  expect(settles(ctx([noteWith([at(12)], 0n)]))).toBe(false); // a zero-value change, there for its payment's receipt
  expect(settles(ctx([noteWith([at(3, { tentative: true })])]))).toBe(false); // not final, but a proved root covers it
  expect(settles(ctx([noteWith([at(3, { confirmed: false })])]))).toBe(true); // its commitment not read yet
  expect(settles(ctx([noteWith([at(12, { spent: true })])]))).toBe(false);
  expect(settles(ctx([], [depositWith(null, 3)]))).toBe(true); // screening
  expect(settles(ctx([], [depositWith('rejected', 3), depositWith('approved', 3)]))).toBe(false);
  expect(settles(ctx([], [depositWith('approved', 12)]))).toBe(true);
});

/** An input whose nullifier was looked for up to `scannedTo`, or one spent. */
const input = (scannedTo: number, spent = false) => ({
  index: 3,
  tentative: false,
  spent,
  nullifier: spent ? undefined : { key: '0x01' as const, from: 0, scannedTo },
});
/** A change whose tag was looked for up to `scannedTo` (null: no longer watched), found where `found` says. */
const change = (scannedTo: number | null, ...found: { tentative: boolean; confirmed?: boolean }[]) => ({
  watch: scannedTo === null ? null : { key: '0x02' as const, from: 0, scannedTo },
  found: found.map((f, i) => ({ index: 50 + i, spent: false, ...f })),
});

test('a relayed step is done once its change is final where it is expected, as only its own transaction puts it there', () => {
  const final = { tentative: false, confirmed: true };
  expect(relayedState(change(null, final), [input(0, true), input(120)], 100, 200)).toBe('landed');
  expect(relayedState(change(150, { tentative: true, confirmed: true }), [input(90)], 100, undefined)).toBe('mined');
  expect(relayedState(change(150), [input(90)], 100, undefined)).toBe('waiting');
});

test("an input spent while the final commitments pass the change's place without it is another transaction's: the step never lands", () => {
  // another device of the wallet spent the first input, or only the second
  expect(relayedState(change(200), [input(0, true), input(120)], 100, 200)).toBe('taken');
  expect(relayedState(change(200), [input(120), input(0, true)], 100, 200)).toBe('taken');
  // the change's tag is not looked for yet as far as that transaction's notes may lie
  expect(relayedState(change(199), [input(0, true)], 100, 200)).toBe('waiting');
  expect(relayedState(change(200), [input(0, true)], 100, undefined)).toBe('waiting');
  // a final position whose commitment is not read yet may be the change
  expect(relayedState(change(200, { tentative: false }), [input(0, true)], 100, 200)).toBe('waiting');
});

test('a relayed step with no input spent is relayed again once the final nullifiers pass where its own would be', () => {
  expect(relayedState(change(150), [input(100), input(100)], 100, undefined)).toBe('dropped');
  expect(relayedState(change(150), [input(100), input(99)], 100, undefined)).toBe('waiting'); // not final there yet
  // the indexer is not past its block yet
  expect(relayedState(change(150), [input(100)], undefined, undefined)).toBe('waiting');
  expect(relayedState(change(150), [undefined], 100, undefined)).toBe('waiting');
});

test('a relayed JoinSplit is counted once the indexer is past its block, by the status read after the one showing it', async () => {
  const statuses = [
    { cursor: 9, nullifiers: 5 },
    { cursor: 10, nullifiers: 5 },
    { cursor: 10, nullifiers: 6 },
  ];
  const indexer = { status: async () => statuses.shift() as IndexerStatus };
  expect(await nullifiersPast(indexer, 10)).toBeUndefined(); // the relayer answered before the indexer read the block
  expect(await nullifiersPast(indexer, 10)).toBe(6); // the status showing the block counted before it read its cursor
});

test('a consolidation of chosen coins waits for those settling, and refuses rejected deposits', () => {
  const ctx = {
    state: {
      notes: [
        { chainId: 1n, tokenId: 1, value: 50n, found: [at(1), at(2, { tentative: true })] },
        { chainId: 1n, tokenId: 1, value: 5n, found: [at(3)] },
      ],
      deposits: [
        {
          chainId: 1n,
          found: [
            { index: 4, tentative: false, spent: false, tokenId: 1, sender: '0x03', amount: 60n, asp: 'rejected' },
          ],
        },
      ],
    },
  } as unknown as Ctx;
  const all = [note(1, 50n), note(3, 5n)]; // the spendable ones
  expect(chosenSettling(ctx, 1n, [1], all)).toBe(false);
  expect(chosenSettling(ctx, 1n, [1, 2], all)).toBe(true); // 2 is not final yet
  expect(chosenSettling(ctx, 1n, [1, 3], all)).toBe(false); // 3 is worth less than a fee, and merges along
  expect(code(() => chosenSettling(ctx, 1n, [4], all))).toBe('invalid'); // 4 was rejected
});

test('a payment is on chain once relayed, and a consolidation round is not a payment', () => {
  const op = (status: string, stage: string | null, kind = 'send') =>
    ({ kind, status, data: { step: stage && { stage } } }) as unknown as SpendOperation;
  expect(landed(op('pending', 'attested'))).toBe(false); // not sent yet
  expect(landed(op('pending', 'relayed'))).toBe(true); // mined, not final
  expect(landed(op('pending', 'relayed', 'consolidate'))).toBe(false);
  expect(landed(op('done', null))).toBe(true);
  expect(landed(op('failed', 'relayed'))).toBe(false);
  expect(landed(op('pending', null, 'deposit'))).toBe(false); // a deposit is on chain once done
});

test('a consolidation is on chain once nothing is left to merge and its merges are in a block, final or not', () => {
  const merge = (index: number, stage: string): MergeStep =>
    ({ inputs: [note(index, 10n)], output: {}, fee: 2n, stage, attempts: 0 }) as unknown as MergeStep;
  const op = (data: object) =>
    ({ kind: 'consolidate', status: 'pending', data: { paid: 1n, step: null, ...data } }) as unknown as SpendOperation;
  const mid = op({ landing: [merge(1, 'relayed')], step: merge(2, 'noted') });
  expect(landed(mid)).toBe(false); // more to merge
  expect(inputsOf(mid).map((c) => c.index)).toEqual([1, 2]); // both its own: no other operation takes them
  expect(minedInputsOf(mid).map((c) => c.index)).toEqual([1]); // spent in a block
  expect(feesOf(mid)).toBe(3n); // the final one's, and the one in a block
  expect(cancellable(mid)).toBe(false); // a merge of it is in a block
  expect(landed(op({ merged: true, landing: [merge(1, 'relayed')], step: merge(2, 'relayed') }))).toBe(true);
  // a reorg dropped one, which is relayed again
  expect(landed(op({ merged: true, landing: [merge(1, 'proved')], step: merge(2, 'relayed') }))).toBe(false);
  // it fails once its merge is final
  expect(landed(op({ merged: true, failure: { code: 'fee-too-high' }, step: merge(2, 'relayed') }))).toBe(false);
});

test('a consolidation that cannot go on fails once its merges in a block are final, their coins and fees its own until then', async () => {
  const ctx = { save: async () => {} } as unknown as Ctx;
  const merge = (index: number) =>
    ({ inputs: [note(index, 10n)], output: {}, fee: 2n, stage: 'planned' }) as unknown as MergeStep;
  const refused = new WalletError('spent-elsewhere', 'another device spent it');
  const tooHigh = new WalletError('fee-too-high', 'the fee rose');
  // scripted: what each merge does next, and each plan
  const consolidation = (plans: (MergeStep | Error)[], answers: Map<MergeStep, ('final' | 'mined' | Error)[]>) => {
    const op = {
      kind: 'consolidate',
      status: 'pending',
      data: { to: { kind: 'self' }, step: null, paid: 0n },
    } as unknown as SpendOperation;
    const sync = () =>
      advanceConsolidation(
        ctx,
        op,
        async (m) => {
          const now = answers.get(m)!.shift()!;
          if (now instanceof Error) throw now;
          m.stage = 'relayed';
          return now;
        },
        async () => {
          const next = plans.shift()!;
          if (next instanceof Error) throw next;
          return next;
        },
      );
    return { op, sync };
  };

  // the next merge cannot be planned while the last is in a block
  const m1 = merge(1);
  const a = consolidation([m1, tooHigh], new Map([[m1, ['mined', 'mined', 'final']]]));
  await a.sync();
  expect([a.op.data.merged, a.op.data.failure?.code, a.op.status, landed(a.op)]).toEqual([
    true,
    'fee-too-high',
    'pending',
    false,
  ]);
  expect([inputsOf(a.op), minedInputsOf(a.op), feesOf(a.op)]).toEqual([m1.inputs, m1.inputs, 2n]);
  await a.sync(); // m1 still not final
  await expect(a.sync()).rejects.toMatchObject({ code: 'fee-too-high' }); // m1 final

  // a merge planned on the last one's note fails while that one is in a block: it is dropped, its coins free again
  const [m2, m3] = [merge(2), merge(3)];
  const b = consolidation(
    [m2, m3],
    new Map<MergeStep, ('final' | 'mined' | Error)[]>([
      [m2, ['mined', 'mined', 'final']],
      [m3, [refused]],
    ]),
  );
  await b.sync();
  expect([b.op.data.step, b.op.data.landing, b.op.data.failure?.code]).toEqual([null, [m2], 'spent-elsewhere']);
  await expect(b.sync()).rejects.toMatchObject({ code: 'spent-elsewhere' }); // m2 final

  // with nothing in a block, it fails at once
  await expect(consolidation([tooHigh], new Map()).sync()).rejects.toMatchObject({ code: 'fee-too-high' });
});

test('a consolidation plans each merge once a block holds the last, sees each to final, and relays one a reorg dropped before any later one', async () => {
  const m1 = { stage: 'planned' } as unknown as MergeStep;
  const m2 = { stage: 'planned' } as unknown as MergeStep;
  const op = {
    kind: 'consolidate',
    status: 'pending',
    data: { to: { kind: 'self' }, step: null, paid: 0n },
  } as unknown as SpendOperation;
  const ctx = { save: async () => {} } as unknown as Ctx;
  // what each merge does next: null while it is not in a block (proving, or dropped and relayed again)
  const answers = new Map<MergeStep, ('final' | 'mined' | null)[]>([
    [m1, ['mined', 'mined', 'mined', 'mined', null, 'final']],
    [m2, [null, 'mined', 'mined', 'final']],
  ]);
  const plans: (MergeStep | null | 'done')[] = [m1, null, m2, 'done'];
  const merged: MergeStep[] = [];
  const merge = (m: MergeStep) => {
    merged.push(m);
    const now = answers.get(m)!.shift()!;
    m.stage = now === null ? 'proved' : 'relayed';
    return Promise.resolve(now);
  };
  const plan = () => Promise.resolve(plans.shift()!);
  const sync = () => advanceConsolidation(ctx, op, merge, plan);

  await sync(); // m1 in a block; the next waits for a proved root over its note
  expect([op.data.step, op.data.landing ?? []]).toEqual([m1, []]);
  await sync(); // m2 planned while m1 is not final, and being proved
  expect([op.data.step, op.data.landing]).toEqual([m2, [m1]]);
  merged.length = 0;
  await sync(); // m2 in a block; nothing left to merge
  expect([op.data.merged, landed(op), op.status]).toEqual([true, true, 'pending']);
  merged.length = 0;
  await sync(); // a reorg dropped m1: m2, which spends its note, waits until m1 is in a block again
  expect(merged).toEqual([m1]);
  expect(landed(op)).toBe(false);
  await sync(); // m1 in a block again and final, m2 not final yet
  expect([op.data.landing, op.status]).toEqual([[], 'pending']);
  await sync();
  expect([op.data.step, op.status]).toEqual([null, 'done']);
});

test('an operation is cancelled only while it has paid nothing and has no request out to the relayer', () => {
  const op = (status: string, step: object | null, kind = 'send', paid = 0n) =>
    ({ kind, status, data: { step, paid } }) as unknown as SpendOperation;
  const joinSplit = (stage: string, attempts = 0) => op('pending', { stage, attempts });
  const merge = (stage: string, more: object = {}) =>
    op('pending', { stage, output: {}, attempts: 0, ...more }, 'consolidate');
  for (const stage of ['planned', 'noted', 'proved']) expect(cancellable(joinSplit(stage))).toBe(true);
  for (const stage of ['attested', 'relayed']) expect(cancellable(joinSplit(stage))).toBe(false);
  // a merge is attested before the merge prover proves it
  for (const stage of ['planned', 'noted', 'attested', 'proving']) expect(cancellable(merge(stage))).toBe(true);
  for (const stage of ['proved', 'relayed']) expect(cancellable(merge(stage))).toBe(false);
  // proved again after a relay that reverted, whose request may still land
  expect(cancellable(joinSplit('noted', 1))).toBe(false);
  expect(cancellable(merge('noted', { attempts: 1, sent: true }))).toBe(false);
  // built again after the prover refused it: nothing went out
  expect(cancellable(merge('noted', { attempts: 1 }))).toBe(true);
  expect(cancellable(op('pending', null, 'consolidate'))).toBe(true); // not planned yet
  expect(cancellable(op('pending', null, 'consolidate', 1n))).toBe(false); // a merge of it landed, and paid
  expect(cancellable(op('done', null))).toBe(false);
  expect(cancellable(op('failed', { stage: 'noted', attempts: 0 }))).toBe(false);
  expect(cancellable({ kind: 'deposit', status: 'pending', data: {} } as unknown as OperationRecord)).toBe(false);
});

test('a deposit seen before it is final is read again once it is', () => {
  const watch = { key: '0xaabbccdd' as const, from: 0, scannedTo: 0 };
  const d = {
    chainId: 1n,
    tokenId: 1,
    address: '0x05',
    watches: [{ tokenId: 1, watch }],
    found: [],
  } as unknown as DepositRecord;
  applyHits([], [d], [{ key: watch.key, position: 7, tentative: true }]);
  Object.assign(d.found[0]!, { sender: '0x03', amount: 60n }); // what sync reads at once, to show it
  applyHits([], [d], [{ key: watch.key, position: 7, tentative: true }]);
  expect(d.found[0]).toMatchObject({ tentative: true, amount: 60n }); // read once while it stays tentative
  applyHits([], [d], [{ key: watch.key, position: 7, tentative: false }]);
  expect(d.found).toEqual([
    { index: 7, tentative: false, spent: false, tokenId: 1, sender: null, amount: null, asp: null, unchecked: true },
  ]);
});

test('a position the final count passes without finding it there is dropped: a reorg moved it', () => {
  const watch = { key: '0xaabbccdd' as const, from: 0, scannedTo: 0 };
  const d = {
    chainId: 1n,
    tokenId: 1,
    address: '0x05',
    watches: [{ tokenId: 1, watch }],
    found: [],
  } as unknown as DepositRecord;
  applyHits([], [d], [{ key: watch.key, position: 7, tentative: true }]);
  dropReorged([d], 7);
  expect(d.found.map((f) => f.index)).toEqual([7]); // not final yet: kept
  applyHits([], [d], [{ key: watch.key, position: 9, tentative: false }]); // the reorg put it at 9
  dropReorged([d], 10);
  expect(d.found.map((f) => [f.index, f.tentative])).toEqual([[9, false]]);
});

test("a note paid to a receive code is spent with the code's own key", () => {
  // the note keeps which code, and the coin hands it to the witness
  const watch = { key: '0xaabbccdd' as const, from: 0, scannedTo: 0 };
  const n = {
    chainId: 1n,
    tokenId: 1,
    value: 50n,
    salt: '0x01',
    keyIndex: 5,
    noteHash: '0x02',
    watch,
    found: [],
  } as unknown as NoteRecord;
  applyHits([n], [], [{ key: watch.key, position: 3, tentative: false }]);
  expect(n.found).toEqual([{ index: 3, tentative: false, spent: false, confirmed: false, unchecked: true }]);
  // its commitment read, and its spend looked for, as the sync that found it does
  n.found[0]!.confirmed = true;
  delete n.found[0]!.unchecked;
  const ctx = { state: { notes: [n], deposits: [], ops: [] } } as unknown as Ctx;
  expect(coins(ctx, 1n, 1, 10)).toEqual([{ kind: 'note', index: 3, value: 50n, keyIndex: 5, salt: '0x01' }]);
});
