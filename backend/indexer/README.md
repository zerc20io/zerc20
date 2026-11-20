# indexer

Reads each chain's `CommitmentLedger` and `Verifier` events into Postgres, and serves them to wallets
and to the other backend nodes. One instance serves every chain in `CHAINS` (`backend/README.md`,
common), each from its own database.

## Why it looks like this

**Wallets download; they never ask.** A query for one leaf, address or nullifier would tell the
server what a wallet holds and when it is about to spend. So every endpoint serves whole chunks of
4096 entries, the same bytes to everyone, and wallets match locally.

Identical answers also let a CDN carry the load. A fetch then reveals only which chunk a wallet has
something in, and it happens when the item arrives, not when it is spent.

- **Tags are 4 bytes.** That keeps a full scan cheap at 10M entries. A false match costs one chunk
  download, and the wallet checks the chunk.
- **Nullifier prefixes are 8 bytes.** A false "spent" cannot be checked afterwards, so it must be
  negligible.

**The tree has no node table.** Commitments only append, so a full chunk never changes, and its root
is stored once. Wallets build their own paths, so the indexer needs neither per-node storage nor
proofs.

**Nothing grows without bound.** Chunk roots are grouped into pages of 4096 the same way, and a full
page's root is also stored once. The tree has 32 levels: 12 inside a chunk, 12 inside a page, and at
most 256 page roots on top. So two levels of grouping are all it will ever need. However large the
chain grows, a path takes one chunk, one page of chunk roots and the page roots, and the indexer
hashes at most a few thousand nodes to derive any root.

Every list that grows (proved roots too) is split into numbered pages the same way, and the latest
proved root sits in `/status`. Whatever a wallet polls therefore has a fixed maximum size.

**getLogs drops logs silently, and one missing commitment breaks every root after it.** So a batch
is stored only once it is shown complete. Otherwise it is refetched, narrower and preferably from
another RPC.

- **All events come from one getLogs call.** A lagging node, an empty answer or a truncated one then
  also loses ledger logs, which are numbered.
- **The ledger exposes its count and hash chain.** Read at the batch's exact block hash, they check
  both the number and the content of the commitments against the chain the logs came from.
- **Nullifiers carry no number, and the contract keeps no count of them.** A missed nullifier fails
  safe: the spend is rejected on chain. So each transaction's nullifier count is checked against its
  other logs, and logsBloom flags blocks that should have had one.

**Follow the head, act on finality.** Wallets want new entries within seconds, so the indexer
follows the head and rolls back on reorgs. Once caught up it looks again every `POLL_SECS` (5 s),
not at every block: each look costs about seven RPC calls however few blocks it finds, and on
Arbitrum's quarter-second blocks looking at each one multiplies the provider's bill several times
over. Wallets sync less often than that. With `FINAL_ONLY=1` it stops at the final block instead and
reads no header per block, which on a fast chain is most of the bill: for an indexer that only
watches for forged roots. Whatever cannot be undone waits for finality:

- CDN responses become immutable only once final.
- asp acts only on the `*_final` counts. The ASP keys approvals by position, so if a
  reorg replaced a screened deposit with another one, that other deposit would be approved without
  screening.
- root-prover does not wait: its proof is bound to a checkpoint the ledger reserved, so a reorg
  costs it one round, and waiting would put finality in series with every round.

The `safe` tag sets that boundary but never bounds a getLogs request, because load-balanced
nodes disagree about it. `safe`, not `finalized`: a reorg past it is rare enough for the ASP's
screening, and on Base it puts final two minutes behind the head rather than twenty. On Ethereum
`REORG_DEPTH` (64 blocks, about thirteen minutes) is the deeper bound of the two.

**Roots are recomputed.** The other nodes trust the indexer rather than `provedRoots`, because a
circuit bug could get a forged root proved. So the indexer derives every root itself and flags any
proved root that differs.

- `/status` serves the first such root as `mismatch`. The root-prover then puts the ledger in an
  emergency (`backend/root-prover/README.md`).
- `latest_root` stays at the last root before it that the indexer derives itself. So wallets and
  nodes keep proving against an honest root through the incident, without a change of their own.
- A recovery (`CommitmentLedger.recover`) steps the root stream back to an earlier root. Its
  `Recovered` log is stored as one more root entry, so the stream stays one unbroken chain of
  old and new indices. It starts a new era: `mismatch` looks only at roots since the last
  recovery, and an index may be proved again.

**The wait for a root is measured.** Anyone may prove roots, at any pace, so no setting says how
long a commitment waits for one. `settle_secs` in `/status` comes from the latest roots' own waits,
taken so that a few slow rounds do not move it. Wallets show a settling coin's time by it, and it
follows the provers as they change.

## API

| path               | per entry                                                                                                                                                                   |
| ------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `/commitments/{p}` | the 4 fields, after the hash chain before the chunk (for rage exits)                                                                                                        |
| `/tags/{p}`        | `keccak256(field0 ‖ to or note hash)[..4]`                                                                                                                                  |
| `/blocks/{p}`      | the commitment's block number (8 bytes), for the ASP's screening delay                                                                                                      |
| `/times/{p}`       | the commitment's block time (8 bytes, unix seconds), so that wallets date what they find the same way on every device                                                       |
| `/nullifiers/{p}`  | the first 8 bytes                                                                                                                                                           |
| `/marks/{p}`       | per page of 4096 commitments: its first commitment's block (8 bytes), then the nullifiers in earlier blocks (8 bytes), where a wallet starts looking for a note's nullifier |
| `/chunk-roots/{p}` | a full chunk's root                                                                                                                                                         |
| `/roots/{p}`       | a proved root: its size, root, partial chunk and page roots, own-root check (105 bytes)                                                                                     |
| `/page-roots`      | a full page's root (at most 256)                                                                                                                                            |
| `/status`          | counts, `*_final`, the latest usable proved root, the first forged one since the last recovery (`mismatch`), how long commitments wait for a root (`settle_secs`)           |

- `{p}` is `index / 4096` within that list. `/status` gives the counts, which tell a wallet which
  pages exist.
- The page still filling is served under its own number too. An answer then always says where its
  entries sit, even when it is a few seconds older or newer than the `/status` the wallet read.

## Run

Configuration is by environment variables, listed in `src/main.rs`.

```sh
cargo test -p zerc20-indexer
backend/indexer/scripts/e2e.sh        # anvil + Postgres: matches the ledger, survives reorgs and restarts
backend/indexer/scripts/e2e_chaos.sh  # the same, through an RPC proxy that drops logs, lags and fails
```

The e2e scripts need anvil, forge, docker and psql. forge crashes inside the Claude Code sandbox, so
run them outside it.

## Changing it

- **A new event stream** needs an order, a way to prove no log is missing, and a block number on
  each row. Those three are what give it the guarantees above: no silent loss, and rollback by
  block.
- **A new endpoint** serves whole chunks or lists only, and turns immutable only once final, for the
  same privacy and caching reasons.
- **Wallet-facing formats** (page size, tag, prefix, root entry) change through new paths, never in
  place: deployed wallets and CDN caches still hold the old bytes.
