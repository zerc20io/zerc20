# root-prover

Advances `CommitmentLedger`'s root with Nova proofs. Each round, it reserves a checkpoint at the
head with `reserveHashChain()`, folds the commitments from `rootState()` up to it with the root
circuit, compresses the result with the decider, and submits it with `proveRootTransition`. One
instance proves every chain in `CHAINS` (`backend/README.md`), each from its own indexer.
Proving is permissionless, so more than one can run.

## Why it looks like this

**It does not wait for finality.** A round reserves the head, then waits until the indexer holds
every commitment up to it. The proof is bound to that checkpoint, so commitments a reorg replaced
fail the checks below, or gas estimation, and cost that round only. Waiting would put finality
(about 16 min on Sepolia) in series with every round.

**The indexer is checked against the ledger before proving.** The ledger pins all of it:

- the hash chain pins every commitment: the one at `rootState().index` and at the checkpoint;
- the root pins the full chunks' and pages' roots.

So a wrong indexer costs a log line, not a decider proof. A ledger root the indexer cannot derive
means a forged root, and the round fails loudly every time.

**It is the ledger's guardian.** A soundness bug in the root circuit lets anyone prove a forged
root. Nothing can be proved on top of one, so proving stops anyway. The prover therefore makes sure
the rest of the protocol stops trusting it:

- Every 5 s it reads the indexer's `/status`. Once `mismatch` names a root the ledger still
  accepts, it calls `enterEmergency(latest_root.index)`. The ledger then accepts no root above the
  last one the indexer derives itself, and proves none.
- "Still accepts" matters right after a recovery. The recovery withdraws the forged root, but the
  indexer names it until it reads the `Recovered` log, a few seconds later. Acting on it then would
  undo the recovery.
- That calls for its account to be a guardian (`GUARDIANS` in `Deploy.s.sol`). A guardian can only
  lower the bound: resuming is `recover`, which only the admin role can call, through its delay
  (`contracts/README.md`).
- It checks every 5 s, apart from the rounds, which spend minutes proving. While the ledger is in
  an emergency, rounds reserve nothing.
- The indexer is the one trusted here, as it is by the attester. A false `mismatch` (an indexer bug)
  stops new roots until a recovery. Spends under earlier roots stay open.
- `GUARD_ONLY=1` runs only this check, with no keys and no rounds: a second guardian on an indexer of
  its own (the sentinel). A forged root then halts the ledger even while the
  prover, its indexer or its host is down or broken into.

**The path comes from what a wallet would fetch.** The tree at `rootState().index` is built from
`/page-roots`, its page of `/chunk-roots`, and the leaves of its partial chunk. That is the input of
`zerc20_zkp::tree::sized`, and nothing grows with the tree. From there each step's siblings come
from `IncrementalTree::append`.

**Nothing is kept between rounds.** A round that fails, or loses to another prover, costs one
reservation, and a restart starts a fresh round.

**The keys are trusted.** It reads `root_decider_pk.bin` (6.65 GB, which also holds the IVC key) and
`root_decider_vk.bin` without subgroup checks, so loading is IO-bound. Whoever puts them in
`ARTIFACTS_DIR` verifies them once, on download. They must come from the setup that rendered the
deployed `RootDeciderVerifier` (see `zkp/README.md`). Otherwise every proof reverts with
`InvalidProof`.

## Run

| env                 |                                                                                               |
| ------------------- | --------------------------------------------------------------------------------------------- |
| `RPC_URL`, `LEDGER` |                                                                                               |
| `INDEXER_URL`       | the indexer's origin, not the CDN                                                             |
| `PRIVATE_KEY`       | pays for reservations and proofs; any account, used by nothing else (see `backend/README.md`) |
| `ARTIFACTS_DIR`     | default `zkp/artifacts/root`                                                                  |
| `PROVE_SECS`        | pause between rounds, default 300                                                             |
| `GUARD_ONLY`        | `1`: only guards the ledger, loading no keys                                                  |

```sh
cargo test -p zerc20-root-prover
backend/root-prover/scripts/e2e.sh  # anvil + Postgres + indexer + the real verifier: proofs from genesis, mid-chunk, of one step; idle
```

The e2e script needs the keys in `zkp/artifacts/root` and what the indexer's script needs. It has to
run outside the Claude Code sandbox for the same reason.
