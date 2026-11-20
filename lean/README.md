# lean

Lean 4 proofs that whoever deposits into zERC20 can always get the value back out, and nobody else can take it.
They run from the contracts down to the constraints of every gadget the circuits use.

## What is proved

The statement is split into safety and liveness, so that each part needs only the assumptions it really depends on.
`Zerc20/Main.lean` and `Zerc20/Nova.lean` pin every theorem below to Lean's own axioms
(`propext`, `Classical.choice`, `Quot.sound`): there is no `sorry`, no added axiom and no `native_decide`.

**No theft** (`Zerc20/Safety.lean`):

| Theorem        | Meaning                                                                                                                                                                                                                                                                                   |
| -------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `no_theft`     | A note or burn deposit of an honest owner is spent only by a JoinSplit or rage-exit proof holding the owner's private key, or by a merge the owner signed first. The merge's message fixes the merged note's owner and salt, its value (the inputs less the fee) and the fee's recipient. |
| `at_most_once` | No ledger position is spent twice.                                                                                                                                                                                                                                                        |
| `conservation` | A token's underlying covers its supply and the unspent notes, less the burn deposits already spent.                                                                                                                                                                                       |
| `solvent`      | The underlying covers every balance outside the burn addresses, every unspent note and every unspent burn deposit: everything the holders can redeem.                                                                                                                                     |

These hold whatever relayers, attesters, the ASP, root provers, merge provers and other users do. The attester is not
trusted for them: proving the circuits sound makes it insurance rather than an assumption.

**Exit** (`Zerc20/Liveness.lean`):

| Theorem                                    | Meaning                                                                                                                                                                                                                                 |
| ------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `rageExit_now`                             | An unspent burn deposit comes back to the account that paid it, as zERC20. It needs only a running Verifier and token, an unblocked sender, and a supply that does not overflow: no ASP, attester, proved root or indexer.              |
| `withdraw_now`                             | A note comes out to any unblocked account, less a fee of at most 3%. It needs an accepted root that holds the note, an accepted ASP root, an attester's answer, a fresh dummy nullifier, and room in the tree for the two change notes. |
| `exec_nonAdmin`, `OwnerHyp.nullifier_kept` | No step but an admin's, or the owner's own spend, closes an exit. Any other step keeps the leaves, the openings, the proved roots, the accepted ASP roots and the stop flags, and spends none of the owner's nullifiers.                |
| `Run.feesOK`                               | No fee schedule ever charges more than 3%.                                                                                                                                                                                              |

A note has no exit without an attester, and the tree can be filled by anyone's transfers. Both stay hypotheses, stated
at the state where the exit runs.

**The deployed circuits** (`Zerc20/Main.lean`, `Zerc20/Nova.lean`):

| Theorem                                                                  | Meaning                                                                                                                                               |
| ------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------- |
| `joinSplit_accepts`, `rageExit_accepts`, `root_accepts`, `merge_accepts` | What the model's verifiers accept is exactly what each circuit's constraints satisfy: soundness and completeness of every circuit against its `Spec`. |
| `decider_sound`                                                          | An accepted call to the root or merge decider contract is a chain of the spec, from the call's initial state to its final one.                        |
| `treeRoot_empty`                                                         | The ledger's initial root is the contract's `EMPTY_ROOT`.                                                                                             |
| `Circomlib.PoseidonEx.opt_eq_std`                                        | circomlib's optimized Poseidon computes the standard permutation that arkworks' sponge computes, on every input.                                      |

## Assumptions

Every assumption is an explicit hypothesis of the theorems that use it.

- **Cryptography, per run.** A run must meet no Poseidon collision among the inputs it hashes, no input that hashes to
  zero, no SHA-256 collision among its hash-chain inputs, and no signature under the owner's key on a message the owner
  did not sign (`RunHyp`, `OwnerHyp`).
  - These are stated about the values of one run, never as a global property. Poseidon and SHA-256 compress, so they
    have collisions. A hypothesis that one is injective everywhere is false, and every theorem resting on it would be
    vacuous.
- **Burn addresses.** A burn address is the low 160 bits of a digest with 16 bits of proof of work. Safety assumes no
  account opened as a burn address in the run is ever debited, and that no two burn openings in the run share an
  address unless they share the digest.
  - Breaking the first needs a burn address that is also an account whose key someone holds. That holder could move
    the deposit and also spend it privately. It is a birthday search between 160-bit addresses: about 2^72 burn
    addresses at 2^16 hashes each, against 2^88 keys, so about 2^89 work.
  - Breaking the second needs two openings with one address, which would let one deposit be spent twice: about 2^80
    digests that pass the proof of work, so about 2^96 hashes.
- **Proof systems.** An action carries the witness that knowledge soundness extracts. This assumes honest setups: the
  testnet's are single-operator, for development only, and the mainnet's come from a multi-party ceremony that needs
  one participant who forgets their secrets.
  - The Groth16 verifiers accept exactly the satisfiable statements.
  - The Nova deciders are proved by sonobe's Lean proofs, which this project imports. `decider_sound` rests on their
    hypotheses, again about the values of one run: the decider's SNARK extracts a valid witness from the accepted call,
    every fold rewinds to accepting witnesses that break no binding, and the state hash meets no collision. sonobe
    also proves that an honest run meets them, so they are not vacuous.
- **Admin.** The model covers pausing, the blocklist, fees, attesters, the ASP publisher, guardians and emergencies,
  `recover`, and token creation. It leaves out upgrades and verifier swaps: the theorems are about this implementation
  and these verifiers.

## What is trusted

- The circom compiler (with `--O2`) and arkworks synthesis, here and in sonobe, turn the composition of the modelled
  templates and gadgets into the circuits' constraints. Picus checks the R1CS for underconstraint.
- BN254 and Grumpkin have prime order, and BN254's pairing is nondegenerate: counting their points and evaluating the
  pairing are beyond these proofs.
- **Model fidelity.** The contracts and gadgets are modelled by hand, one Lean definition per Solidity function, circom
  template or Rust function, under the same name, so a reader can check them side by side.
  - `lake test` runs the Lean spec on `zkp/test-vectors/circuit-vectors.json`, which the circuits' conventions generate.
  - The models are the Solidity and Rust as written: the EVM's SHA-256 is the FIPS spec, and Solidity's checked
    arithmetic and OpenZeppelin's ERC-20 are modelled where they can revert.
- **Poseidon constants.** `scripts/poseidon_constants.mjs` generates them from circomlib's files and has a `--check`
  mode. A Rust test pins arkworks' constants to the same ones.
- Each action is atomic: every contract function makes its external calls last and is `nonReentrant`. Gas and
  front-running are not modelled.

## Layout

| Files                                              | Content                                                                                    |
| -------------------------------------------------- | ------------------------------------------------------------------------------------------ |
| `Field`                                            | BN254's scalar field, prime by a Pratt certificate.                                        |
| `Spec`, `Tree`                                     | Keys, notes, nullifiers, leaves, the commitment tree, and what each circuit proves.        |
| `Model`, `Frame`                                   | The contracts, one function per Solidity function, and what each changes.                  |
| `Hyp`, `Inv`, `Preserve`                           | A run's hypotheses, and the invariant every state of a run keeps.                          |
| `Safety`, `Liveness`, `Main`                       | The theorems above.                                                                        |
| `Circomlib`, `Circom`                              | circomlib's templates and zERC20's circom templates, JoinSplit and RageExit.               |
| `Ark`, `Sha256`, `BabyJubJub`, `Poseidon`, `Steps` | arkworks' gadgets, SHA-256, the Baby-JubJub group, Poseidon, and the root and merge steps. |
| `Nova`                                             | The root and merge deciders, through sonobe's proofs.                                      |

## Build

```
lake build   # Lean v4.30.0, Mathlib and sonobe pinned in lake-manifest.json
lake test    # the spec against the circuits' test vectors
node scripts/poseidon_constants.mjs --check
```
