# zkp

- `circom/`: JoinSplit / Rage Exit circuits.
- `src/`, `tests/`: Rust Nova pipelines for root transitions and merges.

## Artifacts

`scripts/artifacts.mjs` gives each circuit (`joinsplit`, `rageexit`, `root`, `merge`) a fresh
randomized setup, places its verifier in `contracts/`, and uploads its keys to S3:

```sh
npm run artifacts:setup -- rageexit joinsplit   # no names = all four
ZKP_ARTIFACTS_S3=s3://bucket/prefix npm run artifacts:upload -- rageexit joinsplit
```

A network serves its bucket at `https://artifacts.<DOMAIN>/<circuit>/<setup id>/<file>`: wallets
fetch their keys there, and node operators the Nova keys of the setup the deployed verifier names.

- `setup` writes `artifacts/<circuit>/` with the keys and a `setup.json` with the setup id and the
  size and SHA-256 of each key file. The id (`<UTC time>-<git describe>`) is also written into the
  generated contracts, so a contract can be matched to its keys.
  - Circom: compiles with `--O2`, then runs a Groth16 setup on a random ptau. The ptau is generated
    once per power and cached in `artifacts/ptau/`. Keys: `<c>.wasm`, `<c>.zkey`, `<c>_vk.json`.
    Writes `contracts/src/verifiers/generated/<C>Groth16Verifier.sol`. For `rageexit` it also
    re-proves the fixture in `contracts/test/RageExitFixture.sol`.
  - Nova: runs `params_gen`. Keys: `<c>_ivc_key.bin`, `<c>_decider_pk.bin` (several GB),
    `<c>_decider_vk.bin`. Writes `contracts/src/verifiers/generated/<C>NovaVerifier.sol`, which
    flattens sonobe's `LegoGroth16Verifier` and `DeciderVerifier` into `<C>LegoGroth16Verifier`
    and `<C>DeciderVerifier`. `MergeDeciderVerifier` implements `IMergeDeciderVerifier`.
  - Nova setup takes much longer than circom, so name only the circuits you changed.
- `upload` copies the files listed in `setup.json` to `<S3>/<circuit>/<id>/`, the circom wasm and
  zkey Brotli-encoded (`Content-Encoding: br`, which browsers and Node's fetch decode, and curl
  with `--compressed` where it has brotli): CloudFront compresses nothing past 10 MB, and Brotli
  halves a zkey. Then it copies that `setup.json` to
  `<S3>/<circuit>/latest.json`. Credentials come from the usual AWS CLI
  configuration (`AWS_PROFILE` and so on).

The circom and decider keys come from one process with random entropy. They are for development and
testnet only and must never back a mainnet verifier.

The mainnet's keys come from a multi-party ceremony, sound as long as one participant's randomness stays secret. Seven
turns made them: four on the developers' own machines, the initial state and three contributions, and three
contributions inside TEEs, two in AWS Nitro Enclaves and one in Google Cloud Confidential Space on Intel TDX. Opus 5.5
operated the trusted setup in the TEEs, and Mythos 5.1 supervised the process and audited the result.
[leohio/zERC20TrustedSetupwithTEE](https://github.com/leohio/zERC20TrustedSetupwithTEE) holds the ceremony's details:
the TEEs' attestations with their cloud providers' signatures, the record of the final step, and the audit.

## Rage Exit

`circom/main/rageexit.circom` refunds a burn deposit to its sender without the ASP and without a
proved commitment root, so it keeps working when root transitions stop:

1. After the deposit (ideally right after it), anyone calls `CommitmentLedger.reserveHashChain()` to
   record a checkpoint. Exits should end at a recorded checkpoint: the live head stops matching as
   soon as anything else is committed.
2. `Verifier.rageExit` passes the hash chain right before the deposit, the deposit and every later
   commitment up to that checkpoint (all in `Committed` events) to `CommitmentLedger.verifySegment`,
   which re-hashes them onto the checkpoint. This authenticates the deposit and its index on-chain,
   with no SHA-256 or Merkle work in the circuit.
3. The Groth16 proof shows ownership of the burn address and derives the deposit's nullifier, with
   public signals `[nullifier, chain_id, commitment_index, burn_address]`.

Walking costs about 1.5k execution gas plus ~1-1.3k calldata gas per commitment, and one transaction
carries about 1,000 commitments (the 128 KB transaction size limit). For a longer gap, call
`CommitmentLedger.checkpointBefore` repeatedly to move a checkpoint back toward the deposit in chunks.

## Nova Pipelines

Nova folds one step per item and compresses the result into a LegoGroth16 proof verifiable on the
EVM. Two step circuits share the pipeline:

- Root (`src/root.rs`): one step per appended commitment, over `[index, hash_chain, root]`.
  `CommitmentLedger.proveRootTransition` builds `i` (the index delta), `z_0` (its current root
  state) and `z_i` (the claimed state) itself and checks the proof with the rendered decider
  verifier.
- Merge (`src/merge.rs`): one step per spent input (a private note or a burn deposit, with
  JoinSplit's `in0` semantics), over `[token_id, chain_id, commitment_root, asp_root,
nullifier_chain, signed_chain, note_hash, remaining, fee, fee_recipient]`. N inputs become one
  output note:
  - `nullifier_chain` is a SHA-256 chain the contract recomputes from the published nullifiers.
  - `signed_chain` is the chain the inputs' owners signed (see Keys). The contract puts the chain it
    recomputes in `z_0` and `z_i`, so the merge spends exactly the inputs they signed.
  - `note_hash` is the output note accumulated so far.
  - `remaining` counts down the steps left, so the last step, which pays `fee` out of the sum, is
    found from the state alone, not from the step index.
  - `Verifier.merge` builds `i`, `z_0` and `z_i` itself, checks the proof with the rendered decider
    verifier, and mints `fee` to `fee_recipient` (the relayer that sends the merge).

Modules:

- `poseidon.rs`, `tree.rs`: circomlib-compatible Poseidon and the commitment tree, including the
  chunks and pages the backend stores and serves it in
- `primitives.rs`, `commitments.rs`: the keys, nullifiers, note hashes, burn addresses and tree
  leaves of `circom/lib/primitives.circom` and `commitments.circom`, and the SHA-256 hash chain,
  for the circuits, the wallet and the backend alike
- `auth.rs`: the owners' signatures (see Keys)
- `wallet_keys.rs`: the keys and burn salts a wallet derives from its seed
- `root.rs`, `merge.rs`: the two step circuits
- `ivc.rs`: Sonobe IVC / decider types (generic over the state type), key generation, and folding
- `evm.rs`: the on-chain `NovaDeciderProof` of root and merge decider proofs
- `artifacts.rs`: the on-disk key format
- `bin/params_gen.rs`: generates one circuit's keys and Solidity verifiers (see Artifacts)

## Keys

A private key `sk` derives two keys. A note commits to the public key of both:

```
nk         = H(NULLIFYING_KEY, sk)
ask        = SHA-512("zerc20/keys/auth-secret/v1", sk) mod l
ak         = ask·G
public_key = H(PUBLIC_KEY, H(AUTH_KEY, ak.x, ak.y), nk)
```

- `H(TAG, …)` is circomlib's Poseidon over the tag, then the values. A tag is `sha256(label) mod p`,
  listed in `circom/lib/constants.circom`.
- `SHA-512(…)` hashes its fields, each prefixed with its length as 4 bytes big-endian. Field
  elements and scalars are 32 bytes big-endian, and the digest is read as a big-endian integer.
- `ask` is the signing secret, and `ak` is the signing key: a point of Baby-JubJub as
  `ark-ed-on-bn254` writes it (`x² + y² = 1 + d·x²·y²` over BN254's scalar field), `G` its generator
  and `l` the prime order of `G`'s subgroup.
- The circuits accept any `ak`. Deriving `ask` from `sk` is the wallets' convention, so that the
  seed alone restores it, and it fixes every public key: changing it would strand every note.

A signature on a message `m` is `(R, s)`, a Schnorr signature with a Poseidon challenge:

```
sign:    k = SHA-512("zerc20/auth/nonce/v1", ask, m) mod l
         R = k·G
         c = H(SPEND_AUTH, R.x, R.y, H(AUTH_KEY, ak.x, ak.y), m)
         s = k + (c mod l)·ask  mod l
verify:  s·G = R + c·ak, with c taken as an integer below p
```

- The nonce is a hash of the secret and the message, so a wallet needs no randomness, and two
  messages never share a nonce.
- A verifier refuses an `ak` or an `R` off the curve or outside the order-`l` subgroup, and the
  identity as `ak`, under which anyone could sign. The merge step gets the subgroup from allocating
  both as witnesses, which clears the cofactor, and enforces `ak ≠ identity`. It takes `s` as bits
  that may encode a value at or above `l`; that only encodes the same signature another way.
- The messages:
  - merge: `H(MERGE_AUTH, nullifier_chain, out_public_key, out_salt, fee, fee_recipient)`, where
    `nullifier_chain` is the chain `Verifier.merge` computes over the merge's nullifiers;
  - transact: `H(TRANSACT_AUTH, hi, lo)`, where `hi` and `lo` are the high and low 16 bytes of the
    statement's EIP-712 struct hash (`Transact`, the struct the attester signs).

Who spends with what:

- JoinSplit and RageExit, which the wallet proves itself, take `sk` and the signing key's hash.
  `sk` opens `nk`, so only its holder spends there, and they check no signature.
- The merge step takes `ak`, `nk` and the owner's Schnorr signature on the merge: the nullifier
  chain, the output's owner and salt, and the fee. The attester checks transacts and merges the
  same way, natively, against a signature on the statement. So the merge prover and the attester,
  which a wallet sends its witnesses, never hold `sk` or the signing secret, and can spend nothing
  the owner did not sign.

What is checked where, for a transact (JoinSplit) and a merge:

|                                        | JoinSplit circuit          | merge circuit          | attester                                        | contract                                      |
| -------------------------------------- | -------------------------- | ---------------------- | ----------------------------------------------- | --------------------------------------------- |
| the note's owner                       | `sk` → `nk` → `public_key` | `public_key(ak, nk)`   | `public_key(ak, nk)`                            | —                                             |
| the owner's consent                    | knowing `sk`               | signature              | signature                                       | —                                             |
| the nullifier                          | ✓                          | ✓                      | ✓                                               | unspent                                       |
| the set signed is the set spent        | —                          | carries `signed_chain` | the signature covers the statement's nullifiers | puts their chain in a merge's `z_0` and `z_i` |
| membership, ASP approval, conservation | ✓                          | ✓                      | ✓                                               | the roots are accepted                        |
| the proof                              | —                          | —                      | —                                               | Groth16 / Nova decider                        |
| the attestation                        | —                          | —                      | signs it (EIP-712)                              | a registered attester signed                  |

The circuits and the attester check the same things apart: the attester recomputes them natively
from the protocol's definitions, so it insures against a circuit soundness bug. RageExit checks the
owner as JoinSplit does and has no attester: the contract authenticates the deposit itself.

What a merge prover sees:

- The IVC proof (`Folded::ivc_proof`) contains the full step witnesses: every input's opening,
  `ak` and `nk`. Never send or publish it; only the decider proof leaves the prover.
- The decider proof hides the witnesses through hiding Pedersen commitments and LegoGroth16, but
  Sonobe makes no formal zero-knowledge claim.
- With `nk`, a prover can find the key's other spends among the nullifiers on chain.

Normal checks cover Poseidon parity, the circuit vectors, and step constraints:

```sh
cargo fmt --all -- --check
cargo clippy -p zerc20-zkp --all-targets --locked -- -D warnings
cargo test -p zerc20-zkp --locked
```

The full ignored tests (root and merge) generate IVC and LegoGroth16 decider keys, fold two steps,
round-trip the custom key formats, verify the compressed proof natively, and verify it again through
the rendered Solidity contracts in an EVM harness, with the calldata reassembled the way the
on-chain caller does:

```sh
SOLC=/path/to/solc-0.8.37 \
  cargo test -p zerc20-zkp --release --test nova_ivc -- --ignored --nocapture
```

Nova keys come from `npm run artifacts:setup -- root merge` (see Artifacts). They are stored
uncompressed (the decider prover key is several GB), so the prover's startup load is bound by IO
instead of by decompressing ~10^8 curve points.
Production use requires an approved trusted-setup process and a versioned manifest binding the exact
Sonobe revision, circuit, keys, and generated Solidity hashes.

Sonobe is pinned by rev in `Cargo.toml`. Its IVC crate is built without the opt-in
`ark-std/print-trace` feature, which writes prover timing output to stdout, where a binary prints
the results a script reads. Keep any prover progress reporting on stderr.
