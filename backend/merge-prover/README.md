# merge-prover

Proves Nova merges for wallets: N notes or burn deposits into one note, which a wallet cannot prove itself (the merge
decider key is 6.3 GB). A wallet builds the merge, has the attester sign it, sends the witness here sealed to the
enclave, and gets back the decider proof. It then has the transact-relayer send the merge.

- **It serves every chain.** A statement names its own, and the prover reads no chain.
- **It never sends a transaction.** The relayer does, and is paid by the merge's `fee`.

It is a host process and an AWS Nitro Enclave on one instance of its own.

## Why it looks like this

**The witness only opens in the enclave.**

- A merge's witness holds every input's opening and nullifying key, and so does the IVC proof folded from it
  (`zkp/README.md`).
- Wallets seal the witness to the enclave's key with HPKE under `zerc20/merge-prover/witness/v1`, after checking the
  enclave's attestation as they check the attester's.
- Only the decider proof leaves the enclave.
- The enclave's key is made at start and never kept, so a restart forgets nothing it should keep.

**It sees one merge, while it proves it.**

- Nothing is kept: no seed, no state, and no secret on the host.
- A compromised enclave can spend nothing. A witness holds no private key, only each input's signing and nullifying
  keys and its owner's signature on this merge, its output and its fee (`zkp/README.md`, Keys).
- What it learns is the merge's inputs. With their nullifying keys it can find those keys' other spends among the
  nullifiers on chain, but not their notes.
- What a compromised host can do: stop the service, drop jobs, and see statements (nullifiers, roots, the fee). It can
  also replay a sealed witness under statements of its own, which tells it which inputs are burns, by how long the
  check takes and by whether a merge proves any ASP root (`zerc20_attester_proto::check`).

**It checks a witness before folding it**, as the attester does (`zerc20_attester_proto::check::merge`). A witness
that does not prove its statement fails at once, not after minutes of folding.

**Jobs are keyed by the note they output.**

- A wallet that sends the same statement again, from another device or after a restart, gets the same job.
- A failed job is replaced by the next one sent.

**It is open.** Anyone may send a merge, from any frontend, with no key. What bounds what they cost:

- the queue (`QUEUE` jobs waiting or proving);
- `PER_CLIENT` of them per client address, which Caddy, the only way in, passes as `X-Forwarded-For`;
- Caddy's body limit of 2 MB.

It sits on its own instance so that a flood of merges cannot stop what every send and withdrawal needs: the
attester, the relayers, the indexer.

## API

|                                     |                                                                                                                                                                                                                                                      |
| ----------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `GET /enclave`                      | `{publicKey, attestation}`: the key to seal witnesses to, and the NSM document over it (`null` in development)                                                                                                                                       |
| `POST /proofs {statement, witness}` | 202 `{status}`. `statement` is the attester's `Merge`, and `witness` the attester's merge witness JSON sealed to `publicKey`. 400 for more than `MAX_INPUTS` inputs, 429 while the client has `PER_CLIENT` jobs waiting, 503 while `QUEUE` jobs wait |
| `GET /proofs/{noteHash}`            | `{status: queued \| proving \| done \| failed, proof?, error?}`. `proof` is `NovaDeciderProof`, ABI-encoded, for `MergeRequest.proof`. 404 for a job it never had, or lost in a restart: send it again                                               |
| `GET /status`                       | `{mergeKey, queued, proving}`                                                                                                                                                                                                                        |

## Run

| env                                 |                                                                                                                                                                                                                                                                          |
| ----------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `ENCLAVE_CID`                       | the enclave's CID (default 17)                                                                                                                                                                                                                                           |
| `SELF_HOSTED=1`                     | for the wallets of this machine, instead: runs the enclave's logic in this process, on a loopback `LISTEN` only, without CORS and for requests whose `Host` names this machine, and takes only the merge keys whose SHA-256 `MERGE_PK_SHA256` and `MERGE_VK_SHA256` name |
| `DEV_ENCLAVE=1`                     | development, instead: runs the enclave's logic in this process, which then sees every witness                                                                                                                                                                            |
| `DEV_SKIP_PROOF=1`                  | development, with `DEV_ENCLAVE=1`: checks each witness and answers an all-zero proof, without the merge keys. Only a merge verifier that accepts anything (`Deploy.s.sol` with `DEV_ACCEPT_ALL_MERGES`, anvil only) takes it. The enclave binary has no such path        |
| `ARTIFACTS_DIR`                     | the merge decider keys (default `zkp/artifacts/merge`), streamed into the enclave at start                                                                                                                                                                               |
| `QUEUE`, `PER_CLIENT`, `MAX_INPUTS` | default 8, 2, 100                                                                                                                                                                                                                                                        |
| `LISTEN`                            | default `127.0.0.1:3006`                                                                                                                                                                                                                                                 |

```sh
cargo test -p zerc20-merge-prover
SPEED=fast MERGE=1 KEEP=1 wallet/sdk/scripts/e2e.sh   # through wallets, wallet/sdk/test/e2e/pos.test.ts
```

`scripts/dev-stack.sh` runs this node with `MERGE=1`, proving, which needs the merge keys (`npm run artifacts:setup --
merge` in `zkp/`) and about 16 GB of memory. With `SPEED=fast` alone it runs it with `DEV_SKIP_PROOF=1`, which needs
neither.

## Run your own

A wallet's owner can prove their own merges, on the machine the wallet is on: no enclave is needed where the prover
sees only witnesses that machine holds already. `zerc20 prover start` (`@zerc20/cli`) fetches the merge keys, checks
them and runs this node with `SELF_HOSTED=1`; `zerc20 merge --prover local` then seals the merge to it. The wallet SDK
takes such a prover (`mergeProver.trust: { local: true }`) at a loopback address alone, so it cannot stand in for the
network's.

## Deploy on Nitro

1. **Build the image**, with the merge setup whose keys it is to accept:

   ```sh
   backend/eif.sh merge-prover merge-prover.eif zkp/artifacts/merge/setup.json
   ```

   The merge key hashes are compiled in, so PCR0 measures them. Pin the PCR0 it prints: wallets check it
   (`mergeProver.trust` in `network.json`) before they seal a witness to it. Never take it from what this host
   recorded: the host is what it guards against. The same commit and setup print the same PCR0 on any machine, so
   anyone can check it by building.

2. **Run it**, with memory for the merge key and its folding, and never `--debug-mode`:

   ```sh
   nitro-cli run-enclave --eif-path merge-prover.eif --cpu-count 6 --memory 16384 --enclave-cid 17
   ARTIFACTS_DIR=… zerc20-merge-prover
   ```

3. **Check:** `/enclave`'s document verifies, and one testnet merge goes through.

There is no KMS key: the enclave holds no secret that must outlive it.
