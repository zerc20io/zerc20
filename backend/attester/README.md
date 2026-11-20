# attester

Signs the statements of `Verifier.transact` and `Verifier.merge` (EIP-712 `Transact` and `Merge`)
once it has checked them. It is insurance against circuit soundness bugs, plus the AML check on
withdrawals. It is a host process and an AWS Nitro Enclave on the same instance. One host serves
every chain in `CHAINS` (`backend/README.md`), each against its own indexer, and one enclave
signs for them all, since it is chain-agnostic.

## Why it looks like this

**The host checks the public statement, the enclave checks the witness.** A request is checked in
order of cost:

1. the host: `chainId` is this chain's, and `commitmentRoot` is a root the indexer derived itself;
2. the enclave: the witness, sealed to it, proves exactly this statement;
3. the host: for a withdrawal, the recipient passes Chainalysis. Only requests with a valid witness
   get this far, so junk cannot use up the Chainalysis quota.

The enclave signs, and the host returns the signature only if step 3 passes. A compromised host
defeats steps 1 and 3, but not step 2.

**The witness is checked against the protocol's definitions, not against the circuits.**
`proto/src/check.rs` recomputes the statement from the witness with the native primitives in
`zkp/src/primitives.rs` and `zkp/src/commitments.rs`. Running the circuits' constraints
(`MergeCircuit` and `is_satisfied`, or the circom witness) would trust an under-constrained circuit
a second time.

A spend (JoinSplit's `in0`, a real `in1`, and every merge input) is checked like this:

- The note is owned by the public key of the witness's signing key `ak` and nullifying key `nk`. `ak` is a point of
  prime order and not the identity. The witness's own public keys are ignored.
- The owner signed the statement under `ak` (`zkp/src/auth.rs`): a transact's EIP-712 struct hash, or a merge's
  nullifier chain, output owner and salt, and fee.
- For a burn deposit, the burn address has its proof of work, the value is not 0, and the ASP
  approved the deposit at the deposit's own position.
- The leaf sits under `commitmentRoot` at an index below 2^32.
- The nullifier is keyed by that position.

**A witness holds no private key**, only what each input's private key derives and its owner's signature. A
compromised enclave learns the inputs, and with their nullifying keys it can link those keys' spends, but it can spend
nothing: JoinSplit needs the private key, and a merge its owners' signature on that very merge (`zkp/README.md`, Keys).
It can still sign any statement, which matters only together with a circuit soundness bug.

The check also covers range checks on every amount, address, token and chain id, canonical field
elements (never reduced mod p), conservation, distinct nullifiers, and a zero recipient and
`withdrawIntent` when nothing is withdrawn. The intent is otherwise not interpreted here. The
contract enforces the rest: fresh nullifiers, an accepted `aspRoot`, a proved root, a nonzero
recipient on a withdrawal, and an intent it knows.

**Only roots the indexer derived itself are attested.** A circuit soundness bug could put a forged
root into `provedRoots`, and the indexer recomputes every proved root. The host polls `/roots/{p}`
every 2 s and keeps the roots whose entry says they match.

- Before it adds new roots, it checks the newest one with this chain's `provedIn`, so another
  chain's indexer cannot have its roots attested here. That says whether the chain proved it at
  all: in an emergency the ledger accepts no root above its bound, which the contract enforces.
- A root later reorged away stays in memory but fails on chain.

**While Chainalysis is down, the Blocklist alone decides.**

- `Low` and `Medium` pass; `High` and `Severe` get 403.
- Any other answer, a 429 or a timeout gets 503, and the client retries.
- Once Chainalysis has been down for `FALLBACK_SECS` (5 minutes), a screening it fails is decided by
  the protocol's `Blocklist` alone, at once. An outage holds withdrawals back only that long, and
  Chainalysis still decides every recipient it answers about.
- Down is what a probe finds, asking about a fixed address every 30 s. A client chooses when its own
  screenings fail: it can add load until Chainalysis's rate limit refuses them, or retry until one
  hits a blip. So its screenings never count, and the probe takes a 429 for the answer it is.
- Private transfers have no recipient and are never screened. A merge's `feeRecipient` is, when it
  is paid a fee: the fee is a public withdrawal, so a large one to oneself would otherwise skip
  screening.

**Screenings take turns, so that no client uses up the key the ASP shares.** With one note, a
client could otherwise sign withdrawals to any number of recipients and have each one screened.
While Chainalysis refuses for its rate limit, the ASP approves no deposit and withdrawals get 503.

- The attester screens at most 10 a second, every chain together, of the 40 Chainalysis allows. A
  screening waits up to 2 s for its turn, then gets 429.
- A note gets 3 screenings at once, then one per 5 minutes, whatever the recipients. Every
  nullifier of the statement counts, so a dummy `in1`, which is free to pick, cannot stand in for
  the real `in0`.
- Only a statement the enclave signed takes a turn, so junk takes none and never reaches
  Chainalysis.
- A client holding 3000 notes can still take the attester's share and hold withdrawals back for as
  long as it keeps going. The ASP's share stays its own.

**The host never sees a witness.** Wallets seal it to the enclave's X25519 key with HPKE. The host
can still replay a sealed witness under statements of its own, so a witness that does not prove
its statement gets one error, whatever the reason, and a merge's fee above its value takes the
work of one below it: which check failed, or how long it took, would tell which fees are above the
value, and so the value. A burn input still takes more work than a note, so the time an answer
takes can tell the host which inputs are burns, and whether a transact's second input is padding;
and a merge's owners do not sign its ASP root, so a merge of notes alone proves any, and one with a
burn does not. The enclave logs nothing about a request.

**The signing key never leaves the enclave.** It is a secp256k1 KMS data key pair:

1. Once, an admin generates it with `generate-data-key-pair-without-plaintext`. That yields its
   public key and its private half encrypted under a KMS key. The private half never exists in
   plaintext outside KMS.
2. At boot the enclave makes a throwaway RSA key and an NSM attestation document over it, which
   carries the enclave image's measurement (PCR0).
3. `zerc20-attester load-key` calls `kms decrypt` on the blob with that document as `Recipient`.
   KMS checks the document and the key policy's PCR0, and returns the key encrypted to the RSA key
   (CMS). The host only ever holds ciphertext.
4. The enclave decrypts it and signs in memory. `load-key` does nothing while the enclave has a key,
   so a deployment runs it as root every minute, which loads the key again after a restart.

`load-key` is apart from the host that serves, which waits for the key and never holds AWS
credentials: on the instance only root reaches them, and the serving host runs as another user.

Not KMS `Sign`: attestation conditions do not apply to it, and the host holds the same IAM
credentials.

**The enclave binary has no development path.** In development the host runs the same logic in
its own process, over a loopback socket, with `DEV_SIGNING_KEY`. Nothing the host sends can switch
a real enclave into it.

## API

|                    |                                                                                                                                                                                |
| ------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `GET /attestation` | `{publicKey, attestation, address}`: the key to seal witnesses to (32 bytes), the NSM attestation document over it (base64, `null` in development), and the attester's address |
| `POST /transact`   | `{statement, witness}` → `{attestation}`                                                                                                                                       |
| `POST /merge`      | `{statement, witness}` → `{attestation}`                                                                                                                                       |

- `statement` is `TransactSignals` (`{tokenId, chainId, commitmentRoot, aspRoot, nullifier0, …}`)
  or `{tokenId, chainId, commitmentRoot, aspRoot, nullifiers, noteHash, fee, feeRecipient}`.
  Numbers are decimal or `0x` strings.
- `attestation` is the 65-byte signature (`r‖s‖v`) that goes into `TransactRequest.attestation` or
  `MergeRequest.attestation`.

| status | meaning                                                                                                               |
| ------ | --------------------------------------------------------------------------------------------------------------------- |
| 400    | wrong chain, a root the indexer has not derived (yet: retry), or a witness that does not prove the statement          |
| 403    | the withdrawal recipient (or a merge's fee recipient) fails screening                                                 |
| 429    | the statement's notes, or the attester as a whole, have used up their screenings for now: retry later                 |
| 503    | the enclave is unavailable or has no key yet, or screening failed with Chainalysis down for less than `FALLBACK_SECS` |

**Witnesses.** Plaintext is JSON:

- transact: the JoinSplit circuit's input JSON as snarkjs takes it (`zkp/circom/main/joinsplit.circom`), with each
  `private_key{0,1}` replaced by `auth_key{0,1}` (`[x, y]`), `nullifying_key{0,1}` and `signature{0,1}`
  (`{r: [x, y], s}`). Redundant fields such as `in_note0_public_key` and `auth_key_hash0` are ignored, and so are a
  dummy `in1`'s keys.
- merge: `{inputs: [{is_burn, auth_key, nullifying_key, signature, commitment_index, commitment_siblings,
note_value, note_salt, burn_salt, burn_from, burn_value, asp_siblings}, …], out_public_key, out_salt}`. These are
  `zkp::merge::MergeStep`'s fields; the output's opening is given once. The merge prover takes the same.
- The wallet core's `signTransact` and `signMerge` make both from the witness the wallet proves with.

**Sealing.** The wire format is the encapsulated key (32 bytes) followed by the ciphertext, as `0x`
hex. `zerc20_attester_proto::seal` is the reference.

- HPKE (RFC 9180) base mode, with DHKEM(X25519, HKDF-SHA256), HKDF-SHA256 and ChaCha20-Poly1305.
- `info` = `zerc20/attester/witness/v1`, `aad` empty.
- Pad the plaintext with trailing spaces to a fixed size, such as 16 KiB for a transact and 8 KiB
  per merge input. Its length otherwise leaks the amounts' digits.

**Wallets must verify `attestation` before sealing anything**, or the host could hand out its own
key and read every witness:

1. Check the COSE_Sign1 signature and its certificate chain up to the AWS Nitro Enclaves root
   (G1).
2. Check that PCR0 equals the value published for the release.
3. Take the key from the document's `public_key`, not from `publicKey`.

The key belongs to one enclave instance and changes when it restarts; a failure to open says to
fetch `/attestation` again. Behind a load balancer, keep each wallet on one instance.

## Run

| env                                         |                                                                                                                                                                             |
| ------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `RPC_URL`, `VERIFIER`                       |                                                                                                                                                                             |
| `INDEXER_URL`                               | this chain's indexer origin, not the CDN                                                                                                                                    |
| `CHAINALYSIS_API_KEY` or `DEV_PASS_ALL=1`   | exactly one. `DEV_PASS_ALL` passes every recipient, for development. The API takes no chain: on a testnet it screens an address by its mainnet record, which a testnet uses |
| `CHAINALYSIS_API_BASE_URL`, `FALLBACK_SECS` | default `https://api.chainalysis.com`, 300                                                                                                                                  |
| `ENCLAVE_CID`                               | production: the enclave's CID (default 16)                                                                                                                                  |
| `KMS_KEY_ID`, `ATTESTER_KEY_BLOB`           | `load-key` only, with `ENCLAVE_CID`: the KMS key, and the file holding the key pair's encrypted private half                                                                |
| `DEV_SIGNING_KEY`                           | development, instead of an enclave: runs the enclave's logic in this process with this key                                                                                  |
| `LISTEN`, `RUST_LOG`                        | default `0.0.0.0:3002`, `info`                                                                                                                                              |

**Development** needs no Nitro, KMS or Chainalysis:

```sh
DEV_SIGNING_KEY=0x… DEV_PASS_ALL=1 RPC_URL=… VERIFIER=… INDEXER_URL=… cargo run -p zerc20-attester
KEEP=1 backend/attester/scripts/e2e.sh   # or: a whole local stack, left running after the e2e
```

Register the development key with `Verifier.addAttester`. `scripts/e2e.sh` does that for its own
key (anvil account 3).

```sh
cargo test -p zerc20-attester
cargo test -p zerc20-attester --features enclave --bin enclave  # the KMS key unwrapping
backend/attester/scripts/e2e.sh
```

The e2e runs on anvil, Postgres and the indexer with `IndexerFixture`. `examples/e2e.rs` plays the
wallet:

- It makes notes and a burn deposit with known openings, gets the ASP to approve the deposit, and
  proves the true root.
- It has the attester sign a withdrawal from the deposit plus a note, a private transfer, and a
  merge. It submits each one, so the contract checks the signatures.
- It covers rejections: a tampered statement, a root the indexer did not derive, another chain, and
  Chainalysis down for less than `FALLBACK_SECS` and for longer.

It needs what the indexer's e2e needs, and has to run outside the Claude Code sandbox for the same
reason.

## Deploy on Nitro

1. **Build the image:**

   ```sh
   backend/eif.sh attester attester.eif
   ```

   Pin the PCR0 it prints, never one a host recorded:
   the key policy and every wallet trust it, and a host is what they guard against. The same commit
   prints the same PCR0 on any machine, so anyone can check it by building.

2. **Create a symmetric KMS key with this policy.**
   - The Deny statements make the attestation mandatory. A negated condition is true when the key
     is absent, so a plain `Decrypt` is refused even with an IAM grant, and `ReEncrypt` cannot route
     around it.
   - The admin role can rewrite the policy, so guard it like the protocol's `ADMIN_ROLE`. It gets `kms:*`, which is
     no more than that: the Deny statements bind it too. (A narrower list must still hold
     `GenerateDataKeyPairWithoutPlaintext`, which makes the key pair, and what CloudFormation calls on updates.)
   - Admin is the account narrowed by `aws:PrincipalArn`, not one role's ARN: an SSO role is renamed when its
     permission set is made again, and a key naming only the old role is left with no admin. For an SSO role, end
     the pattern in `AWSReservedSSO_<permission set>_*`.
   - `NoOneElseManages` keeps every other role of the account off the key, whatever its IAM policies grant.
   - Never name an all-zero PCR0: that is what a `--debug-mode` enclave measures.
   - During an upgrade, list both PCR0 values.

   ```json
   {
     "Version": "2012-10-17",
     "Statement": [
       {
         "Sid": "Admin",
         "Effect": "Allow",
         "Principal": { "AWS": "arn:aws:iam::<account>:root" },
         "Action": "kms:*",
         "Resource": "*",
         "Condition": { "ArnLike": { "aws:PrincipalArn": "arn:aws:iam::<account>:role/<admin pattern>" } }
       },
       {
         "Sid": "NoOneElseManages",
         "Effect": "Deny",
         "Principal": "*",
         "NotAction": "kms:Decrypt",
         "Resource": "*",
         "Condition": { "ArnNotLike": { "aws:PrincipalArn": "arn:aws:iam::<account>:role/<admin pattern>" } }
       },
       {
         "Sid": "EnclaveDecrypt",
         "Effect": "Allow",
         "Principal": { "AWS": "arn:aws:iam::<account>:role/<attester-host>" },
         "Action": "kms:Decrypt",
         "Resource": "*",
         "Condition": { "StringEqualsIgnoreCase": { "kms:RecipientAttestation:ImageSha384": "<PCR0>" } }
       },
       {
         "Sid": "NoDecryptOutsideTheEnclave",
         "Effect": "Deny",
         "Principal": "*",
         "Action": "kms:Decrypt",
         "Resource": "*",
         "Condition": { "StringNotEqualsIgnoreCase": { "kms:RecipientAttestation:ImageSha384": "<PCR0>" } }
       },
       {
         "Sid": "NoReEncrypt",
         "Effect": "Deny",
         "Principal": "*",
         "Action": ["kms:ReEncryptFrom", "kms:ReEncryptTo"],
         "Resource": "*"
       }
     ]
   }
   ```

3. **Generate the key pair once, and keep both outputs:**

   ```sh
   aws kms generate-data-key-pair-without-plaintext --key-id $KMS_KEY_ID --key-pair-spec ECC_SECG_P256K1 > kp.json
   jq -r .PrivateKeyCiphertextBlob kp.json | base64 -d > attester-key.blob   # ATTESTER_KEY_BLOB
   pub=$(jq -r .PublicKey kp.json | base64 -d | tail -c 64 | xxd -p -c 64)
   cast to-check-sum-address 0x$(cast keccak 0x$pub | tail -c 41)            # the attester's address
   ```

4. **Register that address, and only that one**, with `Verifier.addAttester`, an `ADMIN_ROLE` call through the
   `AccessManager` (`contracts/README.md`).
   - Never register the address the host logs. The host knows the enclave's RSA key, so a
     compromised host could load a key of its own, and registering it would let the host sign
     anything.
   - The logged address is only a cross-check. Unless it matches, nothing the enclave signs is
     accepted.

5. **Run it:**

   ```sh
   nitro-cli run-enclave --eif-path attester.eif --cpu-count 2 --memory 1024 --enclave-cid 16
   KMS_KEY_ID=… ATTESTER_KEY_BLOB=attester-key.blob zerc20-attester load-key   # as root, again after each restart
   CHAINALYSIS_API_KEY=… RPC_URL=… VERIFIER=… INDEXER_URL=… zerc20-attester      # as any other user
   ```

   - Never use `--debug-mode`: it zeroes the PCRs, so KMS refuses the key anyway.
   - `load-key` needs the AWS CLI v2 and an instance role allowed to `kms:Decrypt`. Keep the
     serving host from that role: it is what the public talks to.
   - The host serves only once the enclave holds the key, and logs `the enclave signs as 0x…`.

6. **Check:**
   - a plain `aws kms decrypt` of the blob from the host fails with AccessDenied;
   - the `/attestation` document verifies;
   - one testnet transact goes through.
