// Deterministic test vectors for the circuits' conventions: domain tags, keys, nullifiers, note hashes, burn
// addresses, tree leaves, and what a wallet derives from its seed.
//
// Source of truth: the as-built Circom circuits under `zkp/circom/lib/` (constants, poseidon,
// primitives, commitments, range). This script reproduces those exact derivations with circomlibjs
// (the canonical JavaScript twin of circomlib's Poseidon over BN254 Fr) and emits
// `circuit-vectors.json`, which the Rust, Solidity and Lean implementations are tested against, so
// none of them can silently diverge.
//
// Poseidon parity: circomlibjs `buildPoseidon()` matches `circomlib/circuits/poseidon.circom`
// byte-for-byte (e.g. poseidon([1,2]) == 7853200120776062878684798364095072458815029376092732009249414926327459813530).
//
// Run: `node zkp/test-vectors/gen_circuit_vectors.mjs` (from repo root or zkp/). No randomness — the
// inputs are fixed, so re-running is a no-op unless the convention changes (then it is a deliberate,
// reviewable breaking change committed alongside the code).

import { buildPoseidon } from 'circomlibjs';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const poseidon = await buildPoseidon();
const F = poseidon.F;

/** Poseidon over BN254 Fr, inputs and output as decimal strings (canonical field representative). */
function P(inputs) {
  return F.toString(poseidon(inputs.map((x) => BigInt(x))));
}

// ---- BN254 Fr + convention constants (verbatim from zkp/circom/lib/constants.circom) -------------

const Fr = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

// Poseidon domain-separation provenance. Labels are UTF-8 encoded, SHA-256 hashed, interpreted as
// one unsigned big-endian integer, then reduced modulo BN254 Fr. The corresponding frozen Circom
// constants are checked below so changing either the label or constants.circom alone fails CI.
const DOMAIN_LABELS = Object.freeze({
  NOTE: 'zerc20-note',
  PUBLIC_KEY: 'zerc20-public-key',
  NULLIFYING_KEY: 'zerc20-nullifying-key',
  NULLIFIER: 'zerc20-nullifier',
  DUMMY_NULLIFIER: 'zerc20-dummy-nullifier',
  BURN: 'zerc20-burn',
  ASP_LEAF: 'zerc20-asp-leaf',
  AUTH_KEY: 'zerc20-auth-key',
  SPEND_AUTH: 'zerc20-spend-auth',
  TRANSACT_AUTH: 'zerc20-transact-auth',
  MERGE_AUTH: 'zerc20-merge-auth',
});

function sha256LabelToField(label) {
  const digest = createHash('sha256').update(label, 'utf8').digest('hex');
  return BigInt(`0x${digest}`) % Fr;
}

const DOMAIN = Object.fromEntries(
  Object.entries(DOMAIN_LABELS).map(([name, label]) => [name, sha256LabelToField(label)]),
);

const scriptDir = dirname(fileURLToPath(import.meta.url));
const circomConstantsPath = join(scriptDir, '..', 'circom', 'lib', 'constants.circom');
const circomConstantsSource = readFileSync(circomConstantsPath, 'utf8');

function readCircomConstant(name) {
  const pattern = new RegExp(`function\\s+${name}\\s*\\(\\s*\\)\\s*\\{[^}]*return\\s+([0-9]+)\\s*;`, 's');
  const match = circomConstantsSource.match(pattern);
  if (!match) throw new Error(`unable to read ${name} from ${circomConstantsPath}`);
  return BigInt(match[1]);
}

for (const [name, derived] of Object.entries(DOMAIN)) {
  const circom = readCircomConstant(`DOMAIN_${name}`);
  if (derived !== circom) {
    throw new Error(
      `domain tag mismatch for ${name}: sha256(${JSON.stringify(DOMAIN_LABELS[name])}) mod Fr = ` +
        `${derived}, constants.circom = ${circom}`,
    );
  }
}

// Commitment-leaf field0 type tags: uint32(keccak256(solidity-signature)[:4]) << 32, occupying the
// high bits of field0; the low 32 bits carry the token id. (contracts ProtocolConstants mirror.)
const FIELD0_TAG_SHIFT = 32n;
const TRANSFER_FIELD0_BASE = 15992936129728872448n; // TRANSFER_TAG << 32
const NOTE_FIELD0_BASE = 8691708596607516672n; // NOTE_HASH_TAG << 32

// Field-encoding ranges (bits) — part of the convention; SDK / Solidity must range-check these.
const RANGES = {
  MERKLE_DEPTH: 32,
  AMOUNT_BITS: 248,
  ADDRESS_BITS: 160,
  TOKEN_ID_BITS: 32,
  CHAIN_ID_BITS: 64,
  BURN_POW_BITS: 16,
  FIELD_BIT_LENGTH: 254,
};

const MASK_160 = (1n << 160n) - 1n;
const SPEND_SECRET_DOMAIN = 'zerc20/keys/spend-secret/v1';

function u32Be(value) {
  const bytes = Buffer.alloc(4);
  bytes.writeUInt32BE(value);
  return bytes;
}

function lengthPrefixedDomainHash(label, parts) {
  const hash = createHash('sha256');
  for (const field of [Buffer.from(label, 'utf8'), ...parts]) {
    hash.update(u32Be(field.length));
    hash.update(field);
  }
  return hash.digest();
}

function canonicalSpendSecret(domain, parts) {
  for (let counter = 0; counter <= 0xffff_ffff; counter += 1) {
    const candidate = lengthPrefixedDomainHash(domain, [...parts, u32Be(counter)]);
    candidate[0] &= 0x3f;
    const value = BigInt(`0x${candidate.toString('hex')}`);
    if (value !== 0n && value < Fr) {
      return { counter, bytes: candidate, value };
    }
  }
  throw new Error('failed to derive a canonical spend secret');
}

// ---- spend authorization (zkp/src/auth.rs): Schnorr over Baby-JubJub -------------------------------

// ark-ed-on-bn254's form of Baby-JubJub: x^2 + y^2 = 1 + d x^2 y^2 over Fr, with its prime-order generator. (circomlib
// writes the same curve as 168700 x^2 + y^2 = 1 + 168696 x^2 y^2, in other coordinates.)
const ED_D = 9706598848417545097372247223557719406784115219466060233080913168975159366771n;
const ED_ORDER = 2736030358979909402780800718157159386076813972158567259200215660948447373041n;
const ED_G = [
  19698561148652590122159747500897617769866003486955115824547446575314762165298n,
  19298250018296453272277890825869354524455968081175474282777126169995084727839n,
];

const mod = (a, m) => ((a % m) + m) % m;
function inv(a) {
  let [result, base, e] = [1n, mod(a, Fr), Fr - 2n];
  for (; e > 0n; e >>= 1n, base = (base * base) % Fr) if (e & 1n) result = (result * base) % Fr;
  return result;
}
function edAdd([x1, y1], [x2, y2]) {
  const t = (((((((ED_D * x1) % Fr) * x2) % Fr) * y1) % Fr) * y2) % Fr;
  return [mod((x1 * y2 + y1 * x2) * inv(1n + t), Fr), mod((y1 * y2 - x1 * x2) * inv(1n - t), Fr)];
}
function edMul(point, k) {
  let [result, base] = [[0n, 1n], point];
  for (; k > 0n; k >>= 1n, base = edAdd(base, base)) if (k & 1n) result = edAdd(result, base);
  return result;
}

const be32 = (x) => Buffer.from(BigInt(x).toString(16).padStart(64, '0'), 'hex');
/** SHA-512 over length-prefixed fields, reduced mod the group order. */
function hashToScalar(label, parts) {
  const hash = createHash('sha512');
  for (const field of [Buffer.from(label, 'utf8'), ...parts]) {
    hash.update(u32Be(field.length));
    hash.update(field);
  }
  return BigInt(`0x${hash.digest('hex')}`) % ED_ORDER;
}

const authSecret = (privateKey) => hashToScalar('zerc20/keys/auth-secret/v1', [be32(privateKey)]);
const authKeyHash = ([x, y]) => P([DOMAIN.AUTH_KEY, x, y]); // DomainHash2 -> Poseidon(3)

function sign(secret, message) {
  const nonce = hashToScalar('zerc20/auth/nonce/v1', [be32(secret), be32(message)]);
  const r = edMul(ED_G, nonce);
  const c = BigInt(P([DOMAIN.SPEND_AUTH, r[0], r[1], authKeyHash(edMul(ED_G, secret)), message]));
  return { r, s: mod(nonce + (c % ED_ORDER) * secret, ED_ORDER) };
}

// DomainHash2 -> Poseidon(3) over the EIP-712 struct hash's two 128-bit halves
const transactMessage = (structHash) =>
  P([DOMAIN.TRANSACT_AUTH, BigInt(structHash) >> 128n, BigInt(structHash) & ((1n << 128n) - 1n)]);
// DomainHash5 -> Poseidon(6)
const mergeMessage = (nullifierChain, outPublicKey, outSalt, fee, feeRecipient) =>
  P([DOMAIN.MERGE_AUTH, nullifierChain, outPublicKey, outSalt, fee, feeRecipient]);

// ---- protocol object derivations (verbatim from primitives.circom / commitments.circom) ----------

const nullifyingKey = (privateKey) => P([DOMAIN.NULLIFYING_KEY, privateKey]); // DomainHash1 -> Poseidon(2)
// DomainHash2 -> Poseidon(3): [tag, auth_key_hash, nullifying_key]
const publicKeyOf = (authKeyHash, nk) => P([DOMAIN.PUBLIC_KEY, authKeyHash, nk]);

/** Everything a private key derives. */
function keysOf(privateKey) {
  const secret = authSecret(privateKey);
  const authKey = edMul(ED_G, secret);
  const hash = authKeyHash(authKey);
  const nk = nullifyingKey(privateKey);
  return {
    auth_secret: secret.toString(),
    auth_key: authKey.map(String),
    auth_key_hash: hash,
    nullifying_key: nk,
    public_key: publicKeyOf(hash, nk),
  };
}

// DomainHash5 -> Poseidon(6): [tag, chain_id, public_key, value, token_id, note_salt]
const noteHash = (chainId, pk, value, tokenId, noteSalt) => P([DOMAIN.NOTE, chainId, pk, value, tokenId, noteSalt]);

// DomainHash4 -> Poseidon(5): [tag, chain_id, commitment_index, nullifying_key, 0]
const nullifier = (chainId, commitmentIndex, nk) => P([DOMAIN.NULLIFIER, chainId, commitmentIndex, nk, 0n]);

// DomainHash2 -> Poseidon(3): [tag, chain_id, entropy + dummy_index]. The slot index is folded into
// the entropy additively (NOT a separate field), per DummyNullifier(dummy_index) in primitives.circom.
const dummyNullifier = (chainId, entropy, dummyIndex) => {
  const indexedEntropy = (BigInt(entropy) + BigInt(dummyIndex)) % Fr;
  return { indexedEntropy: indexedEntropy.toString(), value: P([DOMAIN.DUMMY_NULLIFIER, chainId, indexedEntropy]) };
};

// DomainHash4 -> Poseidon(5): [tag, chain_id, public_key, burn_salt, 0]; address = low 160 bits.
const burn = (chainId, pk, burnSalt) => {
  const digest = P([DOMAIN.BURN, chainId, pk, burnSalt, 0n]);
  const address = BigInt(digest) & MASK_160;
  // Burn PoW: the top BURN_POW_BITS of the canonical 254-bit digest must be zero. The checked
  // window must not overlap the low-160 address projection.
  const powOk = BigInt(digest) >> BigInt(RANGES.FIELD_BIT_LENGTH - RANGES.BURN_POW_BITS) === 0n;
  return { digest, address: address.toString(), addressHex: '0x' + address.toString(16).padStart(40, '0'), powOk };
};

// CommitmentLeaf = Poseidon4(field0..field3), with tagged field0 = base + token_id.
const noteLeaf = (tokenId, nh) => {
  const field0 = (NOTE_FIELD0_BASE + BigInt(tokenId)).toString();
  return { field0, leaf: P([field0, nh, 0n, 0n]) };
};
const transferLeaf = (tokenId, from, to, value) => {
  const field0 = (TRANSFER_FIELD0_BASE + BigInt(tokenId)).toString();
  return { field0, leaf: P([field0, from, to, value]) };
};

const merkleNode = (left, right) => P([left, right]); // Hash2 -> Poseidon(2)
// DomainHash1 -> Poseidon(2), the interior-node arity. The tag in the first slot is what keeps this
// preimage out of the untagged interior-node image one line above.
const aspLeaf = (commitmentIndex) => P([DOMAIN.ASP_LEAF, commitmentIndex]);
const merkleRoot = (leaf, index, siblings) => {
  let current = String(leaf);
  for (let level = 0; level < siblings.length; level++) {
    const sibling = String(siblings[level]);
    const bit = (BigInt(index) >> BigInt(level)) & 1n;
    current = bit === 0n ? merkleNode(current, sibling) : merkleNode(sibling, current);
  }
  return current;
};

// SHA256(be32(prev) || be32(v1) || ...) mod 2^248, per hash_chain in zkp/src/primitives.rs: the ledger's
// leaf chain and the merge nullifier chain.
const MASK_248 = (1n << 248n) - 1n;
const hashChain = (prev, values) => {
  const hash = createHash('sha256');
  for (const x of [prev, ...values]) hash.update(be32(x));
  return (BigInt(`0x${hash.digest('hex')}`) & MASK_248).toString();
};

// ---- deterministic inputs (fixed; boundary values pinned) -----------------------------------------

const MAX_TOKEN_ID = (1n << 32n) - 1n;
const MAX_AMOUNT = (1n << 248n) - 1n;
const MAX_CHAIN_ID = (1n << 64n) - 1n;

const privateKeys = [1n, 2n, 42n, Fr - 1n];
const keys = privateKeys.map((pk) => ({ private_key: pk.toString(), ...keysOf(pk) }));

const spendSecretInputs = [
  {
    // counter 0 lands at or above Fr, so this exercises the candidate rule's retry
    name: 'zero seed',
    seed: Buffer.alloc(32),
  },
  {
    name: 'lower-bit sensitivity A',
    seed: Buffer.from('8000000000000000000000000000000000000000000000000000000000000000', 'hex'),
  },
  {
    name: 'lower-bit sensitivity B',
    seed: Buffer.from('8000000000000000000000000000000000000000000000000000000000000001', 'hex'),
  },
];
const spendSecrets = spendSecretInputs.map((input) => {
  const derived = canonicalSpendSecret(SPEND_SECRET_DOMAIN, [input.seed]);
  return {
    name: input.name,
    seed_hex: input.seed.toString('hex'),
    counter: derived.counter,
    spend_secret_hex: derived.bytes.toString('hex'),
    spend_secret: derived.value.toString(),
    public_key: keysOf(derived.value).public_key,
    nullifying_key: nullifyingKey(derived.value),
  };
});

// A couple of concrete accounts to reuse for note/nullifier/burn vectors.
const acct = { pk: BigInt(keys[2].public_key), nk: BigInt(keys[2].nullifying_key) };

const noteHashes = [
  { chain_id: 1n, value: 0n, token_id: 0n, note_salt: 0n },
  { chain_id: 1n, value: 1000n, token_id: 1n, note_salt: 12345n },
  { chain_id: MAX_CHAIN_ID, value: MAX_AMOUNT, token_id: MAX_TOKEN_ID, note_salt: 99n },
].map((n) => ({
  chain_id: n.chain_id.toString(),
  public_key: acct.pk.toString(),
  value: n.value.toString(),
  token_id: n.token_id.toString(),
  note_salt: n.note_salt.toString(),
  note_hash: noteHash(n.chain_id, acct.pk, n.value, n.token_id, n.note_salt),
}));

const nullifiers = [0n, 1n, 5n, (1n << 32n) - 1n].map((idx) => ({
  chain_id: '1',
  commitment_index: idx.toString(),
  nullifying_key: acct.nk.toString(),
  nullifier: nullifier(1n, idx, acct.nk),
}));

const dummyNullifiers = [
  { chain_id: 1n, entropy: 7777n, dummy_index: 0n },
  { chain_id: 1n, entropy: 7777n, dummy_index: 1n },
  { chain_id: 1n, entropy: 7777n, dummy_index: 2n },
].map((d) => {
  const r = dummyNullifier(d.chain_id, d.entropy, d.dummy_index);
  return {
    chain_id: d.chain_id.toString(),
    entropy: d.entropy.toString(),
    dummy_index: d.dummy_index.toString(),
    indexed_entropy: r.indexedEntropy,
    dummy_nullifier: r.value,
  };
});

const burnRow = (salt) => {
  const r = burn(1n, acct.pk, salt);
  return {
    chain_id: '1',
    public_key: acct.pk.toString(),
    burn_salt: salt.toString(),
    burn_digest: r.digest,
    burn_address: r.address,
    burn_address_hex: r.addressHex,
    burn_pow_ok: r.powOk,
  };
};

// Small salts exercise the low-160 address derivation (these do NOT satisfy the digest PoW window).
const burns = [1n, 2n, 3n, 4n, 5n].map(burnRow);

// Deterministically grind to the FIRST salt (starting from 1) whose burn digest satisfies the PoW
// window (top BURN_POW_BITS zero). Including this success case lets downstream tests assert the PoW
// direction / bit window, not just the address derivation.
let powSalt = 1n;
for (; powSalt < 1n << 24n; powSalt++) {
  if (burn(1n, acct.pk, powSalt).powOk) break;
}
if (!burn(1n, acct.pk, powSalt).powOk) throw new Error('no burn PoW salt found in window');
burns.push(burnRow(powSalt));

const noteLeaves = noteHashes.map((n) => {
  const r = noteLeaf(n.token_id, n.note_hash);
  return { token_id: n.token_id, note_hash: n.note_hash, field0: r.field0, note_leaf: r.leaf };
});

const transferLeaves = [
  { token_id: 0n, from: 111n, to: 222n, value: 1000n },
  { token_id: MAX_TOKEN_ID, from: 1n, to: 2n, value: MAX_AMOUNT },
].map((t) => {
  const r = transferLeaf(t.token_id, t.from, t.to, t.value);
  return {
    token_id: t.token_id.toString(),
    from: t.from.toString(),
    to: t.to.toString(),
    value: t.value.toString(),
    field0: r.field0,
    transfer_leaf: r.leaf,
  };
});

const merkleNodes = [
  { left: 0n, right: 0n },
  { left: 1n, right: 2n },
  { left: BigInt(noteLeaves[0].note_leaf), right: BigInt(noteLeaves[1].note_leaf) },
].map((m) => ({ left: m.left.toString(), right: m.right.toString(), hash: merkleNode(m.left, m.right) }));

const aspLeaves = [0n, MAX_TOKEN_ID].map((index) => ({
  commitment_index: index.toString(),
  leaf: aspLeaf(index),
}));

// Cross-boundary burn-intake fixture. The ASP leaf MUST bind the deposit's commitment index, the same
// index that places the transfer commitment in the commitment tree, while the transfer commitment
// binds the derived burn address as transfer.to. The approved index's root must pass, and the
// approval of another deposit cannot be substituted.
const burnForIntake = burns.find((row) => row.burn_pow_ok);
if (!burnForIntake) throw new Error('burn-intake fixture requires a PoW-valid burn address');
const burnIntakeDepth = 2;
const burnIntakeSiblings = Array.from({ length: burnIntakeDepth }, () => '0');
const burnIntakeFrom = 0x1111111111111111111111111111111111111111n;
// Both fit the depth-2 fixture tree; an approval sits at its own index.
const burnIntakeIndex = 1n;
const burnIntakeOtherIndex = 2n;
const burnIntakeTransfer = transferLeaf(7n, burnIntakeFrom, burnForIntake.burn_address, 1000n);
const burnIntakeBinding = {
  tree_depth: burnIntakeDepth,
  chain_id: '1',
  token_id: '7',
  owner_public_key: burnForIntake.public_key,
  burn_public_key: burnForIntake.public_key,
  burn_salt: burnForIntake.burn_salt,
  burn_address: burnForIntake.burn_address,
  transfer_from: burnIntakeFrom.toString(),
  transfer_value: '1000',
  transfer_leaf: burnIntakeTransfer.leaf,
  commitment_index: burnIntakeIndex.toString(),
  other_commitment_index: burnIntakeOtherIndex.toString(),
  asp_siblings: burnIntakeSiblings,
  deposit_asp_leaf: aspLeaf(burnIntakeIndex),
  deposit_asp_root: merkleRoot(aspLeaf(burnIntakeIndex), burnIntakeIndex, burnIntakeSiblings),
  other_deposit_asp_leaf: aspLeaf(burnIntakeOtherIndex),
  other_deposit_asp_root: merkleRoot(aspLeaf(burnIntakeOtherIndex), burnIntakeOtherIndex, burnIntakeSiblings),
};

// Hash chains: one nullifier from zero, as the merge chain starts; a note leaf's four fields; and the
// largest inputs, a full 248-bit prev with field elements just below Fr.
const hashChains = [
  { prev: 0n, values: [BigInt(nullifiers[1].nullifier)] },
  { prev: 0n, values: [BigInt(noteLeaves[1].field0), BigInt(noteLeaves[1].note_hash), 0n, 0n] },
  { prev: MAX_AMOUNT, values: [Fr - 1n, Fr - 2n, MAX_AMOUNT, 0n] },
].map(({ prev, values }) => ({
  prev: prev.toString(),
  values: values.map(String),
  hash_chain: hashChain(prev, values),
}));

// The empty commitment tree's root: each level hashes two copies of the level below, from zero leaves.
let emptyRoot = '0';
for (let level = 0; level < RANGES.MERKLE_DEPTH; level++) emptyRoot = merkleNode(emptyRoot, emptyRoot);
const emptyTree = { depth: RANGES.MERKLE_DEPTH, root: emptyRoot };

// Signatures: an ordinary message, zero, and the largest field element, under two keys.
const signatures = [
  { private_key: 42n, message: 7n },
  { private_key: 42n, message: 0n },
  { private_key: 2n, message: Fr - 1n },
].map(({ private_key, message }) => {
  const { r, s } = sign(authSecret(private_key), message);
  return { private_key: private_key.toString(), message: message.toString(), r: r.map(String), s: s.toString() };
});

const messages = {
  transact: [
    '0x0000000000000000000000000000000000000000000000000000000000000000',
    '0x8f2a4c1d00000000000000000000000000000000000000000000000000000001',
  ].map((struct_hash) => ({ struct_hash, message: transactMessage(struct_hash) })),
  merge: [
    { nullifier_chain: 1n, out_public_key: BigInt(keys[2].public_key), out_salt: 99n, fee: 0n, fee_recipient: 0n },
    { nullifier_chain: (1n << 248n) - 1n, out_public_key: 2n, out_salt: 3n, fee: 5n, fee_recipient: 0xbeefn },
  ].map((m) => ({
    ...Object.fromEntries(Object.entries(m).map(([k, v]) => [k, v.toString()])),
    message: mergeMessage(m.nullifier_chain, m.out_public_key, m.out_salt, m.fee, m.fee_recipient),
  })),
};

// ---- emit -----------------------------------------------------------------------------------------

const out = {
  _comment:
    "Shared deterministic vectors for the circuits' conventions, their domain tags, and a wallet seed's derivations. Generated by gen_circuit_vectors.mjs (SHA-256 plus circomlibjs Poseidon / BN254 Fr).",
  field: {
    name: 'BN254 Fr',
    modulus: Fr.toString(),
    poseidon: 'circomlib Poseidon (circomlibjs parity)',
  },
  spend_secret_derivation: {
    seed_bytes: 32,
    domain: SPEND_SECRET_DOMAIN,
    hash: 'SHA-256',
    field_encoding: 'unsigned 32-byte big-endian',
    candidate_rule: 'clear the top two digest bits; accept the first candidate where 0 < candidate < Fr',
    counter_encoding: 'u32 big-endian, starting at 0',
    fields: 'seed || u32_be(counter)',
    framing: 'u32_be(length) || field for UTF-8 domain and every field',
  },
  entropy_regression: {
    name: 'lower-bit sensitivity',
    vector_names: ['lower-bit sensitivity A', 'lower-bit sensitivity B'],
    invariant:
      'The 256-bit seeds have identical upper 53 bits and differ only below that boundary. ' +
      'Although a JavaScript Number conversion collapses them, their spend secrets and Circom-derived keys must differ.',
  },
  auth: {
    curve: 'Baby-JubJub as ark-ed-on-bn254: x^2 + y^2 = 1 + d x^2 y^2',
    d: ED_D.toString(),
    order: ED_ORDER.toString(),
    generator: ED_G.map(String),
    auth_secret: "SHA-512 over framed 'zerc20/keys/auth-secret/v1' and the private key (32 bytes), mod order",
    nonce: "SHA-512 over framed 'zerc20/auth/nonce/v1', the auth secret and the message (32 bytes each), mod order",
    signature:
      's = nonce + (c mod order) * secret, R = nonce * G, c = DomainHash4(SPEND_AUTH, R.x, R.y, auth_key_hash, message)',
  },
  domain_tag_provenance: {
    hash: 'SHA-256',
    label_encoding: 'UTF-8',
    digest_encoding: 'unsigned big-endian',
    field_reduction: 'digest mod BN254 Fr',
    labels: DOMAIN_LABELS,
  },
  domain_tags: Object.fromEntries(Object.entries(DOMAIN).map(([k, v]) => [k, v.toString()])),
  field0_tags: {
    FIELD0_TAG_SHIFT: FIELD0_TAG_SHIFT.toString(),
    TRANSFER_FIELD0_BASE: TRANSFER_FIELD0_BASE.toString(),
    NOTE_FIELD0_BASE: NOTE_FIELD0_BASE.toString(),
  },
  ranges: RANGES,
  vectors: {
    keys,
    spend_secrets: spendSecrets,
    note_hashes: noteHashes,
    nullifiers,
    dummy_nullifiers: dummyNullifiers,
    burns,
    note_leaves: noteLeaves,
    transfer_leaves: transferLeaves,
    merkle_nodes: merkleNodes,
    asp_leaves: aspLeaves,
    burn_intake_bindings: [burnIntakeBinding],
    hash_chains: hashChains,
    empty_tree: emptyTree,
    signatures,
    auth_messages: messages,
  },
};

const outPath = join(scriptDir, 'circuit-vectors.json');
const serialized = JSON.stringify(out, null, 2) + '\n';
const summary =
  `  keys=${keys.length} spend_secrets=${spendSecrets.length} ` +
  `note_hashes=${noteHashes.length} nullifiers=${nullifiers.length} ` +
  `dummy=${dummyNullifiers.length} burns=${burns.length} note_leaves=${noteLeaves.length} ` +
  `transfer_leaves=${transferLeaves.length} merkle=${merkleNodes.length} asp=${aspLeaves.length} ` +
  `burn_intake_bindings=1 hash_chains=${hashChains.length} signatures=${signatures.length}`;

// `--check`: regenerate in memory and diff against the committed file (CI drift guard, no writes).
if (process.argv.includes('--check')) {
  let committed;
  try {
    committed = readFileSync(outPath, 'utf8');
  } catch {
    console.error(`FAIL: ${outPath} is missing — run the generator and commit it.`);
    process.exit(1);
  }
  if (committed !== serialized) {
    console.error(
      `FAIL: ${outPath} is out of date. Re-run \`node test-vectors/gen_circuit_vectors.mjs\` and commit the result.`,
    );
    process.exit(1);
  }
  console.log(`OK: circuit-vectors.json matches the generator.\n${summary}`);
} else {
  writeFileSync(outPath, serialized);
  console.log(`wrote ${outPath}\n${summary}`);
}
