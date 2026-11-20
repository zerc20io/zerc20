//! A wallet's protocol computations, for `@zerc20/wallet-sdk` through wasm: keys, burn addresses, tags, leaves,
//! Merkle paths, statements, sealing and attestation checks. Everything is pure; the SDK does all I/O.
//!
//! Field elements cross as `0x` hex (32 bytes, big-endian), the way the indexer's JSON and the attester take them.
//! Bulk data crosses as raw bytes in the indexer's layouts. Each export wraps a plain function, so the logic is tested
//! natively.

use alloy_primitives::{U256, keccak256};
use serde::Serialize;
use serde_json::Value;
use wasm_bindgen::prelude::*;
use zerc20_attester_proto::{Merge, Transact, check, nitro};
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::ark_ff::{BigInt, PrimeField, Zero};
use zerc20_zkp::primitives::Keys;
use zerc20_zkp::{commitments, primitives, tree, wallet_keys};

type Res<T> = Result<T, String>;

fn js<T>(r: Res<T>) -> Result<T, JsError> {
    r.map_err(|e| JsError::new(&e))
}

fn to_js<T: Serialize>(v: &T) -> Result<JsValue, JsError> {
    Ok(serde_wasm_bindgen::to_value(v)?)
}

/// A field element from `0x` hex or decimal, canonical, never reduced.
fn fr(v: &str) -> Res<Fr> {
    let v: U256 = v.parse().map_err(|_| format!("{v:?} is not a number"))?;
    Fr::from_bigint(BigInt(v.into_limbs())).ok_or_else(|| format!("{v} is not a field element"))
}

fn u256(f: Fr) -> U256 {
    U256::from_limbs(f.into_bigint().0)
}

fn hex(f: Fr) -> String {
    format!("{:#066x}", u256(f))
}

/// 32-byte big-endian field elements, back to back.
fn frs(b: &[u8]) -> Res<Vec<Fr>> {
    if !b.len().is_multiple_of(32) {
        return Err(format!("{} bytes is not a list of 32-byte values", b.len()));
    }
    b.chunks(32)
        .map(|c| {
            Fr::from_bigint(BigInt(U256::from_be_slice(c).into_limbs()))
                .ok_or_else(|| "a value is not a field element".to_string())
        })
        .collect()
}

fn bytes(fs: impl IntoIterator<Item = Fr>) -> Vec<u8> {
    fs.into_iter()
        .flat_map(|f| u256(f).to_be_bytes::<32>())
        .collect()
}

fn seed(b: &[u8]) -> Res<[u8; 32]> {
    b.try_into()
        .map_err(|_| format!("a seed is 32 bytes, not {}", b.len()))
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SpendKey {
    /// The circuits' `private_key`, which only the wallet's own proofs take.
    pub secret: String,
    /// The hash of the key that signs what spends the key's notes, which the circuits take with the secret.
    pub auth_key_hash: String,
    pub public_key: String,
    pub nullifying_key: String,
}

fn key_of(sk: Fr) -> SpendKey {
    let k = Keys::of(sk);
    SpendKey {
        secret: hex(sk),
        auth_key_hash: hex(k.auth_key_hash()),
        public_key: hex(k.public_key),
        nullifying_key: hex(k.nullifying_key),
    }
}

pub fn spend_key_of(seed_bytes: &[u8]) -> Res<SpendKey> {
    Ok(key_of(wallet_keys::spend_secret(&seed(seed_bytes)?)))
}

/// The key that owns a seed's notes and deposits on every chain and token: `{secret, authKeyHash, publicKey,
/// nullifyingKey}`.
#[wasm_bindgen(js_name = spendKey)]
pub fn spend_key(seed: &[u8]) -> Result<JsValue, JsError> {
    to_js(&js(spend_key_of(seed))?)
}

pub fn code_spend_key_of(
    seed_bytes: &[u8],
    chain_id: u64,
    token_id: u32,
    index: u32,
) -> Res<SpendKey> {
    Ok(key_of(wallet_keys::code_spend_secret(
        &seed(seed_bytes)?,
        chain_id,
        token_id,
        index,
    )))
}

/// The key that owns the notes paid to a seed's `index`-th receive code for one chain and token, shaped like
/// `spendKey`.
#[wasm_bindgen(js_name = codeSpendKey)]
pub fn code_spend_key(
    seed: &[u8],
    chain_id: u64,
    token_id: u32,
    index: u32,
) -> Result<JsValue, JsError> {
    to_js(&js(code_spend_key_of(seed, chain_id, token_id, index))?)
}

#[derive(Serialize)]
pub struct Burn {
    pub salt: String,
    /// `0x` and 40 hex digits.
    pub address: String,
}

fn burn_from((salt, address): (Fr, Fr)) -> Burn {
    Burn {
        salt: hex(salt),
        address: format!("0x{:040x}", u256(address)),
    }
}

pub fn burn_block_of(
    burn_key: &[u8],
    chain_id: u64,
    token_id: u32,
    index: u32,
    public_key: &str,
    from: u32,
    to: u32,
) -> Res<Option<Burn>> {
    let burn_key: [u8; 32] = burn_key
        .try_into()
        .map_err(|_| format!("a burn key is 32 bytes, not {}", burn_key.len()))?;
    let burn = wallet_keys::derive_burn_address(
        &burn_key,
        chain_id,
        token_id,
        index,
        fr(public_key)?,
        from..=to,
    );
    Ok(burn.map(burn_from))
}

/// The `index`-th burn address of `public_key` on one chain and token from `burn_key`, and its salt, if the salt's
/// counter is in `from..=to`: `{salt, address}` or `undefined`. Searched in blocks of counters from 0, the result is
/// the first block's hit.
#[wasm_bindgen(js_name = burnBlock)]
pub fn burn_block(
    burn_key: &[u8],
    chain_id: u64,
    token_id: u32,
    index: u32,
    public_key: &str,
    from: u32,
    to: u32,
) -> Result<JsValue, JsError> {
    to_js(&js(burn_block_of(
        burn_key, chain_id, token_id, index, public_key, from, to,
    ))?)
}

pub fn burn_block_for_of(
    chain_id: u64,
    public_key: &str,
    start: &str,
    count: u32,
) -> Res<Option<Burn>> {
    let (chain, public_key, start) = (Fr::from(chain_id), fr(public_key)?, fr(start)?);
    Ok((0..count).map(|i| start + Fr::from(i)).find_map(|salt| {
        primitives::burn_address(chain, public_key, salt).map(|address| burn_from((salt, address)))
    }))
}

/// A burn address of someone else's `public_key` on a chain, with its salt: the first of the `count` salts from
/// `start` that has the proof of work, `{salt, address}`, or `undefined`. A random `start` makes the salt
/// unguessable.
#[wasm_bindgen(js_name = burnBlockFor)]
pub fn burn_block_for(
    chain_id: u64,
    public_key: &str,
    start: &str,
    count: u32,
) -> Result<JsValue, JsError> {
    to_js(&js(burn_block_for_of(chain_id, public_key, start, count))?)
}

/// The burn address of `public_key` and `salt` on a chain, or `None` if the salt lacks the proof of work: one hash,
/// where deriving an address from its index takes about 2^16. How a wallet checks the salts of burn addresses another
/// device handed out.
pub fn burn_address_of(chain_id: u64, public_key: &str, salt: &str) -> Res<Option<String>> {
    let address = primitives::burn_address(Fr::from(chain_id), fr(public_key)?, fr(salt)?);
    Ok(address.map(|a| format!("0x{:040x}", u256(a))))
}

#[wasm_bindgen(js_name = burnAddressOf)]
pub fn burn_address_of_js(
    chain_id: u64,
    public_key: &str,
    salt: &str,
) -> Result<Option<String>, JsError> {
    js(burn_address_of(chain_id, public_key, salt))
}

/// The note hash a note's opening commits to.
#[wasm_bindgen(js_name = noteHash)]
pub fn note_hash(
    chain_id: u64,
    public_key: &str,
    value: &str,
    token_id: u32,
    salt: &str,
) -> Result<String, JsError> {
    js((|| {
        Ok(hex(primitives::note_hash(
            Fr::from(chain_id),
            fr(public_key)?,
            fr(value)?,
            Fr::from(token_id),
            fr(salt)?,
        )))
    })())
}

/// The nullifier that spending the note or deposit at `commitment_index` publishes.
#[wasm_bindgen]
pub fn nullifier(
    chain_id: u64,
    commitment_index: u64,
    nullifying_key: &str,
) -> Result<String, JsError> {
    js((|| {
        Ok(hex(primitives::nullifier(
            Fr::from(chain_id),
            Fr::from(commitment_index),
            fr(nullifying_key)?,
        )))
    })())
}

pub fn public_key_of(auth_key_hash: &str, nullifying_key: &str) -> Res<String> {
    Ok(hex(primitives::public_key(
        fr(auth_key_hash)?,
        fr(nullifying_key)?,
    )))
}

/// The public key a signing key's hash and a nullifying key make: how a view key's holder checks that the nullifying
/// key it was given is the one the account's notes commit to.
#[wasm_bindgen(js_name = publicKey)]
pub fn public_key(auth_key_hash: &str, nullifying_key: &str) -> Result<String, JsError> {
    js(public_key_of(auth_key_hash, nullifying_key))
}

// `field0`'s high 32 bits: the first 4 bytes of the event signatures' keccak (`contracts/src/libs/Protocol.sol`)
const TRANSFER_TAG: u64 = 0xddf252ad;
const NOTE_TAG: u64 = 0x789f26eb;

/// The indexer's 4-byte tag (`backend/indexer/src/events.rs`) as a big-endian u32: `keccak256(field0 ‖ key)[..4]`.
pub fn tag(kind: u64, token_id: u32, key: U256) -> u32 {
    let field0 = U256::from(kind << 32 | u64::from(token_id));
    let mut pre = [0u8; 64];
    pre[..32].copy_from_slice(&field0.to_be_bytes::<32>());
    pre[32..].copy_from_slice(&key.to_be_bytes::<32>());
    let [a, b, c, d, ..] = keccak256(pre).0;
    u32::from_be_bytes([a, b, c, d])
}

/// The tag of a note commitment.
#[wasm_bindgen(js_name = noteTag)]
pub fn note_tag(token_id: u32, note_hash: &str) -> Result<u32, JsError> {
    Ok(tag(NOTE_TAG, token_id, u256(js(fr(note_hash))?)))
}

/// The tag of a transfer to `to` (`0x` address), such as a deposit to a burn address.
#[wasm_bindgen(js_name = transferTag)]
pub fn transfer_tag(token_id: u32, to: &str) -> Result<u32, JsError> {
    let to: U256 = js(to.parse().map_err(|_| format!("{to:?} is not an address")))?;
    if to.bit_len() > 160 {
        return Err(JsError::new("an address is 160 bits"));
    }
    Ok(tag(TRANSFER_TAG, token_id, to))
}

pub fn leaves_of(entries: &[u8]) -> Res<Vec<u8>> {
    if !entries.len().is_multiple_of(128) {
        return Err(format!(
            "{} bytes is not a list of commitments",
            entries.len()
        ));
    }
    let fields = frs(entries)?;
    Ok(bytes(
        fields
            .as_chunks()
            .0
            .iter()
            .map(commitments::commitment_leaf),
    ))
}

/// The leaves of commitments in the indexer's layout (4 fields of 32 bytes each, as after a `/commitments/{p}` page's
/// 32-byte header), 32 bytes each.
#[wasm_bindgen]
pub fn leaves(entries: &[u8]) -> Result<Vec<u8>, JsError> {
    js(leaves_of(entries))
}

pub fn asp_leaves_of(bitmap: &[u8], first: u64, count: u32) -> Res<Vec<u8>> {
    if count as usize > bitmap.len() * 8 {
        return Err("the bitmap is too short".into());
    }
    Ok(bytes((0..u64::from(count)).map(|j| {
        let approved = bitmap[(j / 8) as usize] >> (j % 8) & 1 == 1;
        match approved {
            true => commitments::asp_leaf(Fr::from(first + j)),
            false => Fr::zero(),
        }
    })))
}

/// The ASP tree's leaves for `count` positions from `first`, from an ASP `/bitmap/{c}` page (position `first + j` is
/// bit `j % 8`, least significant first, of byte `j / 8`): `asp_leaf(position)` where approved, 0 elsewhere.
#[wasm_bindgen(js_name = aspLeaves)]
pub fn asp_leaves(bitmap: &[u8], first: u64, count: u32) -> Result<Vec<u8>, JsError> {
    js(asp_leaves_of(bitmap, first, count))
}

/// A root entry's partial root: zero means there is none.
fn partial(v: Option<String>) -> Res<Option<Fr>> {
    Ok(v.map(|v| fr(&v)).transpose()?.filter(|f| !f.is_zero()))
}

pub fn path_of(
    i: u64,
    n: u64,
    chunk_leaves: &[u8],
    page_chunks: &[u8],
    page_roots: &[u8],
    partial_chunk: Option<String>,
    partial_page: Option<String>,
) -> Res<Vec<String>> {
    if i >= n {
        return Err(format!("position {i} is not in a tree of {n} leaves"));
    }
    let at = tree::Sized {
        // not read by `path`
        root: Fr::zero(),
        partial_chunk: partial(partial_chunk)?,
        partial_page: partial(partial_page)?,
    };
    let siblings = tree::path(
        i,
        n,
        &frs(chunk_leaves)?,
        &frs(page_chunks)?,
        &frs(page_roots)?,
        &at,
    );
    Ok(siblings.into_iter().map(hex).collect())
}

/// The sibling path (32 hex values) of position `i` in the tree at `n` leaves, from what a wallet downloads: the leaves
/// of `i`'s chunk, the chunk roots of `i`'s page, the page roots, and the root entry's partial chunk and page roots
/// (zero or absent where there is none). Lists may run past `n`. Check the path with `pathRoot` against a root the chain
/// accepts.
#[wasm_bindgen]
pub fn path(
    i: u64,
    n: u64,
    chunk_leaves: &[u8],
    page_chunks: &[u8],
    page_roots: &[u8],
    partial_chunk: Option<String>,
    partial_page: Option<String>,
) -> Result<Vec<String>, JsError> {
    js(path_of(
        i,
        n,
        chunk_leaves,
        page_chunks,
        page_roots,
        partial_chunk,
        partial_page,
    ))
}

pub fn path_root_of(leaf: &str, i: u64, siblings: &[String]) -> Res<String> {
    let siblings: Vec<Fr> = siblings.iter().map(|s| fr(s)).collect::<Res<_>>()?;
    let siblings: [Fr; tree::TREE_HEIGHT] = siblings
        .try_into()
        .map_err(|_| "a path has 32 siblings".to_string())?;
    Ok(hex(tree::path_root(fr(leaf)?, i, &siblings)))
}

/// The root of the tree holding `leaf` at position `i` with path `siblings`.
#[wasm_bindgen(js_name = pathRoot)]
pub fn path_root(leaf: &str, i: u64, siblings: Vec<String>) -> Result<String, JsError> {
    js(path_root_of(leaf, i, &siblings))
}

fn four(fields: &[String]) -> Res<[Fr; 4]> {
    let f: Vec<Fr> = fields.iter().map(|s| fr(s)).collect::<Res<_>>()?;
    f.try_into()
        .map_err(|_| "a commitment has 4 fields".to_string())
}

/// One commitment's leaf, from its 4 fields.
#[wasm_bindgen]
pub fn leaf(fields: Vec<String>) -> Result<String, JsError> {
    js(four(&fields).map(|f| hex(commitments::commitment_leaf(&f))))
}

/// `CommitmentLedger`'s hash chain after appending a commitment with `fields` to `prev`.
#[wasm_bindgen(js_name = hashChain)]
pub fn hash_chain(prev: &str, fields: Vec<String>) -> Result<String, JsError> {
    js((|| {
        Ok(hex(primitives::hash_chain(fr(prev)?, &four(&fields)?)))
    })())
}

/// The public inputs a statement starts from.
#[derive(serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct Inputs {
    token_id: U256,
    chain_id: U256,
    commitment_root: U256,
    asp_root: U256,
}

/// Takes the private key out of a witness's `private` field and puts in the keys it derives, as the attester and the
/// merge prover take them: `auth` (`[x, y]`) and `nullifying`. `None` when the field is zero: a dummy input's.
fn put_keys(w: &mut Value, private: &str, auth: &str, nullifying: &str) -> Res<Option<Keys>> {
    let o = w.as_object_mut().ok_or("a witness is a JSON object")?;
    let sk = match o.remove(private) {
        Some(Value::String(v)) => fr(&v)?,
        _ => return Err(format!("the witness has no {private}")),
    };
    let keys = (!sk.is_zero()).then(|| Keys::of(sk));
    let (key, nk) = keys.map_or((Value::from(["0", "0"]), Value::from("0")), |k| {
        let key = [k.auth_key.x, k.auth_key.y].map(hex);
        (
            Value::from(key.to_vec()),
            Value::from(hex(k.nullifying_key)),
        )
    });
    o.insert(auth.into(), key);
    o.insert(nullifying.into(), nk);
    Ok(keys)
}

/// The statement a JoinSplit witness proves and the attester's witness for it.
#[derive(Serialize)]
pub struct Signed<S, W> {
    pub statement: S,
    pub witness: W,
}

pub fn sign_transact_of(statement: &str, witness: &str) -> Res<String> {
    let i: Inputs =
        serde_json::from_str(statement).map_err(|e| format!("malformed statement: {e}"))?;
    let s = Transact {
        tokenId: i.token_id,
        chainId: i.chain_id,
        commitmentRoot: i.commitment_root,
        aspRoot: i.asp_root,
        ..Default::default()
    };
    let mut v: Value =
        serde_json::from_str(witness).map_err(|e| format!("malformed witness: {e}"))?;
    let k0 = put_keys(&mut v, "private_key0", "auth_key0", "nullifying_key0")?
        .ok_or("in0 has no private key")?;
    let k1 = put_keys(&mut v, "private_key1", "auth_key1", "nullifying_key1")?;
    let mut w: check::JoinSplit =
        serde_json::from_value(v).map_err(|e| format!("malformed witness: {e}"))?;
    let s = check::transact_statement(&s, &w)?;
    let message = check::transact_message(&s);
    w.signature0 = check::sign(k0.auth_secret, message);
    if let Some(k1) = k1 {
        w.signature1 = check::sign(k1.auth_secret, message);
    }
    serde_json::to_string(&Signed {
        statement: s,
        witness: w,
    })
    .map_err(|e| e.to_string())
}

/// The statement a JoinSplit witness (snarkjs's input JSON) proves, given the public inputs in `statement` (JSON with
/// `tokenId`, `chainId`, `commitmentRoot` and `aspRoot`; the rest is ignored), and the attester's witness for it:
/// `{statement, witness}`. The statement is the public signals the proof and the attestation cover. The attester's
/// witness has each input's private key replaced by its signing and nullifying keys, and its owner's signature on the
/// statement. Fails, with the reason, where the attester would refuse the witness.
#[wasm_bindgen(js_name = signTransact)]
pub fn sign_transact(statement: &str, witness: &str) -> Result<String, JsError> {
    js(sign_transact_of(statement, witness))
}

/// The public inputs and the fee a merge statement starts from.
#[derive(serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct MergeInputs {
    token_id: U256,
    chain_id: U256,
    commitment_root: U256,
    asp_root: U256,
    fee: U256,
    fee_recipient: U256,
}

pub fn sign_merge_of(statement: &str, witness: &str) -> Res<String> {
    let i: MergeInputs =
        serde_json::from_str(statement).map_err(|e| format!("malformed statement: {e}"))?;
    let mut s = Merge {
        tokenId: i.token_id,
        chainId: i.chain_id,
        commitmentRoot: i.commitment_root,
        aspRoot: i.asp_root,
        fee: i.fee,
        feeRecipient: i.fee_recipient,
        ..Default::default()
    };
    let mut v: Value =
        serde_json::from_str(witness).map_err(|e| format!("malformed witness: {e}"))?;
    let inputs = v["inputs"]
        .as_array_mut()
        .ok_or("the witness has no inputs")?;
    let keys = inputs
        .iter_mut()
        .map(|i| {
            put_keys(i, "private_key", "auth_key", "nullifying_key")?
                .ok_or("an input has no private key".into())
        })
        .collect::<Res<Vec<_>>>()?;
    let mut w: check::MergeWitness =
        serde_json::from_value(v).map_err(|e| format!("malformed witness: {e}"))?;
    (s.nullifiers, s.noteHash) = check::merge_outputs(&s, &w)?;
    let message = check::merge_message(&s, &w)?;
    for (input, k) in w.inputs.iter_mut().zip(keys) {
        input.signature = check::sign(k.auth_secret, message);
    }
    serde_json::to_string(&Signed {
        statement: s,
        witness: w,
    })
    .map_err(|e| e.to_string())
}

/// The statement a merge witness proves and the witness the attester and the merge prover take, as [`sign_transact`]
/// for a JoinSplit: `{statement, witness}`. `statement` holds the public inputs and the fee (JSON with `tokenId`,
/// `chainId`, `commitmentRoot`, `aspRoot`, `fee` and `feeRecipient`), and `witness` is the attester's merge witness
/// JSON with each input's `private_key` in place of its keys. The statement gains the nullifiers and the note.
#[wasm_bindgen(js_name = signMerge)]
pub fn sign_merge(statement: &str, witness: &str) -> Result<String, JsError> {
    js(sign_merge_of(statement, witness))
}

pub fn seal_of(info: &[u8], public_key: &[u8], msg: &str, pad_to: usize) -> Res<Vec<u8>> {
    if msg.len() > pad_to {
        return Err(format!("the message is {} bytes, over {pad_to}", msg.len()));
    }
    // its length would otherwise leak the digits of the amounts. Not `format!` with a width: one over u16::MAX panics,
    // as a merge of 8 inputs' pad is
    let mut padded = msg.as_bytes().to_vec();
    padded.resize(pad_to, b' ');
    let sealed = zerc20_attester_proto::seal(info, public_key, &padded)
        .map_err(|e| format!("cannot seal to this key: {e}"))?;
    Ok(sealed.to_vec())
}

/// Seals a witness (JSON) to an attester's key, padded with spaces to `pad_to` bytes so its length is the same for
/// every amount. Take the key from `verifyAttestation`; only a development attester, which has no document, is taken
/// at its word.
#[wasm_bindgen(js_name = sealWitness)]
pub fn seal_witness(public_key: &[u8], witness: &str, pad_to: usize) -> Result<Vec<u8>, JsError> {
    js(seal_of(
        zerc20_attester_proto::WITNESS,
        public_key,
        witness,
        pad_to,
    ))
}

/// Seals a merge witness (JSON) to the merge prover's key, padded with spaces to `pad_to` bytes. Take the key from
/// `verifyAttestation`, as for the attester's.
#[wasm_bindgen(js_name = sealMergeWitness)]
pub fn seal_merge_witness(
    public_key: &[u8],
    witness: &str,
    pad_to: usize,
) -> Result<Vec<u8>, JsError> {
    js(seal_of(
        zerc20_attester_proto::MERGE_WITNESS,
        public_key,
        witness,
        pad_to,
    ))
}

/// The key an attester's enclave opens witnesses with, once its `/attestation` document (`attestation`, decoded from
/// base64) checks out: signed by a certificate chain up to the root whose DER has SHA-256 `root_sha256` (hex), valid
/// at `now` (Unix seconds), and measuring `pcr0` (hex).
#[wasm_bindgen(js_name = verifyAttestation)]
pub fn verify_attestation(
    attestation: &[u8],
    root_sha256: &str,
    pcr0: &str,
    now: u64,
) -> Result<Vec<u8>, JsError> {
    js(nitro::verify(attestation, root_sha256, pcr0, now))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tags_match_the_indexer() {
        // backend/indexer/src/events.rs pins the same values for the same commitments
        assert_eq!(tag(NOTE_TAG, 1, U256::from(12345)), 0x5f67ca8a);
        assert_eq!(tag(TRANSFER_TAG, 1, U256::from(0xbeef)), 0x4e66b741);
    }

    #[test]
    fn public_keys_make_from_their_parts() {
        let k = spend_key_of(&[7u8; 32]).unwrap();
        assert_eq!(
            public_key_of(&k.auth_key_hash, &k.nullifying_key).unwrap(),
            k.public_key
        );
        assert_ne!(
            public_key_of(&k.auth_key_hash, &k.public_key).unwrap(),
            k.public_key
        );
    }

    #[test]
    fn burn_addresses_check_from_their_salts() {
        let pk = hex(Keys::of(wallet_keys::spend_secret(&[7u8; 32])).public_key);
        let b = burn_block_of(&[9u8; 32], 1, 1, 0, &pk, 0, u32::MAX)
            .unwrap()
            .unwrap();
        assert_eq!(burn_address_of(1, &pk, &b.salt).unwrap(), Some(b.address));
        let other = hex(fr(&b.salt).unwrap() + Fr::from(1u64));
        assert_eq!(burn_address_of(1, &pk, &other).unwrap(), None);
        assert!(burn_block_of(&[9u8; 31], 1, 1, 0, &pk, 0, u32::MAX).is_err());
    }

    #[test]
    fn burn_addresses_for_others_check_from_their_salts() {
        let pk = hex(Keys::of(wallet_keys::spend_secret(&[7u8; 32])).public_key);
        let start = hex(Fr::from(12345u64));
        let b = burn_block_for_of(1, &pk, &start, u32::MAX)
            .unwrap()
            .unwrap();
        assert_eq!(burn_address_of(1, &pk, &b.salt).unwrap(), Some(b.address));
        assert!(burn_block_for_of(1, &pk, &start, 0).unwrap().is_none());
    }

    #[test]
    fn asp_bits_are_least_significant_first() {
        let leaves = asp_leaves_of(&[0b0000_0010], 8, 3).unwrap();
        let leaves = frs(&leaves).unwrap();
        assert_eq!(
            leaves,
            [
                Fr::zero(),
                commitments::asp_leaf(Fr::from(9u64)),
                Fr::zero()
            ]
        );
    }

    #[test]
    fn paths_fold_to_the_tree_root() {
        let fields: Vec<[Fr; 4]> = (1..=5u64)
            .map(|v| {
                [
                    Fr::from(v),
                    Fr::from(v + 1),
                    Fr::from(v + 2),
                    Fr::from(v + 3),
                ]
            })
            .collect();
        let entries = bytes(fields.iter().flatten().copied());
        let leaves = leaves_of(&entries).unwrap();
        let (root, _) = tree::merkle_path(&frs(&leaves).unwrap(), 3);
        let siblings = path_of(3, 5, &leaves, &[], &[], None, None).unwrap();
        let leaf = hex(commitments::commitment_leaf(&fields[3]));
        assert_eq!(path_root_of(&leaf, 3, &siblings).unwrap(), hex(root));
        assert!(path_of(5, 5, &leaves, &[], &[], None, None).is_err());
    }

    #[test]
    fn seals_pad_to_one_length() {
        let key = [9u8; 32];
        let info = zerc20_attester_proto::WITNESS;
        let a = seal_of(info, &key, "{\"a\":1}", 64).unwrap();
        let b = seal_of(info, &key, "{\"a\":100000}", 64).unwrap();
        assert_eq!((a.len(), b.len()), (32 + 64 + 16, 32 + 64 + 16));
        assert!(seal_of(info, &key, &"x".repeat(65), 64).is_err());
        // a merge of 100 inputs, 8 KiB each: past what a format width takes
        assert_eq!(
            seal_of(info, &key, "{}", 100 * 8192).unwrap().len(),
            32 + 100 * 8192 + 16
        );
    }

    #[test]
    fn signs_what_the_attester_checks() {
        let sk = hex(check::tests::keys().private_key);
        // the fixtures' witnesses as a wallet builds them: a private key in place of each input's keys and signature
        let unkeyed = |v: &mut Value, keys: &[&str], private: &str| {
            let o = v.as_object_mut().unwrap();
            for k in keys {
                o.remove(*k);
            }
            o.insert(private.into(), sk.clone().into());
        };

        let (s, w) = check::tests::burn_and_note();
        let mut v = serde_json::to_value(&w).unwrap();
        for i in ["0", "1"] {
            let keys = ["auth_key", "nullifying_key", "signature"].map(|k| format!("{k}{i}"));
            unkeyed(
                &mut v,
                &keys.each_ref().map(String::as_str),
                &format!("private_key{i}"),
            );
        }
        let inputs = serde_json::json!({
            "tokenId": s.tokenId, "chainId": s.chainId, "commitmentRoot": s.commitmentRoot, "aspRoot": s.aspRoot,
        });
        let got: Value =
            serde_json::from_str(&sign_transact_of(&inputs.to_string(), &v.to_string()).unwrap())
                .unwrap();
        assert_eq!(
            serde_json::from_value::<Transact>(got["statement"].clone()).unwrap(),
            s
        );
        assert!(got["witness"].get("private_key0").is_none());
        assert_eq!(
            check::transact(&s, got["witness"].to_string().as_bytes()),
            Ok(())
        );

        let (s, w) = check::tests::merge_fixture();
        let mut v = serde_json::to_value(&w).unwrap();
        for i in v["inputs"].as_array_mut().unwrap() {
            unkeyed(
                i,
                &["auth_key", "nullifying_key", "signature"],
                "private_key",
            );
        }
        let inputs = serde_json::json!({
            "tokenId": s.tokenId, "chainId": s.chainId, "commitmentRoot": s.commitmentRoot, "aspRoot": s.aspRoot,
            "fee": s.fee, "feeRecipient": s.feeRecipient,
        });
        let got: Value =
            serde_json::from_str(&sign_merge_of(&inputs.to_string(), &v.to_string()).unwrap())
                .unwrap();
        assert_eq!(
            serde_json::from_value::<Merge>(got["statement"].clone()).unwrap(),
            s
        );
        assert!(got["witness"]["inputs"][0].get("private_key").is_none());
        assert_eq!(
            check::merge(&s, got["witness"].to_string().as_bytes()),
            Ok(())
        );
    }
}
