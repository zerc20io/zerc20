//! Re-checks a witness against its statement from the protocol's definitions, not from the circuits' constraints, so
//! that an under-constrained circuit is not trusted twice. JoinSplit's `in0` and every merge input are the same spend,
//! checked by one function.
//!
//! A witness carries no private key. Each input carries its owner's signing key and nullifying key, which give the
//! owner's public key, and the owner's signature on the statement (`zerc20_zkp::auth`). So whoever opens a witness, an
//! attester or the merge prover, can spend nothing its owner did not sign.
//!
//! The host relays what [`transact`] and [`merge`] answer, and may replay a sealed witness under statements of its own
//! choosing. So a witness that does not parse gets one error, and anything else wrong gets [`MISMATCH`], whatever the
//! reason. A merge's fee above its value also takes the work of one below it. Otherwise the reason, or the work, would
//! tell the host which fees are above the merged value, and so that value.
//!
//! What the host can still learn: a burn takes more work than a note, and a check fails at the first input it fails
//! on, so the time an answer takes tells which inputs are burns and whether a transact's second input is padding. A
//! merge's owners do not sign its ASP root, which no note reads, so a merge of notes alone proves any ASP root, and
//! one with a burn does not.
use crate::{Merge, Transact};
use alloy_primitives::U256;
use alloy_sol_types::SolStruct;
use serde::{Deserialize, Serialize};
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::ark_ec::AffineRepr;
use zerc20_zkp::ark_ff::{BigInt, PrimeField};
use zerc20_zkp::auth::{self, AuthKey, AuthSecret};
use zerc20_zkp::commitments::{asp_leaf, note_leaf, transfer_leaf};
use zerc20_zkp::poseidon::{self, POSEIDON2};
use zerc20_zkp::primitives::{
    burn_address, dummy_nullifier, note_hash, nullifier, nullifier_chain, public_key,
};
use zerc20_zkp::tree::TREE_HEIGHT;

pub type Error = &'static str;

/// What [`transact`] and [`merge`] answer for a witness that parses but does not prove the statement with its owners'
/// signatures, whatever the reason.
pub const MISMATCH: Error = "the statement does not match the witness";
type Path = [U256; TREE_HEIGHT];

// `circom/lib/constants.circom`
const AMOUNT_BITS: usize = 248;
const ADDRESS_BITS: usize = 160;
const TOKEN_ID_BITS: usize = 32;
const CHAIN_ID_BITS: usize = 64;

/// An owner's signature (`zerc20_zkp::auth::Signature`): the nonce point `[x, y]` and `s`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Signature {
    pub r: [U256; 2],
    pub s: U256,
}

impl From<auth::Signature> for Signature {
    fn from(sig: auth::Signature) -> Self {
        Signature {
            r: [u256(sig.r.x), u256(sig.r.y)],
            s: U256::from_limbs(sig.s.into_bigint().0),
        }
    }
}

/// A spent input: a private note, or (`is_burn`) a transfer to a burn address that the ASP approved. Named like
/// `zkp::merge::MergeStep`; the other branch's fields are ignored.
#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Input {
    #[serde(default)]
    pub is_burn: bool,
    /// The owner's signing key, `[x, y]`.
    pub auth_key: [U256; 2],
    pub nullifying_key: U256,
    /// The owner's signature on the merge.
    #[serde(default)]
    pub signature: Signature,
    pub commitment_index: U256,
    pub commitment_siblings: Path,
    #[serde(default)]
    pub note_value: U256,
    #[serde(default)]
    pub note_salt: U256,
    #[serde(default)]
    pub burn_salt: U256,
    #[serde(default)]
    pub burn_from: U256,
    #[serde(default)]
    pub burn_value: U256,
    /// The path of the deposit's own position in the ASP tree.
    #[serde(default)]
    pub asp_siblings: Path,
}

/// The JoinSplit circuit's input JSON, as given to snarkjs, with each input's keys and signature in place of its
/// private key. Fields that only repeat what the keys and the statement determine (`in_note*_public_key`,
/// `burn_public_key`, `auth_key_hash*`, the public inputs) are ignored, and so are a dummy `in1`'s keys.
#[derive(Clone, Serialize, Deserialize)]
pub struct JoinSplit {
    pub entropy: U256,
    pub in0_is_burn: U256,
    pub in1_is_dummy: U256,
    pub in_note0_value: U256,
    pub in_note0_salt: U256,
    pub in_note1_value: U256,
    pub in_note1_salt: U256,
    pub burn_salt: U256,
    pub burn_transfer_from: U256,
    pub burn_transfer_value: U256,
    pub withdraw_recipient_private: U256,
    pub withdraw_amount_private: U256,
    pub withdraw_intent_private: U256,
    pub out_note1_public_key: U256,
    pub out_note1_value: U256,
    pub out_note1_salt: U256,
    pub out_note2_public_key: U256,
    pub out_note2_value: U256,
    pub out_note2_salt: U256,
    pub auth_key0: [U256; 2],
    pub auth_key1: [U256; 2],
    pub nullifying_key0: U256,
    pub nullifying_key1: U256,
    /// The owners' signatures on the statement.
    #[serde(default)]
    pub signature0: Signature,
    #[serde(default)]
    pub signature1: Signature,
    pub commitment_index0: U256,
    pub commitment_index1: U256,
    pub in0_merkle_siblings: Path,
    pub in1_merkle_siblings: Path,
    pub in0_asp_siblings: Path,
}

/// N inputs merged into one note owned by `out_public_key`.
#[derive(Clone, Serialize, Deserialize)]
pub struct MergeWitness {
    pub inputs: Vec<Input>,
    pub out_public_key: U256,
    pub out_salt: U256,
}

/// The public inputs every spend is checked against.
struct Public {
    token: Fr,
    chain: Fr,
    root: Fr,
    asp_root: Fr,
}

/// Whether `witness` proves `s`, signed by the owners of what it spends; [`MISMATCH`] for anything wrong but a witness
/// that does not parse.
pub fn transact(s: &Transact, witness: &[u8]) -> Result<(), Error> {
    let w: JoinSplit = serde_json::from_slice(witness).map_err(|_| "malformed witness")?;
    let proved = || {
        if transact_statement(s, &w)? != *s {
            return Err(MISMATCH);
        }
        let message = transact_message(s);
        signed(&w.auth_key0, message, &w.signature0)?;
        if !flag(w.in1_is_dummy)? {
            signed(&w.auth_key1, message, &w.signature1)?;
        }
        Ok(())
    };
    proved().map_err(|_| MISMATCH)
}

/// Whether `witness` proves `s`, signed by the owners of what it merges; [`MISMATCH`] for anything wrong but a witness
/// that does not parse.
pub fn merge(s: &Merge, witness: &[u8]) -> Result<(), Error> {
    let w: MergeWitness = serde_json::from_slice(witness).map_err(|_| "malformed witness")?;
    let proved = || {
        let (nullifiers, note) = merge_outputs(s, &w)?;
        if nullifiers != s.nullifiers || note != s.noteHash {
            return Err(MISMATCH);
        }
        let message = merge_message(s, &w)?;
        for input in &w.inputs {
            signed(&input.auth_key, message, &input.signature)?;
        }
        Ok(())
    };
    proved().map_err(|_| MISMATCH)
}

/// What the owner of each of a transact's inputs signs.
pub fn transact_message(s: &Transact) -> Fr {
    auth::transact_message(s.eip712_hash_struct().0)
}

/// What the owner of each of a merge's inputs signs: its nullifiers, its fee and the output note's owner and salt.
pub fn merge_message(s: &Merge, w: &MergeWitness) -> Result<Fr, Error> {
    let nullifiers = s
        .nullifiers
        .iter()
        .map(|n| fr(*n))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(auth::merge_message(
        nullifier_chain(&nullifiers),
        fr(w.out_public_key)?,
        fr(w.out_salt)?,
        fr(s.fee)?,
        fr(s.feeRecipient)?,
    ))
}

/// `secret`'s signature on `message`, as a witness carries it: how a wallet signs a statement.
pub fn sign(secret: AuthSecret, message: Fr) -> Signature {
    auth::sign(secret, message).into()
}

fn signed(key: &[U256; 2], message: Fr, sig: &Signature) -> Result<(), Error> {
    if !auth::verify(&auth_key(key)?, message, &signature(sig)?) {
        return Err("an input's owner did not sign this statement");
    }
    Ok(())
}

/// A signing key, on the curve and in its prime-order subgroup, and not the identity, under which anyone could sign.
pub fn auth_key(key: &[U256; 2]) -> Result<AuthKey, Error> {
    let key = AuthKey::new_unchecked(fr(key[0])?, fr(key[1])?);
    if !key.is_on_curve() || !key.is_in_correct_subgroup_assuming_on_curve() || key.is_zero() {
        return Err("a signing key is not a valid point");
    }
    Ok(key)
}

/// A signature as `zerc20_zkp::auth` takes it; [`auth::verify`] checks its nonce point.
pub fn signature(sig: &Signature) -> Result<auth::Signature, Error> {
    Ok(auth::Signature {
        r: AuthKey::new_unchecked(fr(sig.r[0])?, fr(sig.r[1])?),
        s: AuthSecret::from_bigint(BigInt(sig.s.into_limbs()))
            .ok_or("a signature is not canonical")?,
    })
}

/// The statement `w` proves, with the public inputs of `s`, if its keys own what it spends. The signatures are left to
/// [`transact`], so a wallet can sign what this returns.
pub fn transact_statement(s: &Transact, w: &JoinSplit) -> Result<Transact, Error> {
    let p = public(s.tokenId, s.chainId, s.commitmentRoot, s.aspRoot)?;
    let in0 = Input {
        is_burn: flag(w.in0_is_burn)?,
        auth_key: w.auth_key0,
        nullifying_key: w.nullifying_key0,
        signature: w.signature0,
        commitment_index: w.commitment_index0,
        commitment_siblings: w.in0_merkle_siblings,
        note_value: w.in_note0_value,
        note_salt: w.in_note0_salt,
        burn_salt: w.burn_salt,
        burn_from: w.burn_transfer_from,
        burn_value: w.burn_transfer_value,
        asp_siblings: w.in0_asp_siblings,
    };
    let (n0, v0) = spend(&p, &in0)?;
    // in1 is a note, or padding worth nothing whose nullifier only has to be fresh
    let (n1, v1) = if flag(w.in1_is_dummy)? {
        (dummy_nullifier(p.chain, fr(w.entropy)?), U256::ZERO)
    } else {
        spend(
            &p,
            &Input {
                auth_key: w.auth_key1,
                nullifying_key: w.nullifying_key1,
                commitment_index: w.commitment_index1,
                commitment_siblings: w.in1_merkle_siblings,
                note_value: w.in_note1_value,
                note_salt: w.in_note1_salt,
                ..Default::default()
            },
        )?
    };
    if n0 == n1 {
        return Err("both inputs have the same nullifier");
    }
    let (withdraw, recipient) = (w.withdraw_amount_private, w.withdraw_recipient_private);
    let outs = [w.out_note1_value, w.out_note2_value];
    if !below(withdraw, AMOUNT_BITS) || !outs.iter().all(|v| below(*v, AMOUNT_BITS)) {
        return Err("an amount is out of range");
    }
    // every term is below 2^248, so no sum wraps
    if v0 + v1 != withdraw + outs[0] + outs[1] {
        return Err("value is not conserved");
    }
    if !below(recipient, ADDRESS_BITS) || (withdraw.is_zero() && !recipient.is_zero()) {
        return Err("the withdrawal recipient is not canonical");
    }
    // Opaque here: the contract decides which intents it pays out.
    let intent = u256(fr(w.withdraw_intent_private)?);
    if withdraw.is_zero() && !intent.is_zero() {
        return Err("the withdrawal intent is not canonical");
    }
    let out = |pk: U256, value: U256, salt: U256| -> Result<U256, Error> {
        Ok(u256(note_hash(
            p.chain,
            fr(pk)?,
            fr(value)?,
            p.token,
            fr(salt)?,
        )))
    };
    Ok(Transact {
        tokenId: s.tokenId,
        chainId: s.chainId,
        commitmentRoot: s.commitmentRoot,
        aspRoot: s.aspRoot,
        nullifier0: u256(n0),
        nullifier1: u256(n1),
        withdrawRecipient: recipient,
        withdrawAmount: withdraw,
        withdrawIntent: intent,
        noteHash1: out(w.out_note1_public_key, outs[0], w.out_note1_salt)?,
        noteHash2: out(w.out_note2_public_key, outs[1], w.out_note2_salt)?,
    })
}

/// The nullifiers, in order, and the merged note that `w` proves, with the public inputs of `s` (its fee included), if
/// its keys own what it spends. The signatures are left to [`merge`], so a wallet can sign what this returns.
pub fn merge_outputs(s: &Merge, w: &MergeWitness) -> Result<(Vec<U256>, U256), Error> {
    let p = public(s.tokenId, s.chainId, s.commitmentRoot, s.aspRoot)?;
    if w.inputs.is_empty() {
        return Err("a merge spends at least one input");
    }
    if !below(s.fee, AMOUNT_BITS) || !below(s.feeRecipient, ADDRESS_BITS) {
        return Err("the fee or its recipient is out of range");
    }
    if s.fee.is_zero() != s.feeRecipient.is_zero() {
        return Err("a fee needs a recipient, and a recipient a fee");
    }
    let mut sum = U256::ZERO;
    let mut nullifiers = Vec::with_capacity(w.inputs.len());
    for input in &w.inputs {
        let (n, v) = spend(&p, input)?;
        sum += v;
        if !below(sum, AMOUNT_BITS) {
            return Err("the merged value is out of range");
        }
        nullifiers.push(u256(n));
    }
    // the contract rejects a repeated nullifier too; this keeps the enclave from vouching for one
    let mut distinct = nullifiers.clone();
    distinct.sort();
    distinct.dedup();
    if distinct.len() != nullifiers.len() {
        return Err("an input is spent twice");
    }
    // the note is hashed either way, so that a fee above the merged value takes the work of one below it
    let value = sum.checked_sub(s.fee);
    // black_box keeps the compiler from moving the hash into the branch that uses it
    let note = std::hint::black_box(note_hash(
        p.chain,
        fr(w.out_public_key)?,
        fr(value.unwrap_or_default())?,
        p.token,
        fr(w.out_salt)?,
    ));
    value.ok_or("the fee is above the merged value")?;
    Ok((nullifiers, u256(note)))
}

/// The nullifier and the value of a note or an ASP-approved burn deposit at `commitment_index` in `p.root`, owned by
/// the public key of `auth_key` and `nullifying_key`. JoinSplit's `NoteSpend` / `BurnIntake` plus its membership check.
fn spend(p: &Public, i: &Input) -> Result<(Fr, U256), Error> {
    if !below(i.commitment_index, TREE_HEIGHT) {
        return Err("a commitment index is out of range");
    }
    let index = i.commitment_index.to::<u64>();
    let nk = fr(i.nullifying_key)?;
    let pk = public_key(auth::auth_key_hash(&auth_key(&i.auth_key)?), nk);
    let (leaf, value) = if i.is_burn {
        if i.burn_value.is_zero() || !below(i.burn_value, AMOUNT_BITS) {
            return Err("a burn value is out of range");
        }
        if !below(i.burn_from, ADDRESS_BITS) {
            return Err("a burn sender is out of range");
        }
        let to = burn_address(p.chain, pk, fr(i.burn_salt)?)
            .ok_or("a burn salt misses the proof of work")?;
        // the ASP approves this deposit, at its own position
        if root(asp_leaf(Fr::from(index)), index, &i.asp_siblings)? != p.asp_root {
            return Err("the ASP has not approved a deposit");
        }
        let leaf = transfer_leaf(p.token, fr(i.burn_from)?, to, fr(i.burn_value)?);
        (leaf, i.burn_value)
    } else {
        if !below(i.note_value, AMOUNT_BITS) {
            return Err("a note value is out of range");
        }
        let hash = note_hash(p.chain, pk, fr(i.note_value)?, p.token, fr(i.note_salt)?);
        (note_leaf(p.token, hash), i.note_value)
    };
    if root(leaf, index, &i.commitment_siblings)? != p.root {
        return Err("an input is not in commitmentRoot");
    }
    Ok((nullifier(p.chain, Fr::from(index), nk), value))
}

fn public(token: U256, chain: U256, root: U256, asp_root: U256) -> Result<Public, Error> {
    if !below(token, TOKEN_ID_BITS) || !below(chain, CHAIN_ID_BITS) {
        return Err("tokenId or chainId is out of range");
    }
    Ok(Public {
        token: fr(token)?,
        chain: fr(chain)?,
        root: fr(root)?,
        asp_root: fr(asp_root)?,
    })
}

/// Root of the tree holding `leaf` at `index` (below 2^32), with sibling path `siblings`.
fn root(leaf: Fr, index: u64, siblings: &Path) -> Result<Fr, Error> {
    siblings
        .iter()
        .enumerate()
        .try_fold(leaf, |node, (level, sibling)| {
            let sibling = fr(*sibling)?;
            let pair = if index >> level & 1 == 1 {
                [sibling, node]
            } else {
                [node, sibling]
            };
            Ok(poseidon::hash(&POSEIDON2, &pair))
        })
}

/// A field element as the circuits take it: canonical, never reduced.
fn fr(v: U256) -> Result<Fr, Error> {
    Fr::from_bigint(BigInt(v.into_limbs())).ok_or("a value is not a field element")
}

fn u256(f: Fr) -> U256 {
    U256::from_limbs(f.into_bigint().0)
}

fn below(v: U256, bits: usize) -> bool {
    v.bit_len() <= bits
}

fn flag(v: U256) -> Result<bool, Error> {
    if v > U256::from(1) {
        return Err("a flag is neither 0 nor 1");
    }
    Ok(v == U256::from(1))
}

/// Fixtures for this crate's tests and, with the `fixtures` feature, for other crates' tests, which unwrap as tests do.
#[cfg(any(test, feature = "fixtures"))]
#[allow(dead_code, clippy::unwrap_used)]
pub mod tests {
    use super::*;
    use zerc20_zkp::primitives::Keys;
    use zerc20_zkp::tree::merkle_path;

    const CHAIN: u64 = 1;
    const TOKEN: u64 = 7;
    const SK: u64 = 42;
    const BURN_SALT: u64 = 2279; // has the proof of work at chain 1 for SK
    const RECIPIENT: u64 = 0xbeef;
    const INTENT: u64 = 0x1d; // any value: the attester does not interpret it

    fn n(v: u64) -> U256 {
        U256::from(v)
    }

    fn path(p: [Fr; TREE_HEIGHT]) -> Path {
        p.map(u256)
    }

    pub fn keys() -> Keys {
        Keys::of(Fr::from(SK))
    }

    pub fn auth_key_of(k: &Keys) -> [U256; 2] {
        [u256(k.auth_key.x), u256(k.auth_key.y)]
    }

    /// `w` with each real input's owner, `SK`, signing `s`.
    fn signed(s: &Transact, mut w: JoinSplit) -> JoinSplit {
        let sig = sign(keys().auth_secret, transact_message(s));
        w.signature0 = sig;
        w.signature1 = if w.in1_is_dummy == n(1) {
            Signature::default()
        } else {
            sig
        };
        w
    }

    /// The tree: note A (30) at 0, a 45 burn deposit at 1 (approved by the ASP), note B (20) at 2, all owned by SK.
    struct Tree {
        root: U256,
        asp_root: U256,
        leaves: Vec<Fr>,
        asp_path: Path,
    }

    fn tree() -> Tree {
        let (chain, token, pk) = (Fr::from(CHAIN), Fr::from(TOKEN), keys().public_key);
        let to = burn_address(chain, pk, Fr::from(BURN_SALT)).unwrap();
        let leaves = vec![
            note_leaf(
                token,
                note_hash(chain, pk, Fr::from(30), token, Fr::from(5)),
            ),
            transfer_leaf(token, Fr::from(0x1111), to, Fr::from(45)),
            note_leaf(
                token,
                note_hash(chain, pk, Fr::from(20), token, Fr::from(6)),
            ),
        ];
        let approvals = [Fr::from(0), asp_leaf(Fr::from(1))];
        let (asp_root, asp_path) = merkle_path(&approvals, 1);
        Tree {
            root: u256(merkle_path(&leaves, 0).0),
            asp_root: u256(asp_root),
            leaves,
            asp_path: path(asp_path),
        }
    }

    fn siblings(t: &Tree, index: usize) -> Path {
        path(merkle_path(&t.leaves, index).1)
    }

    fn statement(t: &Tree) -> Transact {
        Transact {
            tokenId: n(TOKEN),
            chainId: n(CHAIN),
            commitmentRoot: t.root,
            aspRoot: t.asp_root,
            ..Default::default()
        }
    }

    /// Burns the deposit (45) and spends note A (30): 25 withdrawn, 30 and 20 to two new notes.
    pub fn burn_and_note() -> (Transact, JoinSplit) {
        let t = tree();
        let w = JoinSplit {
            entropy: n(0),
            in0_is_burn: n(1),
            in1_is_dummy: n(0),
            in_note0_value: n(0),
            in_note0_salt: n(0),
            in_note1_value: n(30),
            in_note1_salt: n(5),
            burn_salt: n(BURN_SALT),
            burn_transfer_from: n(0x1111),
            burn_transfer_value: n(45),
            withdraw_recipient_private: n(RECIPIENT),
            withdraw_amount_private: n(25),
            withdraw_intent_private: n(INTENT),
            out_note1_public_key: n(77),
            out_note1_value: n(30),
            out_note1_salt: n(1),
            out_note2_public_key: n(78),
            out_note2_value: n(20),
            out_note2_salt: n(2),
            auth_key0: auth_key_of(&keys()),
            auth_key1: auth_key_of(&keys()),
            nullifying_key0: u256(keys().nullifying_key),
            nullifying_key1: u256(keys().nullifying_key),
            signature0: Signature::default(),
            signature1: Signature::default(),
            commitment_index0: n(1),
            commitment_index1: n(0),
            in0_merkle_siblings: siblings(&t, 1),
            in1_merkle_siblings: siblings(&t, 0),
            in0_asp_siblings: t.asp_path,
        };
        let s = transact_statement(&statement(&t), &w).unwrap();
        let w = signed(&s, w);
        (s, w)
    }

    /// Spends note B alone into one note, privately.
    fn note_and_dummy() -> (Transact, JoinSplit) {
        let t = tree();
        let (_, mut w) = burn_and_note();
        w.in0_is_burn = n(0);
        w.in1_is_dummy = n(1);
        w.entropy = n(7777);
        (w.burn_salt, w.burn_transfer_from, w.burn_transfer_value) = (n(0), n(0), n(0));
        (w.in_note0_value, w.in_note0_salt) = (n(20), n(6));
        (w.in_note1_value, w.in_note1_salt) = (n(0), n(0));
        (w.commitment_index0, w.commitment_index1) = (n(2), n(0));
        w.in0_merkle_siblings = siblings(&t, 2);
        w.in1_merkle_siblings = [U256::ZERO; TREE_HEIGHT];
        w.in0_asp_siblings = [U256::ZERO; TREE_HEIGHT];
        (
            w.withdraw_amount_private,
            w.withdraw_recipient_private,
            w.withdraw_intent_private,
        ) = (n(0), n(0), n(0));
        (w.out_note1_value, w.out_note2_value) = (n(20), n(0));
        // a dummy has no owner
        (w.auth_key1, w.nullifying_key1) = ([U256::ZERO; 2], U256::ZERO);
        let s = transact_statement(&statement(&t), &w).unwrap();
        let w = signed(&s, w);
        (s, w)
    }

    fn bytes(w: &impl serde::Serialize) -> Vec<u8> {
        serde_json::to_vec(w).unwrap()
    }

    #[test]
    fn accepts_valid_transacts() {
        let (s, w) = burn_and_note();
        assert_eq!(transact(&s, &bytes(&w)), Ok(()));
        let nk = keys().nullifying_key;
        assert_eq!(
            s.nullifier0,
            u256(nullifier(Fr::from(CHAIN), Fr::from(1), nk))
        );
        assert_eq!(
            s.nullifier1,
            u256(nullifier(Fr::from(CHAIN), Fr::from(0), nk))
        );
        assert_eq!(
            (s.withdrawRecipient, s.withdrawAmount, s.withdrawIntent),
            (n(RECIPIENT), n(25), n(INTENT))
        );

        let (s, w) = note_and_dummy();
        assert_eq!(transact(&s, &bytes(&w)), Ok(()));
        assert_eq!(
            s.nullifier1,
            u256(dummy_nullifier(Fr::from(CHAIN), Fr::from(7777)))
        );
        // circom input JSON: decimal strings, with fields this check ignores
        let mut json = serde_json::to_value(&w).unwrap();
        for (_, v) in json.as_object_mut().unwrap().iter_mut() {
            if let Some(d) = v
                .as_str()
                .map(|h| U256::from_str_radix(&h[2..], 16).unwrap())
            {
                *v = d.to_string().into();
            }
        }
        json["burn_public_key"] = "0".into();
        assert_eq!(transact(&s, &bytes(&json)), Ok(()));
    }

    #[test]
    fn rejects_invalid_transacts() {
        type Case = (&'static str, Box<dyn Fn(&mut Transact, &mut JoinSplit)>);
        let cases: Vec<Case> = vec![
            (
                "foreign nullifying key",
                Box::new(|_, w| {
                    w.nullifying_key0 = u256(Keys::of(Fr::from(SK + 1)).nullifying_key)
                }),
            ),
            (
                "foreign signing key",
                Box::new(|_, w| w.auth_key1 = auth_key_of(&Keys::of(Fr::from(SK + 1)))),
            ),
            (
                "signing key off the curve",
                Box::new(|_, w| w.auth_key0[0] += n(1)),
            ),
            (
                "flag that is not boolean",
                Box::new(|_, w| w.in1_is_dummy = n(2)),
            ),
            (
                "index aliasing position 1 above 2^32",
                Box::new(|_, w| w.commitment_index0 = (n(1) << 32) + n(1)),
            ),
            (
                "salt not below p",
                Box::new(|_, w| {
                    w.out_note1_salt = U256::from_limbs(Fr::MODULUS.0) + n(1);
                }),
            ),
            (
                "amount above 2^248 balanced by another",
                Box::new(|_, w| {
                    w.out_note1_value = (n(1) << 248) + n(30);
                    w.withdraw_amount_private = w.withdraw_amount_private.wrapping_sub(n(1) << 248);
                }),
            ),
            (
                "value not conserved",
                Box::new(|_, w| w.out_note1_value += n(1)),
            ),
            (
                "one note in both slots",
                Box::new(|_, w| {
                    w.in0_is_burn = n(0);
                    (w.in_note0_value, w.in_note0_salt) = (n(30), n(5));
                    w.commitment_index0 = n(0);
                    w.in0_merkle_siblings = w.in1_merkle_siblings;
                    w.out_note1_value -= n(15);
                }),
            ),
            (
                "recipient without a withdrawal",
                Box::new(|_, w| {
                    w.out_note2_value += w.withdraw_amount_private;
                    w.withdraw_amount_private = n(0);
                }),
            ),
            (
                "recipient above 2^160",
                Box::new(|_, w| w.withdraw_recipient_private = n(1) << 160),
            ),
            (
                "intent without a withdrawal",
                Box::new(|_, w| {
                    w.out_note2_value += w.withdraw_amount_private;
                    w.withdraw_amount_private = n(0);
                    w.withdraw_recipient_private = n(0);
                }),
            ),
            (
                "intent not below p",
                Box::new(|_, w| w.withdraw_intent_private = U256::from_limbs(Fr::MODULUS.0)),
            ),
            (
                "burn without proof of work",
                Box::new(|_, w| w.burn_salt = n(1)),
            ),
            (
                "zero-value burn",
                Box::new(|_, w| w.burn_transfer_value = n(0)),
            ),
            (
                "ASP approved another deposit",
                Box::new(|s, w| {
                    let (root, other) = merkle_path(&[asp_leaf(Fr::from(0))], 1);
                    s.aspRoot = u256(root);
                    w.in0_asp_siblings = path(other);
                }),
            ),
            (
                "out of chain id range",
                Box::new(|s, _| s.chainId = n(1) << 64),
            ),
        ];
        let (s0, w0) = burn_and_note();
        for (name, mutate) in cases {
            let (mut s, mut w) = (s0.clone(), w0.clone());
            mutate(&mut s, &mut w);
            assert!(transact_statement(&s, &w).is_err(), "{name}");
        }
        // a valid witness does not vouch for another statement
        let mut s = s0.clone();
        s.noteHash1 += n(1);
        assert!(transact(&s, &bytes(&w0)).is_err());
        assert!(transact(&s0, b"{}").is_err());

        // the owner signs the statement, each real input
        let unsigned = |w: &mut JoinSplit| w.signature1 = Signature::default();
        let other_key = |w: &mut JoinSplit| {
            w.signature0 = sign(
                Keys::of(Fr::from(SK + 1)).auth_secret,
                transact_message(&s0),
            );
        };
        let other_statement = |w: &mut JoinSplit| {
            let mut other = s0.clone();
            other.withdrawAmount += n(1);
            w.signature0 = sign(keys().auth_secret, transact_message(&other));
        };
        let not_canonical =
            |w: &mut JoinSplit| w.signature0.s += U256::from_limbs(AuthSecret::MODULUS.0);
        let mutations: [&dyn Fn(&mut JoinSplit); 4] =
            [&unsigned, &other_key, &other_statement, &not_canonical];
        for mutate in mutations {
            let mut w = w0.clone();
            mutate(&mut w);
            assert!(transact_statement(&s0, &w).is_ok());
            assert!(transact(&s0, &bytes(&w)).is_err());
        }
    }

    #[test]
    fn a_replayed_transact_witness_tells_no_wrong_statement_from_another() {
        // in0 a burn, then a note: a wrong ASP root fails the burn's own check, and the owners' signature for a note
        for (s, w) in [burn_and_note(), note_and_dummy()] {
            let w = bytes(&w);
            for other in [
                Transact {
                    aspRoot: s.aspRoot + n(1),
                    ..s.clone()
                },
                Transact {
                    commitmentRoot: s.commitmentRoot + n(1),
                    ..s.clone()
                },
                Transact {
                    withdrawAmount: s.withdrawAmount + n(1),
                    ..s.clone()
                },
                Transact {
                    noteHash2: s.noteHash2 + n(1),
                    ..s.clone()
                },
            ] {
                assert_eq!(transact(&other, &w), Err(MISMATCH));
            }
        }
    }

    pub fn merge_fixture() -> (Merge, MergeWitness) {
        let t = tree();
        let k = keys();
        let note = |index: usize, value, salt| Input {
            auth_key: auth_key_of(&k),
            nullifying_key: u256(k.nullifying_key),
            commitment_index: n(index as u64),
            commitment_siblings: siblings(&t, index),
            note_value: n(value),
            note_salt: n(salt),
            ..Default::default()
        };
        let burn = Input {
            is_burn: true,
            auth_key: auth_key_of(&k),
            nullifying_key: u256(k.nullifying_key),
            commitment_index: n(1),
            commitment_siblings: siblings(&t, 1),
            burn_salt: n(BURN_SALT),
            burn_from: n(0x1111),
            burn_value: n(45),
            asp_siblings: t.asp_path,
            ..Default::default()
        };
        let w = MergeWitness {
            inputs: vec![note(0, 30, 5), burn, note(2, 20, 6)],
            out_public_key: n(77),
            out_salt: n(9),
        };
        let s = Merge {
            tokenId: n(TOKEN),
            chainId: n(CHAIN),
            commitmentRoot: t.root,
            aspRoot: t.asp_root,
            fee: n(5),
            feeRecipient: n(0xbeef),
            ..Default::default()
        };
        merge_signed(s, w)
    }

    /// `s` with the outputs of `w`, and `w` with every input's owner, `SK`, signing it.
    fn merge_signed(mut s: Merge, mut w: MergeWitness) -> (Merge, MergeWitness) {
        (s.nullifiers, s.noteHash) = merge_outputs(&s, &w).unwrap();
        let sig = sign(keys().auth_secret, merge_message(&s, &w).unwrap());
        for input in &mut w.inputs {
            input.signature = sig;
        }
        (s, w)
    }

    #[test]
    fn merges() {
        let (s, w) = merge_fixture();
        assert_eq!(merge(&s, &bytes(&w)), Ok(()));
        // 95 merged, less the fee of 5
        let expected = note_hash(
            Fr::from(CHAIN),
            Fr::from(77),
            Fr::from(90),
            Fr::from(TOKEN),
            Fr::from(9),
        );
        assert_eq!(s.noteHash, u256(expected));

        let reject = |name: &str, s: &Merge, w: &MergeWitness| {
            assert!(merge(s, &bytes(w)).is_err(), "{name}");
        };
        let (mut other, w0) = merge_fixture();
        other.noteHash += n(1);
        reject("another output", &other, &w0);
        let (mut other, w0) = merge_fixture();
        other.nullifiers.swap(0, 1);
        reject("nullifiers out of order", &other, &w0);
        let (s, mut w) = merge_fixture();
        w.out_salt = n(10);
        reject("output salt changed", &s, &w);
        let (s, mut w) = merge_fixture();
        let again = w.inputs[0].clone();
        w.inputs.push(again);
        assert!(merge_outputs(&s, &w).is_err(), "input spent twice");
        let (s, mut w) = merge_fixture();
        w.inputs.clear();
        assert!(merge_outputs(&s, &w).is_err(), "empty merge");
        let (s, mut w) = merge_fixture();
        w.inputs[1].is_burn = false;
        assert!(merge_outputs(&s, &w).is_err(), "burn spent as a note");
        let (mut other, w0) = merge_fixture();
        other.fee = n(6);
        reject("another fee", &other, &w0);

        // the owner signs the merge, every input
        let (s, mut w) = merge_fixture();
        w.inputs[2].signature = Signature::default();
        reject("an input unsigned", &s, &w);
        let (s, w0) = merge_fixture();
        let (other, mut w) = merge_signed(Merge { fee: n(6), ..s }, w0.clone());
        for (input, old) in w.inputs.iter_mut().zip(&w0.inputs) {
            input.signature = old.signature;
        }
        assert!(merge_outputs(&other, &w).is_ok());
        reject("signed for another fee", &other, &w);
        let (s, w) = merge_fixture();
        let mut fewer = w.clone();
        fewer.inputs.pop();
        let mut fewer_s = s.clone();
        (fewer_s.nullifiers, fewer_s.noteHash) = merge_outputs(&fewer_s, &fewer).unwrap();
        reject("signed for another set of inputs", &fewer_s, &fewer);
        let fee = |fee: u64, to: U256| {
            let (mut s, w) = merge_fixture();
            (s.fee, s.feeRecipient) = (n(fee), to);
            merge_outputs(&s, &w)
        };
        assert!(fee(0, U256::ZERO).is_ok(), "no fee");
        assert!(fee(95, n(0xbeef)).is_ok(), "all of it");
        assert!(fee(96, n(0xbeef)).is_err(), "fee above the merged value");
        assert!(fee(5, U256::ZERO).is_err(), "fee without a recipient");
        assert!(fee(0, n(0xbeef)).is_err(), "recipient without a fee");
        assert!(fee(5, n(1) << 160).is_err(), "recipient above 2^160");
    }

    #[test]
    fn a_replayed_merge_witness_tells_no_wrong_fee_from_another() {
        let (s, w) = merge_fixture();
        let w = bytes(&w);
        // 95 merged: a fee below it and one above it are as wrong as each other
        for fee in [0, 4, 6, 94, 95, 96, 1000] {
            let to = if fee == 0 { U256::ZERO } else { s.feeRecipient };
            assert_eq!(
                merge(
                    &Merge {
                        fee: n(fee),
                        feeRecipient: to,
                        ..s.clone()
                    },
                    &w
                ),
                Err(MISMATCH),
                "fee {fee}"
            );
        }
        for other in [
            Merge {
                commitmentRoot: s.commitmentRoot + n(1),
                ..s.clone()
            },
            Merge {
                aspRoot: s.aspRoot + n(1),
                ..s.clone()
            },
            Merge {
                tokenId: n(TOKEN + 1),
                ..s.clone()
            },
        ] {
            assert_eq!(merge(&other, &w), Err(MISMATCH));
        }
    }

    #[test]
    fn merged_value_stays_in_range() {
        let (chain, token, pk) = (Fr::from(CHAIN), Fr::from(TOKEN), keys().public_key);
        let half = n(1) << 247;
        let leaves: Vec<Fr> = (0..2)
            .map(|salt| {
                note_leaf(
                    token,
                    note_hash(chain, pk, fr(half).unwrap(), token, Fr::from(salt)),
                )
            })
            .collect();
        let (root, _) = merkle_path(&leaves, 0);
        let inputs = (0..2)
            .map(|i| Input {
                auth_key: auth_key_of(&keys()),
                nullifying_key: u256(keys().nullifying_key),
                commitment_index: n(i),
                commitment_siblings: path(merkle_path(&leaves, i as usize).1),
                note_value: half,
                note_salt: n(i),
                ..Default::default()
            })
            .collect();
        let s = Merge {
            tokenId: n(TOKEN),
            chainId: n(CHAIN),
            commitmentRoot: u256(root),
            ..Default::default()
        };
        let w = MergeWitness {
            inputs,
            out_public_key: n(77),
            out_salt: n(9),
        };
        assert_eq!(
            merge_outputs(&s, &w),
            Err("the merged value is out of range")
        );
    }
}
