//! The merge step circuit folded by Nova: N private inputs into one note.
//!
//! The state is `[token_id, chain_id, commitment_root, asp_root,
//! nullifier_chain, signed_chain, note_hash, remaining, fee, fee_recipient]`.
//! One step spends one input with the semantics of JoinSplit's `in0`
//! (`circom/main/joinsplit.circom`):
//!
//! - the input is a private note, or (`is_burn`) a transfer to a burn address
//!   that the ASP approved as a deposit in `asp_root`;
//! - its leaf is in `commitment_root` and owned by `public_key(auth_key_hash,
//!   nullifying_key)`, and its owner signed the merge under `auth_key`
//!   (`auth.rs`). The prover never holds the private key, so it can prove no
//!   merge the owner did not sign;
//! - `nullifier_chain = hash_chain(nullifier_chain, [nullifier])`, so the
//!   contract can recompute it from the published nullifiers;
//! - `note_hash` is the output note being accumulated: `0` before the first
//!   step, then `NoteHash(chain_id, out_public_key, sum, token_id, out_salt)`
//!   over the values spent so far, and at the last step over that sum less
//!   `fee`. The final `note_hash` is the merged note;
//! - `remaining` counts the steps left, so the last step is the one that finds
//!   it at 1;
//! - the signed message is `merge_message(signed_chain, out_public_key,
//!   out_salt, fee, fee_recipient)`.
//!
//! The contract builds `z_0` with `nullifier_chain = note_hash = 0` and
//! `remaining` = the number of inputs, and `z_i` with `remaining = 0`. It sets
//! `signed_chain` in both to the chain of the nullifiers it spends, so every
//! owner signed exactly that set. It mints `fee` publicly to `fee_recipient`
//! (the relayer's pay) and checks both are in range: `fee < 2^248`, so a sum
//! below it wraps and fails the range check. All words but `nullifier_chain`,
//! `note_hash` and `remaining` pass through.
//!
//! Unlike JoinSplit, the inactive branch's witness is not pinned to zero: Nova
//! witnesses stay private and the branch is muxed out, so only its gated
//! checks have to remain satisfiable. Distinct nullifiers are enforced by the
//! contract, which spends every published nullifier.

use ark_bn254::Fr;
use ark_ed_on_bn254::constraints::EdwardsVar;
use ark_r1cs_std::{
    GR1CSVar, alloc::AllocVar, boolean::Boolean, eq::EqGadget, fields::FieldVar, fields::fp::FpVar,
};
use ark_relations::gr1cs::SynthesisError;
use sonobe_ivc::compilers::cyclefold::evm_verifier::{DeciderStateFragment, FCircuitEVMExt};
use sonobe_primitives::circuits::FCircuit;

use crate::{
    auth::{self, AuthKey, Signature},
    poseidon::{self, POSEIDON2, POSEIDON3, POSEIDON4, POSEIDON5},
    primitives::{
        ADDRESS_BITS, AMOUNT_BITS, BURN_POW_BITS, CHAIN_ID_BITS, DOMAIN_ASP_LEAF, DOMAIN_BURN,
        DOMAIN_NULLIFIER, DOMAIN_PUBLIC_KEY, FIELD_BIT_LENGTH, NOTE_FIELD0_BASE, TOKEN_ID_BITS,
        TRANSFER_FIELD0_BASE, domain_hash_var, hash_chain_var, note_hash_var,
    },
    tree::{TREE_HEIGHT, merkle_root_var},
};

pub const STATE_LEN: usize = 10;

/// `[token_id, chain_id, commitment_root, asp_root, nullifier_chain,
/// signed_chain, note_hash, remaining, fee, fee_recipient]`.
pub type MergeState = [Fr; STATE_LEN];

/// One spent input, the output note opening, and the sum spent before it.
/// The fields of the branch not selected by `is_burn` are ignored.
#[derive(Clone, Debug, Default)]
pub struct MergeStep {
    pub is_burn: bool,
    pub auth_key: AuthKey,
    pub nullifying_key: Fr,
    /// The owner's signature on the merge, under `auth_key`.
    pub signature: Signature,
    pub commitment_index: Fr,
    pub commitment_siblings: [Fr; TREE_HEIGHT],

    pub note_value: Fr,
    pub note_salt: Fr,

    pub burn_salt: Fr,
    pub burn_from: Fr,
    pub burn_value: Fr,
    /// The path of the deposit's own position in the ASP tree.
    pub asp_siblings: [Fr; TREE_HEIGHT],

    pub out_public_key: Fr,
    pub out_salt: Fr,
    /// The output note's value before this step, `0` on the first step.
    pub prev_sum: Fr,
}

/// Enforces `value < 2^bits` and returns its `bits` little-endian bits.
fn range_check(value: &FpVar<Fr>, bits: usize) -> Result<Vec<Boolean<Fr>>, SynthesisError> {
    Ok(value.to_bits_le_with_top_bits_zero(bits)?.0)
}

#[derive(Clone, Copy, Debug)]
pub struct MergeCircuit;

impl FCircuit for MergeCircuit {
    type Field = Fr;
    type State = MergeState;
    type StateVar = [FpVar<Fr>; STATE_LEN];
    type ExternalInputs = MergeStep;
    type ExternalOutputs = ();

    fn same_state_shape(_: &MergeState, _: &MergeState) -> bool {
        true
    }

    fn dummy_state(&self) -> MergeState {
        MergeState::default()
    }

    fn dummy_external_inputs(&self) -> MergeStep {
        MergeStep::default()
    }

    // The last step is found by `remaining`, not by the step index `_i`: the
    // step stays a function of the state alone, as the IVC soundness that
    // `lean/README.md` builds on assumes.
    fn synthesize_step(
        &self,
        _i: FpVar<Fr>,
        [
            token_id,
            chain_id,
            commitment_root,
            asp_root,
            nullifier_chain,
            signed_chain,
            note_hash,
            remaining,
            fee,
            fee_recipient,
        ]: Self::StateVar,
        step: MergeStep,
    ) -> Result<(Self::StateVar, ()), SynthesisError> {
        let cs = token_id.cs();
        let witness = |value: Fr| FpVar::new_witness(cs.clone(), || Ok(value));
        let path = |siblings: [Fr; TREE_HEIGHT]| {
            <[FpVar<Fr>; TREE_HEIGHT] as AllocVar<[Fr; TREE_HEIGHT], _>>::new_witness(
                cs.clone(),
                || Ok(siblings),
            )
        };
        let zero = FpVar::zero();
        let is_burn = Boolean::new_witness(cs.clone(), || Ok(step.is_burn))?;

        range_check(&token_id, TOKEN_ID_BITS)?;
        range_check(&chain_id, CHAIN_ID_BITS)?;

        // Ownership: the public key of the signing key and the nullifying key
        // is the committed owner of either branch, which is JoinSplit's owner
        // check with the keys substituted. The signature is checked below,
        // once the output note it covers is allocated.
        let auth_key = EdwardsVar::new_witness(cs.clone(), || Ok(step.auth_key))?;
        let auth_key_hash = auth::auth_key_hash_var(&auth_key)?;
        let nullifying_key = witness(step.nullifying_key)?;
        let public_key = domain_hash_var(
            &POSEIDON3,
            DOMAIN_PUBLIC_KEY,
            &[auth_key_hash.clone(), nullifying_key.clone()],
        )?;

        // Note branch.
        let note_value = witness(step.note_value)?;
        range_check(&note_value, AMOUNT_BITS)?;
        let input_note_hash = note_hash_var(
            &chain_id,
            &public_key,
            &note_value,
            &token_id,
            &witness(step.note_salt)?,
        )?;
        let note_leaf = poseidon::hash_var(
            &POSEIDON4,
            &[
                &token_id + NOTE_FIELD0_BASE,
                input_note_hash,
                zero.clone(),
                zero.clone(),
            ],
        )?;

        // Burn branch, every check gated by `is_burn`.
        let burn_from = witness(step.burn_from)?;
        let burn_value = witness(step.burn_value)?;
        range_check(&burn_from, ADDRESS_BITS)?;
        range_check(&burn_value, AMOUNT_BITS)?;
        burn_value.conditional_enforce_not_equal(&zero, &is_burn)?;

        // Proof of work: the top `BURN_POW_BITS` of the canonical digest are
        // zero. Below 2^238 < p the decomposition is unique, so it needs no
        // in-field check; the inactive branch decomposes zero instead.
        let digest = domain_hash_var(
            &POSEIDON5,
            DOMAIN_BURN,
            &[
                chain_id.clone(),
                public_key,
                witness(step.burn_salt)?,
                zero.clone(),
            ],
        )?;
        let digest_bits = range_check(
            &is_burn.select(&digest, &zero)?,
            FIELD_BIT_LENGTH - BURN_POW_BITS,
        )?;
        let burn_address = Boolean::le_bits_to_fp(&digest_bits[..ADDRESS_BITS])?;
        let transfer_leaf = poseidon::hash_var(
            &POSEIDON4,
            &[
                &token_id + TRANSFER_FIELD0_BASE,
                burn_from,
                burn_address,
                burn_value.clone(),
            ],
        )?;

        // The ASP approves this deposit at its own position, the same index
        // that proves its membership below, as in BurnIntake.
        let commitment_index = witness(step.commitment_index)?;
        let index_bits = range_check(&commitment_index, TREE_HEIGHT)?;
        let asp_leaf = domain_hash_var(
            &POSEIDON2,
            DOMAIN_ASP_LEAF,
            std::slice::from_ref(&commitment_index),
        )?;
        merkle_root_var(&asp_leaf, &index_bits, &path(step.asp_siblings)?)?
            .conditional_enforce_equal(&asp_root, &is_burn)?;

        // Membership of the selected leaf.
        let leaf = is_burn.select(&transfer_leaf, &note_leaf)?;
        let value = is_burn.select(&burn_value, &note_value)?;
        merkle_root_var(&leaf, &index_bits, &path(step.commitment_siblings)?)?
            .enforce_equal(&commitment_root)?;

        // Position-keyed nullifier, valid for both branches.
        let nullifier = domain_hash_var(
            &POSEIDON5,
            DOMAIN_NULLIFIER,
            &[
                chain_id.clone(),
                commitment_index,
                nullifying_key,
                zero.clone(),
            ],
        )?;
        let next_nullifier_chain = hash_chain_var(&nullifier_chain, &[nullifier])?;

        // Output note accumulator. `note_hash == 0` only before the first step:
        // `z_0` is fixed by the contract and every later value is a Poseidon
        // output. Otherwise the opening binds owner, salt and the prior sum.
        let out_public_key = witness(step.out_public_key)?;
        let out_salt = witness(step.out_salt)?;
        let message = auth::merge_message_var(
            &signed_chain,
            &out_public_key,
            &out_salt,
            &fee,
            &fee_recipient,
        )?;
        auth::verify_var(
            cs.clone(),
            &auth_key,
            &auth_key_hash,
            &message,
            &step.signature,
        )?;
        let prev_sum = witness(step.prev_sum)?;
        let is_empty = note_hash.is_zero()?;
        prev_sum.conditional_enforce_equal(&zero, &is_empty)?;
        note_hash_var(&chain_id, &out_public_key, &prev_sum, &token_id, &out_salt)?
            .conditional_enforce_equal(&note_hash, &!is_empty)?;
        // Both terms are below 2^248, so the sum cannot wrap. The last step
        // pays the fee out of it: below the fee, it wraps and fails the check.
        let sum = prev_sum + value;
        let is_last = remaining.is_eq(&FpVar::one())?;
        let out = is_last.select(&(&sum - &fee), &sum)?;
        range_check(&out, AMOUNT_BITS)?;
        let next_note_hash = note_hash_var(&chain_id, &out_public_key, &out, &token_id, &out_salt)?;

        Ok((
            [
                token_id,
                chain_id,
                commitment_root,
                asp_root,
                next_nullifier_chain,
                signed_chain,
                next_note_hash,
                remaining - FpVar::one(),
                fee,
                fee_recipient,
            ],
            (),
        ))
    }
}

impl FCircuitEVMExt for MergeCircuit {
    fn decider_state_fragment(_: &MergeState) -> DeciderStateFragment {
        DeciderStateFragment {
            // The state words in order; the array length pins the shape.
            type_name: "uint256[10]".to_string(),
            type_def: String::new(),
            shape_check_body: String::new(),
            flatten_body: "return z;".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use ark_relations::gr1cs::{ConstraintSystem, ConstraintSystemRef};

    use super::*;
    use crate::{
        commitments::{asp_leaf, note_leaf, transfer_leaf},
        primitives::{
            Keys, burn_digest, digest_address, hash_chain, note_hash, nullifier, nullifier_chain,
        },
        tree::merkle_path,
    };

    fn fr(value: u64) -> Fr {
        Fr::from(value)
    }

    const CHAIN: u64 = 1;
    const TOKEN: u64 = 7;
    const SK: u64 = 42;
    /// Has the proof of work at chain 1 for `SK`'s public key.
    const BURN_SALT: u64 = 2279;

    fn keys() -> Keys {
        Keys::of(fr(SK))
    }

    /// A tree holding a 30-value note at 0 and a burn transfer at 1, both owned
    /// by `SK`, and the two steps merging them into one note, paying no fee.
    /// The ASP approved the deposit at `approved`.
    fn fixture(
        burn_salt: u64,
        burn_value: u64,
        approved: u64,
    ) -> (MergeState, MergeStep, MergeStep) {
        let (chain, token, k) = (fr(CHAIN), fr(TOKEN), keys());
        let pk = k.public_key;
        let from = fr(0x1111);
        let address = digest_address(burn_digest(chain, pk, fr(burn_salt)));
        let leaves = [
            note_leaf(token, note_hash(chain, pk, fr(30), token, fr(5))),
            transfer_leaf(token, from, address, fr(burn_value)),
        ];
        let (root, note_path) = merkle_path(&leaves, 0);
        let (_, burn_path) = merkle_path(&leaves, 1);
        // The ASP tree holds the approval at its own position; the burn sits at 1.
        let mut approvals = vec![fr(0); approved as usize + 1];
        approvals[approved as usize] = asp_leaf(fr(approved));
        let (asp_root, _) = merkle_path(&approvals, approved as usize);
        let (_, asp_path) = merkle_path(&approvals, 1);

        let out = MergeStep {
            auth_key: k.auth_key,
            nullifying_key: k.nullifying_key,
            out_public_key: Keys::of(fr(7)).public_key,
            out_salt: fr(99),
            ..Default::default()
        };
        let note = MergeStep {
            commitment_index: fr(0),
            commitment_siblings: note_path,
            note_value: fr(30),
            note_salt: fr(5),
            ..out.clone()
        };
        let burn = MergeStep {
            is_burn: true,
            commitment_index: fr(1),
            commitment_siblings: burn_path,
            burn_salt: fr(burn_salt),
            burn_from: from,
            burn_value: fr(burn_value),
            asp_siblings: asp_path,
            prev_sum: fr(30),
            ..out
        };
        let z0 = [
            token,
            chain,
            root,
            asp_root,
            fr(0),
            fr(0),
            fr(0),
            fr(2),
            fr(0),
            fr(0),
        ];
        signed(z0, note, burn)
    }

    /// `z0` committing to the two steps' nullifiers, and the steps signed by
    /// their owner over that and the rest of `z0`.
    fn signed(
        mut z0: MergeState,
        mut note: MergeStep,
        mut burn: MergeStep,
    ) -> (MergeState, MergeStep, MergeStep) {
        let nf = |s: &MergeStep| nullifier(z0[1], s.commitment_index, s.nullifying_key);
        z0[5] = nullifier_chain(&[nf(&note), nf(&burn)]);
        let message = auth::merge_message(z0[5], note.out_public_key, note.out_salt, z0[8], z0[9]);
        let signature = auth::sign(keys().auth_secret, message);
        (note.signature, burn.signature) = (signature, signature);
        (z0, note, burn)
    }

    /// `(z0, note, burn)` paying `fee` to `RELAYER`, signed again.
    fn paying(
        (mut z0, note, burn): (MergeState, MergeStep, MergeStep),
        fee: u64,
    ) -> (MergeState, MergeStep, MergeStep) {
        (z0[8], z0[9]) = (fr(fee), fr(RELAYER));
        signed(z0, note, burn)
    }

    const RELAYER: u64 = 0xbeef;

    fn synthesize(state: MergeState, step: MergeStep) -> (ConstraintSystemRef<Fr>, MergeState) {
        let cs = ConstraintSystem::new_ref();
        let state: [FpVar<Fr>; STATE_LEN] =
            AllocVar::<MergeState, _>::new_witness(cs.clone(), || Ok(state)).unwrap();
        let (next, ()) = MergeCircuit
            .synthesize_step(FpVar::zero(), state, step)
            .unwrap();
        (cs, next.value().unwrap())
    }

    #[test]
    fn steps_merge_note_and_burn() {
        let (z0, note, burn) = fixture(BURN_SALT, 45, 1);
        let (chain, token, nk) = (fr(CHAIN), fr(TOKEN), keys().nullifying_key);
        let output = |sum| note_hash(chain, note.out_public_key, fr(sum), token, note.out_salt);

        let (cs, z1) = synthesize(z0, note.clone());
        assert!(cs.is_satisfied().unwrap());
        let chain1 = hash_chain(fr(0), &[nullifier(chain, fr(0), nk)]);
        assert_eq!(z1[..4], z0[..4]);
        assert_eq!(z1[4..], [chain1, z0[5], output(30), fr(1), fr(0), fr(0)]);

        let (cs, z2) = synthesize(z1, burn);
        assert!(cs.is_satisfied().unwrap());
        let chain2 = hash_chain(chain1, &[nullifier(chain, fr(1), nk)]);
        assert_eq!(z2[..4], z0[..4]);
        assert_eq!(z2[4..], [chain2, z0[5], output(75), fr(0), fr(0), fr(0)]);
        // what the contract checks: the chain spent is the chain signed
        assert_eq!(chain2, z0[5]);
    }

    #[test]
    fn last_step_pays_the_fee() {
        let (z0, note, burn) = paying(fixture(BURN_SALT, 45, 1), 5);
        let (chain, token) = (fr(CHAIN), fr(TOKEN));
        let output = |sum| note_hash(chain, note.out_public_key, fr(sum), token, note.out_salt);

        // only the last step subtracts it; the fee and its recipient pass through
        let (cs, z1) = synthesize(z0, note.clone());
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(z1[6..], [output(30), fr(1), fr(5), fr(RELAYER)]);
        let (cs, z2) = synthesize(z1, burn);
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(z2[6..], [output(70), fr(0), fr(5), fr(RELAYER)]);

        // a merge of one input pays it at its only step
        let (mut single, note, _) = paying(fixture(BURN_SALT, 45, 1), 5);
        single[7] = fr(1);
        single[5] = nullifier_chain(&[nullifier(chain, fr(0), note.nullifying_key)]);
        let message = auth::merge_message(
            single[5],
            note.out_public_key,
            note.out_salt,
            fr(5),
            fr(RELAYER),
        );
        let note = MergeStep {
            signature: auth::sign(keys().auth_secret, message),
            ..note
        };
        let (cs, z1) = synthesize(single, note);
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(z1[6..8], [output(25), fr(0)]);
    }

    #[test]
    fn step_rejects_invalid_inputs() {
        let satisfied = |(z0, note, burn): (MergeState, MergeStep, MergeStep)| {
            let (cs, z1) = synthesize(z0, note);
            cs.is_satisfied().unwrap() && synthesize(z1, burn).0.is_satisfied().unwrap()
        };
        let valid = || fixture(BURN_SALT, 45, 1);
        assert!(satisfied(valid()));

        // another key's nullifying key, signed by the owner
        let mut foreign_key = valid();
        foreign_key.1.nullifying_key = Keys::of(fr(SK + 1)).nullifying_key;
        let foreign_key = signed(foreign_key.0, foreign_key.1, foreign_key.2);
        // the owner's keys, signed by another key
        let mut foreign_signer = valid();
        foreign_signer.1.signature = auth::sign(Keys::of(fr(SK + 1)).auth_secret, fr(1));
        // a merge the owner signed for another fee, or another set of nullifiers
        let mut other_fee = valid();
        other_fee.0[8] = fr(1);
        other_fee.0[9] = fr(RELAYER);
        let mut other_set = valid();
        other_set.0[5] = fr(1);
        let mut minted_prev_sum = valid();
        minted_prev_sum.1.prev_sum = fr(1);
        let mut tampered_prev_sum = valid();
        tampered_prev_sum.2.prev_sum = fr(31);
        let mut swapped_out_salt = valid();
        swapped_out_salt.2.out_salt = fr(100);
        let cases = [
            ("foreign key", foreign_key),
            ("signed by another key", foreign_signer),
            ("fee the owner did not sign", other_fee),
            ("nullifiers the owner did not sign", other_set),
            ("non-zero sum before the first step", minted_prev_sum),
            ("tampered prior sum", tampered_prev_sum),
            ("output salt changed mid-merge", swapped_out_salt),
            ("fee above the sum", paying(valid(), 76)),
            ("ASP approved another deposit", fixture(BURN_SALT, 45, 0)),
            ("burn salt without proof of work", fixture(1, 45, 1)),
            ("zero-value burn", fixture(BURN_SALT, 0, 1)),
        ];
        for (name, case) in cases {
            assert!(!satisfied(case), "{name}");
        }
    }
}
