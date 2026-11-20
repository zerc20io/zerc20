//! The root transition step circuit folded by Nova.
//!
//! The state is `[index, hash_chain, root]`. One step appends one commitment
//! `fields` at position `index` of the commitment tree:
//!
//! - `root`: the slot is empty under the old root, and the new root is the same
//!   path with the leaf `Poseidon4(fields)`;
//! - `hash_chain = SHA256(hash_chain || fields) mod 2^248` over 32-byte
//!   big-endian words, with the old `hash_chain < 2^248`;
//! - `index += 1`, with `index < 2^TREE_HEIGHT`.

use ark_bn254::Fr;
use ark_r1cs_std::{
    GR1CSVar, alloc::AllocVar, boolean::Boolean, convert::ToBitsGadget, eq::EqGadget,
    fields::FieldVar, fields::fp::FpVar,
};
use ark_relations::gr1cs::SynthesisError;
use sonobe_ivc::compilers::cyclefold::evm_verifier::{DeciderStateFragment, FCircuitEVMExt};
use sonobe_primitives::circuits::FCircuit;

use crate::{
    commitments::COMMITMENT_FIELDS,
    poseidon::{self, POSEIDON4},
    primitives::hash_chain_var,
    tree::{TREE_HEIGHT, merkle_root_var},
};

pub const STATE_LEN: usize = 3;

/// `[index, hash_chain, root]`.
pub type RootState = [Fr; STATE_LEN];

/// One appended commitment and the sibling path of its slot.
#[derive(Clone, Debug, Default)]
pub struct RootStep {
    pub fields: [Fr; COMMITMENT_FIELDS],
    pub siblings: [Fr; TREE_HEIGHT],
}

#[derive(Clone, Copy, Debug)]
pub struct RootCircuit;

impl FCircuit for RootCircuit {
    type Field = Fr;
    type State = RootState;
    type StateVar = [FpVar<Fr>; STATE_LEN];
    type ExternalInputs = RootStep;
    type ExternalOutputs = ();

    fn same_state_shape(_: &RootState, _: &RootState) -> bool {
        true
    }

    fn dummy_state(&self) -> RootState {
        RootState::default()
    }

    fn dummy_external_inputs(&self) -> RootStep {
        RootStep::default()
    }

    fn synthesize_step(
        &self,
        _i: FpVar<Fr>,
        [index, hash_chain, root]: Self::StateVar,
        step: RootStep,
    ) -> Result<(Self::StateVar, ()), SynthesisError> {
        let cs = index.cs();
        let fields: [FpVar<Fr>; COMMITMENT_FIELDS] =
            AllocVar::<[Fr; COMMITMENT_FIELDS], _>::new_witness(cs.clone(), || Ok(step.fields))?;
        let siblings: [FpVar<Fr>; TREE_HEIGHT] =
            AllocVar::<[Fr; TREE_HEIGHT], _>::new_witness(cs, || Ok(step.siblings))?;

        let index_bits = index.to_bits_le()?;
        for bit in &index_bits[TREE_HEIGHT..] {
            bit.enforce_equal(&Boolean::FALSE)?;
        }
        let index_bits = &index_bits[..TREE_HEIGHT];

        merkle_root_var(&FpVar::zero(), index_bits, &siblings)?.enforce_equal(&root)?;
        let leaf = poseidon::hash_var(&POSEIDON4, &fields)?;
        let new_root = merkle_root_var(&leaf, index_bits, &siblings)?;
        let new_hash_chain = hash_chain_var(&hash_chain, &fields)?;

        Ok(([index + FpVar::one(), new_hash_chain, new_root], ()))
    }
}

impl FCircuitEVMExt for RootCircuit {
    fn decider_state_fragment(_: &RootState) -> DeciderStateFragment {
        DeciderStateFragment {
            // `index | hash_chain | root`; the array length pins the shape.
            type_name: "uint256[3]".to_string(),
            type_def: String::new(),
            shape_check_body: String::new(),
            flatten_body: "return z;".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use ark_relations::gr1cs::{ConstraintSystem, ConstraintSystemRef};

    use ark_ff::PrimeField;

    use super::*;
    use crate::{commitments::commitment_leaf, primitives::hash_chain, tree::IncrementalTree};

    /// Fields with non-zero high bytes so the byte order of the hash chain
    /// input is exercised.
    fn fields(seed: u8) -> [Fr; COMMITMENT_FIELDS] {
        std::array::from_fn(|i| Fr::from_be_bytes_mod_order(&[seed + i as u8; 31]))
    }

    fn synthesize(state: RootState, step: RootStep) -> (ConstraintSystemRef<Fr>, RootState) {
        let cs = ConstraintSystem::new_ref();
        let state: [FpVar<Fr>; STATE_LEN] =
            AllocVar::<RootState, _>::new_witness(cs.clone(), || Ok(state)).unwrap();
        let (next, ()) = RootCircuit
            .synthesize_step(FpVar::zero(), state, step)
            .unwrap();
        (cs, next.value().unwrap())
    }

    #[test]
    fn step_appends_commitment() {
        let mut tree = IncrementalTree::default();
        for seed in [0x10, 0x20, 0x30] {
            tree.append(commitment_leaf(&fields(seed)));
        }
        let state = [
            Fr::from(3u64),
            Fr::from_be_bytes_mod_order(&[0xab; 31]),
            tree.root,
        ];
        let step = RootStep {
            fields: fields(0x40),
            siblings: tree.append(commitment_leaf(&fields(0x40))),
        };

        let (cs, next) = synthesize(state, step.clone());
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(
            next,
            [
                Fr::from(4u64),
                hash_chain(state[1], &step.fields),
                tree.root
            ]
        );
    }

    #[test]
    fn step_rejects_occupied_slot() {
        let mut tree = IncrementalTree::default();
        let siblings = tree.append(commitment_leaf(&fields(0x10)));
        let (cs, _) = synthesize(
            [Fr::from(0u64), Fr::from(0u64), tree.root],
            RootStep {
                fields: fields(0x20),
                siblings,
            },
        );
        assert!(!cs.is_satisfied().unwrap());
    }
}
