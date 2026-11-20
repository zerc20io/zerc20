//! On-chain encoding of a decider proof.
//!
//! The rendered decider takes sonobe's calldata
//!
//! ```text
//! calldata = i (32B) || z0 (N words) || zi (N words) || challenge (32B)
//!         || U_cm_e (64B) || cm_t (64B) || U_cm_w (64B) || u_cm_w (64B)
//!         || lego proof (384B)
//! ```
//!
//! but its callers rebuild `i`, `z_0` and `z_i` themselves:
//!
//! - `CommitmentLedger.proveRootTransition`: `i = newIndex - oldIndex` (one step per commitment),
//!   `z_0` its current root state, `z_i` the claimed new state (N = 3);
//! - `Verifier.merge`: `i = nullifiers.length`, `z_0` / `z_i` from the request (N = 9).
//!
//! So an on-chain proof is only the calldata after `z_i`, which is also the ABI encoding of the
//! static `NovaDeciderProof` struct (672B).

use sonobe_ivc::IVCProofCompressorEVMExt;

use crate::{
    ivc::{DeciderProof, DeciderVerifierKey, NovaDecider},
    merge::{self, MergeCircuit, MergeState},
    root::{self, RootCircuit, RootState},
};

const WORD_BYTES: usize = 32;

pub const DECIDER_PROOF_BYTES: usize = 21 * WORD_BYTES;

#[derive(thiserror::Error, Debug)]
pub enum EncodeError {
    #[error(transparent)]
    Ivc(#[from] sonobe_ivc::Error),

    #[error("unexpected decider calldata length {0}")]
    UnexpectedCalldataLength(usize),
}

/// The `NovaDeciderProof` part of `calldata` for a state of `state_len` words.
fn after_zi(calldata: Vec<u8>, state_len: usize) -> Result<Vec<u8>, EncodeError> {
    let head = (1 + 2 * state_len) * WORD_BYTES;
    if calldata.len() != head + DECIDER_PROOF_BYTES {
        return Err(EncodeError::UnexpectedCalldataLength(calldata.len()));
    }
    Ok(calldata[head..].to_vec())
}

/// The `NovaDeciderProof` passed to `CommitmentLedger.proveRootTransition`.
pub fn root_proof_calldata(
    vk: &DeciderVerifierKey<RootState>,
    steps: usize,
    z0: &RootState,
    zi: &RootState,
    proof: &DeciderProof,
) -> Result<Vec<u8>, EncodeError> {
    let calldata = NovaDecider::verify_calldata::<RootCircuit>(vk, steps, z0, zi, proof)?;
    after_zi(calldata, root::STATE_LEN)
}

/// The `NovaDeciderProof` passed to `Verifier.merge`.
pub fn merge_proof_calldata(
    vk: &DeciderVerifierKey<MergeState>,
    steps: usize,
    z0: &MergeState,
    zi: &MergeState,
    proof: &DeciderProof,
) -> Result<Vec<u8>, EncodeError> {
    let calldata = NovaDecider::verify_calldata::<MergeCircuit>(vk, steps, z0, zi, proof)?;
    after_zi(calldata, merge::STATE_LEN)
}
