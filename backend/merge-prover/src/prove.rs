//! Merges, proved inside the enclave. The witness holds every input's signing and nullifying keys and its owner's
//! signature on this merge, but no private key: a compromised enclave could not prove any other merge. The IVC proof
//! folded from it holds the same, and the openings of every input, so neither leaves: only the decider proof.
use alloy_primitives::{Bytes, U256};
use parking_lot::Mutex;
use sha2::{Digest, Sha256};
use std::io::{self, BufReader, Read};
use std::sync::OnceLock;
use zerc20_attester_proto::Merge;
use zerc20_attester_proto::check::{self, MergeWitness};
use zerc20_common::fields::{fr, u256};
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::ark_std::rand::thread_rng;
use zerc20_zkp::artifacts::{read_decider_prover_key_trusted, read_decider_verifier_key_trusted};
use zerc20_zkp::evm::{DECIDER_PROOF_BYTES, merge_proof_calldata};
use zerc20_zkp::ivc::{DeciderProverKey, DeciderVerifierKey, NovaDecider, fold};
use zerc20_zkp::merge::{MergeCircuit, MergeState, MergeStep};
use zerc20_zkp::primitives::nullifier_chain;
use zerc20_zkp::sonobe_ivc::IVCProofCompressor;

pub type Error = String;

pub struct Prover {
    keys: OnceLock<(DeciderProverKey<MergeState>, DeciderVerifierKey<MergeState>)>,
    /// SHA-256 of the prover and verifier keys, pinned in the image; `None` takes them as they come (development).
    pinned: Option<([u8; 32], [u8; 32])>,
    /// Development only: checks each witness and proves nothing, for a merge verifier that accepts anything.
    skip: bool,
    /// One proof at a time: each takes most of the enclave's memory.
    proving: Mutex<()>,
}

impl Prover {
    pub fn new(pinned: Option<([u8; 32], [u8; 32])>) -> Self {
        Self {
            keys: OnceLock::new(),
            pinned,
            skip: false,
            proving: Mutex::default(),
        }
    }

    /// Development only: a prover that needs no keys, checks each witness as [`Prover::prove`] does, and answers an
    /// all-zero proof, which only a merge verifier that accepts anything takes.
    pub fn skipping() -> Self {
        Self {
            skip: true,
            ..Self::new(None)
        }
    }

    pub fn has_keys(&self) -> bool {
        self.skip || self.keys.get().is_some()
    }

    /// The decider prover key, then the verifier key, `pk_len` and `vk_len` bytes from `r`, checked against the pins.
    pub fn load_keys(&self, r: &mut dyn Read, pk_len: u64, vk_len: u64) -> Result<(), Error> {
        let pins = self
            .pinned
            .map_or([None, None], |(pk, vk)| [Some(pk), Some(vk)]);
        let pk = pinned_read(r, pk_len, pins[0], |r| {
            read_decider_prover_key_trusted::<MergeState>(r)
                .map_err(|_| "the merge prover key does not parse")
        })?;
        let vk = pinned_read(r, vk_len, pins[1], |r| {
            read_decider_verifier_key_trusted::<MergeState>(r)
                .map_err(|_| "the merge verifier key does not parse")
        })?;
        let _ = self.keys.set((pk, vk));
        Ok(())
    }

    /// The `NovaDeciderProof` (ABI-encoded) of `s`, from `witness`, which must prove it: checked as the attester checks
    /// it before minutes of folding. A witness that does not prove `s` gets [`check::MISMATCH`], whatever the reason.
    pub fn prove(&self, s: &Merge, witness: &[u8]) -> Result<Bytes, Error> {
        if self.skip {
            check::merge(s, witness)?;
            return Ok(vec![0u8; DECIDER_PROOF_BYTES].into());
        }
        let (pk, vk) = self.keys.get().ok_or("no merge key loaded yet")?;
        check::merge(s, witness)?;
        let w: MergeWitness = serde_json::from_slice(witness).map_err(|_| "malformed witness")?;
        let _one = self.proving.lock();
        let mut rng = thread_rng();
        let f = fold(&pk.1, &MergeCircuit, initial_state(s), steps(&w)?, &mut rng)
            .map_err(|_| "the merge does not fold")?;
        if u256(f.zi[6]) != s.noteHash {
            return Err("the merge folds to another note".into());
        }
        let proof =
            NovaDecider::prove::<MergeCircuit>(pk, f.steps, &f.z0, &f.zi, &f.ivc_proof, &mut rng)
                .map_err(|_| "the decider failed")?;
        let calldata = merge_proof_calldata(vk, f.steps, &f.z0, &f.zi, &proof)
            .map_err(|_| "the decider proof does not encode")?;
        Ok(calldata.into())
    }
}

/// `z_0` as `Verifier.merge` builds it: an empty chain, the chain of the nullifiers spent, which the owners signed, an
/// empty note, one step per nullifier left, and the fee.
pub fn initial_state(s: &Merge) -> MergeState {
    let nullifiers: Vec<Fr> = s.nullifiers.iter().map(|n| fr(*n)).collect();
    [
        fr(s.tokenId),
        fr(s.chainId),
        fr(s.commitmentRoot),
        fr(s.aspRoot),
        Fr::from(0),
        nullifier_chain(&nullifiers),
        Fr::from(0),
        Fr::from(s.nullifiers.len() as u64),
        fr(s.fee),
        fr(s.feeRecipient),
    ]
}

/// The Nova steps of `w`, which [`check::merge`] accepted: each input with the output's opening and the sum before it.
pub fn steps(w: &MergeWitness) -> Result<Vec<MergeStep>, Error> {
    let mut sum = U256::ZERO;
    w.inputs
        .iter()
        .map(|i| {
            let step = MergeStep {
                is_burn: i.is_burn,
                auth_key: check::auth_key(&i.auth_key)?,
                nullifying_key: fr(i.nullifying_key),
                signature: check::signature(&i.signature)?,
                commitment_index: fr(i.commitment_index),
                commitment_siblings: i.commitment_siblings.map(fr),
                note_value: fr(i.note_value),
                note_salt: fr(i.note_salt),
                burn_salt: fr(i.burn_salt),
                burn_from: fr(i.burn_from),
                burn_value: fr(i.burn_value),
                asp_siblings: i.asp_siblings.map(fr),
                out_public_key: fr(w.out_public_key),
                out_salt: fr(w.out_salt),
                prev_sum: fr(sum),
            };
            sum += if i.is_burn {
                i.burn_value
            } else {
                i.note_value
            };
            Ok(step)
        })
        .collect()
}

/// Feeds `len` bytes of `r` to `parse`, then checks their SHA-256 against `pin`.
fn pinned_read<T>(
    r: &mut dyn Read,
    len: u64,
    pin: Option<[u8; 32]>,
    parse: impl FnOnce(&mut dyn Read) -> Result<T, &'static str>,
) -> Result<T, Error> {
    let mut hashing = Hashing {
        inner: r.take(len),
        hash: Sha256::new(),
    };
    let value = {
        let mut buffered = BufReader::with_capacity(1 << 20, &mut hashing);
        let value = parse(&mut buffered)?;
        // whatever the parser left, so the hash covers all of it
        io::copy(&mut buffered, &mut io::sink()).map_err(|e| e.to_string())?;
        value
    };
    if hashing.inner.limit() != 0 {
        return Err("the merge key ends early".into());
    }
    if pin.is_some_and(|pin| hashing.hash.finalize()[..] != pin) {
        return Err("the merge key is not the one pinned in this image".into());
    }
    Ok(value)
}

struct Hashing<R> {
    inner: io::Take<R>,
    hash: Sha256,
}

impl<R: Read> Read for Hashing<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.inner.read(buf)?;
        self.hash.update(&buf[..n]);
        Ok(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_r1cs_std::GR1CSVar;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::fields::FieldVar;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_relations::gr1cs::ConstraintSystem;
    use sonobe_primitives::circuits::FCircuit;
    use zerc20_attester_proto::check::tests::merge_fixture;

    #[test]
    fn steps_the_circuit_accepts_fold_to_the_statement() {
        let (s, w) = merge_fixture();
        let mut z = initial_state(&s);
        for step in steps(&w).unwrap() {
            let cs = ConstraintSystem::new_ref();
            let state: [FpVar<Fr>; 10] =
                AllocVar::<MergeState, _>::new_witness(cs.clone(), || Ok(z)).unwrap();
            let (next, ()) = MergeCircuit
                .synthesize_step(FpVar::zero(), state, step)
                .unwrap();
            assert!(cs.is_satisfied().unwrap());
            z = next.value().unwrap();
        }
        // the note is the one the attester checks, every step is spent, and the fee passes through
        assert_eq!(u256(z[6]), s.noteHash);
        assert_eq!(z[7..], [Fr::from(0), fr(s.fee), fr(s.feeRecipient)]);
        // the chain spent is the chain signed, as the contract checks
        assert_eq!(z[4], z[5]);
    }

    #[test]
    fn checks_the_witness_before_folding() {
        let prover = Prover::new(None);
        let (s, w) = merge_fixture();
        let witness = serde_json::to_vec(&w).unwrap();
        // without the merge key it proves nothing; with it, a statement the witness does not prove fails at once
        assert_eq!(
            prover.prove(&s, &witness),
            Err("no merge key loaded yet".into())
        );
        let mut other = s;
        other.fee += U256::from(1);
        assert!(check::merge(&other, &witness).is_err());
    }

    #[test]
    fn skipping_checks_the_witness_and_proves_nothing() {
        let prover = Prover::skipping();
        let (s, w) = merge_fixture();
        let witness = serde_json::to_vec(&w).unwrap();
        assert!(prover.has_keys());
        assert_eq!(
            prover.prove(&s, &witness),
            Ok(vec![0u8; DECIDER_PROOF_BYTES].into())
        );
        let mut other = s;
        other.fee += U256::from(1);
        assert!(prover.prove(&other, &witness).is_err());
    }

    #[test]
    fn checks_the_merge_key_against_its_pin() {
        let bytes = vec![1u8; 100];
        let pin: [u8; 32] = Sha256::digest(&bytes).into();
        let read = |pin: Option<[u8; 32]>, len: u64| {
            pinned_read(&mut &bytes[..], len, pin, |r| {
                let mut first = [0u8; 10];
                r.read_exact(&mut first).map_err(|_| "short")?;
                Ok(first)
            })
        };
        assert_eq!(read(Some(pin), 100).unwrap(), [1u8; 10]);
        assert!(read(Some([0u8; 32]), 100).is_err());
        assert!(read(None, 200).is_err()); // shorter than said
    }
}
