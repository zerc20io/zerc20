//! Generates the Nova artifacts of one step circuit (`root` or `merge`):
//!
//! - `<name>_ivc_key.bin`: the CycleFold IVC key (prover key == verifier key)
//! - `<name>_decider_pk.bin` / `<name>_decider_vk.bin`: LegoGroth16 decider keys
//! - `<Name>DeciderVerifier.sol` / `LegoGroth16Verifier.sol`: EVM verifiers
//!
//! `zkp/scripts/artifacts.mjs` runs this, renames and places the contracts,
//! and hashes the keys.
//!
//! The randomized LegoGroth16 setup is for development and integration only.
//!
//! Usage: `params_gen <root|merge> [OUT_DIR]` (default `zkp/artifacts/<name>`).

use std::{error::Error, path::Path, time::Instant};

use ark_bn254::Fr;
use ark_serialize::CanonicalSerialize;
use sonobe_fs::DeciderKey;
use sonobe_ivc::{IVCProofCompressor, compilers::cyclefold::evm_verifier::FCircuitEVMExt};
use sonobe_primitives::arithmetizations::Arith;
use zerc20_zkp::{
    artifacts::write_nova_artifacts,
    ivc::{NovaDecider, deterministic_ivc_key},
    merge::MergeCircuit,
    root::RootCircuit,
};

fn generate<FC: FCircuitEVMExt<Field = Fr>>(
    circuit: &FC,
    name: &str,
    title: &str,
    out_dir: &Path,
) -> Result<(), Box<dyn Error>>
where
    FC::State: CanonicalSerialize,
{
    let started = Instant::now();
    let ivc_key = deterministic_ivc_key(circuit, name)?;
    println!(
        "IVC keys: {:.1?} (primary {} constraints, secondary {} constraints)",
        started.elapsed(),
        ivc_key.0.to_arith_config().n_constraints,
        ivc_key.1.to_arith_config().n_constraints,
    );

    let started = Instant::now();
    let (decider_pk, decider_vk) =
        NovaDecider::preprocess_and_generate_keys(circuit, ivc_key, ark_std::rand::thread_rng())?;
    println!(
        "Decider keys: {:.1?} ({} constraints)",
        started.elapsed(),
        decider_pk.0.r1cs.config().n_constraints,
    );

    write_nova_artifacts::<FC>(out_dir, name, title, &decider_pk, &decider_vk)?;
    println!("Artifacts written to {}", out_dir.display());
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args().skip(1);
    let name = args.next().unwrap_or_default();
    let out_dir = args
        .next()
        .unwrap_or_else(|| format!("zkp/artifacts/{name}"));
    let out_dir = Path::new(&out_dir);
    match name.as_str() {
        "root" => generate(&RootCircuit, "root", "Root", out_dir),
        "merge" => generate(&MergeCircuit, "merge", "Merge", out_dir),
        _ => Err("usage: params_gen <root|merge> [OUT_DIR]".into()),
    }
}
