//! End-to-end Nova pipelines: key generation, folding, decider proof, and
//! verification both natively and through the rendered Solidity verifiers.
//!
//! Ignored by default since they take minutes:
//! `SOLC=/path/to/solc cargo test -p zerc20-zkp --release --test nova_ivc -- --ignored --nocapture`
//!
//! With `ZKP_ARTIFACTS` naming a directory such as `zkp/artifacts`, they prove with the keys in its
//! `<circuit>/` instead of fresh ones, which checks a setup's keys end to end before they ship.

use std::{error::Error, fs::File, io::BufReader, path::Path, time::Instant};

use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
use askama::Template;
use sonobe_ivc::{
    IVCProofCompressor, IVCProofCompressorEVMExt,
    compilers::cyclefold::evm_verifier::{
        CycleFoldBasedIVCDeciderVerifierTemplate, FCircuitEVMExt,
    },
};
use sonobe_primitives::utils::evm::{compiler::SolidityCompiler, harness::TestEVM};
use sonobe_snarks::cp::legogroth16::evm_verifier::LegoGroth16VerifierTemplate;
use zerc20_zkp::{
    artifacts, auth,
    commitments::{self, commitment_leaf},
    evm::{merge_proof_calldata, root_proof_calldata},
    ivc::{DeciderProof, DeciderVerifierKey, NovaDecider, PrimaryNova, fold, generate_ivc_key},
    merge::{MergeCircuit, MergeStep},
    primitives::{self, hash_chain},
    root::{RootCircuit, RootStep},
    tree::{IncrementalTree, merkle_path},
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

/// Rebuilds the verifier calldata for `zi` the way the on-chain caller does.
type Calldata<S> = fn(&DeciderVerifierKey<S>, usize, &S, &S, &DeciderProof) -> Result<Vec<u8>>;

fn words(values: &[Fr]) -> Vec<u8> {
    values
        .iter()
        .flat_map(|value| value.into_bigint().to_bytes_be())
        .collect()
}

/// Runs the whole pipeline for `steps` from `z0`, checks the folded state is
/// `expected_zi`, and that both verifiers accept it and reject a tampered one.
fn run_pipeline<FC, const N: usize>(
    circuit: &FC,
    name: &str,
    z0: [Fr; N],
    steps: Vec<FC::ExternalInputs>,
    expected_zi: [Fr; N],
    calldata: Calldata<[Fr; N]>,
) -> Result<()>
where
    FC: FCircuitEVMExt<Field = Fr, State = [Fr; N]>,
{
    let mut rng = ark_std::rand::thread_rng();

    let started = Instant::now();
    let given = match std::env::var("ZKP_ARTIFACTS") {
        Ok(dir) => {
            let dir = Path::new(&dir).join(name);
            let open = |file: &str| File::open(dir.join(file)).map(BufReader::new);
            let pk = artifacts::read_decider_prover_key(open(&format!("{name}_decider_pk.bin"))?)?;
            let vk =
                artifacts::read_decider_verifier_key(open(&format!("{name}_decider_vk.bin"))?)?;
            Some((pk, vk))
        }
        Err(_) => None,
    };
    let mut buffer = Vec::new();
    let ivc_key = match &given {
        Some((pk, _)) => pk.1.clone(),
        None => {
            let ivc_key = generate_ivc_key(circuit, &mut rng)?;
            artifacts::write_ivc_key(&mut buffer, &ivc_key)?;
            artifacts::read_ivc_key(&buffer[..])?
        }
    };
    println!("ivc keys: {:.1?}", started.elapsed());

    let started = Instant::now();
    let count = steps.len();
    let folded = fold(&ivc_key, circuit, z0, steps, &mut rng)?;
    println!("folding {count} steps: {:.1?}", started.elapsed());
    assert_eq!(folded.zi, expected_zi);

    let started = Instant::now();
    let (decider_pk, decider_vk) = match given {
        Some(keys) => keys,
        None => {
            let (pk, vk) = NovaDecider::preprocess_and_generate_keys(circuit, ivc_key, &mut rng)?;
            buffer.clear();
            artifacts::write_decider_prover_key(&mut buffer, &pk)?;
            let pk = artifacts::read_decider_prover_key(&buffer[..])?;
            buffer.clear();
            artifacts::write_decider_verifier_key(&mut buffer, &vk)?;
            (pk, artifacts::read_decider_verifier_key(&buffer[..])?)
        }
    };
    println!("decider keys: {:.1?}", started.elapsed());

    let started = Instant::now();
    let proof = NovaDecider::prove::<FC>(
        &decider_pk,
        folded.steps,
        &folded.z0,
        &folded.zi,
        &folded.ivc_proof,
        &mut rng,
    )?;
    println!("decider prove: {:.1?}", started.elapsed());

    let mut wrong_zi = folded.zi;
    wrong_zi[0] += Fr::from(1u64);
    NovaDecider::verify::<FC>(&decider_vk, folded.steps, &folded.z0, &folded.zi, &proof)?;
    assert!(
        NovaDecider::verify::<FC>(&decider_vk, folded.steps, &folded.z0, &wrong_zi, &proof)
            .is_err()
    );
    // The caller's reassembly must reproduce sonobe's own calldata.
    assert_eq!(
        calldata(&decider_vk, folded.steps, &folded.z0, &folded.zi, &proof)?,
        NovaDecider::verify_calldata::<FC>(
            &decider_vk,
            folded.steps,
            &folded.z0,
            &folded.zi,
            &proof
        )?
    );

    let solc = SolidityCompiler::new(std::env::var("SOLC").unwrap_or_else(|_| "solc".into()));
    assert!(solc.available(), "set SOLC to a solc >= 0.8.35 binary");
    let (bytecode, selectors) = solc.compile(
        vec![
            (
                "DeciderVerifier.sol",
                CycleFoldBasedIVCDeciderVerifierTemplate::<PrimaryNova, FC>::new(
                    &decider_vk.0,
                    &decider_vk.4,
                )
                .render()?,
            ),
            (
                "LegoGroth16Verifier.sol",
                LegoGroth16VerifierTemplate { vk: &decider_vk.0 }.render()?,
            ),
        ],
        "DeciderVerifier",
    )?;
    let mut evm = TestEVM::default();
    let verifier = evm
        .deploy(&bytecode, ())?
        .ok_or("verifier deployment returned no address")?;
    let selector = selectors["verifyDeciderProof"];
    let mut evm_accepts = |zi| -> Result<bool> {
        let calldata = calldata(&decider_vk, folded.steps, &folded.z0, zi, &proof)?;
        Ok(evm.view(verifier, selector, &calldata)?.is_success())
    };
    assert!(evm_accepts(&folded.zi)?);
    assert!(!evm_accepts(&wrong_zi)?);
    Ok(())
}

#[test]
#[ignore = "takes minutes; run with --ignored"]
fn nova_root_pipeline_end_to_end() -> Result<()> {
    let mut tree = IncrementalTree::default();
    let z0 = [Fr::from(0u64), Fr::from(0u64), tree.root];
    let steps: Vec<RootStep> = (0..2u64)
        .map(|step| {
            let fields = std::array::from_fn(|i| Fr::from(step * 4 + i as u64 + 1));
            let siblings = tree.append(commitment_leaf(&fields));
            RootStep { fields, siblings }
        })
        .collect();
    let expected_hash_chain = steps
        .iter()
        .fold(z0[1], |chain, step| hash_chain(chain, &step.fields));

    run_pipeline(
        &RootCircuit,
        "root",
        z0,
        steps,
        [Fr::from(2u64), expected_hash_chain, tree.root],
        // `CommitmentLedger.proveRootTransition` passes `i = newIndex - oldIndex`, its
        // root state as `z_0`, the claimed state as `z_i`, and the `NovaDeciderProof`.
        // The EVM accepting the honest `z_i` pins `i` to the folded step count.
        |vk, steps, z0, zi, proof| {
            Ok([
                words(&[zi[0] - z0[0]]),
                words(z0),
                words(zi),
                root_proof_calldata(vk, steps, z0, zi, proof)?,
            ]
            .concat())
        },
    )
}

#[test]
#[ignore = "takes minutes; run with --ignored"]
fn nova_merge_pipeline_end_to_end() -> Result<()> {
    let fr = |value: u64| Fr::from(value);
    let (chain, token, keys) = (fr(1), fr(7), primitives::Keys::of(fr(42)));
    let (out_public_key, out_salt) = (primitives::Keys::of(fr(7)).public_key, fr(99));
    let from = fr(0x1111);
    let pk = keys.public_key;
    let burn_address = primitives::burn_address(chain, pk, fr(2279)).ok_or("salt misses PoW")?;

    let leaves = [
        commitments::note_leaf(
            token,
            primitives::note_hash(chain, pk, fr(30), token, fr(5)),
        ),
        commitments::transfer_leaf(token, from, burn_address, fr(45)),
    ];
    let (root, note_path) = merkle_path(&leaves, 0);
    let (_, burn_path) = merkle_path(&leaves, 1);
    // The ASP approved the burn deposit at its own position, 1.
    let (asp_root, asp_path) = merkle_path(&[fr(0), commitments::asp_leaf(fr(1))], 1);
    let nullifiers =
        [fr(0), fr(1)].map(|index| primitives::nullifier(chain, index, keys.nullifying_key));
    let nullifier_chain = primitives::nullifier_chain(&nullifiers);
    // Two inputs, paying a fee of 5 to a relayer out of the 75 merged.
    let (fee, relayer) = (fr(5), fr(0xbeef));
    let message = auth::merge_message(nullifier_chain, out_public_key, out_salt, fee, relayer);
    let out = MergeStep {
        auth_key: keys.auth_key,
        nullifying_key: keys.nullifying_key,
        signature: auth::sign(keys.auth_secret, message),
        out_public_key,
        out_salt,
        ..Default::default()
    };
    let steps = vec![
        MergeStep {
            commitment_index: fr(0),
            commitment_siblings: note_path,
            note_value: fr(30),
            note_salt: fr(5),
            ..out.clone()
        },
        MergeStep {
            is_burn: true,
            commitment_index: fr(1),
            commitment_siblings: burn_path,
            burn_salt: fr(2279),
            burn_from: from,
            burn_value: fr(45),
            asp_siblings: asp_path,
            prev_sum: fr(30),
            ..out
        },
    ];

    let z0 = [
        token,
        chain,
        root,
        asp_root,
        fr(0),
        nullifier_chain,
        fr(0),
        fr(2),
        fee,
        relayer,
    ];
    let merged = primitives::note_hash(chain, out_public_key, fr(70), token, out_salt);

    run_pipeline(
        &MergeCircuit,
        "merge",
        z0,
        steps,
        [
            token,
            chain,
            root,
            asp_root,
            nullifier_chain,
            nullifier_chain,
            merged,
            fr(0),
            fee,
            relayer,
        ],
        // `Verifier.merge` passes `i = nullifiers.length`, its own `z_0` / `z_i`,
        // and the request's `NovaDeciderProof`.
        |vk, steps, z0, zi, proof| {
            let i = Fr::from(steps as u64);
            Ok([
                words(&[i]),
                words(z0),
                words(zi),
                merge_proof_calldata(vk, steps, z0, zi, proof)?,
            ]
            .concat())
        },
    )
}
