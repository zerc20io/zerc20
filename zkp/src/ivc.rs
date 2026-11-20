//! Sonobe IVC and decider wiring shared by the step circuits
//! ([`RootCircuit`](crate::root::RootCircuit),
//! [`MergeCircuit`](crate::merge::MergeCircuit)): the key types, key
//! generation, and folding steps into an IVC proof.
//!
//! The primary folding scheme is Nova over BN254 with Pedersen commitments,
//! the secondary (CycleFold) scheme is Nova over Grumpkin, and the decider
//! compresses the IVC proof into a LegoGroth16 proof over BN254 so it can be
//! verified on the EVM.
//!
//! The Fiat-Shamir transcript and the hash of the IVC state are one sponge:
//! circomlib's Poseidon(4) ([`POSEIDON4`]). Poseidon is the most analysed
//! arithmetization-oriented hash, and no known attack reaches its full rounds,
//! while Gröbner basis attacks reach most of Griffin's. These constants are the
//! ones [`crate::poseidon`] already checks against circomlib.
//!
//! The key types depend on a circuit only through its state, so they are
//! parameterized by the state type `S` and stay inferable at call sites.

use ark_bn254::{Bn254, Fr, G1Projective as G1};
use ark_crypto_primitives::sponge::poseidon::{PoseidonConfig, PoseidonSponge};
use ark_grumpkin::Projective as G2;
use ark_std::rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use sha2::{Digest, Sha256};
use sonobe_fs::{
    DeciderKey, FoldingSchemeDef,
    nova::{CycleFoldNova, Nova},
};
use sonobe_ivc::{
    IVCKeyGenerator, IVCPreprocessor, IVCStatefulProver, IVCVerifier,
    compilers::cyclefold::{CycleFoldBasedIVCDecider, Key, Proof, adapters::nova::NovaNovaIVC},
};
use sonobe_primitives::{circuits::FCircuit, commitments::pedersen::Pedersen};
use sonobe_snarks::cp::legogroth16::{self as lego, LegoGroth16};

use crate::poseidon::POSEIDON4;

type CM1 = Pedersen<G1, true>;
type CM2 = Pedersen<G2, true>;
type Transcript = PoseidonSponge<Fr>;
type TranscriptConfig = PoseidonConfig<Fr>;
type SecondaryNova = CycleFoldNova<CM2>;
type PrimaryDeciderKey = <PrimaryNova as FoldingSchemeDef>::DeciderKey;

pub type PrimaryNova = Nova<CM1>;
pub type NovaIvc = NovaNovaIVC<CM1, CM2, Transcript>;
/// The decider over the commit-and-prove SNARK `S`; the setup ceremony runs it
/// with an `S` that only captures the relation.
pub type Decider<S> = CycleFoldBasedIVCDecider<PrimaryNova, SecondaryNova, Transcript, S>;
pub type NovaDecider = Decider<LegoGroth16<Bn254>>;

/// The CycleFold IVC key; its prover and verifier key are the same value.
pub type IvcKey<S> = Key<
    PrimaryDeciderKey,
    <SecondaryNova as FoldingSchemeDef>::DeciderKey,
    (TranscriptConfig, Fr, S),
>;
/// Holds the full step witnesses, including any secret; never publish it.
pub type IvcProof = Proof<PrimaryNova, SecondaryNova>;
pub type DeciderProverKey<S> = (lego::ProverKey<Bn254>, IvcKey<S>);
pub type DeciderVerifierKey<S> = (
    lego::VerifierKey<Bn254>,
    <PrimaryDeciderKey as DeciderKey>::VerifierKey,
    TranscriptConfig,
    Fr,
    S,
);
pub type DeciderProof = (
    lego::Proof<Bn254>,
    <PrimaryNova as FoldingSchemeDef>::RU,
    <PrimaryNova as FoldingSchemeDef>::IU,
    <PrimaryNova as FoldingSchemeDef>::Proof<1, 1>,
    Vec<Fr>,
);

/// Initial Pedersen key lengths for the primary and secondary curves.
const INITIAL_CK_LENS: (usize, usize) = (1 << 18, 1 << 11);
const MAX_CK_LEN: usize = 1 << 26;

/// Generates the IVC key, doubling the Pedersen key lengths until they cover
/// the augmented circuits.
pub fn generate_ivc_key<FC: FCircuit<Field = Fr>>(
    circuit: &FC,
    mut rng: impl RngCore,
) -> Result<IvcKey<FC::State>, sonobe_ivc::Error> {
    let (mut ck1_len, mut ck2_len) = INITIAL_CK_LENS;
    loop {
        let pp = NovaIvc::preprocess((ck1_len, ck2_len, POSEIDON4.config.clone()), &mut rng)?;
        match NovaIvc::generate_keys(pp, circuit) {
            // Sonobe does not say which curve's key was too short, so grow both;
            // the secondary key is small enough that overshooting is cheap.
            Err(sonobe_ivc::Error::FoldingError(err))
                if ck1_len < MAX_CK_LEN
                    && err.to_string().contains("commitment key is too short") =>
            {
                ck1_len *= 2;
                ck2_len *= 2;
            }
            result => return result.map(|(key, _)| key),
        }
    }
}

/// The IVC key of `circuit` from a ChaCha20 stream seeded with
/// `sha256("zerc20/nova/<name>/v1")`. Its Pedersen generators then come from
/// a public seed, so no one knows a discrete-log relation between them, and
/// anyone can regenerate the key to check it.
pub fn deterministic_ivc_key<FC: FCircuit<Field = Fr>>(
    circuit: &FC,
    name: &str,
) -> Result<IvcKey<FC::State>, sonobe_ivc::Error> {
    let seed = Sha256::digest(format!("zerc20/nova/{name}/v1"));
    generate_ivc_key(circuit, ChaCha20Rng::from_seed(seed.into()))
}

pub struct Folded<S> {
    pub ivc_proof: IvcProof,
    pub z0: S,
    pub zi: S,
    pub steps: usize,
}

/// Folds every step from `z0` and verifies the resulting IVC proof.
pub fn fold<FC: FCircuit<Field = Fr>>(
    key: &IvcKey<FC::State>,
    circuit: &FC,
    z0: FC::State,
    steps: impl IntoIterator<Item = FC::ExternalInputs>,
    mut rng: impl RngCore,
) -> Result<Folded<FC::State>, sonobe_ivc::Error> {
    let mut prover = IVCStatefulProver::<_, NovaIvc>::new(key, circuit, z0.clone())?;
    for step in steps {
        prover.prove_step(step, &mut rng)?;
    }
    NovaIvc::verify::<FC>(
        key,
        prover.i,
        &z0,
        &prover.current_state,
        &prover.current_proof,
    )?;
    Ok(Folded {
        ivc_proof: prover.current_proof,
        z0,
        zi: prover.current_state,
        steps: prover.i,
    })
}
