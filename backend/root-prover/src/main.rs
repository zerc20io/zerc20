//! Proves root transitions on the ledger, and puts it in an emergency once the indexer finds a forged root. With
//! GUARD_ONLY=1 it only does the latter: a second guardian, on an indexer of its own.
use alloy::primitives::{Address, U256};
use alloy::providers::DynProvider;
use alloy::sol_types::SolValue;
use anyhow::{Context, Result, ensure};
use parking_lot::Mutex;
use serde_json::Value;
use std::fs::File;
use std::io::BufReader;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tracing::{Instrument, error, info, warn};
use zerc20_common::contracts::{ILedger, NovaDeciderProof};
use zerc20_common::fields::{fr, leaf, next_hash_chain, u256};
use zerc20_common::{Chain, Indexer, Sender, each_chain};
use zerc20_zkp::ark_std::rand::thread_rng;
use zerc20_zkp::artifacts::{read_decider_prover_key_trusted, read_decider_verifier_key_trusted};
use zerc20_zkp::evm::root_proof_calldata;
use zerc20_zkp::ivc::{DeciderProverKey, DeciderVerifierKey, NovaDecider, fold};
use zerc20_zkp::root::{self, RootCircuit, RootStep};
use zerc20_zkp::sonobe_ivc::IVCProofCompressor;
use zerc20_zkp::tree::{CHUNK, CHUNK_BITS, PAGE_BITS, frontier};

const POLL: Duration = Duration::from_secs(5);

struct App {
    sender: Sender,
    /// `sender`'s, for reads.
    provider: DynProvider,
    ledger: Address,
    /// This chain's. Everything it serves is checked against the ledger before proving.
    indexer: Indexer,
    /// `None` with DEV_SKIP_PROOF=1: roots go to the ledger without a proof. Every chain's, locked while proving.
    ///
    /// ponytail: one key in memory, so chains prove one at a time. Once a round of every chain no longer fits in
    /// PROVE_SECS, run a second root-prover for some of CHAINS.
    keys: Option<Arc<Mutex<Keys>>>,
}

type Keys = (
    DeciderProverKey<root::RootState>,
    DeciderVerifierKey<root::RootState>,
);

fn open(path: &str) -> Result<BufReader<File>> {
    Ok(BufReader::new(
        File::open(path).with_context(|| format!("open {path}"))?,
    ))
}

#[tokio::main]
async fn main() -> Result<()> {
    zerc20_common::init_logging()?;
    let on = |k: &str| std::env::var(k).is_ok_and(|v| v == "1");
    if on("GUARD_ONLY") {
        return each_chain(guard_only).await;
    }
    let keys = if on("DEV_SKIP_PROOF") {
        warn!(
            "DEV_SKIP_PROOF=1: roots are sent without a proof, which only a ledger whose root verifier accepts \
             anything takes (scripts/dev-stack.sh SPEED=fast). Never where funds are real."
        );
        None
    } else {
        // Trusted: the keys were verified once, when they were put there. Skipping the subgroup checks keeps
        // loading the multi-GB prover key IO-bound.
        let dir = std::env::var("ARTIFACTS_DIR").unwrap_or("zkp/artifacts/root".into());
        let started = Instant::now();
        let pk = read_decider_prover_key_trusted(open(&format!("{dir}/root_decider_pk.bin"))?)?;
        let vk = read_decider_verifier_key_trusted(open(&format!("{dir}/root_decider_vk.bin"))?)?;
        info!("loaded the keys from {dir} in {:.0?}", started.elapsed());
        Some(Arc::new(Mutex::new((pk, vk))))
    };
    each_chain(move |c| run(c, keys.clone())).await
}

async fn app(c: &Chain, keys: Option<Arc<Mutex<Keys>>>) -> Result<Arc<App>> {
    let sender = Sender::new(&c.env("RPC_URL")?, &c.env("PRIVATE_KEY")?)?;
    let provider = sender.provider().clone();
    let ledger = c.contract(&provider, "LEDGER").await?;
    Ok(Arc::new(App {
        sender,
        provider,
        ledger,
        indexer: Indexer::new(&c.env("INDEXER_URL")?)?,
        keys,
    }))
}

async fn guarding(app: &App) -> ! {
    loop {
        if let Err(e) = guard(app).await {
            warn!("guarding the ledger failed: {e:#}");
        }
        tokio::time::sleep(POLL).await;
    }
}

async fn guard_only(c: Chain) -> Result<()> {
    let app = app(&c, None).await?;
    info!("guarding from {}", app.sender.address());
    guarding(&app).await
}

async fn run(c: Chain, keys: Option<Arc<Mutex<Keys>>>) -> Result<()> {
    let app = app(&c, keys).await?;
    info!("proving from {}", app.sender.address());
    // apart from the rounds, which spend minutes proving (and wait for other chains' proofs)
    tokio::spawn({
        let app = app.clone();
        async move { guarding(&app).await }.in_current_span()
    });
    let every = Duration::from_secs(c.env_u64("PROVE_SECS", 300));
    loop {
        if let Err(e) = round(&app).await {
            warn!("round failed: {e:#}");
        }
        tokio::time::sleep(every).await;
    }
}

/// Reserves a checkpoint at the head, waits until the indexer has every commitment below it, and proves the root up
/// to it. Nothing is kept between rounds: a failed round costs one reservation.
///
/// It does not wait for them to be final. The proof is bound to the checkpoint, so commitments a reorg replaced fail
/// the ledger checks below, or gas estimation, and cost this round only. Waiting would put finality in series with
/// every round.
///
/// ponytail: one proof covers everything since the last proved root, however much that is; add a step cap (proving to
/// an earlier checkpoint) if a long outage ever makes one round too slow.
async fn round(app: &App) -> Result<()> {
    let l = ILedger::new(app.ledger, &app.provider);
    // a reservation now would only cost gas: no root can be proved until a recovery
    if l.bound().call().await? != u64::MAX || forged(app).await?.is_some() {
        info!("the ledger has a forged root: proving nothing until it recovers");
        return Ok(());
    }
    let old = l.rootState().call().await?;
    if l.nextIndex().call().await? == old.index {
        return Ok(());
    }
    // the index comes from the event: one read before sending could be overtaken by a commit
    let receipt = app
        .sender
        .send(l.reserveHashChain().into_transaction_request())
        .await?;
    let cp = receipt
        .decoded_log::<ILedger::CheckpointRecorded>()
        .context("no CheckpointRecorded")?
        .data;
    let (end, checkpoint) = (cp.index, cp.hashChain);
    info!("reserved the hash chain at {end}; waiting for the indexer to reach it");
    loop {
        match app.indexer.commitment_counts().await {
            Ok((held, _)) if held >= end => break,
            Ok(_) => {}
            Err(e) => warn!("indexer status failed: {e:#}"),
        }
        tokio::time::sleep(POLL).await;
    }

    // what `sized` takes for the tree at `n`, plus every commitment up to `end`
    let n = old.index;
    let page_roots = app.indexer.roots("/page-roots").await?;
    let page_chunks = app
        .indexer
        .roots(&format!("/chunk-roots/{}", n >> PAGE_BITS))
        .await?;
    let (pages, chunks) = (
        (n >> PAGE_BITS) as usize,
        ((n >> CHUNK_BITS) % CHUNK) as usize,
    );
    ensure!(
        page_roots.len() >= pages && page_chunks.len() >= chunks,
        "the indexer lacks full chunk or page roots below {n}"
    );
    let lo = n >> CHUNK_BITS << CHUNK_BITS;
    let mut chain = U256::ZERO;
    let mut fields = vec![];
    for c in lo >> CHUNK_BITS..=(end - 1) >> CHUNK_BITS {
        let (before, page) = app.indexer.commitments(c).await?;
        if c << CHUNK_BITS == lo {
            chain = before;
        }
        fields.extend(page);
    }
    ensure!(
        lo + fields.len() as u64 >= end,
        "the indexer serves {} commitments, not {end}",
        lo + fields.len() as u64
    );
    fields.truncate((end - lo) as usize);
    let (before, new) = fields.split_at((n - lo) as usize);

    // The ledger's hash chain pins every commitment, and its root the chunk and page roots. A mismatch here would
    // only fail later, after the proving.
    let mid = before.iter().fold(chain, next_hash_chain);
    ensure!(
        mid == old.hashChain,
        "the indexer's commitments below {n} are not the ledger's"
    );
    ensure!(
        new.iter().fold(mid, next_hash_chain) == checkpoint,
        "the indexer's commitments {n}..{end} are not the ledger's"
    );
    let mut tree = frontier(
        n,
        &page_roots[..pages],
        &page_chunks[..chunks],
        &before.iter().map(leaf).collect::<Vec<_>>(),
    );
    ensure!(
        u256(tree.root) == old.root,
        "the ledger's root {:#066x} at {n} is not the indexer's {:#066x}: a forged root?",
        old.root,
        u256(tree.root)
    );

    let z0 = [U256::from(old.index), old.hashChain, old.root].map(fr);
    let steps = new.iter().enumerate().map(|(i, f)| {
        if i % 1000 == 0 {
            info!("folding {n}+{i} of ..{end}");
        }
        RootStep {
            fields: f.map(fr),
            siblings: tree.append(leaf(f)),
        }
    });
    let (zi, proof) = match &app.keys {
        Some(keys) => tokio::task::block_in_place(|| prove(&keys.lock(), z0, steps))?,
        None => {
            // the state the steps reach, as the circuit would fold it: the tree after the appends
            steps.for_each(drop);
            let zi = [fr(U256::from(end)), fr(checkpoint), tree.root];
            (zi, NovaDeciderProof::default())
        }
    };

    // anyone may prove, and a proof from a state that moved on reverts
    if l.rootState().call().await?.index != old.index {
        warn!("dropping the proof up to {end}: the root moved on while proving");
        return Ok(());
    }
    let state = ILedger::RootState {
        index: u64::try_from(u256(zi[0]))?,
        hashChain: u256(zi[1]),
        root: u256(zi[2]),
    };
    let receipt = app
        .sender
        .send(
            l.proveRootTransition(state.clone(), proof)
                .into_transaction_request(),
        )
        .await?;
    info!(
        "proved {:#066x} over {end} in {}",
        state.root, receipt.transaction_hash
    );
    Ok(())
}

/// As the ledger's guardian, puts it in an emergency once the indexer finds a proved root it does not derive: no
/// root above the last one it does is accepted, and none is proved. A pauser can do the same by hand.
async fn guard(app: &App) -> Result<()> {
    let Some(status) = forged(app).await? else {
        return Ok(());
    };
    let l = ILedger::new(app.ledger, &app.provider);
    let Some(to) = emergency_bound(&status, l.bound().call().await?) else {
        return Ok(());
    };
    error!(
        "the ledger proved {}, which the indexer does not derive: bounding its roots at {to}",
        status["mismatch"]
    );
    app.sender
        .send(l.enterEmergency(to).into_transaction_request())
        .await?;
    Ok(())
}

/// The indexer's `/status`, if it names a forged root the ledger still accepts. A recovery withdraws the forged root,
/// but the indexer names it until it reads the recovery, a few seconds on: acting on it then would undo the recovery.
async fn forged(app: &App) -> Result<Option<Value>> {
    let status = app.indexer.status().await?;
    let m = &status["mismatch"];
    if m.is_null() {
        return Ok(None);
    }
    let index = m["index"].as_u64().context("mismatch.index")?;
    let root: U256 = m["root"].as_str().context("mismatch.root")?.parse()?;
    let accepted = ILedger::new(app.ledger, &app.provider)
        .provedRoots(index, root)
        .call()
        .await?;
    Ok(accepted.then_some(status))
}

/// The bound for an emergency, given the indexer's `/status` with a `mismatch` and the ledger's bound now: the last
/// root before it the indexer derives (0, genesis, if none), unless the ledger already bounds at or below it.
fn emergency_bound(status: &Value, bound: u64) -> Option<u64> {
    let honest = status["latest_root"]["index"].as_u64().unwrap_or(0);
    (bound > honest).then_some(honest)
}

fn prove(
    (pk, vk): &Keys,
    z0: root::RootState,
    steps: impl Iterator<Item = RootStep>,
) -> Result<(root::RootState, NovaDeciderProof)> {
    let mut rng = thread_rng();
    let started = Instant::now();
    let f = fold(&pk.1, &RootCircuit, z0, steps, &mut rng)?;
    info!("folded {} steps in {:.0?}", f.steps, started.elapsed());
    let started = Instant::now();
    let proof =
        NovaDecider::prove::<RootCircuit>(pk, f.steps, &f.z0, &f.zi, &f.ivc_proof, &mut rng)?;
    let calldata = root_proof_calldata(vk, f.steps, &f.z0, &f.zi, &proof)?;
    info!("decided in {:.0?}", started.elapsed());
    Ok((f.zi, NovaDeciderProof::abi_decode(&calldata)?))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emergency_bounds_at_the_last_honest_root_once() {
        let status =
            serde_json::json!({ "latest_root": { "index": 70 }, "mismatch": { "index": 90 } });
        assert_eq!(emergency_bound(&status, u64::MAX), Some(70));
        assert_eq!(emergency_bound(&status, 80), Some(70));
        assert_eq!(emergency_bound(&status, 70), None, "already bounded");
        assert_eq!(emergency_bound(&status, 0), None, "never raised");
        let genesis = serde_json::json!({ "latest_root": null, "mismatch": { "index": 90 } });
        assert_eq!(emergency_bound(&genesis, u64::MAX), Some(0));
    }
}
