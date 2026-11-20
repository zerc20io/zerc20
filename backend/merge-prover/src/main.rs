//! The merge prover's host: queues proofs, keeps the enclave loaded with the merge keys, and never sees a witness. It
//! serves every chain: a statement names its own.
use alloy_primitives::{Bytes, U256};
use anyhow::{Result, anyhow, bail};
use axum::Router;
use axum::extract::{Json, Path, State};
use axum::http::{HeaderMap, StatusCode};
use axum::routing::{get, post};
use parking_lot::Mutex;
use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::HashMap;
use std::fs::File;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Notify;
use tracing::{info, warn};
use zerc20_attester_proto::Merge;
use zerc20_common::{env_u64, init_logging};
use zerc20_enclave::Target;
use zerc20_merge_prover::{Enclave, PORT, Request};

/// How long the enclave may take over a request, but for proving.
const TIMEOUT: Duration = Duration::from_secs(60);
/// Folding and deciding a merge of `MAX_INPUTS`.
const PROVE_TIMEOUT: Duration = Duration::from_secs(3600);
/// Streaming the multi-GB merge key in.
const LOAD_TIMEOUT: Duration = Duration::from_secs(3600);
const KEY_POLL: Duration = Duration::from_secs(10);
/// How long a finished job's result is kept for its wallet to fetch.
const KEEP: Duration = Duration::from_secs(24 * 3600);

type Res = Result<(StatusCode, Json<Value>), (StatusCode, String)>;

/// A request to prove, keyed by the note it outputs, with when it last moved and who sent it.
struct Entry {
    at: Instant,
    client: String,
    job: Job,
}

enum Job {
    Queued {
        statement: Box<Merge>,
        witness: Bytes,
    },
    Proving,
    Done {
        proof: Bytes,
    },
    Failed {
        error: String,
    },
}

struct App {
    enclave: Target,
    /// ponytail: in memory, so a restart loses them and wallets send theirs again
    jobs: Mutex<HashMap<U256, Entry>>,
    work: Notify,
    /// Jobs queued or proving at most; more get 503.
    queue: usize,
    /// Jobs queued or proving at most per client address, so that one cannot take the whole queue.
    per_client: usize,
    max_inputs: usize,
}

impl App {
    async fn ask(&self, request: Request, timeout: Duration) -> Result<Value> {
        self.enclave
            .ask(request, timeout)
            .await?
            .map_err(|e| anyhow!("the enclave: {e}"))
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    init_logging()?;
    let skip = std::env::var("DEV_SKIP_PROOF").is_ok_and(|v| v == "1");
    let enclave = match std::env::var("DEV_ENCLAVE").is_ok_and(|v| v == "1") {
        true => {
            warn!(
                "DEV_ENCLAVE: the enclave's logic runs in this process, which then sees every witness. Never where \
                 funds are real."
            );
            let e = Arc::new(match skip {
                true => {
                    warn!(
                        "DEV_SKIP_PROOF: merges are checked but not proved, which only a merge verifier that \
                         accepts anything takes"
                    );
                    Enclave::skipping_proofs()
                }
                false => Enclave::new(None),
            });
            Target::local(Arc::new(move |r, body| e.handle(r, body)))?
        }
        false if skip => bail!("DEV_SKIP_PROOF needs DEV_ENCLAVE=1: an enclave always proves"),
        false => Target::Vsock(env_u64("ENCLAVE_CID", 17).try_into()?, PORT),
    };
    let app = Arc::new(App {
        enclave,
        jobs: Mutex::default(),
        work: Notify::new(),
        queue: env_u64("QUEUE", 8) as usize,
        per_client: env_u64("PER_CLIENT", 2) as usize,
        max_inputs: env_u64("MAX_INPUTS", 100) as usize,
    });
    let dir = std::env::var("ARTIFACTS_DIR").unwrap_or("zkp/artifacts/merge".into());
    let keys = (
        format!("{dir}/merge_decider_pk.bin"),
        format!("{dir}/merge_decider_vk.bin"),
    );
    let listen = std::env::var("LISTEN").unwrap_or("127.0.0.1:3006".into());
    info!("serving merge proofs on {listen}");
    let router = Router::new()
        .route("/enclave", get(enclave_info))
        .route("/proofs", post(submit))
        .route("/proofs/{note_hash}", get(job))
        .route("/status", get(status))
        .with_state(app.clone())
        .layer(zerc20_common::cors());
    tokio::select! {
        r = key_loop(app.clone(), keys), if !skip => r,
        r = work(app.clone()) => r,
        r = zerc20_common::serve(&listen, router) => r,
    }
}

/// The key to seal witnesses to, and the attestation document over it (`null` in development).
async fn enclave_info(State(app): State<Arc<App>>) -> Res {
    let info = app
        .ask(Request::Attestation, TIMEOUT)
        .await
        .map_err(|e| unavailable(&e))?;
    Ok((
        StatusCode::OK,
        Json(json!({ "publicKey": info["publicKey"], "attestation": info["attestation"] })),
    ))
}

#[derive(Deserialize)]
struct Submit {
    statement: Merge,
    /// The witness, sealed to the enclave's key (`zerc20_attester_proto::seal` with `MERGE_WITNESS`).
    witness: Bytes,
}

/// Queues a proof. The same statement sent again is taken once, unless it failed.
/// ponytail: open to anyone; prove only merges that pay the operator's relayer once abuse calls for it
async fn submit(State(app): State<Arc<App>>, headers: HeaderMap, Json(b): Json<Submit>) -> Res {
    // Caddy, the only way in (this listens on loopback), sets it to the client's address, whatever the client sent
    let client = headers
        .get("x-forwarded-for")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.split(',').next_back())
        .unwrap_or("local")
        .trim()
        .to_owned();
    let n = b.statement.nullifiers.len();
    if n == 0 || n > app.max_inputs {
        return Err((
            StatusCode::BAD_REQUEST,
            format!("a merge spends 1 to {} inputs", app.max_inputs),
        ));
    }
    let key = b.statement.noteHash;
    let mut jobs = app.jobs.lock();
    jobs.retain(|_, e| !finished(&e.job) || e.at.elapsed() < KEEP);
    if let Some(e) = jobs.get(&key)
        && !matches!(e.job, Job::Failed { .. })
    {
        return Ok((StatusCode::ACCEPTED, Json(view(&e.job))));
    }
    let busy = || jobs.values().filter(|e| !finished(&e.job));
    if busy().count() >= app.queue {
        return Err((
            StatusCode::SERVICE_UNAVAILABLE,
            "the prover is busy: try again later".into(),
        ));
    }
    if busy().filter(|e| e.client == client).count() >= app.per_client {
        return Err((
            StatusCode::TOO_MANY_REQUESTS,
            "this client's merges are still being proved: try again once one is done".into(),
        ));
    }
    let job = Job::Queued {
        statement: Box::new(b.statement),
        witness: b.witness,
    };
    let reply = view(&job);
    let at = Instant::now();
    jobs.insert(key, Entry { at, client, job });
    app.work.notify_one();
    Ok((StatusCode::ACCEPTED, Json(reply)))
}

/// Where the proof of the merge that outputs `note_hash` stands.
async fn job(State(app): State<Arc<App>>, Path(note_hash): Path<U256>) -> Res {
    match app.jobs.lock().get(&note_hash) {
        Some(e) => Ok((StatusCode::OK, Json(view(&e.job)))),
        None => Err((StatusCode::NOT_FOUND, "no such proof: send it".into())),
    }
}

async fn status(State(app): State<Arc<App>>) -> Res {
    let merge_key = match app.ask(Request::Attestation, TIMEOUT).await {
        Ok(info) => info["mergeKey"] == true,
        Err(_) => false,
    };
    let jobs = app.jobs.lock();
    let count = |f: fn(&Job) -> bool| jobs.values().filter(|e| f(&e.job)).count();
    Ok((
        StatusCode::OK,
        Json(json!({
            "mergeKey": merge_key,
            "queued": count(|j| matches!(j, Job::Queued { .. })),
            "proving": count(|j| matches!(j, Job::Proving)),
        })),
    ))
}

fn finished(job: &Job) -> bool {
    matches!(job, Job::Done { .. } | Job::Failed { .. })
}

fn view(job: &Job) -> Value {
    match job {
        Job::Queued { .. } => json!({ "status": "queued" }),
        Job::Proving => json!({ "status": "proving" }),
        Job::Done { proof } => json!({ "status": "done", "proof": proof }),
        Job::Failed { error } => json!({ "status": "failed", "error": error }),
    }
}

fn unavailable(e: &anyhow::Error) -> (StatusCode, String) {
    warn!("{e:#}");
    (
        StatusCode::SERVICE_UNAVAILABLE,
        "the enclave is unavailable".into(),
    )
}

/// Proves queued jobs one at a time, oldest first: each takes most of the enclave's memory. Jobs wait while the enclave
/// lacks the merge keys (loading them at start, or after it restarts), rather than fail for it.
/// ponytail: one enclave proving; more instances behind a load balancer if the queue stays full
async fn work(app: Arc<App>) -> Result<()> {
    loop {
        let ready = matches!(app.ask(Request::Attestation, TIMEOUT).await, Ok(info) if info["mergeKey"] == true);
        if !ready {
            tokio::time::sleep(KEY_POLL).await;
            continue;
        }
        let next = {
            let mut jobs = app.jobs.lock();
            let oldest = jobs
                .iter()
                .filter(|(_, e)| matches!(e.job, Job::Queued { .. }))
                .min_by_key(|(_, e)| e.at)
                .map(|(k, _)| *k);
            oldest.and_then(|k| {
                let e = jobs.get_mut(&k)?;
                match std::mem::replace(&mut e.job, Job::Proving) {
                    Job::Queued { statement, witness } => Some((k, statement, witness)),
                    _ => None,
                }
            })
        };
        let Some((key, statement, sealed)) = next else {
            app.work.notified().await;
            continue;
        };
        info!(
            "proving a merge of {} inputs on chain {}",
            statement.nullifiers.len(),
            statement.chainId
        );
        let reply = app
            .enclave
            .ask(Request::Prove { statement, sealed }, PROVE_TIMEOUT)
            .await;
        let job = match reply {
            Ok(Ok(proof)) => match serde_json::from_value(proof) {
                Ok(proof) => Job::Done { proof },
                Err(e) => Job::Failed {
                    error: format!("the enclave answered no proof: {e}"),
                },
            },
            // the witness or the statement is the wallet's to fix
            Ok(Err(error)) => Job::Failed { error },
            Err(e) => Job::Failed {
                error: unavailable(&e).1,
            },
        };
        if let Job::Failed { error } = &job {
            info!("a merge failed: {error}");
        }
        if let Some(e) = app.jobs.lock().get_mut(&key) {
            (e.at, e.job) = (Instant::now(), job);
        }
    }
}

/// Streams the merge keys into the enclave whenever it lacks them, as after it restarts.
async fn key_loop(app: Arc<App>, (pk, vk): (String, String)) -> Result<()> {
    if !std::path::Path::new(&pk).exists() || !std::path::Path::new(&vk).exists() {
        bail!("no merge keys at {pk} and {vk}: set ARTIFACTS_DIR");
    }
    loop {
        if let Err(e) = load(&app, &pk, &vk).await {
            warn!("loading the merge keys into the enclave failed: {e:#}");
        }
        tokio::time::sleep(KEY_POLL).await;
    }
}

async fn load(app: &App, pk: &str, vk: &str) -> Result<()> {
    if app.ask(Request::Attestation, TIMEOUT).await?["mergeKey"] == true {
        return Ok(());
    }
    let (pk_file, vk_file) = (File::open(pk)?, File::open(vk)?);
    let request = Request::LoadMergeKey {
        pk_len: pk_file.metadata()?.len(),
        vk_len: vk_file.metadata()?.len(),
    };
    info!("streaming the merge keys from {pk} into the enclave");
    let body = std::io::Read::chain(pk_file, vk_file);
    app.enclave
        .ask_with(request, body, LOAD_TIMEOUT)
        .await?
        .map_err(|e| anyhow!("the enclave: {e}"))?;
    info!("the enclave holds the merge keys");
    Ok(())
}
