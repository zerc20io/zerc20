//! The merge prover's Nitro Enclave: answers its host over vsock. It has no development path: a development host runs
//! the same logic in its own process, so nothing the host sends can switch a real enclave into it.
use alloy_primitives::hex;
use anyhow::{Context, Result};
use serde_json::json;
use std::sync::Arc;
use zerc20_enclave::nitro::{Nsm, listen};
use zerc20_merge_prover::{Enclave, PORT, Request};

// Pinned when the image is built, so PCR0 measures them: the hashes of the merge decider keys it accepts, from
// `zkp/artifacts/merge/setup.json`.
const MERGE_PK_SHA256: Option<&str> = option_env!("MERGE_PK_SHA256");
const MERGE_VK_SHA256: Option<&str> = option_env!("MERGE_VK_SHA256");

fn main() -> Result<()> {
    let enclave = Arc::new(pinned()?);
    let nsm = Nsm::open()?;
    listen(
        PORT,
        Arc::new(move |request, body| match request {
            Request::Attestation => {
                let mut info = enclave.info();
                info["attestation"] = json!(nsm.attest(enclave.public_key())?);
                Ok(info)
            }
            other => enclave.handle(other, body),
        }),
    )?;
    Ok(())
}

fn pinned() -> Result<Enclave> {
    let missing = "built without MERGE_PK_SHA256 and MERGE_VK_SHA256 (see Dockerfile)";
    let sha = |v: Option<&str>| -> Result<[u8; 32]> {
        hex::decode(v.context(missing)?)?
            .try_into()
            .map_err(|_| anyhow::anyhow!("a merge key hash is not 32 bytes"))
    };
    Ok(Enclave::new(Some((
        sha(MERGE_PK_SHA256)?,
        sha(MERGE_VK_SHA256)?,
    ))))
}
