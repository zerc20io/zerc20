//! The merge prover: a host and an AWS Nitro Enclave on one instance. A wallet seals a merge's witness to the enclave,
//! which folds it with Nova and proves the fold with the decider. The witness holds the inputs' openings and their
//! owners' signatures on the merge, and so does the IVC proof folded from it, so neither leaves: only the decider proof
//! does. The host queues requests and never sees a witness.
pub mod prove;

use alloy_primitives::Bytes;
use prove::Prover;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::io::Read;
use zerc20_attester_proto::{MERGE_WITNESS, Merge, WitnessKey};
use zerc20_enclave::Reply;

/// The enclave's vsock port.
pub const PORT: u32 = 5006;

/// One request from the host to the enclave.
#[derive(Serialize, Deserialize)]
pub enum Request {
    /// The key witnesses are sealed to, whether the merge key is loaded, and (Nitro only) an attestation document over
    /// the key.
    Attestation,
    /// The merge decider's prover key and then its verifier key follow, `pk_len` and `vk_len` bytes.
    LoadMergeKey { pk_len: u64, vk_len: u64 },
    /// The decider proof of `statement` (`NovaDeciderProof`, ABI-encoded), from its witness sealed to the enclave's key.
    Prove {
        statement: Box<Merge>,
        sealed: Bytes,
    },
}

/// The enclave's state: a key to open witnesses with, made at start and never kept, and the merge keys.
pub struct Enclave {
    key: WitnessKey,
    prover: Prover,
}

impl Enclave {
    pub fn new(merge_key_sha256: Option<([u8; 32], [u8; 32])>) -> Self {
        Self {
            key: WitnessKey::default(),
            prover: Prover::new(merge_key_sha256),
        }
    }

    /// Development only, for a host running the enclave's logic itself (`DEV_ENCLAVE` with `DEV_SKIP_PROOF`): checks
    /// each witness and proves nothing ([`Prover::skipping`]). The enclave binary never builds one.
    pub fn skipping_proofs() -> Self {
        Self {
            key: WitnessKey::default(),
            prover: Prover::skipping(),
        }
    }

    pub fn public_key(&self) -> &[u8] {
        self.key.public_key()
    }

    pub fn info(&self) -> Value {
        json!({
            "publicKey": self.key.public_key(),
            "attestation": null,
            "mergeKey": self.prover.has_keys(),
        })
    }

    /// Answers the host. `body` holds what follows a request that carries one.
    pub fn handle(&self, request: Request, body: &mut dyn Read) -> Reply {
        match request {
            Request::Attestation => Ok(self.info()),
            Request::LoadMergeKey { pk_len, vk_len } => {
                self.prover.load_keys(body, pk_len, vk_len)?;
                Ok(json!(true))
            }
            Request::Prove { statement, sealed } => {
                let witness = self.open(&sealed)?;
                Ok(json!(self.prover.prove(&statement, &witness)?))
            }
        }
    }

    /// Opens what a wallet sealed to this enclave's key, the way it seals witnesses to the attester's.
    fn open(&self, sealed: &[u8]) -> Result<Vec<u8>, String> {
        self.key
            .open(MERGE_WITNESS, sealed)
            .ok_or_else(|| "the witness does not open: fetch /enclave again".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use zerc20_attester_proto::{WITNESS, seal};
    use zerc20_enclave::{call, serve};

    #[test]
    fn opens_only_what_is_sealed_to_it_as_a_merge_witness() {
        let enclave = Arc::new(Enclave::new(None));
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let e = enclave.clone();
        std::thread::spawn(move || {
            serve(
                listener.incoming(),
                Arc::new(move |r, body| e.handle(r, body)),
            )
        });
        let ask = |r: &Request| call(std::net::TcpStream::connect(addr).unwrap(), r, None).unwrap();

        let info = ask(&Request::Attestation).unwrap();
        assert_eq!(info["mergeKey"], json!(false));
        let prove = |info: &[u8]| Request::Prove {
            statement: Box::default(),
            sealed: seal(info, enclave.public_key(), b"{}").unwrap(),
        };
        // sealed for the attester: does not open here
        assert!(ask(&prove(WITNESS)).unwrap_err().contains("does not open"));
        // opens, but there is nothing to prove with yet
        assert_eq!(
            ask(&prove(MERGE_WITNESS)),
            Err("no merge key loaded yet".into())
        );
    }
}
