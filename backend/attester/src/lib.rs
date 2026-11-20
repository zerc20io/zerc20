//! What the attester's host and its Nitro Enclave share: the enclave's logic and the protocol between them. The
//! statements, sealing and checks are in `proto`, which wallets share too.
pub use zerc20_attester_proto::{Merge, Transact, WITNESS, check, seal};

use alloy::primitives::{Address, Bytes, U256};
use alloy::signers::SignerSync;
use alloy::signers::local::PrivateKeySigner;
use alloy::sol_types::{Eip712Domain, SolStruct};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::sync::OnceLock;
use zerc20_attester_proto::WitnessKey;
use zerc20_enclave::Reply;

/// The enclave's vsock port.
pub const PORT: u32 = 5005;
/// One request from the host to the enclave.
#[derive(Serialize, Deserialize)]
pub enum Request {
    /// The key witnesses are sealed to, the attester's address once loaded, and (Nitro only) an attestation document
    /// over the key.
    Attestation,
    Transact {
        verifier: Address,
        statement: Transact,
        witness: Bytes,
    },
    Merge {
        verifier: Address,
        statement: Merge,
        witness: Bytes,
    },
    /// Nitro only: an attestation document over the enclave's RSA key, base64, for KMS's `Recipient`.
    KmsAttestation,
    /// Nitro only: KMS's `CiphertextForRecipient`, base64: the signing key encrypted to that RSA key.
    LoadKey { cms: String },
}

/// The enclave's reply until the host has loaded its signing key.
pub const NO_KEY: &str = "no signing key loaded yet";

/// The enclave's state. Both keys live only in its memory.
#[derive(Default)]
pub struct Enclave {
    key: WitnessKey,
    signer: OnceLock<PrivateKeySigner>,
}

impl Enclave {
    pub fn public_key(&self) -> &[u8] {
        self.key.public_key()
    }

    /// The first key loaded is kept for the enclave's life.
    pub fn load(&self, signer: PrivateKeySigner) -> Reply {
        Ok(json!(self.signer.get_or_init(|| signer).address()))
    }

    pub fn info(&self) -> Value {
        json!({
            "publicKey": self.key.public_key(),
            "address": self.signer.get().map(|s| s.address()),
            "attestation": null,
        })
    }

    /// Signs a statement once its witness checks out. The host checked the statement's public side before asking.
    pub fn handle(&self, request: Request) -> Reply {
        match request {
            Request::Attestation => Ok(self.info()),
            Request::Transact {
                verifier,
                statement,
                witness,
            } => {
                let signer = self.signer()?;
                check::transact(&statement, &self.open(&witness)?)?;
                sign(signer, verifier, statement.chainId, &statement)
            }
            Request::Merge {
                verifier,
                statement,
                witness,
            } => {
                let signer = self.signer()?;
                check::merge(&statement, &self.open(&witness)?)?;
                sign(signer, verifier, statement.chainId, &statement)
            }
            Request::KmsAttestation | Request::LoadKey { .. } => Err("not a Nitro Enclave".into()),
        }
    }

    fn signer(&self) -> Result<&PrivateKeySigner, String> {
        self.signer.get().ok_or(NO_KEY.into())
    }

    fn open(&self, sealed: &[u8]) -> Result<Vec<u8>, String> {
        self.key
            .open(WITNESS, sealed)
            .ok_or_else(|| "the witness does not open: fetch /attestation again".into())
    }
}

/// The attestation `Verifier` recovers: r, s, v (27 or 28) over the EIP-712 hash in its domain.
pub fn sign<T: SolStruct>(
    signer: &PrivateKeySigner,
    verifier: Address,
    chain_id: U256,
    statement: &T,
) -> Reply {
    let domain = Eip712Domain::new(
        Some("zERC20 Verifier".into()),
        Some("1".into()),
        Some(chain_id),
        Some(verifier),
        None,
    );
    let signature = signer
        .sign_hash_sync(&statement.eip712_signing_hash(&domain))
        .map_err(|e| e.to_string())?;
    Ok(json!(Bytes::from(signature.as_bytes())))
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy::primitives::{Signature, keccak256};
    use std::sync::Arc;
    use zerc20_enclave::{call, serve};

    #[test]
    fn type_hashes_match_the_verifier() {
        // contracts/src/Verifier.sol
        assert_eq!(
            Transact::default().eip712_type_hash(),
            keccak256(
                "Transact(uint256 tokenId,uint256 chainId,uint256 commitmentRoot,uint256 aspRoot,uint256 nullifier0,\
                 uint256 nullifier1,uint256 withdrawRecipient,uint256 withdrawAmount,uint256 withdrawIntent,\
                 uint256 noteHash1,uint256 noteHash2)"
            )
        );
        assert_eq!(
            Merge::default().eip712_type_hash(),
            keccak256(
                "Merge(uint256 tokenId,uint256 chainId,uint256 commitmentRoot,uint256 aspRoot,uint256[] nullifiers,\
                 uint256 noteHash,uint256 fee,uint256 feeRecipient)"
            )
        );
    }

    #[test]
    fn signs_a_sealed_witness_over_a_socket() {
        let enclave = Arc::new(Enclave::default());
        let signer = PrivateKeySigner::random();
        let me = signer.address();
        enclave.load(signer).unwrap();
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let e = enclave.clone();
        std::thread::spawn(move || serve(listener.incoming(), Arc::new(move |r, _| e.handle(r))));
        let ask = |r: &Request| call(std::net::TcpStream::connect(addr).unwrap(), r, None).unwrap();

        let (statement, witness) = check::tests::burn_and_note();
        let witness = seal(
            WITNESS,
            enclave.public_key(),
            &serde_json::to_vec(&witness).unwrap(),
        )
        .unwrap();
        let verifier = Address::repeat_byte(0x11);
        let request = |statement: &Transact| Request::Transact {
            verifier,
            statement: statement.clone(),
            witness: witness.clone(),
        };
        let sig: Bytes = serde_json::from_value(ask(&request(&statement)).unwrap()).unwrap();
        let domain = Eip712Domain::new(
            Some("zERC20 Verifier".into()),
            Some("1".into()),
            Some(statement.chainId),
            Some(verifier),
            None,
        );
        let hash = statement.eip712_signing_hash(&domain);
        let sig = Signature::from_raw(&sig).unwrap();
        assert_eq!(sig.recover_address_from_prehash(&hash).unwrap(), me);

        let mut other = statement.clone();
        other.withdrawAmount += U256::from(1);
        assert!(ask(&request(&other)).is_err());
        let info = ask(&Request::Attestation).unwrap();
        assert_eq!(info["address"], json!(me));
        assert!(ask(&Request::LoadKey { cms: String::new() }).is_err());
    }
}
