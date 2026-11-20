//! What wallets and the enclaves they seal witnesses to (the attester's and the merge prover's) share: the statements an
//! attester signs, how a witness is sealed and opened, and the checks an enclave runs on it. No I/O, so it builds for
//! wasm too, and wallet code stays out of the enclaves' images.
pub mod check;
#[cfg(feature = "nitro")]
pub mod nitro;

use alloy_primitives::Bytes;
use alloy_sol_types::sol;
use hpke::aead::ChaCha20Poly1305;
use hpke::kdf::HkdfSha256;
use hpke::kem::X25519HkdfSha256;
use hpke::{Deserializable, Kem as _, OpModeR, OpModeS, Serializable};
use serde::{Deserialize, Serialize};

sol! {
    /// `Verifier.TransactSignals`, which an attester signs as EIP-712 `Transact`.
    #[derive(Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
    struct Transact {
        uint256 tokenId;
        uint256 chainId;
        uint256 commitmentRoot;
        uint256 aspRoot;
        uint256 nullifier0;
        uint256 nullifier1;
        uint256 withdrawRecipient;
        uint256 withdrawAmount;
        uint256 withdrawIntent;
        uint256 noteHash1;
        uint256 noteHash2;
    }

    /// What `Verifier.merge` checks an attestation against. `chainId` is the chain's own. `fee` is paid publicly to
    /// `feeRecipient` (the relayer) out of the merged value; both zero for none.
    #[derive(Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
    struct Merge {
        uint256 tokenId;
        uint256 chainId;
        uint256 commitmentRoot;
        uint256 aspRoot;
        uint256[] nullifiers;
        uint256 noteHash;
        uint256 fee;
        uint256 feeRecipient;
    }
}

/// HPKE `info` of a witness sealed to the attester's enclave: what is sealed for something else does not open there.
pub const WITNESS: &[u8] = b"zerc20/attester/witness/v1";
/// HPKE `info` of a merge witness sealed to the merge prover's enclave.
pub const MERGE_WITNESS: &[u8] = b"zerc20/merge-prover/witness/v1";

pub type Kem = X25519HkdfSha256;

/// Seals `msg` to an enclave's key: HPKE base mode, DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, ChaCha20-Poly1305, the
/// given `info`, empty `aad`. The result is the encapsulated key (32 bytes), then the ciphertext.
pub fn seal(info: &[u8], public_key: &[u8], msg: &[u8]) -> anyhow::Result<Bytes> {
    let pk = <Kem as hpke::Kem>::PublicKey::from_bytes(public_key)?;
    let (enc, ct) = hpke::single_shot_seal::<ChaCha20Poly1305, HkdfSha256, Kem>(
        &OpModeS::Base,
        &pk,
        info,
        msg,
        b"",
    )?;
    Ok([enc.to_bytes().as_slice(), &ct].concat().into())
}

/// The key an enclave has witnesses sealed to: made at start and never kept, so it belongs to one enclave instance.
pub struct WitnessKey {
    sk: <Kem as hpke::Kem>::PrivateKey,
    public_key: Bytes,
}

impl Default for WitnessKey {
    fn default() -> Self {
        let (sk, pk) = Kem::gen_keypair();
        Self {
            sk,
            public_key: Bytes::copy_from_slice(&pk.to_bytes()),
        }
    }
}

impl WitnessKey {
    pub fn public_key(&self) -> &Bytes {
        &self.public_key
    }

    /// What [`seal`] sealed to this key under `info`; `None` for anything else.
    pub fn open(&self, info: &[u8], sealed: &[u8]) -> Option<Vec<u8>> {
        let (enc, ct) = sealed.split_at_checked(32)?;
        let enc = <Kem as hpke::Kem>::EncappedKey::from_bytes(enc).ok()?;
        hpke::single_shot_open::<ChaCha20Poly1305, HkdfSha256, Kem>(
            &OpModeR::Base,
            &self.sk,
            &enc,
            info,
            ct,
            b"",
        )
        .ok()
    }
}
