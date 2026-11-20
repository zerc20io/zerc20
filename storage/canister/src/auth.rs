//! EIP-191 signer recovery, ported from zERC20-v2 `icp/canisters/key_manager/src/auth.rs`.

use k256::ecdsa::{RecoveryId, Signature, VerifyingKey};
use sha3::{Digest, Keccak256};

pub type EvmAddress = [u8; 20];

fn keccak256(data: &[u8]) -> [u8; 32] {
    Keccak256::digest(data).into()
}

/// EIP-191 `personal_sign` digest of `msg`.
pub fn eip191_hash(msg: &[u8]) -> [u8; 32] {
    let mut buf = format!("\x19Ethereum Signed Message:\n{}", msg.len()).into_bytes();
    buf.extend_from_slice(msg);
    keccak256(&buf)
}

/// Recover the signer of a 65-byte `r || s || v` signature. High-s (malleable) signatures are rejected.
fn recover_evm_address(prehash: &[u8; 32], signature: &[u8]) -> Option<EvmAddress> {
    if signature.len() != 65 {
        return None;
    }
    let v = match signature[64] {
        27 | 28 => signature[64] - 27,
        x @ (0 | 1) => x,
        _ => return None,
    };
    let sig = Signature::from_slice(&signature[..64]).ok()?;
    if sig.normalize_s().is_some() {
        return None;
    }
    let vk = VerifyingKey::recover_from_prehash(prehash, &sig, RecoveryId::from_byte(v)?).ok()?;
    Some(evm_address(&vk))
}

/// The address that signed `msg` with EIP-191 `personal_sign`, if `signature` is valid.
pub fn eip191_signer(msg: &str, signature: &[u8]) -> Option<EvmAddress> {
    recover_evm_address(&eip191_hash(msg.as_bytes()), signature)
}

/// `keccak256(uncompressed_pubkey[1..])[12..]`.
pub fn evm_address(vk: &VerifyingKey) -> EvmAddress {
    let [_, _, _, _, _, _, _, _, _, _, _, _, address @ ..] =
        keccak256(&vk.to_encoded_point(false).as_bytes()[1..]);
    address
}
