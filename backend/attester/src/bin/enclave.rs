//! The attester's Nitro Enclave: answers its host over vsock. It has no development path: a development host runs the
//! same logic in its own process, so nothing the host sends can switch a real enclave into it.
use alloy::signers::local::PrivateKeySigner;
use openssl::pkey::PKey;
use serde_json::json;
use std::sync::Arc;
use zerc20_attester::{Enclave, PORT, Request};
use zerc20_enclave::nitro::{Nsm, Recipient, listen};

fn main() -> anyhow::Result<()> {
    let nsm = Nsm::open()?;
    let enclave = Arc::new(Enclave::default());
    // KMS encrypts the signing key to this; it never leaves the enclave
    let recipient = Recipient::new()?;
    listen(
        PORT,
        Arc::new(move |request, _| match request {
            Request::Attestation => {
                let mut info = enclave.info();
                info["attestation"] = json!(nsm.attest(enclave.public_key())?);
                Ok(info)
            }
            Request::KmsAttestation => Ok(json!(nsm.attest(recipient.spki())?)),
            Request::LoadKey { cms } => enclave.load(signer(&recipient.unwrap(&cms)?)?),
            other => enclave.handle(other),
        }),
    )?;
    Ok(())
}

/// The signing key from the key pair's private half, PKCS#8.
fn signer(pkcs8: &[u8]) -> Result<PrivateKeySigner, String> {
    let fail = || "the key from KMS does not parse".to_string();
    let secret = PKey::private_key_from_pkcs8(pkcs8)
        .and_then(|k| k.ec_key())
        .and_then(|k| k.private_key().to_vec_padded(32))
        .map_err(|_| fail())?;
    PrivateKeySigner::from_slice(&secret).map_err(|_| fail())
}

#[cfg(test)]
mod tests {
    use super::*;
    use openssl::ec::{EcGroup, EcKey};
    use openssl::nid::Nid;
    use zerc20_enclave::nitro::cms_for;

    /// What KMS returns, built the same way for a key we know.
    #[test]
    fn unwraps_a_key_encrypted_to_the_enclave() {
        let recipient = Recipient::new().unwrap();
        let ec = EcKey::generate(&EcGroup::from_curve_name(Nid::SECP256K1).unwrap()).unwrap();
        let expected = PrivateKeySigner::from_slice(&ec.private_key().to_vec_padded(32).unwrap())
            .unwrap()
            .address();
        let pkcs8 = PKey::from_ec_key(ec)
            .unwrap()
            .private_key_to_pkcs8()
            .unwrap();
        let cms = cms_for(recipient.spki(), &pkcs8).unwrap();
        let unwrapped = recipient.unwrap(&cms).unwrap();
        assert_eq!(signer(&unwrapped).unwrap().address(), expected);
        assert!(Recipient::new().unwrap().unwrap(&cms).is_err());
    }
}
