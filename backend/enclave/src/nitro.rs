//! The enclave's half: its vsock listener, attestation documents from the Nitro Security Module, and the RSA key KMS
//! encrypts a key to.
//! Runs in a Nitro Enclave only; a development host runs its node's logic in its own process instead.
use crate::Handler;
use aws_nitro_enclaves_nsm_api::api::{Request, Response};
use aws_nitro_enclaves_nsm_api::driver::{nsm_init, nsm_process_request};
use openssl::base64;
use openssl::cms::CmsContentInfo;
use openssl::error::ErrorStack;
use openssl::pkey::{PKey, Private};
use openssl::rsa::Rsa;
use serde::de::DeserializeOwned;
use serde_bytes::ByteBuf;

/// Answers the host with `handler` on vsock `port`, for as long as the enclave runs.
pub fn listen<R: DeserializeOwned + 'static>(
    port: u32,
    handler: Handler<R>,
) -> std::io::Result<()> {
    let listener = vsock::VsockListener::bind_with_cid_port(vsock::VMADDR_CID_ANY, port)?;
    eprintln!("listening on vsock port {port}");
    crate::serve(listener.incoming(), handler);
    Ok(())
}

/// The Nitro Security Module.
#[derive(Clone, Copy)]
pub struct Nsm(i32);

impl Nsm {
    pub fn open() -> anyhow::Result<Self> {
        let fd = nsm_init();
        anyhow::ensure!(fd >= 0, "no NSM device: this runs in a Nitro Enclave only");
        Ok(Self(fd))
    }

    /// A fresh attestation document over `public_key`, base64: its certificate is short-lived, so none is kept.
    pub fn attest(self, public_key: &[u8]) -> Result<String, String> {
        let request = Request::Attestation {
            user_data: None,
            nonce: None,
            public_key: Some(ByteBuf::from(public_key)),
        };
        match nsm_process_request(self.0, request) {
            Response::Attestation { document } => Ok(base64::encode_block(&document)),
            other => Err(format!("NSM: {other:?}")),
        }
    }
}

/// A throwaway RSA key that KMS encrypts a key to, once the enclave's attestation document over it checks out against
/// the key policy. It never leaves the enclave.
pub struct Recipient {
    rsa: PKey<Private>,
    spki: Vec<u8>,
}

impl Recipient {
    pub fn new() -> anyhow::Result<Self> {
        let rsa = PKey::from_rsa(Rsa::generate(2048)?)?;
        let spki = rsa.public_key_to_der()?;
        Ok(Self { rsa, spki })
    }

    /// The public key, DER: what the attestation document for KMS is over.
    pub fn spki(&self) -> &[u8] {
        &self.spki
    }

    /// The plaintext of KMS's `CiphertextForRecipient` (base64): CMS EnvelopedData (RSAES-OAEP-SHA256, AES-256-CBC).
    pub fn unwrap(&self, cms: &str) -> Result<Vec<u8>, String> {
        let fail = |what: &str| format!("the key from KMS does not {what}");
        let der = base64::decode_block(cms.trim()).map_err(|_| fail("decode"))?;
        CmsContentInfo::from_der(&der)
            .and_then(|c| c.decrypt_without_cert_check(&self.rsa))
            .map_err(|_| fail("decrypt"))
    }
}

/// What KMS returns for `plaintext`, encrypted to the RSA key `spki` the same way, for tests.
///
/// ponytail: it encrypts with OpenSSL's default RSA key transport (PKCS#1 v1.5). KMS uses RSAES-OAEP-SHA256, which
/// OpenSSL reads from the recipient info, so only a real deployment exercises that path. Set OAEP on the recipient
/// info through openssl-sys if that path ever needs a test.
pub fn cms_for(spki: &[u8], plaintext: &[u8]) -> Result<String, ErrorStack> {
    use openssl::cms::CMSOptions;
    use openssl::stack::Stack;
    use openssl::x509::{X509, X509NameBuilder};
    // CMS needs a certificate for the recipient; KMS names it by key id instead. Any key may sign it.
    let mut name = X509NameBuilder::new()?;
    name.append_entry_by_text("CN", "enclave")?;
    let name = name.build();
    let signer = PKey::from_rsa(Rsa::generate(2048)?)?;
    let mut cert = X509::builder()?;
    cert.set_subject_name(&name)?;
    cert.set_issuer_name(&name)?;
    let recipient = PKey::public_key_from_der(spki)?;
    cert.set_pubkey(&recipient)?;
    cert.sign(&signer, openssl::hash::MessageDigest::sha256())?;
    let mut certs = Stack::new()?;
    certs.push(cert.build())?;
    let cms = CmsContentInfo::encrypt(
        &certs,
        plaintext,
        openssl::symm::Cipher::aes_256_cbc(),
        CMSOptions::BINARY,
    )?;
    Ok(base64::encode_block(&cms.to_der()?))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unwraps_a_key_encrypted_to_the_enclave() {
        let r = Recipient::new().unwrap();
        let cms = cms_for(r.spki(), b"a key").unwrap();
        assert_eq!(r.unwrap(&cms).unwrap(), b"a key");
        let other = Recipient::new().unwrap();
        assert!(other.unwrap(&cms).is_err());
    }
}
