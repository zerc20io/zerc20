//! Checks an AWS Nitro Enclaves attestation document before a wallet seals a witness to the key in it, the attester's or
//! the merge prover's. Without this, a host could hand out its own key and read every witness, private keys included.
//!
//! The document is a COSE_Sign1 (ES384) over a CBOR map. Its `certificate` must chain through `cabundle` up to the
//! pinned root, every certificate must be valid at the time given, and PCR0 must be the release's measurement.
use ciborium::Value;
use p384::ecdsa::signature::Verifier;
use p384::ecdsa::{Signature, VerifyingKey};
use sha2::{Digest, Sha256};
use x509_cert::Certificate;
use x509_cert::der::{Decode, Encode};

type Res<T> = Result<T, String>;

/// COSE algorithm ES384.
const ES384: i64 = -35;
/// ecdsa-with-SHA384, the only signature algorithm in the Nitro chain.
const ECDSA_SHA384: &str = "1.2.840.10045.4.3.3";

fn cbor(b: &[u8]) -> Res<Value> {
    ciborium::from_reader(b).map_err(|e| format!("not CBOR: {e}"))
}

fn field<'a>(map: &'a [(Value, Value)], key: &str) -> Res<&'a Value> {
    map.iter()
        .find(|(k, _)| k.as_text() == Some(key))
        .map(|(_, v)| v)
        .ok_or_else(|| format!("the document has no {key}"))
}

fn bstr(v: &Value) -> Res<&[u8]> {
    v.as_bytes()
        .map(|b| b.as_slice())
        .ok_or_else(|| "expected a byte string".into())
}

fn unhex(s: &str) -> Res<Vec<u8>> {
    let s = s.trim_start_matches("0x");
    if !s.len().is_multiple_of(2) {
        return Err(format!("{s:?} is not hex"));
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|_| format!("{s:?} is not hex")))
        .collect()
}

fn key_of(cert: &Certificate) -> Res<VerifyingKey> {
    let spki = &cert.tbs_certificate.subject_public_key_info;
    VerifyingKey::from_sec1_bytes(spki.subject_public_key.raw_bytes())
        .map_err(|_| "a certificate's key is not P-384".into())
}

/// `cert` is signed by `issuer` and valid at `now`.
fn check_cert(cert: &Certificate, issuer: &Certificate, now: u64) -> Res<()> {
    if cert.signature_algorithm.oid.to_string() != ECDSA_SHA384 {
        return Err("a certificate is not signed with ecdsa-with-SHA384".into());
    }
    let tbs = cert.tbs_certificate.to_der().map_err(|e| e.to_string())?;
    let sig = cert
        .signature
        .as_bytes()
        .and_then(|b| Signature::from_der(b).ok())
        .ok_or("a certificate's signature is malformed")?;
    key_of(issuer)?
        .verify(&tbs, &sig)
        .map_err(|_| "a certificate is not signed by its issuer")?;
    valid_at(cert, now)
}

fn valid_at(cert: &Certificate, now: u64) -> Res<()> {
    let v = &cert.tbs_certificate.validity;
    let (from, to) = (
        v.not_before.to_unix_duration().as_secs(),
        v.not_after.to_unix_duration().as_secs(),
    );
    if now < from || now > to {
        return Err(format!(
            "a certificate is valid from {from} to {to}, not at {now}"
        ));
    }
    Ok(())
}

/// The enclave key (`public_key`) of the attestation document `doc`, if it checks out.
pub fn verify(doc: &[u8], root_sha256: &str, pcr0: &str, now: u64) -> Res<Vec<u8>> {
    let cose = match cbor(doc)? {
        Value::Tag(18, v) => *v,
        v => v,
    };
    let [protected, _, payload, signature] = cose
        .into_array()
        .ok()
        .and_then(|a| <[Value; 4]>::try_from(a).ok())
        .ok_or("not a COSE_Sign1")?;
    let (protected, payload, signature) = (bstr(&protected)?, bstr(&payload)?, bstr(&signature)?);
    let alg = cbor(protected)?
        .into_map()
        .ok()
        .and_then(|m| {
            m.into_iter()
                .find(|(k, _)| k.as_integer() == Some(1.into()))
        })
        .and_then(|(_, v)| v.as_integer());
    if alg != Some(ES384.into()) {
        return Err("the document is not signed with ES384".into());
    }

    let map = cbor(payload)?
        .into_map()
        .map_err(|_| "the document is not a map")?;
    let parse = |der: &[u8]| Certificate::from_der(der).map_err(|e| format!("a certificate: {e}"));
    let leaf = parse(bstr(field(&map, "certificate")?)?)?;
    let bundle: Vec<Certificate> = field(&map, "cabundle")?
        .as_array()
        .ok_or("cabundle is not a list")?
        .iter()
        .map(|c| parse(bstr(c)?))
        .collect::<Res<_>>()?;
    let root = bundle.first().ok_or("cabundle is empty")?;
    let root_der = root.to_der().map_err(|e| e.to_string())?;
    if Sha256::digest(&root_der)[..] != unhex(root_sha256)? {
        return Err("the chain does not end at the pinned root".into());
    }
    valid_at(root, now)?;
    // leaf, then the bundle from the root's side down: each is signed by the next
    let chain: Vec<&Certificate> = std::iter::once(&leaf).chain(bundle.iter().rev()).collect();
    for pair in chain.windows(2) {
        check_cert(pair[0], pair[1], now)?;
    }

    let sig_structure = Value::Array(vec![
        Value::Text("Signature1".into()),
        Value::Bytes(protected.to_vec()),
        Value::Bytes(vec![]),
        Value::Bytes(payload.to_vec()),
    ]);
    let mut signed = Vec::new();
    ciborium::into_writer(&sig_structure, &mut signed).map_err(|e| e.to_string())?;
    let sig =
        Signature::from_slice(signature).map_err(|_| "the document's signature is malformed")?;
    key_of(&leaf)?
        .verify(&signed, &sig)
        .map_err(|_| "the document is not signed by its certificate")?;

    let pcrs = field(&map, "pcrs")?.as_map().ok_or("pcrs is not a map")?;
    let measured = pcrs
        .iter()
        .find(|(k, _)| k.as_integer() == Some(0.into()))
        .map(|(_, v)| bstr(v))
        .ok_or("the document has no PCR0")??;
    if measured != unhex(pcr0)? {
        return Err("PCR0 is not the release's".into());
    }
    let key = bstr(field(&map, "public_key")?)?;
    if key.len() != 32 {
        return Err("the document's public_key is not an X25519 key".into());
    }
    Ok(key.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;
    use p384::ecdsa::{DerSignature, SigningKey};
    use std::str::FromStr;
    use std::time::Duration;
    use x509_cert::builder::{Builder, CertificateBuilder, Profile};
    use x509_cert::name::Name;
    use x509_cert::serial_number::SerialNumber;
    use x509_cert::spki::SubjectPublicKeyInfoOwned;
    use x509_cert::time::Validity;

    const NOW: u64 = 1_800_000_000;
    const PCR0: [u8; 48] = [0xab; 48];
    const KEY: [u8; 32] = [0x42; 32];

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_slice(&[seed; 48]).unwrap()
    }

    /// A certificate for `subject`'s key, signed by `issuer` (self-signed when they are the same), valid for an hour
    /// either side of `NOW`.
    fn cert(name: &str, subject: &SigningKey, issuer: (&str, &SigningKey), ca: bool) -> Vec<u8> {
        let spki = SubjectPublicKeyInfoOwned::from_key(*subject.verifying_key()).unwrap();
        let validity = Validity {
            not_before: x509_cert::time::Time::UtcTime(
                x509_cert::der::asn1::UtcTime::from_unix_duration(Duration::from_secs(NOW - 3600))
                    .unwrap(),
            ),
            not_after: x509_cert::time::Time::UtcTime(
                x509_cert::der::asn1::UtcTime::from_unix_duration(Duration::from_secs(NOW + 3600))
                    .unwrap(),
            ),
        };
        let profile = match ca {
            true => Profile::SubCA {
                issuer: Name::from_str(&format!("CN={}", issuer.0)).unwrap(),
                path_len_constraint: None,
            },
            false => Profile::Leaf {
                issuer: Name::from_str(&format!("CN={}", issuer.0)).unwrap(),
                enable_key_agreement: false,
                enable_key_encipherment: false,
            },
        };
        let builder = CertificateBuilder::new(
            profile,
            SerialNumber::from(1u32),
            validity,
            Name::from_str(&format!("CN={name}")).unwrap(),
            spki,
            issuer.1,
        )
        .unwrap();
        builder.build::<DerSignature>().unwrap().to_der().unwrap()
    }

    fn doc(signer: &SigningKey, leaf: Vec<u8>, bundle: Vec<Vec<u8>>, pcr0: &[u8]) -> Vec<u8> {
        let map = Value::Map(vec![
            (
                Value::Text("module_id".into()),
                Value::Text("i-test".into()),
            ),
            (
                Value::Text("pcrs".into()),
                Value::Map(vec![(
                    Value::Integer(0.into()),
                    Value::Bytes(pcr0.to_vec()),
                )]),
            ),
            (Value::Text("certificate".into()), Value::Bytes(leaf)),
            (
                Value::Text("cabundle".into()),
                Value::Array(bundle.into_iter().map(Value::Bytes).collect()),
            ),
            (Value::Text("public_key".into()), Value::Bytes(KEY.to_vec())),
        ]);
        let mut payload = Vec::new();
        ciborium::into_writer(&map, &mut payload).unwrap();
        let mut protected = Vec::new();
        ciborium::into_writer(
            &Value::Map(vec![(
                Value::Integer(1.into()),
                Value::Integer(ES384.into()),
            )]),
            &mut protected,
        )
        .unwrap();
        let mut signed = Vec::new();
        ciborium::into_writer(
            &Value::Array(vec![
                Value::Text("Signature1".into()),
                Value::Bytes(protected.clone()),
                Value::Bytes(vec![]),
                Value::Bytes(payload.clone()),
            ]),
            &mut signed,
        )
        .unwrap();
        let sig: Signature = p384::ecdsa::signature::Signer::sign(signer, &signed);
        let mut out = Vec::new();
        ciborium::into_writer(
            &Value::Tag(
                18,
                Box::new(Value::Array(vec![
                    Value::Bytes(protected),
                    Value::Map(vec![]),
                    Value::Bytes(payload),
                    Value::Bytes(sig.to_bytes().to_vec()),
                ])),
            ),
            &mut out,
        )
        .unwrap();
        out
    }

    #[test]
    fn checks_the_whole_document() {
        let (root, mid, leaf) = (key(1), key(2), key(3));
        let root_der = cert("root", &root, ("root", &root), true);
        let mid_der = cert("mid", &mid, ("root", &root), true);
        let leaf_der = cert("leaf", &leaf, ("mid", &mid), false);
        let pin: String = Sha256::digest(&root_der)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let pcr0: String = PCR0.iter().map(|b| format!("{b:02x}")).collect();
        let bundle = vec![root_der.clone(), mid_der.clone()];

        let good = doc(&leaf, leaf_der.clone(), bundle.clone(), &PCR0);
        assert_eq!(verify(&good, &pin, &pcr0, NOW).unwrap(), KEY);

        let fails =
            |d: &[u8], pin: &str, pcr0: &str, now: u64| verify(d, pin, pcr0, now).unwrap_err();
        assert!(fails(&good, &pin, &pcr0, NOW + 7200).contains("valid"));
        assert!(fails(&good, &"00".repeat(32), &pcr0, NOW).contains("pinned root"));
        assert!(fails(&good, &pin, &"00".repeat(48), NOW).contains("PCR0"));
        // signed by a key other than the leaf certificate's
        let forged = doc(&mid, leaf_der.clone(), bundle.clone(), &PCR0);
        assert!(fails(&forged, &pin, &pcr0, NOW).contains("not signed by its certificate"));
        // a leaf certificate that its claimed issuer did not sign
        let stray = cert("leaf", &leaf, ("mid", &key(9)), false);
        let unchained = doc(&leaf, stray, bundle.clone(), &PCR0);
        assert!(fails(&unchained, &pin, &pcr0, NOW).contains("not signed by its issuer"));
    }
}
