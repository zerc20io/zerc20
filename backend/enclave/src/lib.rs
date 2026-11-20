//! What a host and its Nitro Enclave share, for every node with one (attester, merge-prover): one JSON
//! line in and one out per connection, over vsock or, in development, a loopback socket; and the host's half of
//! loading a KMS key that only the enclave's image can decrypt. The enclave's half is in [`nitro`].
#[cfg(feature = "nitro")]
pub mod nitro;

use anyhow::{Context, Result, ensure};
use serde::Serialize;
use serde::de::DeserializeOwned;
use serde_json::{Value, json};
use std::io::{self, BufRead, BufReader, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::Arc;
use std::time::Duration;

pub type Reply = Result<Value, String>;

/// Answers a request. The reader holds whatever the client sent after the request's line, for requests that carry a
/// body (a key too large for one line). The connection stays open for the reply, so the request must say how long its
/// body is.
pub type Handler<R> = Arc<dyn Fn(R, &mut dyn Read) -> Reply + Send + Sync>;

/// Answers each connection on its own thread: one JSON line in, an optional body, one line out.
pub fn serve<R: DeserializeOwned + 'static, S: Read + Write + Send + 'static>(
    incoming: impl Iterator<Item = io::Result<S>>,
    handler: Handler<R>,
) {
    for stream in incoming.flatten() {
        let handler = handler.clone();
        std::thread::spawn(move || answer(stream, &*handler));
    }
}

fn answer<R: DeserializeOwned, S: Read + Write>(
    mut stream: S,
    handler: &dyn Fn(R, &mut dyn Read) -> Reply,
) -> io::Result<()> {
    let mut reader = BufReader::new(&mut stream);
    let mut line = String::new();
    reader.read_line(&mut line)?;
    let reply = match serde_json::from_str(&line) {
        Ok(request) => handler(request, &mut reader),
        Err(_) => Err("malformed request".into()),
    };
    drop(reader);
    writeln!(stream, "{}", serde_json::to_string(&reply)?)
}

/// Sends one request, then `body` if any, over a fresh connection, and reads the reply.
pub fn call<R: Serialize, S: Read + Write>(
    mut stream: S,
    request: &R,
    body: Option<&mut dyn Read>,
) -> io::Result<Reply> {
    writeln!(stream, "{}", serde_json::to_string(request)?)?;
    if let Some(body) = body {
        io::copy(body, &mut stream)?;
    }
    let mut line = String::new();
    BufReader::new(stream).read_line(&mut line)?;
    Ok(serde_json::from_str(&line)?)
}

/// Where a host reaches its enclave.
#[derive(Clone, Copy, Debug)]
pub enum Target {
    /// Development: the enclave's logic, in the host's own process.
    Tcp(SocketAddr),
    /// The Nitro Enclave's CID and vsock port.
    Vsock(u32, u32),
}

impl Target {
    /// Development: answers with `handler` on a loopback socket, in this process.
    pub fn local<R: DeserializeOwned + 'static>(handler: Handler<R>) -> io::Result<Self> {
        let listener = TcpListener::bind("127.0.0.1:0")?;
        let target = Target::Tcp(listener.local_addr()?);
        std::thread::spawn(move || serve(listener.incoming(), handler));
        Ok(target)
    }

    /// One request over a fresh connection, waiting at most `timeout` for the reply.
    pub async fn ask<R: Serialize + Send + 'static>(
        self,
        request: R,
        timeout: Duration,
    ) -> Result<Reply> {
        self.exchange(request, None::<io::Empty>, timeout).await
    }

    /// Like [`Target::ask`], followed by `body`.
    pub async fn ask_with<R: Serialize + Send + 'static, B: Read + Send + 'static>(
        self,
        request: R,
        body: B,
        timeout: Duration,
    ) -> Result<Reply> {
        self.exchange(request, Some(body), timeout).await
    }

    async fn exchange<R: Serialize + Send + 'static, B: Read + Send + 'static>(
        self,
        request: R,
        mut body: Option<B>,
        timeout: Duration,
    ) -> Result<Reply> {
        let reply = tokio::task::spawn_blocking(move || {
            let body = body.as_mut().map(|b| b as &mut dyn Read);
            match self {
                Target::Tcp(a) => {
                    let s = TcpStream::connect(a)?;
                    s.set_read_timeout(Some(timeout))?;
                    call(s, &request, body)
                }
                Target::Vsock(cid, port) => {
                    let s = vsock::VsockStream::connect_with_cid_port(cid, port)?;
                    s.set_read_timeout(Some(timeout))?;
                    call(s, &request, body)
                }
            }
        })
        .await?;
        reply.context("the enclave is unreachable")
    }
}

/// KMS decrypts `blob` (a file) for the enclave whose attestation `document` (base64) names its RSA key, and returns
/// `CiphertextForRecipient` (base64): the plaintext encrypted to that key. The host only ever holds ciphertext, and the
/// key policy refuses any other image.
pub async fn kms_decrypt(key_id: &str, blob: &str, document: &str) -> Result<String> {
    let recipient = json!({
        "KeyEncryptionAlgorithm": "RSAES_OAEP_SHA_256",
        "AttestationDocument": document,
    });
    let out = tokio::process::Command::new("aws")
        .args(["kms", "decrypt", "--key-id", key_id])
        .args(["--ciphertext-blob", &format!("fileb://{blob}")])
        .args(["--recipient", &recipient.to_string()])
        .args(["--query", "CiphertextForRecipient", "--output", "text"])
        .output()
        .await
        .context("running the aws CLI")?;
    ensure!(
        out.status.success(),
        "aws kms decrypt: {}",
        String::from_utf8_lossy(&out.stderr).trim()
    );
    Ok(String::from_utf8(out.stdout)?.trim().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    #[derive(Serialize, Deserialize)]
    enum Request {
        Echo(String),
        /// A body of this many bytes follows.
        Count(u64),
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn answers_lines_and_bodies() {
        let handler: Handler<Request> = Arc::new(|r, body| match r {
            Request::Echo(s) => Ok(json!(s)),
            Request::Count(len) => {
                let n =
                    io::copy(&mut body.take(len), &mut io::sink()).map_err(|e| e.to_string())?;
                Ok(json!(n))
            }
        });
        let target = Target::local(handler).unwrap();
        let t = Duration::from_secs(5);
        let echo = target.ask(Request::Echo("hi".into()), t).await.unwrap();
        assert_eq!(echo, Ok(json!("hi")));
        let body = io::repeat(7).take(100_000);
        let count = target
            .ask_with(Request::Count(100_000), body, t)
            .await
            .unwrap();
        assert_eq!(count, Ok(json!(100_000)));
    }
}
