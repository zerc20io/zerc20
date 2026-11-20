//! Runs blocks of burn address searches natively, beside a server: some three times faster than the wasm a browser
//! runs, and on every core. The SDK hands it the blocks (`runBurnsOn`) and keeps the searches.
//!
//! One JSON line in per block: `{id, burnKey, chainId, tokenId, index, publicKey, from, to}` for an address a burn key
//! derives (`burnBlock`), or `{id, chainId, publicKey, start, count}` for someone else's key (`burnBlockFor`), with
//! `chainId` in decimal and the rest of the keys in hex. One line out per block, in the order they finish: `{id, burn}`,
//! with a null burn where the block holds none, or `{id, error}`. Its argument is how many blocks it runs at once. It
//! ends when its input does, and at a line it cannot read.

use std::io::{BufRead, Write};
use std::process::ExitCode;
use std::sync::{Arc, Mutex, PoisonError, mpsc};
use std::thread;

use alloy_primitives::hex;
use serde::Deserialize;
use serde_json::json;
use zerc20_wallet_core::{burn_block_for_of, burn_block_of};

#[derive(Deserialize)]
struct Block {
    id: u64,
    #[serde(flatten)]
    call: Call,
}

#[derive(Deserialize)]
#[serde(untagged)]
enum Call {
    #[serde(rename_all = "camelCase")]
    Derived {
        burn_key: String,
        chain_id: String,
        token_id: u32,
        index: u32,
        public_key: String,
        from: u32,
        to: u32,
    },
    #[serde(rename_all = "camelCase")]
    For {
        chain_id: String,
        public_key: String,
        start: String,
        count: u32,
    },
}

fn chain(id: &str) -> Result<u64, String> {
    id.parse().map_err(|_| format!("{id:?} is not a chain id"))
}

/// The answer to one block's line.
fn answer(line: &str) -> Result<String, String> {
    let block: Block = serde_json::from_str(line).map_err(|e| format!("{line:?}: {e}"))?;
    let burn = match block.call {
        Call::Derived {
            burn_key,
            chain_id,
            token_id,
            index,
            public_key,
            from,
            to,
        } => hex::decode(&burn_key)
            .map_err(|e| format!("the burn key: {e}"))
            .and_then(|key| {
                burn_block_of(
                    &key,
                    chain(&chain_id)?,
                    token_id,
                    index,
                    &public_key,
                    from,
                    to,
                )
            }),
        Call::For {
            chain_id,
            public_key,
            start,
            count,
        } => chain(&chain_id).and_then(|c| burn_block_for_of(c, &public_key, &start, count)),
    };
    Ok(match burn {
        Ok(burn) => json!({ "id": block.id, "burn": burn }),
        Err(error) => json!({ "id": block.id, "error": error }),
    }
    .to_string())
}

fn main() -> ExitCode {
    let threads = match std::env::args().nth(1).map(|n| n.parse::<usize>()) {
        None => 1,
        Some(Ok(n)) if n > 0 => n,
        _ => {
            eprintln!("usage: zerc20-burn-blocks <blocks at once>");
            return ExitCode::FAILURE;
        }
    };
    let (send, receive) = mpsc::channel::<String>();
    let receive = Arc::new(Mutex::new(receive));
    let out = Arc::new(Mutex::new(std::io::stdout()));
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let (receive, out) = (Arc::clone(&receive), Arc::clone(&out));
            thread::spawn(move || {
                loop {
                    // the lock is let go as the line comes, so that the others take the next ones meanwhile
                    let next = receive
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .recv();
                    let Ok(line) = next else { return };
                    let answer = match answer(&line) {
                        Ok(answer) => answer,
                        Err(e) => {
                            eprintln!("zerc20-burn-blocks: {e}");
                            std::process::exit(1);
                        }
                    };
                    let mut out = out.lock().unwrap_or_else(PoisonError::into_inner);
                    // the server that reads it is gone
                    if writeln!(out, "{answer}")
                        .and_then(|()| out.flush())
                        .is_err()
                    {
                        std::process::exit(1);
                    }
                }
            })
        })
        .collect();
    for line in std::io::stdin().lock().lines() {
        let Ok(line) = line else { break };
        if send.send(line).is_err() {
            break;
        }
    }
    drop(send);
    for worker in workers {
        let _ = worker.join();
    }
    ExitCode::SUCCESS
}
