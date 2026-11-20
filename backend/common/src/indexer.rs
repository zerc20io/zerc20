//! Reads one chain's indexer, which the nodes downstream of it trust: it is the operator's own, and it says what the
//! ledger holds. Point it at the origin, not the CDN, so what it says is fresh.
use crate::fields::{fields_of, fr};
use alloy::primitives::U256;
use alloy::transports::http::reqwest;
use anyhow::{Context, Result, ensure};
use serde_json::Value;
use std::time::Duration;
use zerc20_zkp::ark_bn254::Fr;

pub struct Indexer {
    http: reqwest::Client,
    base: String,
}

impl Indexer {
    pub fn new(base: &str) -> Result<Self> {
        Ok(Self {
            http: reqwest::Client::builder()
                .timeout(Duration::from_secs(20))
                .build()?,
            base: base.trim_end_matches('/').into(),
        })
    }

    pub fn base(&self) -> &str {
        &self.base
    }

    pub async fn get(&self, path: &str) -> Result<Vec<u8>> {
        let r = self.http.get(format!("{}{path}", self.base)).send().await?;
        Ok(r.error_for_status()?.bytes().await?.to_vec())
    }

    pub async fn status(&self) -> Result<Value> {
        Ok(serde_json::from_slice(&self.get("/status").await?)?)
    }

    /// How many commitments it holds, and how many of them are final: what a downstream node may act on.
    pub async fn commitment_counts(&self) -> Result<(u64, u64)> {
        let s = self.status().await?;
        let count = |k: &str| s[k].as_u64().context(k.to_string());
        Ok((count("commitments")?, count("commitments_final")?))
    }

    /// Page `c`: the hash chain before it, and its commitments (fewer than 4096 while it fills).
    pub async fn commitments(&self, c: u64) -> Result<(U256, Vec<[U256; 4]>)> {
        let b = self.get(&format!("/commitments/{c}")).await?;
        ensure!(
            b.len() >= 32 && (b.len() - 32) % 128 == 0,
            "malformed commitments page {c}"
        );
        Ok((
            U256::from_be_slice(&b[..32]),
            b[32..].chunks_exact(128).map(fields_of).collect(),
        ))
    }

    /// Page `c`: the block of each commitment.
    pub async fn blocks(&self, c: u64) -> Result<Vec<u64>> {
        let b = self.get(&format!("/blocks/{c}")).await?;
        let (words, rest) = b.as_chunks::<8>();
        ensure!(rest.is_empty(), "malformed blocks page {c}");
        Ok(words.iter().map(|&w| u64::from_be_bytes(w)).collect())
    }

    /// Page `p` of proved roots, in the order they were proved: each one's size and root, and whether the indexer
    /// derives the same root itself.
    pub async fn proved_roots(&self, p: u64) -> Result<Vec<(u64, U256, bool)>> {
        // size (8), root, partial chunk and page roots (32 each), derived (1)
        const ENTRY: usize = 105;
        let b = self.get(&format!("/roots/{p}")).await?;
        let (entries, rest) = b.as_chunks::<ENTRY>();
        ensure!(rest.is_empty(), "malformed roots page {p}");
        Ok(entries
            .iter()
            .map(|e| {
                let size = u64::from_be_bytes(std::array::from_fn(|i| e[i]));
                (size, U256::from_be_slice(&e[8..40]), e[104] == 1)
            })
            .collect())
    }

    /// A list of 32-byte roots, such as `/page-roots` or `/chunk-roots/{p}`.
    pub async fn roots(&self, path: &str) -> Result<Vec<Fr>> {
        let b = self.get(path).await?;
        ensure!(b.len() % 32 == 0, "malformed {path}");
        Ok(b.chunks_exact(32)
            .map(|w| fr(U256::from_be_slice(w)))
            .collect())
    }
}
