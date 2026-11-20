//! Drives `scripts/e2e.sh` as a wallet would: makes notes and a burn deposit with known openings on the
//! IndexerFixture deployment, proves the true root, then has the attester sign a transact and a merge and submits them,
//! so the contract itself checks the signatures. The deployer key owns the fixture, signs its own attestations and
//! publishes ASP roots.
use alloy::network::{Ethereum, EthereumWallet};
use alloy::primitives::{Address, B256, Bytes, U256};
use alloy::providers::{PendingTransactionBuilder, Provider, ProviderBuilder};
use alloy::signers::local::PrivateKeySigner;
use alloy::sol;
use alloy::transports::http::reqwest;
use anyhow::{Context, Result, ensure};
use serde_json::{Value, json};
use std::time::{Duration, Instant};
use zerc20_attester::check::{
    self, Input, JoinSplit, MergeWitness, Signature, merge_message, merge_outputs,
    transact_message, transact_statement,
};
use zerc20_attester::{Merge, Transact, WITNESS, seal, sign};
use zerc20_common::contracts::ILedger::{self, RootState};
use zerc20_common::contracts::{
    Groth16Proof, IVerifier, MergeRequest, NovaDeciderProof, TransactRequest, TransactSignals,
};
use zerc20_common::fields::{fr, leaf, u256};
use zerc20_common::{Indexer, env};
use zerc20_zkp::ark_bn254::Fr;
use zerc20_zkp::commitments::{asp_leaf, note_leaf, transfer_leaf};
use zerc20_zkp::primitives::{Keys, burn_address, note_hash};
use zerc20_zkp::tree::{TREE_HEIGHT, merkle_path};

// what only this test calls, on the IndexerFixture its deployer owns
sol! {
    #[sol(rpc)]
    interface IVerifierAdmin {
        function addAttester(address attester) external;
    }
    #[sol(rpc)]
    interface ITokenRegistry {
        function tokenById(uint32 tokenId) external view returns (address);
    }
    #[sol(rpc)]
    interface IToken {
        function wrap(uint256 amount, address receiver) external payable;
        function balanceOf(address account) external view returns (uint256);
    }
}

const TOKEN_ID: u64 = 1; // IndexerFixture's zETH
const SK: u64 = 4242; // the wallet's private key
const WAIT: Duration = Duration::from_secs(30);

fn n(v: u64) -> U256 {
    U256::from(v)
}

struct Attester {
    http: reqwest::Client,
    url: String,
}

impl Attester {
    async fn get(&self) -> Result<Value> {
        Ok(self
            .http
            .get(format!("{}/attestation", self.url))
            .send()
            .await?
            .error_for_status()?
            .json()
            .await?)
    }

    /// The status and body of a request for an attestation.
    async fn post(
        &self,
        path: &str,
        statement: &impl serde::Serialize,
        witness: &[u8],
    ) -> Result<(u16, String)> {
        let key: Bytes = serde_json::from_value(self.get().await?["publicKey"].clone())?;
        let body = json!({ "statement": statement, "witness": seal(WITNESS, &key, witness)? });
        let r = self
            .http
            .post(format!("{}{path}", self.url))
            .json(&body)
            .send()
            .await?;
        Ok((r.status().as_u16(), r.text().await?))
    }

    /// Like `post`, once the attester has caught up with the root.
    async fn post_known(
        &self,
        path: &str,
        statement: &impl serde::Serialize,
        witness: &[u8],
    ) -> Result<(u16, String)> {
        let start = Instant::now();
        loop {
            let (status, body) = self.post(path, statement, witness).await?;
            if status != 400
                || !body.contains("not a root the indexer derived")
                || start.elapsed() > WAIT
            {
                return Ok((status, body));
            }
            tokio::time::sleep(Duration::from_millis(500)).await;
        }
    }

    async fn attest(
        &self,
        path: &str,
        statement: &impl serde::Serialize,
        witness: &[u8],
    ) -> Result<Bytes> {
        let (status, body) = self.post_known(path, statement, witness).await?;
        ensure!(status == 200, "{path} {status}: {body}");
        let v: Value = serde_json::from_str(&body)?;
        Ok(serde_json::from_value(v["attestation"].clone())?)
    }

    async fn expect(
        &self,
        path: &str,
        statement: &impl serde::Serialize,
        witness: &[u8],
        want: u16,
        what: &str,
    ) -> Result<()> {
        let (status, body) = match want {
            400 => self.post(path, statement, witness).await?,
            _ => self.post_known(path, statement, witness).await?,
        };
        ensure!(
            status == want,
            "{what}: expected {want}, got {status}: {body}"
        );
        println!("ok: {what} -> {status}");
        Ok(())
    }
}

async fn mined(tx: PendingTransactionBuilder<Ethereum>) -> Result<()> {
    let receipt = tx.get_receipt().await?;
    ensure!(
        receipt.status(),
        "transaction {} reverted",
        receipt.transaction_hash
    );
    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    let owner: PrivateKeySigner = env("PRIVATE_KEY")?.parse()?;
    let provider = ProviderBuilder::new()
        .wallet(EthereumWallet::from(owner.clone()))
        .connect_http(env("RPC_URL")?.parse()?)
        .erased();
    let chain = n(provider.get_chain_id().await?);
    let verifier: Address = env("VERIFIER")?.parse()?;
    let v = IVerifier::new(verifier, &provider);
    let ledger = ILedger::new(v.ledger().call().await?, &provider);
    let token = IToken::new(
        ITokenRegistry::new(v.factory().call().await?, &provider)
            .tokenById(TOKEN_ID as u32)
            .call()
            .await?,
        &provider,
    );
    let indexer = Indexer::new(&env("INDEXER_URL")?)?;
    let http = reqwest::Client::new();
    let a = Attester {
        http: http.clone(),
        url: env("ATTESTER_A")?,
    };
    let b = Attester {
        http: http.clone(),
        url: env("ATTESTER_B")?,
    };
    let c = Attester {
        http,
        url: env("ATTESTER_C")?,
    };

    // the attester's key
    let info = a.get().await?;
    let key: Bytes = serde_json::from_value(info["publicKey"].clone())?;
    ensure!(key.len() == 32, "/attestation: {info}");
    // null from a development host; a wallet checks a Nitro host's document before it seals anything
    let kind = match info["attestation"].is_null() {
        true => "development, no document",
        false => "with an attestation document",
    };
    let attester: Address = serde_json::from_value(info["address"].clone())?;
    let admin = IVerifierAdmin::new(verifier, &provider);
    mined(admin.addAttester(attester).send().await?).await?;
    println!("ok: registered the attester {attester} ({kind})");

    // notes A..D owned by SK, made by two transacts that the fixture's own attester signs
    let keys = Keys::of(Fr::from(SK));
    let auth_key = [u256(keys.auth_key.x), u256(keys.auth_key.y)];
    let (cid, tid, pk) = (fr(chain), Fr::from(TOKEN_ID), keys.public_key);
    let notes = [(30u64, 1u64), (20, 2), (11, 3), (12, 4)];
    let hash = |(value, salt): (u64, u64)| note_hash(cid, pk, Fr::from(value), tid, Fr::from(salt));
    let empty_root = ledger.rootState().call().await?.root;
    let fixture_asp_root = v.latestAspRoot().call().await?;
    for (k, pair) in notes.chunks(2).enumerate() {
        let s = Transact {
            tokenId: n(TOKEN_ID),
            chainId: chain,
            commitmentRoot: empty_root,
            aspRoot: fixture_asp_root,
            nullifier0: n(1000 + 2 * k as u64),
            nullifier1: n(1001 + 2 * k as u64),
            noteHash1: u256(hash(pair[0])),
            noteHash2: u256(hash(pair[1])),
            ..Default::default()
        };
        let attestation =
            serde_json::from_value(sign(&owner, verifier, chain, &s).map_err(anyhow::Error::msg)?)?;
        mined(v.transact(request(0, &s, attestation)).send().await?).await?;
    }

    // a burn deposit of 50 from the owner
    let (burn_salt, burn) = (0u64..)
        .find_map(|s| Some((s, burn_address(cid, pk, Fr::from(s))?)))
        .context("no burn salt")?;
    let burn_to = Address::from_word(B256::from(u256(burn)));
    mined(token.wrap(n(50), burn_to).value(n(50)).send().await?).await?;

    // where they landed, from the indexer, as a wallet would see them
    let size = ledger.nextIndex().call().await?;
    let start = Instant::now();
    while indexer.status().await?["commitments"].as_u64() != Some(size) {
        ensure!(
            start.elapsed() < WAIT,
            "the indexer never reached {size} commitments"
        );
        tokio::time::sleep(Duration::from_millis(200)).await;
    }
    let (_, fields) = indexer.commitments(0).await?;
    let leaves: Vec<Fr> = fields.iter().map(leaf).collect();
    let at = |l: Fr| {
        leaves
            .iter()
            .position(|x| *x == l)
            .context("leaf not in the tree")
    };
    let index: Vec<usize> = notes
        .iter()
        .map(|p| at(note_leaf(tid, hash(*p))))
        .collect::<Result<_>>()?;
    let burn_index = at(transfer_leaf(
        tid,
        fr(U256::from_be_slice(owner.address().as_slice())),
        burn,
        Fr::from(50),
    ))?;

    // the ASP approves the deposit, and the true root is proved
    let mut approvals = vec![Fr::from(0); burn_index + 1];
    approvals[burn_index] = asp_leaf(Fr::from(burn_index as u64));
    let (asp_root, asp_path) = merkle_path(&approvals, burn_index);
    let asp_root = u256(asp_root);
    mined(v.publishAspRoot(asp_root).send().await?).await?;
    let root = u256(merkle_path(&leaves, 0).0);
    let state = RootState {
        index: size,
        hashChain: ledger.hashChain().call().await?,
        root,
    };
    mined(
        ledger
            .proveRootTransition(state, NovaDeciderProof::default())
            .send()
            .await?,
    )
    .await?;
    let start = Instant::now();
    loop {
        let latest = indexer.status().await?["latest_root"].clone();
        if latest["index"].as_u64() == Some(size) && latest["matches"] == true {
            break;
        }
        ensure!(
            start.elapsed() < WAIT,
            "the indexer never matched the root: {latest}"
        );
        tokio::time::sleep(Duration::from_millis(200)).await;
    }
    println!("ok: proved the root over {size} commitments");

    let path = |i: usize| merkle_path(&leaves, i).1.map(u256);
    let public = |asp: U256| Transact {
        tokenId: n(TOKEN_ID),
        chainId: chain,
        commitmentRoot: root,
        aspRoot: asp,
        ..Default::default()
    };

    // T1: the burn deposit and note A, 25 withdrawn to a fresh address, the rest to two notes
    let recipient = Address::repeat_byte(0x77);
    let w = JoinSplit {
        entropy: n(0),
        in0_is_burn: n(1),
        in1_is_dummy: n(0),
        in_note0_value: n(0),
        in_note0_salt: n(0),
        in_note1_value: n(notes[0].0),
        in_note1_salt: n(notes[0].1),
        burn_salt: n(burn_salt),
        burn_transfer_from: U256::from_be_slice(owner.address().as_slice()),
        burn_transfer_value: n(50),
        withdraw_recipient_private: U256::from_be_slice(recipient.as_slice()),
        withdraw_amount_private: n(25),
        withdraw_intent_private: n(0),
        out_note1_public_key: u256(pk),
        out_note1_value: n(35),
        out_note1_salt: n(5),
        out_note2_public_key: u256(pk),
        out_note2_value: n(20),
        out_note2_salt: n(6),
        auth_key0: auth_key,
        auth_key1: auth_key,
        nullifying_key0: u256(keys.nullifying_key),
        nullifying_key1: u256(keys.nullifying_key),
        signature0: Signature::default(),
        signature1: Signature::default(),
        commitment_index0: n(burn_index as u64),
        commitment_index1: n(index[0] as u64),
        in0_merkle_siblings: path(burn_index),
        in1_merkle_siblings: path(index[0]),
        in0_asp_siblings: asp_path.map(u256),
    };
    let s1 = transact_statement(&public(asp_root), &w).map_err(anyhow::Error::msg)?;
    let mut w = w;
    w.signature0 = check::sign(keys.auth_secret, transact_message(&s1));
    w.signature1 = w.signature0;
    let w1 = serde_json::to_vec(&w)?;
    let mut tampered = s1.clone();
    tampered.noteHash1 += n(1);
    let attestation = a.attest("/transact", &s1, &w1).await?;
    a.expect(
        "/transact",
        &tampered,
        &w1,
        400,
        "a statement the witness does not prove",
    )
    .await?;
    let mut tampered = s1.clone();
    tampered.commitmentRoot = empty_root;
    a.expect(
        "/transact",
        &tampered,
        &w1,
        400,
        "a root proved on chain but not derived by the indexer",
    )
    .await?;
    let mut tampered = s1.clone();
    tampered.chainId += n(1);
    a.expect("/transact", &tampered, &w1, 400, "another chain")
        .await?;
    // B's Chainalysis is down: retry, then the Blocklist alone decides
    b.expect(
        "/transact",
        &s1,
        &w1,
        503,
        "the recipient while Chainalysis is down for less than FALLBACK_SECS",
    )
    .await?;
    // C has found Chainalysis down since it started, so after this for longer than FALLBACK_SECS: its first screening
    // of the recipient falls back
    tokio::time::sleep(Duration::from_secs(
        env("FALLBACK_SECS")?.parse::<u64>()? + 1,
    ))
    .await;
    let from_c = c.attest("/transact", &s1, &w1).await?;
    ensure!(from_c == attestation, "deterministic signatures differ");
    println!("ok: with Chainalysis down for FALLBACK_SECS the Blocklist decides at once");
    mined(v.transact(request(size, &s1, attestation)).send().await?).await?;
    let got = token.balanceOf(recipient).call().await?;
    ensure!(got == n(25), "the recipient got {got}");
    println!("ok: transact with a withdrawal accepted on chain");

    // T2: note B alone, a private transfer: nothing to screen, so B answers at once
    (w.in0_is_burn, w.in1_is_dummy, w.entropy) = (n(0), n(1), n(99));
    (w.burn_salt, w.burn_transfer_from, w.burn_transfer_value) = (n(0), n(0), n(0));
    (w.in_note0_value, w.in_note0_salt) = (n(notes[1].0), n(notes[1].1));
    (w.in_note1_value, w.in_note1_salt) = (n(0), n(0));
    (w.commitment_index0, w.commitment_index1) = (n(index[1] as u64), n(0));
    w.in0_merkle_siblings = path(index[1]);
    w.in1_merkle_siblings = [U256::ZERO; TREE_HEIGHT];
    w.in0_asp_siblings = [U256::ZERO; TREE_HEIGHT];
    (w.withdraw_amount_private, w.withdraw_recipient_private) = (n(0), n(0));
    (w.out_note1_value, w.out_note2_value) = (n(notes[1].0), n(0));
    let s2 = transact_statement(&public(asp_root), &w).map_err(anyhow::Error::msg)?;
    w.signature0 = check::sign(keys.auth_secret, transact_message(&s2));
    w.signature1 = Signature::default();
    let attestation = b.attest("/transact", &s2, &serde_json::to_vec(&w)?).await?;
    mined(v.transact(request(size, &s2, attestation)).send().await?).await?;
    println!("ok: private transfer accepted on chain");

    // merge notes C and D into one
    let inputs = [2, 3].map(|k| Input {
        auth_key,
        nullifying_key: u256(keys.nullifying_key),
        commitment_index: n(index[k] as u64),
        commitment_siblings: path(index[k]),
        note_value: n(notes[k].0),
        note_salt: n(notes[k].1),
        ..Default::default()
    });
    let mut w = MergeWitness {
        inputs: inputs.to_vec(),
        out_public_key: u256(pk),
        out_salt: n(7),
    };
    let mut s3 = Merge {
        tokenId: n(TOKEN_ID),
        chainId: chain,
        commitmentRoot: root,
        aspRoot: asp_root,
        ..Default::default()
    };
    (s3.nullifiers, s3.noteHash) = merge_outputs(&s3, &w).map_err(anyhow::Error::msg)?;
    let signature = check::sign(
        keys.auth_secret,
        merge_message(&s3, &w).map_err(anyhow::Error::msg)?,
    );
    for input in &mut w.inputs {
        input.signature = signature;
    }
    let attestation = a.attest("/merge", &s3, &serde_json::to_vec(&w)?).await?;
    let r = MergeRequest {
        rootIndex: size,
        tokenId: s3.tokenId,
        commitmentRoot: s3.commitmentRoot,
        aspRoot: s3.aspRoot,
        noteHash: s3.noteHash,
        fee: s3.fee,
        feeRecipient: s3.feeRecipient,
        nullifiers: s3.nullifiers.clone(),
        proof: NovaDeciderProof::default(),
        attestation,
    };
    mined(v.merge(r).send().await?).await?;
    println!("ok: merge accepted on chain");
    Ok(())
}

fn request(root_index: u64, s: &Transact, attestation: Bytes) -> TransactRequest {
    TransactRequest {
        rootIndex: root_index,
        proof: Groth16Proof::default(),
        publicSignals: TransactSignals {
            tokenId: s.tokenId,
            chainId: s.chainId,
            commitmentRoot: s.commitmentRoot,
            aspRoot: s.aspRoot,
            nullifier0: s.nullifier0,
            nullifier1: s.nullifier1,
            withdrawRecipient: s.withdrawRecipient,
            withdrawAmount: s.withdrawAmount,
            withdrawIntent: s.withdrawIntent,
            noteHash1: s.noteHash1,
            noteHash2: s.noteHash2,
        },
        attestation,
    }
}
