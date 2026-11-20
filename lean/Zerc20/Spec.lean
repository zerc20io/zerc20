import Zerc20.Field

/-!
# What the circuits prove

The protocol objects (keys, nullifiers, notes, leaves, the commitment tree) and the statement each
circuit proves, over an abstract family of hash functions. `Hashes` keeps Poseidon, SHA-256 and the
Schnorr check abstract here, so the protocol proofs depend only on the properties a run assumes of
them; `Main` plugs in the concrete functions the gadgets are proved to compute.

Each circuit's `Spec` is exactly what its constraints imply about its public signals and the
witness parts the protocol needs: the gadget-level theorems prove the constraints imply `Spec`
(soundness) and that every `Spec` witness extends to a satisfying assignment (completeness).
-/

namespace Zerc20

/-! ## Constants shared by the circuits and the contracts -/

/-- Depth of the commitment tree and of the ASP tree. -/
def DEPTH : ℕ := 32

/-- Exclusive bound of every amount, and of the hash chain. -/
def AMOUNT_BOUND : ℕ := 2 ^ 248

def ADDRESS_BOUND : ℕ := 2 ^ 160
def TOKEN_BOUND : ℕ := 2 ^ 32
def CHAIN_BOUND : ℕ := 2 ^ 64

/-- A burn digest's proof of work: its top 16 of 254 bits are zero. -/
def POW_BOUND : ℕ := 2 ^ 238

/-- `Protocol.TRANSFER_TAG`, the selector of `Transfer(address,address,uint256)`. -/
def TRANSFER_TAG : ℕ := 3723645613

/-- `Protocol.NOTE_HASH_TAG`. -/
def NOTE_HASH_TAG : ℕ := 2023696107

/-- `field0` of a leaf: `tag << 32 | tokenId`. -/
def field0 (tag token : ℕ) : ℕ := tag * 2 ^ 32 + token

/-! Domain tags: `sha256("zerc20-<name>") mod r`, as `zkp/circom/lib/constants.circom` lists them. -/

def DOMAIN_NOTE : F := 12890024175661825764581542883111592339070511154523346722771315793398079606973
def DOMAIN_PUBLIC_KEY : F := 12748143626193170683619257575461114475162050184551511165632901980951779591788
def DOMAIN_NULLIFYING_KEY : F := 17471194487513808174444331798961284844045019683771872456746961298409210755086
def DOMAIN_NULLIFIER : F := 21656625071485835455144987912439041855442440977080724417184138235324194035747
def DOMAIN_DUMMY_NULLIFIER : F := 7044432322484129783600934309074221576946257299516531409248588859126398254720
def DOMAIN_BURN : F := 7812678369084671832725575743163273348609229243038681297431930412876960276650
def DOMAIN_ASP_LEAF : F := 20989222074995585771835793404421254795991252548608321040973959344582939809523
def DOMAIN_AUTH_KEY : F := 10225447400557743590985446737842398671604622534850121808755795315749324473275
def DOMAIN_MERGE_AUTH : F := 16474997453874937243622623791033663138618536810477243309426195930856928586225

/-! ## The hash functions -/

/-- The primitives the protocol is built from. -/
structure Hashes where
  /-- Poseidon over `x.length + 1` lanes, the output lane 0 after one permutation. -/
  H : List F → F
  /-- `SHA256(be32 prev ‖ be32 v₁ ‖ …) mod 2^248`: `CommitmentLedger._next`,
  `Verifier._nullifierChain` and `hash_chain_var` all compute it. -/
  hc : ℕ → List ℕ → ℕ
  hc_lt : ∀ c vs, hc c vs < AMOUNT_BOUND
  /-- A valid owner signature on a merge message under an auth key `(x, y)`: the Schnorr check of
  `auth::verify_var`. -/
  sigOK : F × F → F → Prop

variable (h : Hashes)

/-! ## Keys, notes and nullifiers (`zkp/circom/lib/primitives.circom`) -/

def nullifyingKey (sk : F) : F := h.H [DOMAIN_NULLIFYING_KEY, sk]
def publicKey (akh nk : F) : F := h.H [DOMAIN_PUBLIC_KEY, akh, nk]
def authKeyHash (ak : F × F) : F := h.H [DOMAIN_AUTH_KEY, ak.1, ak.2]
def nullifier (chain idx nk : F) : F := h.H [DOMAIN_NULLIFIER, chain, idx, nk, 0]
def dummyNullifier (chain entropy : F) : F := h.H [DOMAIN_DUMMY_NULLIFIER, chain, entropy + 1]
def noteHash (chain pk value token salt : F) : F := h.H [DOMAIN_NOTE, chain, pk, value, token, salt]
def burnDigest (chain pk salt : F) : F := h.H [DOMAIN_BURN, chain, pk, salt, 0]
def aspLeaf (idx : F) : F := h.H [DOMAIN_ASP_LEAF, idx]
def mergeMessage (nfChain pk salt fee recipient : F) : F :=
  h.H [DOMAIN_MERGE_AUTH, nfChain, pk, salt, fee, recipient]

/-- The address a burn digest pays to: its low 160 bits. -/
def addressOf (digest : F) : ℕ := digest.val % ADDRESS_BOUND

/-! ## Ledger leaves (`zkp/circom/lib/commitments.circom`, `CommitmentLedger`) -/

/-- A ledger entry, as `ZERC20` commits it: a transfer between two real accounts, or a note hash. -/
inductive Leaf
  | transfer (token : ℕ) (src dst : ℕ) (value : ℕ)
  | note (token : ℕ) (hash : F)
  deriving DecidableEq

namespace Leaf

def token : Leaf → ℕ
  | transfer t .. => t
  | note t _ => t

/-- The four uint256 fields the ledger hashes and the root circuit opens. -/
def words : Leaf → List ℕ
  | transfer t a b v => [field0 TRANSFER_TAG t, a, b, v]
  | note t nh => [field0 NOTE_HASH_TAG t, nh.val, 0, 0]

/-- The commitment-tree leaf: Poseidon of the four fields. -/
def hash (l : Leaf) : F := h.H (l.words.map (↑))

end Leaf

/-- The ledger's hash chain after `ls`, from zero. -/
def chainOf (ls : List Leaf) : ℕ := ls.foldl (fun c l => h.hc c l.words) 0

/-! ## The commitment tree (`MerkleRoot`, `merkle_root_var`) -/

/-- Node `j` at height `k` of the depth-32 tree whose leaves are `ls`, empty slots being zero. -/
def node (ls : List F) : ℕ → ℕ → F
  | 0, j => ls.getD j 0
  | k + 1, j => h.H [node ls k (2 * j), node ls k (2 * j + 1)]

def treeRoot (ls : List F) : F := node h ls DEPTH 0

/-- The root a Merkle path computes: at level `k`, bit `k` of `idx` set means the running value is
the right child. -/
def pathRoot (leaf : F) (idx : ℕ) (sib : Fin DEPTH → F) : ℕ → F
  | 0 => leaf
  | k + 1 =>
    if hk : k < DEPTH then
      if idx / 2 ^ k % 2 = 1 then h.H [sib ⟨k, hk⟩, pathRoot leaf idx sib k]
      else h.H [pathRoot leaf idx sib k, sib ⟨k, hk⟩]
    else pathRoot leaf idx sib k

def merkleRoot (leaf : F) (idx : ℕ) (sib : Fin DEPTH → F) : F := pathRoot h leaf idx sib DEPTH

/-- The index of the other child of node `m`'s parent. -/
def sibIndex (m : ℕ) : ℕ := if m % 2 = 1 then m - 1 else m + 1

/-- The siblings of slot `idx` in the tree of `ls`. -/
def siblings (ls : List F) (idx : ℕ) : Fin DEPTH → F := fun k => node h ls k (sibIndex (idx / 2 ^ k.val))

/-- The pair a Merkle path hashes at level `k`. -/
def pathPair (leaf : F) (idx : ℕ) (sib : Fin DEPTH → F) (k : Fin DEPTH) : List F :=
  if idx / 2 ^ k.val % 2 = 1 then [sib k, pathRoot h leaf idx sib k] else [pathRoot h leaf idx sib k, sib k]

/-- Every Poseidon input of a Merkle path. -/
def pathCalls (leaf : F) (idx : ℕ) (sib : Fin DEPTH → F) : Set (List F) :=
  Set.range (pathPair h leaf idx sib)

/-- Every Poseidon input of the tree of `ls`. -/
def treeCalls (ls : List F) : Set (List F) :=
  {x | ∃ k < DEPTH, ∃ j, x = [node h ls k (2 * j), node h ls k (2 * j + 1)]}

/-! ## JoinSplit (`zkp/circom/main/joinsplit.circom`) -/

namespace JS

/-- The public signals, in the order the verifier passes them. -/
structure Pub where
  nf0 : F
  nf1 : F
  recipient : F
  amount : F
  intent : F
  nh1 : F
  nh2 : F
  token : F
  chain : F
  root : F
  asp : F

/-- A note opening. -/
structure Opening where
  pk : F
  value : F
  salt : F

def Opening.zero : Opening := ⟨0, 0, 0⟩

/-- The witness parts the statement is about. -/
structure Wit where
  in0IsBurn : Bool
  in1IsDummy : Bool
  entropy : F
  note0 : Opening
  note1 : Opening
  burnPk : F
  burnSalt : F
  burnFrom : F
  burnValue : F
  out1 : Opening
  out2 : Opening
  sk0 : F
  sk1 : F
  akh0 : F
  akh1 : F
  idx0 : F
  idx1 : F
  sib0 : Fin DEPTH → F
  sib1 : Fin DEPTH → F
  aspSib : Fin DEPTH → F

variable {h}

def nk0 (w : Wit) : F := nullifyingKey h w.sk0
def nk1 (w : Wit) : F := nullifyingKey h w.sk1
def pk0 (w : Wit) : F := publicKey h w.akh0 (nk0 (h := h) w)
def pk1 (w : Wit) : F := publicKey h w.akh1 (nk1 (h := h) w)

/-- The leaf `in0` opens. -/
def leaf0 (h : Hashes) (x : Pub) (w : Wit) : F :=
  if w.in0IsBurn then
    h.H [↑(field0 TRANSFER_TAG x.token.val), w.burnFrom,
      ↑(addressOf (burnDigest h x.chain w.burnPk w.burnSalt)), w.burnValue]
  else
    h.H [↑(field0 NOTE_HASH_TAG x.token.val),
      noteHash h x.chain w.note0.pk w.note0.value x.token w.note0.salt, 0, 0]

def leaf1 (h : Hashes) (x : Pub) (w : Wit) : F :=
  h.H [↑(field0 NOTE_HASH_TAG x.token.val),
    noteHash h x.chain w.note1.pk w.note1.value x.token w.note1.salt, 0, 0]

/-- The value `in0` brings. -/
def value0 (w : Wit) : ℕ := if w.in0IsBurn then w.burnValue.val else w.note0.value.val

def value1 (w : Wit) : ℕ := if w.in1IsDummy then 0 else w.note1.value.val

/-- What a JoinSplit proof proves. -/
structure Spec (h : Hashes) (x : Pub) (w : Wit) : Prop where
  token_lt : x.token.val < TOKEN_BOUND
  chain_lt : x.chain.val < CHAIN_BOUND
  amount_lt : x.amount.val < AMOUNT_BOUND
  burnValue_lt : w.burnValue.val < AMOUNT_BOUND
  note0_lt : w.note0.value.val < AMOUNT_BOUND
  note1_lt : w.note1.value.val < AMOUNT_BOUND
  out1_lt : w.out1.value.val < AMOUNT_BOUND
  out2_lt : w.out2.value.val < AMOUNT_BOUND
  recipient_lt : x.recipient.val < ADDRESS_BOUND
  burnFrom_lt : w.burnFrom.val < ADDRESS_BOUND
  idx0_lt : w.idx0.val < 2 ^ DEPTH
  idx1_lt : w.idx1.val < 2 ^ DEPTH
  /-- `in0` as a note: the owner's key opens it; the burn fields are pinned to zero. -/
  note0 : w.in0IsBurn = false →
    w.note0.pk = pk0 (h := h) w ∧ w.burnPk = 0 ∧ w.burnSalt = 0 ∧ w.burnFrom = 0 ∧ w.burnValue = 0
  /-- `in0` as a burn deposit: the owner's key derives the burn address with its proof of work, the
  deposit is non-zero, and the ASP approves its position; the note fields are pinned to zero. -/
  burn0 : w.in0IsBurn = true →
    w.burnPk = pk0 (h := h) w ∧ w.burnValue ≠ 0 ∧
    (burnDigest h x.chain w.burnPk w.burnSalt).val < POW_BOUND ∧
    merkleRoot h (aspLeaf h w.idx0) w.idx0.val w.aspSib = x.asp ∧ w.note0 = Opening.zero
  member0 : merkleRoot h (leaf0 h x w) w.idx0.val w.sib0 = x.root
  nf0 : x.nf0 = nullifier h x.chain w.idx0 (nk0 (h := h) w)
  /-- `in1` as a real note. -/
  real1 : w.in1IsDummy = false →
    w.note1.pk = pk1 (h := h) w ∧ merkleRoot h (leaf1 h x w) w.idx1.val w.sib1 = x.root ∧
    x.nf1 = nullifier h x.chain w.idx1 (nk1 (h := h) w)
  /-- `in1` as padding: a fresh dummy nullifier, and a canonical zero opening. -/
  dummy1 : w.in1IsDummy = true →
    x.nf1 = dummyNullifier h x.chain w.entropy ∧ w.note1 = Opening.zero ∧ w.idx1 = 0 ∧ w.sib1 = 0
  nf_ne : x.nf0 ≠ x.nf1
  nh1 : x.nh1 = noteHash h x.chain w.out1.pk w.out1.value x.token w.out1.salt
  nh2 : x.nh2 = noteHash h x.chain w.out2.pk w.out2.value x.token w.out2.salt
  /-- Conservation over amounts below `2^248`, so nothing wraps. -/
  conserve : value0 w + value1 w = x.amount.val + w.out1.value.val + w.out2.value.val
  /-- An inactive withdrawal leg is canonical. -/
  noWithdraw : x.amount = 0 → x.recipient = 0 ∧ x.intent = 0

end JS

/-! ## RageExit (`zkp/circom/main/rageexit.circom`) -/

namespace RE

structure Pub where
  nf : F
  chain : F
  idx : F
  address : F

structure Wit where
  sk : F
  akh : F
  salt : F

/-- What a RageExit proof proves: the deposit's burn address derives from the prover's key, and the
nullifier is the one JoinSplit's `in0` would publish for that position. -/
structure Spec (h : Hashes) (x : Pub) (w : Wit) : Prop where
  chain_lt : x.chain.val < CHAIN_BOUND
  idx_lt : x.idx.val < 2 ^ DEPTH
  pow : (burnDigest h x.chain (publicKey h w.akh (nullifyingKey h w.sk)) w.salt).val < POW_BOUND
  address : x.address =
    ↑(addressOf (burnDigest h x.chain (publicKey h w.akh (nullifyingKey h w.sk)) w.salt))
  nf : x.nf = nullifier h x.chain x.idx (nullifyingKey h w.sk)

end RE

/-! ## Root step (`zkp/src/root.rs`) -/

namespace Root

/-- `[index, hash_chain, root]`. -/
structure Z where
  index : F
  chain : F
  root : F

structure Wit where
  fields : Fin 4 → F
  sib : Fin DEPTH → F

def leaf (h : Hashes) (w : Wit) : F := h.H (List.ofFn w.fields)

/-- The state after a step: the next index, the chain over the step's fields, and the root with
the step's leaf in the slot. -/
def next (h : Hashes) (z : Z) (w : Wit) : Z :=
  ⟨z.index + 1, ↑(h.hc z.chain.val (List.ofFn fun i => (w.fields i).val)),
    merkleRoot h (leaf h w) z.index.val w.sib⟩

/-- One root step: the slot at `index` is empty in `root`, the new root holds the leaf of `fields`
there, and the hash chain absorbs `fields`. -/
structure Spec (h : Hashes) (z : Z) (w : Wit) (z' : Z) : Prop where
  index_lt : z.index.val < 2 ^ DEPTH
  chain_lt : z.chain.val < AMOUNT_BOUND
  empty : merkleRoot h 0 z.index.val w.sib = z.root
  next : z' = next h z w

end Root

/-! ## Merge step (`zkp/src/merge.rs`) -/

namespace Merge

/-- `[token_id, chain_id, commitment_root, asp_root, nullifier_chain, signed_chain, note_hash,
remaining, fee, fee_recipient]`. -/
structure Z where
  token : F
  chain : F
  root : F
  asp : F
  nfChain : F
  signedChain : F
  noteHash : F
  remaining : F
  fee : F
  feeRecipient : F

structure Wit where
  isBurn : Bool
  ak : F × F
  nk : F
  idx : F
  sib : Fin DEPTH → F
  noteValue : F
  noteSalt : F
  burnSalt : F
  burnFrom : F
  burnValue : F
  aspSib : Fin DEPTH → F
  outPk : F
  outSalt : F
  prevSum : F

variable {h}

def pk (w : Wit) : F := publicKey h (authKeyHash h w.ak) w.nk

def leaf (h : Hashes) (z : Z) (w : Wit) : F :=
  if w.isBurn then
    h.H [↑(field0 TRANSFER_TAG z.token.val), w.burnFrom,
      ↑(addressOf (burnDigest h z.chain (pk (h := h) w) w.burnSalt)), w.burnValue]
  else
    h.H [↑(field0 NOTE_HASH_TAG z.token.val),
      noteHash h z.chain (pk (h := h) w) w.noteValue z.token w.noteSalt, 0, 0]

def value (w : Wit) : F := if w.isBurn then w.burnValue else w.noteValue

def nf (h : Hashes) (z : Z) (w : Wit) : F := nullifier h z.chain w.idx w.nk

/-- The output note's value after this step: the fee comes off at the last one. -/
def out (z : Z) (w : Wit) : F :=
  if z.remaining = 1 then w.prevSum + value w - z.fee else w.prevSum + value w

/-- The state after a step: the nullifier chain absorbs the input's nullifier, the output note
grows, and one step fewer remains. -/
def next (h : Hashes) (z : Z) (w : Wit) : Z :=
  { z with
    nfChain := ↑(h.hc z.nfChain.val [(nf h z w).val])
    noteHash := noteHash h z.chain w.outPk (out z w) z.token w.outSalt
    remaining := z.remaining - 1 }

/-- One merge step: spend one input the signer owns, chain its nullifier, and grow the output note. -/
structure Spec (h : Hashes) (z : Z) (w : Wit) (z' : Z) : Prop where
  token_lt : z.token.val < TOKEN_BOUND
  chain_lt : z.chain.val < CHAIN_BOUND
  noteValue_lt : w.noteValue.val < AMOUNT_BOUND
  burnFrom_lt : w.burnFrom.val < ADDRESS_BOUND
  burnValue_lt : w.burnValue.val < AMOUNT_BOUND
  idx_lt : w.idx.val < 2 ^ DEPTH
  burn : w.isBurn = true →
    w.burnValue ≠ 0 ∧ (burnDigest h z.chain (pk (h := h) w) w.burnSalt).val < POW_BOUND ∧
    merkleRoot h (aspLeaf h w.idx) w.idx.val w.aspSib = z.asp
  member : merkleRoot h (leaf h z w) w.idx.val w.sib = z.root
  nfChain_lt : z.nfChain.val < AMOUNT_BOUND
  /-- The input's owner signed the merge: the chain of its nullifiers, the output note's owner and
  salt, and the fee. -/
  signed : h.sigOK w.ak (mergeMessage h z.signedChain w.outPk w.outSalt z.fee z.feeRecipient)
  first : z.noteHash = 0 → w.prevSum = 0
  later : z.noteHash ≠ 0 → noteHash h z.chain w.outPk w.prevSum z.token w.outSalt = z.noteHash
  out_lt : (out z w).val < AMOUNT_BOUND
  next : z' = next h z w

end Merge

/-- `n` steps of a step relation. -/
inductive Chain {Z W : Type} (S : Z → W → Z → Prop) : Z → List W → Z → Prop
  | nil (z : Z) : Chain S z [] z
  | cons {z z' z'' : Z} {w : W} {ws : List W} : S z w z' → Chain S z' ws z'' → Chain S z (w :: ws) z''

/-! ## What each circuit hashes

The run hypotheses ask Poseidon to be collision-free on the inputs a run actually evaluates; these
are a circuit's, inactive branches included, since the circuit computes them too.
-/

namespace JS

def calls (h : Hashes) (x : Pub) (w : Wit) : Set (List F) :=
  {[DOMAIN_NULLIFYING_KEY, w.sk0], [DOMAIN_NULLIFYING_KEY, w.sk1],
    [DOMAIN_PUBLIC_KEY, w.akh0, nk0 (h := h) w], [DOMAIN_PUBLIC_KEY, w.akh1, nk1 (h := h) w],
    [DOMAIN_NOTE, x.chain, w.note0.pk, w.note0.value, x.token, w.note0.salt],
    [DOMAIN_NOTE, x.chain, w.note1.pk, w.note1.value, x.token, w.note1.salt],
    [DOMAIN_NOTE, x.chain, w.out1.pk, w.out1.value, x.token, w.out1.salt],
    [DOMAIN_NOTE, x.chain, w.out2.pk, w.out2.value, x.token, w.out2.salt],
    [DOMAIN_BURN, x.chain, w.burnPk, w.burnSalt, 0],
    [↑(field0 TRANSFER_TAG x.token.val), w.burnFrom,
      ↑(addressOf (burnDigest h x.chain w.burnPk w.burnSalt)), w.burnValue],
    [↑(field0 NOTE_HASH_TAG x.token.val),
      noteHash h x.chain w.note0.pk w.note0.value x.token w.note0.salt, 0, 0],
    [↑(field0 NOTE_HASH_TAG x.token.val),
      noteHash h x.chain w.note1.pk w.note1.value x.token w.note1.salt, 0, 0],
    [DOMAIN_ASP_LEAF, w.idx0],
    [DOMAIN_NULLIFIER, x.chain, w.idx0, nk0 (h := h) w, 0],
    [DOMAIN_NULLIFIER, x.chain, w.idx1, nk1 (h := h) w, 0],
    [DOMAIN_DUMMY_NULLIFIER, x.chain, w.entropy + 1]} ∪
  pathCalls h (leaf0 h x w) w.idx0.val w.sib0 ∪ pathCalls h (leaf1 h x w) w.idx1.val w.sib1 ∪
  pathCalls h (aspLeaf h w.idx0) w.idx0.val w.aspSib

end JS

namespace RE

def pk (h : Hashes) (w : Wit) : F := publicKey h w.akh (nullifyingKey h w.sk)

def calls (h : Hashes) (x : Pub) (w : Wit) : Set (List F) :=
  {[DOMAIN_NULLIFYING_KEY, w.sk], [DOMAIN_PUBLIC_KEY, w.akh, nullifyingKey h w.sk],
    [DOMAIN_BURN, x.chain, pk h w, w.salt, 0],
    [DOMAIN_NULLIFIER, x.chain, x.idx, nullifyingKey h w.sk, 0]}

end RE

namespace Root

def calls (h : Hashes) (z : Z) (w : Wit) : Set (List F) :=
  {List.ofFn w.fields} ∪ pathCalls h 0 z.index.val w.sib ∪ pathCalls h (leaf h w) z.index.val w.sib

/-- The SHA-256 input of a step. -/
def shaCall (z : Z) (w : Wit) : ℕ × List ℕ := (z.chain.val, List.ofFn fun i => (w.fields i).val)

def callsAlong (h : Hashes) : Z → List Wit → Set (List F)
  | _, [] => ∅
  | z, w :: ws => calls h z w ∪ callsAlong h (next h z w) ws

def shaAlong (h : Hashes) : Z → List Wit → Set (ℕ × List ℕ)
  | _, [] => ∅
  | z, w :: ws => {shaCall z w} ∪ shaAlong h (next h z w) ws

end Root

namespace Merge

def calls (h : Hashes) (z : Z) (w : Wit) : Set (List F) :=
  {[DOMAIN_AUTH_KEY, w.ak.1, w.ak.2], [DOMAIN_PUBLIC_KEY, authKeyHash h w.ak, w.nk],
    [DOMAIN_NOTE, z.chain, pk (h := h) w, w.noteValue, z.token, w.noteSalt],
    [↑(field0 NOTE_HASH_TAG z.token.val),
      noteHash h z.chain (pk (h := h) w) w.noteValue z.token w.noteSalt, 0, 0],
    [DOMAIN_BURN, z.chain, pk (h := h) w, w.burnSalt, 0],
    [↑(field0 TRANSFER_TAG z.token.val), w.burnFrom,
      ↑(addressOf (burnDigest h z.chain (pk (h := h) w) w.burnSalt)), w.burnValue],
    [DOMAIN_ASP_LEAF, w.idx],
    [DOMAIN_NULLIFIER, z.chain, w.idx, w.nk, 0],
    [DOMAIN_MERGE_AUTH, z.signedChain, w.outPk, w.outSalt, z.fee, z.feeRecipient],
    [DOMAIN_NOTE, z.chain, w.outPk, w.prevSum, z.token, w.outSalt],
    [DOMAIN_NOTE, z.chain, w.outPk, out z w, z.token, w.outSalt]} ∪
  pathCalls h (aspLeaf h w.idx) w.idx.val w.aspSib ∪ pathCalls h (leaf h z w) w.idx.val w.sib

def shaCall (h : Hashes) (z : Z) (w : Wit) : ℕ × List ℕ := (z.nfChain.val, [(nf h z w).val])

def callsAlong (h : Hashes) : Z → List Wit → Set (List F)
  | _, [] => ∅
  | z, w :: ws => calls h z w ∪ callsAlong h (next h z w) ws

def shaAlong (h : Hashes) : Z → List Wit → Set (ℕ × List ℕ)
  | _, [] => ∅
  | z, w :: ws => {shaCall h z w} ∪ shaAlong h (next h z w) ws

end Merge

end Zerc20
