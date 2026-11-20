import Zerc20.Spec
import Mathlib.Data.Finsupp.Basic

/-!
# The contracts

`ZERC20`, `CommitmentLedger` and `Verifier`, one Lean function per Solidity function under the same
name. Each returns `none` exactly where the Solidity function reverts; consecutive `require`s are
merged into one `guard`, which reverts in the same cases. Every action is atomic: each function makes its external calls last (the
underlying's transfer), and all of them are `nonReentrant`.

A proof verifier accepts exactly the statements its circuit's constraints can satisfy, so an action
carries the witness that knowledge soundness extracts, and the contract step checks the circuit's
`Spec` on it. EIP-712 attestations are an oracle the safety theorems leave arbitrary.

Left out: upgrades and verifier swaps (the theorems are about this implementation and these
verifiers), allowances and signatures behind a transfer (any party may move any balance, which only
gives the adversary more power), and the deposit-address clones, which are ordinary callers of
`wrap`. A `ghost` part of the state records what the proofs need about witnesses: the opening of
every note, the positions every spend opened, and the merge messages the owner signed.
-/

namespace Zerc20

open scoped Classical

noncomputable section

abbrev Addr := ℕ

def UINT256 : ℕ := 2 ^ 256

/-- `type(uint64).max`: the bound outside an emergency. -/
def NO_BOUND : ℕ := 2 ^ 64 - 1

def TREE_SIZE : ℕ := 2 ^ DEPTH

/-- The deployment's fixed parameters. -/
structure Env where
  chainId : ℕ
  /-- The Verifier's address, where fees are held. -/
  verifier : Addr
  /-- `Protocol.UNWRAP_INTENT`. -/
  unwrapIntent : ℕ
  chainId_lt : chainId < CHAIN_BOUND
  verifier_ne : verifier ≠ 0
  verifier_lt : verifier < ADDRESS_BOUND
  unwrapIntent_ne : unwrapIntent ≠ 0
  unwrapIntent_lt : unwrapIntent < r

/-! ## State -/

structure TokenSt where
  bal : Addr →₀ ℕ
  supply : ℕ
  /-- The underlying the token proxy holds. -/
  underlying : ℕ

def TokenSt.empty : TokenSt := ⟨0, 0, 0⟩

namespace TokenSt

/-- OpenZeppelin `ERC20._update`'s balance change: `src = 0` mints, `dst = 0` burns. -/
def move (tk : TokenSt) (src dst : Addr) (v : ℕ) : TokenSt :=
  let tk := if src = 0 then { tk with supply := tk.supply + v }
    else { tk with bal := tk.bal.update src (tk.bal src - v) }
  if dst = 0 then { tk with supply := tk.supply - v }
  else { tk with bal := tk.bal.update dst (tk.bal dst + v) }

/-- Where `ERC20._update` reverts: a mint overflowing the supply, or a balance too small. -/
def canMove (tk : TokenSt) (src : Addr) (v : ℕ) : Prop :=
  if src = 0 then tk.supply + v < UINT256 else v ≤ tk.bal src

end TokenSt

structure RootSt where
  index : ℕ
  chain : ℕ
  root : F

structure LedgerSt where
  leaves : List Leaf
  /-- `hashChain`, the live head. -/
  head : ℕ
  /-- Zero marks an empty slot. -/
  checkpoints : ℕ → ℕ
  rootState : RootSt
  /-- The era a root was proved in at an index, zero for never. -/
  provedIn : ℕ → F → ℕ
  era : ℕ
  bound : ℕ
  eraEnd : ℕ → ℕ

/-- `FeeSchedule.Schedule`: `(minAmount, feeBps)` tiers. -/
structure FeeSch where
  recipient : Addr
  tiers : List (ℕ × ℕ)

def FeeSch.none : FeeSch := ⟨0, []⟩

structure VerifierSt where
  used : Set F
  paused : Bool
  tokenPaused : ℕ → Bool
  aspPublisher : Addr
  aspEpoch : ℕ
  aspRootEpoch : ℕ → ℕ
  attesters : Set Addr
  fees : ℕ → FeeSch
  accrued : ℕ → Addr → ℕ

structure Ghost where
  /-- The opening of the note at each ledger index, from the witness that committed it. -/
  notes : ℕ → Option JS.Opening
  /-- The ledger positions spends opened, in order. -/
  spent : List ℕ
  /-- The merge messages the owner signed. -/
  signed : List F

structure State where
  /-- Registered tokens by id: `ZERC20Factory.tokenById`. -/
  tokens : ℕ → Option TokenSt
  ledger : LedgerSt
  verifier : VerifierSt
  blocked : Set Addr
  ghost : Ghost

variable (h : Hashes) (E : Env)

def State.init (publisher : Addr) : State where
  tokens := fun _ => none
  ledger :=
    { leaves := []
      head := 0
      checkpoints := fun _ => 0
      rootState := ⟨0, 0, treeRoot h []⟩
      provedIn := fun i ρ => if i = 0 ∧ ρ = treeRoot h [] then 1 else 0
      era := 1
      bound := NO_BOUND
      eraEnd := fun _ => 0 }
  verifier :=
    { used := ∅
      paused := false
      tokenPaused := fun _ => false
      aspPublisher := publisher
      aspEpoch := 1
      aspRootEpoch := fun _ => 0
      attesters := ∅
      fees := fun _ => FeeSch.none
      accrued := fun _ _ => 0 }
  blocked := ∅
  ghost := ⟨fun _ => none, [], []⟩

namespace State

variable (s : State)

def setToken (t : ℕ) (tk : TokenSt) : State := { s with tokens := Function.update s.tokens t (some tk) }

/-- The ledger with `l` appended. -/
def append (l : Leaf) : State := { s with ledger := { s.ledger with
  leaves := s.ledger.leaves ++ [l]
  head := h.hc s.ledger.head l.words } }

/-- `Verifier.tokenStopped`. -/
def stopped (t : ℕ) : Prop := s.verifier.paused = true ∨ s.verifier.tokenPaused t = true

/-- `ZERC20._requireNotBlocked`: the zero address and the Verifier are exempt. -/
def notBlocked (a : Addr) : Prop := a = 0 ∨ a = E.verifier ∨ a ∉ s.blocked

/-- `CommitmentLedger._hashChainAt`. -/
def hashChainAt (i : ℕ) : Option ℕ :=
  if s.ledger.leaves.length < i then none
  else if i = s.ledger.leaves.length then some s.ledger.head
  else if i = 0 then some 0
  else if s.ledger.checkpoints i ≠ 0 then some (s.ledger.checkpoints i) else none

/-- `CommitmentLedger._inEra`. -/
def inEra (i : ℕ) (ρ : F) : Prop :=
  s.ledger.provedIn i ρ ≠ 0 ∧
    (s.ledger.provedIn i ρ = s.ledger.era ∨ i ≤ s.ledger.eraEnd (s.ledger.provedIn i ρ))

/-- `CommitmentLedger.provedRoots`. -/
def provedRoots (i : ℕ) (ρ : F) : Prop := i ≤ s.ledger.bound ∧ s.inEra i ρ

/-- `Verifier.aspRootAccepted`. -/
def aspAccepted (a : ℕ) : Prop := s.verifier.aspRootEpoch a = s.verifier.aspEpoch

end State

/-! ## CommitmentLedger -/

namespace CommitmentLedger

/-- `commit`, for the leaves `ZERC20` builds: their fields are always in range (amounts and addresses
are checked before, a note hash is below `r`), and the caller is always the token of their id, so
only the tree's capacity can fail. -/
def commit (l : Leaf) (s : State) : Option State := do
  guard (s.ledger.leaves.length < TREE_SIZE)
  pure (s.append h l)

/-- `reserveHashChain`. -/
def reserveHashChain (s : State) : Option State :=
  if s.ledger.leaves.length = 0 then some s
  else do
    guard (s.ledger.head ≠ 0)
    pure { s with ledger := { s.ledger with
      checkpoints := Function.update s.ledger.checkpoints s.ledger.leaves.length s.ledger.head } }

/-- `verifySegment`: the index of `commits[0]`, if hashing `commits` onto `prev` reaches the chain
at `end_`. -/
def verifySegment (end_ prev : ℕ) (commits : List (List ℕ)) (s : State) : Option ℕ := do
  guard (commits ≠ [])
  guard (commits.length ≤ end_)
  let chain := commits.foldl h.hc prev
  let c ← s.hashChainAt end_
  guard (chain = c)
  pure (end_ - commits.length)

/-- `checkpointBefore`. -/
def checkpointBefore (end_ prev : ℕ) (commits : List (List ℕ)) (s : State) : Option State := do
  let start ← verifySegment h end_ prev commits s
  guard (prev ≠ 0)
  pure { s with ledger := { s.ledger with
    checkpoints := Function.update s.ledger.checkpoints start prev } }

/-- `proveRootTransition`, with `ws` the steps extracted from the accepted Nova proof: an accepted
decider call chains the root spec from the old state to the new (`decider_sound`). -/
def proveRootTransition (new : RootSt) (ws : List Root.Wit) (s : State) : Option State := do
  guard (new.index ≤ TREE_SIZE ∧ new.chain < AMOUNT_BOUND)
  guard (s.ledger.bound = NO_BOUND)
  let old := s.ledger.rootState
  guard (old.index < new.index)
  let c ← s.hashChainAt new.index
  guard (c = new.chain)
  guard (ws.length = new.index - old.index ∧
    Chain (Root.Spec h) ⟨old.index, old.chain, old.root⟩ ws ⟨new.index, new.chain, new.root⟩)
  pure { s with ledger := { s.ledger with
    rootState := new
    provedIn := fun i ρ => if i = new.index ∧ ρ = new.root then s.ledger.era else s.ledger.provedIn i ρ } }

/-- `enterEmergency`, by the owner or a guardian: it only lowers the bound. -/
def enterEmergency (b : ℕ) (s : State) : State :=
  if b < s.ledger.bound then { s with ledger := { s.ledger with bound := b } } else s

/-- `recover`, keeping the root verifier. It restarts no lower than the previous recovery did. -/
def recover (index : ℕ) (root : F) (s : State) : Option State := do
  guard (s.ledger.bound ≠ NO_BOUND)
  guard (s.ledger.eraEnd (s.ledger.era - 1) ≤ index)
  guard (s.inEra index root)
  let c ← s.hashChainAt index
  pure { s with ledger := { s.ledger with
    eraEnd := Function.update s.ledger.eraEnd s.ledger.era index
    era := s.ledger.era + 1
    bound := NO_BOUND
    rootState := ⟨index, c, root⟩ } }

end CommitmentLedger

/-! ## ZERC20 -/

namespace ZERC20

/-- `_update`: OpenZeppelin's balance update behind zERC20's checks, then a `Transfer` leaf for a
non-zero transfer between two real accounts. -/
def update (t : ℕ) (src dst : Addr) (v : ℕ) (s : State) : Option State := do
  let tk ← s.tokens t
  -- Addresses are 160-bit by their Solidity type.
  guard (src < ADDRESS_BOUND ∧ dst < ADDRESS_BOUND)
  guard (¬ s.stopped t ∧ v < AMOUNT_BOUND ∧ s.notBlocked E src ∧ s.notBlocked E dst ∧
    tk.canMove src v)
  let s := s.setToken t (tk.move src dst v)
  if src = 0 ∨ dst = 0 ∨ v = 0 then pure s
  else CommitmentLedger.commit h (Leaf.transfer t src dst v) s

/-- `transfer` (and `transferFrom`, `permit` + `transferFrom`, ERC-3009): OpenZeppelin's
`_transfer` refuses the zero address on either side. -/
def transfer (t : ℕ) (src dst : Addr) (v : ℕ) (s : State) : Option State := do
  guard (src ≠ 0 ∧ dst ≠ 0)
  update h E t src dst v s

/-- `_release`: the token pays out underlying it holds. -/
def release (t : ℕ) (v : ℕ) (s : State) : Option State := do
  let tk ← s.tokens t
  guard (v ≤ tk.underlying)
  pure (s.setToken t { tk with underlying := tk.underlying - v })

/-- `wrap`: mint to the caller and forward, so a deposit to another address is a `Transfer` leaf
with the caller as its sender. -/
def wrap (t : ℕ) (caller receiver : Addr) (v : ℕ) (s : State) : Option State := do
  -- `msg.sender` is never the zero address, which OpenZeppelin's `_mint` and `_burn` refuse.
  guard (caller ≠ 0 ∧ receiver ≠ 0 ∧ v ≠ 0)
  let tk ← s.tokens t
  let s := s.setToken t { tk with underlying := tk.underlying + v }
  let s ← update h E t 0 caller v s
  if receiver ≠ caller then update h E t caller receiver v s else pure s

/-- `unwrap`. -/
def unwrap (t : ℕ) (caller receiver : Addr) (v : ℕ) (s : State) : Option State := do
  guard (caller ≠ 0 ∧ receiver ≠ 0 ∧ v ≠ 0)
  guard (s.notBlocked E receiver)
  let s ← update h E t caller 0 v s
  release t v s

/-- `commitNote`. -/
def commitNote (t : ℕ) (nh : F) (s : State) : Option State :=
  CommitmentLedger.commit h (Leaf.note t nh) s

/-- `payOut`: minted as zERC20, or released as the underlying. -/
def payOut (t : ℕ) (recipient : Addr) (v : ℕ) (asUnderlying : Bool) (s : State) : Option State := do
  guard (recipient ≠ 0 ∧ v ≠ 0)
  if asUnderlying then do
    guard (¬ s.stopped t)
    guard (s.notBlocked E recipient)
    release t v s
  else update h E t 0 recipient v s

end ZERC20

/-- An underlying transfer straight to the token proxy, outside `wrap`. -/
def donate (t v : ℕ) (s : State) : Option State := do
  let tk ← s.tokens t
  pure (s.setToken t { tk with underlying := tk.underlying + v })

/-! ## Verifier -/

/-- The EIP-712 attestations attesters give: arbitrary for safety, assumed for liveness. -/
structure Attest where
  transact : Addr → JS.Pub → Prop
  merge : Addr → ℕ → F → ℕ → F → ℕ → ℕ → List F → Prop

namespace Verifier

/-- `FeeSchedule.quote`: the rate of the last tier the amount reaches, on the whole amount. -/
def quote (fs : FeeSch) (v : ℕ) : ℕ :=
  v * ((fs.tiers.takeWhile fun tier => tier.1 ≤ v).getLast?.map Prod.snd |>.getD 0) / 10000

def withdrawFee (s : State) (t v : ℕ) : ℕ := quote (s.verifier.fees t) v

/-- `_token`. -/
def token (t : ℕ) (s : State) : Prop :=
  t < TOKEN_BOUND ∧ s.tokens t ≠ none ∧ s.verifier.tokenPaused t = false

/-- `_spend` of each nullifier in turn: a nullifier spent before, or twice in the list, reverts. -/
def spend (nfs : List F) (s : State) : Option State := do
  guard (nfs.Nodup ∧ ∀ nf ∈ nfs, nf ∉ s.verifier.used)
  pure { s with verifier := { s.verifier with used := s.verifier.used ∪ {nf | nf ∈ nfs} } }

/-- The fee of `_settleWithdraw`: minted to the Verifier and owed to the fee recipient. -/
def payFee (t fee : ℕ) (s : State) : Option State :=
  if fee = 0 then some s
  else do
    let s ← ZERC20.payOut h E t E.verifier fee false s
    let feeTo := (s.verifier.fees t).recipient
    pure { s with verifier := { s.verifier with
      accrued := Function.update s.verifier.accrued t
        (Function.update (s.verifier.accrued t) feeTo (s.verifier.accrued t feeTo + fee)) } }

/-- `_settleWithdraw`: the fee, then the net amount to the recipient. A fee above the gross amount
underflows, which the zero payout's check rejects here. -/
def settleWithdraw (t : ℕ) (recipient : Addr) (gross : ℕ) (unwrap : Bool) (s : State) :
    Option State :=
  if gross = 0 then some s
  else
    let fee := withdrawFee s t gross
    (payFee h E t fee s).bind fun s =>
      if gross = fee then some s else ZERC20.payOut h E t recipient (gross - fee) unwrap s

def recordNote (j : ℕ) (o : JS.Opening) (s : State) : State :=
  { s with ghost := { s.ghost with notes := Function.update s.ghost.notes j (some o) } }

def recordSpent (js : List ℕ) (s : State) : State :=
  { s with ghost := { s.ghost with spent := s.ghost.spent ++ js } }

/-- The request of `transact`. -/
structure TransactReq where
  rootIndex : ℕ
  pub : JS.Pub
  /-- The attester whose signature `attestation` recovers to. -/
  attester : Addr

/-- `transact`'s checks: `whenNotPaused`, `_token`, `_validate` (the signals are field elements
already, so only the narrower ranges remain), the attestation and the proof. -/
structure TransactOK (A : Attest) (req : TransactReq) (w : JS.Wit) (s : State) : Prop where
  notPaused : s.verifier.paused = false
  token : token req.pub.token.val s
  chain : req.pub.chain.val = E.chainId
  root : s.provedRoots req.rootIndex req.pub.root
  ranges : req.pub.amount.val < AMOUNT_BOUND ∧ req.pub.recipient.val < ADDRESS_BOUND
  asp : s.aspAccepted req.pub.asp.val
  nfs : req.pub.nf0 ≠ req.pub.nf1 ∧ req.pub.nf0 ∉ s.verifier.used ∧ req.pub.nf1 ∉ s.verifier.used
  leg : if req.pub.amount = 0 then req.pub.recipient = 0 ∧ req.pub.intent = 0
    else req.pub.recipient ≠ 0 ∧ (req.pub.intent = 0 ∨ req.pub.intent.val = E.unwrapIntent)
  attested : req.attester ∈ s.verifier.attesters ∧ A.transact req.attester req.pub
  proof : JS.Spec h req.pub w

/-- `transact`. -/
def transact (A : Attest) (req : TransactReq) (w : JS.Wit) (s : State) : Option State := do
  let x := req.pub
  let t := x.token.val
  guard (TransactOK h E A req w s)
  let s ← spend [x.nf0, x.nf1] s
  let j := s.ledger.leaves.length
  let s ← ZERC20.commitNote h t x.nh1 s
  let s ← ZERC20.commitNote h t x.nh2 s
  let s ← settleWithdraw h E t x.recipient.val x.amount.val (x.intent.val = E.unwrapIntent) s
  pure (recordSpent (w.idx0.val :: if w.in1IsDummy then [] else [w.idx1.val])
    (recordNote (j + 1) w.out2 (recordNote j w.out1 s)))

/-- The request of `merge`. -/
structure MergeReq where
  rootIndex : ℕ
  token : ℕ
  root : F
  asp : ℕ
  noteHash : F
  fee : ℕ
  feeRecipient : ℕ
  nullifiers : List F
  attester : Addr

/-- `_nullifierChain`. -/
def nullifierChain (nfs : List F) : ℕ := nfs.foldl (fun c nf => h.hc c [nf.val]) 0

def MergeReq.z0 (req : MergeReq) : Merge.Z :=
  ⟨req.token, E.chainId, req.root, req.asp, 0, nullifierChain h req.nullifiers, 0,
    req.nullifiers.length, req.fee, req.feeRecipient⟩

def MergeReq.zi (req : MergeReq) : Merge.Z :=
  ⟨req.token, E.chainId, req.root, req.asp, nullifierChain h req.nullifiers,
    nullifierChain h req.nullifiers, req.noteHash, 0, req.fee, req.feeRecipient⟩

/-- The merged note's opening: the owner and salt of the last step, worth the inputs less the fee. -/
def mergeOpening (req : MergeReq) (ws : List Merge.Wit) : JS.Opening :=
  match ws.getLast? with
  | some w => ⟨w.outPk, (ws.map Merge.value).sum - req.fee, w.outSalt⟩
  | none => JS.Opening.zero

/-- `merge`'s checks: `whenNotPaused`, `_token`, `_validate`, the attestation and the proof, whose
acceptance chains the merge spec over the extracted steps (`decider_sound`). -/
structure MergeOK (A : Attest) (req : MergeReq) (ws : List Merge.Wit) (s : State) : Prop where
  notPaused : s.verifier.paused = false
  token : token req.token s
  root : s.provedRoots req.rootIndex req.root
  ranges : req.fee < AMOUNT_BOUND ∧ req.feeRecipient < ADDRESS_BOUND
  asp : s.aspAccepted req.asp
  nfs : req.nullifiers ≠ [] ∧ ∀ nf ∈ req.nullifiers, nf ∉ s.verifier.used
  feeLeg : req.fee = 0 ↔ req.feeRecipient = 0
  attested : req.attester ∈ s.verifier.attesters ∧
    A.merge req.attester req.token req.root req.asp req.noteHash req.fee req.feeRecipient
      req.nullifiers
  proof : ws.length = req.nullifiers.length ∧ Chain (Merge.Spec h) (req.z0 h E) ws (req.zi h E)

/-- `merge`, `ws` being the extracted steps. -/
def merge (A : Attest) (req : MergeReq) (ws : List Merge.Wit) (s : State) : Option State := do
  guard (MergeOK h E A req ws s)
  let s ← spend req.nullifiers s
  let j := s.ledger.leaves.length
  let s ← ZERC20.commitNote h req.token req.noteHash s
  let s ← settleWithdraw h E req.token req.feeRecipient req.fee false s
  pure (recordSpent (ws.map fun w => w.idx.val) (recordNote j (mergeOpening req ws) s))

/-- The request of `rageExit`. -/
structure RageReq where
  checkpointIndex : ℕ
  prev : ℕ
  commits : List (List ℕ)
  nf : F

/-- The position of the deposit a rage exit refunds: the first of its segment. -/
def RageReq.index (req : RageReq) : ℕ := req.checkpointIndex - req.commits.length

/-- `Protocol.decode`: `(tag, tokenId)`. -/
def decode (f0 : ℕ) : ℕ × ℕ := (f0 / 2 ^ 32 % 2 ^ 32, f0 % 2 ^ 32)

/-- `rageExit`: the deposit is authenticated on the hash chain; the Groth16 verifier refuses a public
signal outside the field. -/
def rageExit (req : RageReq) (w : RE.Wit) (s : State) : Option State := do
  guard (s.verifier.paused = false ∧ ∀ c ∈ req.commits, c.length = 4 ∧ ∀ v ∈ c, v < UINT256)
  let index ← CommitmentLedger.verifySegment h req.checkpointIndex req.prev req.commits s
  let deposit := req.commits.headD []
  let t := (decode (deposit.getD 0 0)).2
  guard ((decode (deposit.getD 0 0)).1 = TRANSFER_TAG ∧ token t s ∧ deposit.getD 2 0 < r ∧
    RE.Spec h ⟨req.nf, E.chainId, index, deposit.getD 2 0⟩ w)
  let s ← spend [req.nf] s
  let s ← ZERC20.payOut h E t (deposit.getD 1 0 % ADDRESS_BOUND) (deposit.getD 3 0) false s
  pure (recordSpent [index] s)

/-- `publishAspRoot`. -/
def publishAspRoot (caller : Addr) (a : ℕ) (s : State) : Option State := do
  guard (caller = s.verifier.aspPublisher)
  guard (a ≠ 0 ∧ a < r)
  pure { s with verifier := { s.verifier with
    aspRootEpoch := Function.update s.verifier.aspRootEpoch a s.verifier.aspEpoch } }

/-- `claimFees`: anyone may trigger it; the Verifier transfers to the recipient. -/
def claimFees (t : ℕ) (recipient : Addr) (s : State) : Option State :=
  let v := s.verifier.accrued t recipient
  if v = 0 then some s
  else do
    let s := { s with verifier := { s.verifier with
      accrued := Function.update s.verifier.accrued t
        (Function.update (s.verifier.accrued t) recipient 0) } }
    ZERC20.transfer h E t E.verifier recipient v s

/-- `FeeSchedule._validate`: whether the schedule charges anything, if it is valid. -/
def validFees (fs : FeeSch) : Option Bool := do
  guard (fs.tiers ≠ [] ∧ fs.tiers.length ≤ 16)
  guard (fs.tiers.head?.map Prod.fst = some 0)
  guard (fs.tiers.Pairwise fun a b => a.1 < b.1 ∧ b.2 ≤ a.2)
  guard (∀ tier ∈ fs.tiers, tier.1 < AMOUNT_BOUND ∧ tier.2 ≤ 300)
  let charges := fs.tiers.any fun tier => tier.2 ≠ 0
  guard (charges → fs.recipient ≠ 0)
  pure charges

end Verifier

/-! ## Admin -/

/-- What the owner (through the AccessManager's roles) and the guardians can do, upgrades and
verifier swaps aside. -/
inductive AdminOp
  | pause | unpause
  | pauseToken (t : ℕ) | unpauseToken (t : ℕ)
  | setBlocked (a : Addr) (b : Bool)
  | setFee (t : ℕ) (fs : FeeSch)
  | setAttester (a : Addr) (b : Bool)
  | setAspPublisher (p : Addr)
  | enterEmergency (b : ℕ)
  | recover (index : ℕ) (root : F)
  | createToken (t : ℕ)

def AdminOp.exec : AdminOp → State → Option State
  | .pause, s => some { s with verifier := { s.verifier with paused := true } }
  | .unpause, s => some { s with verifier := { s.verifier with paused := false } }
  | .pauseToken t, s => do
    guard (s.tokens t ≠ none)
    pure { s with verifier := { s.verifier with
      tokenPaused := Function.update s.verifier.tokenPaused t true } }
  | .unpauseToken t, s => do
    guard (s.tokens t ≠ none)
    pure { s with verifier := { s.verifier with
      tokenPaused := Function.update s.verifier.tokenPaused t false } }
  | .setBlocked a b, s => do
    guard (a ≠ 0)
    pure { s with blocked := if b then insert a s.blocked else s.blocked \ {a} }
  | .setFee t fs, s => do
    guard (s.tokens t ≠ none)
    let charges ← Verifier.validFees fs
    guard (charges → fs.recipient ∉ s.blocked)
    pure { s with verifier := { s.verifier with fees := Function.update s.verifier.fees t fs } }
  | .setAttester a b, s => do
    guard (b → a ≠ 0)
    pure { s with verifier := { s.verifier with
      attesters := if b then insert a s.verifier.attesters else s.verifier.attesters \ {a} } }
  | .setAspPublisher p, s =>
    some { s with verifier := { s.verifier with
      aspPublisher := p, aspEpoch := s.verifier.aspEpoch + 1 } }
  | .enterEmergency b, s => some (CommitmentLedger.enterEmergency b s)
  | .recover i ρ, s => CommitmentLedger.recover i ρ s
  | .createToken t, s => do
    guard (s.tokens t = none ∧ t ≠ 0 ∧ t < TOKEN_BOUND)
    pure { s with tokens := Function.update s.tokens t (some TokenSt.empty) }

/-! ## Runs -/

inductive Action
  | wrap (t : ℕ) (caller receiver : Addr) (v : ℕ)
  | unwrap (t : ℕ) (caller receiver : Addr) (v : ℕ)
  | transfer (t : ℕ) (src dst : Addr) (v : ℕ)
  | donate (t v : ℕ)
  | reserveHashChain
  | checkpointBefore (end_ prev : ℕ) (commits : List (List ℕ))
  | proveRoot (new : RootSt) (ws : List Root.Wit)
  | transact (req : Verifier.TransactReq) (w : JS.Wit)
  | merge (req : Verifier.MergeReq) (ws : List Merge.Wit)
  | rageExit (req : Verifier.RageReq) (w : RE.Wit)
  | publishAspRoot (caller : Addr) (a : ℕ)
  | claimFees (t : ℕ) (recipient : Addr)
  /-- The owner signs a merge message. -/
  | sign (m : F)
  | admin (op : AdminOp)

def exec (A : Attest) : Action → State → Option State
  | .wrap t c rc v, s => ZERC20.wrap h E t c rc v s
  | .unwrap t c rc v, s => ZERC20.unwrap h E t c rc v s
  | .transfer t a b v, s => ZERC20.transfer h E t a b v s
  | .donate t v, s => donate t v s
  | .reserveHashChain, s => CommitmentLedger.reserveHashChain s
  | .checkpointBefore e p cs, s => CommitmentLedger.checkpointBefore h e p cs s
  | .proveRoot new ws, s => CommitmentLedger.proveRootTransition h new ws s
  | .transact req w, s => Verifier.transact h E A req w s
  | .merge req ws, s => Verifier.merge h E A req ws s
  | .rageExit req w, s => Verifier.rageExit h E req w s
  | .publishAspRoot c a, s => Verifier.publishAspRoot c a s
  | .claimFees t rc, s => Verifier.claimFees h E t rc s
  | .sign m, s => some { s with ghost := { s.ghost with signed := s.ghost.signed ++ [m] } }
  | .admin op, s => op.exec s

/-- A run from the deployment: `n` actions, each one accepted. -/
structure Run (A : Attest) where
  publisher : Addr
  n : ℕ
  s : ℕ → State
  a : ℕ → Action
  init : s 0 = State.init h publisher
  step : ∀ i < n, exec h E A (a i) (s i) = some (s (i + 1))

end

end Zerc20
