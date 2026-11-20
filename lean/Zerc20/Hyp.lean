import Zerc20.Model
import Zerc20.Tree

/-!
# What a run assumes

The cryptographic assumptions are stated about the values one run evaluates, never as global
properties: Poseidon and SHA-256 compress, so they have collisions, and assuming them injective
everywhere would make every theorem vacuous. A run that meets no collision, no forged signature
and no key for a burn address satisfies these hypotheses; an adversary breaking one has found such
a value among the run's own.
-/

namespace Zerc20

open scoped Classical

noncomputable section

variable (h : Hashes) (E : Env)

/-- The chain id as a circuit value. -/
def Env.chain : F := E.chainId

/-- An honest owner: a private key, a signing key, and the salts of its burn addresses. -/
structure Owner where
  sk : F
  ak : F × F
  salts : List F

namespace Owner

variable (U : Owner)

def nk : F := nullifyingKey h U.sk
def akh : F := authKeyHash h U.ak
def pk : F := publicKey h (U.akh h) (U.nk h)

/-- The address of the burn deposit with salt `salt`. -/
def burnAddr (salt : F) : ℕ := addressOf (burnDigest h E.chain (U.pk h) salt)

/-- What the owner hashes to derive its keys, its burn addresses and the nullifiers of its
positions. -/
def calls : Set (List F) :=
  {[DOMAIN_NULLIFYING_KEY, U.sk], [DOMAIN_AUTH_KEY, U.ak.1, U.ak.2],
    [DOMAIN_PUBLIC_KEY, U.akh h, U.nk h]} ∪
  {x | ∃ salt ∈ U.salts, x = [DOMAIN_BURN, E.chain, U.pk h, salt, 0]} ∪
  {x | ∃ j : ℕ, j < 2 ^ DEPTH ∧ x = [DOMAIN_NULLIFIER, E.chain, (j : F), U.nk h, 0]}

def openings : Set (F × F × F) := {o | ∃ salt ∈ U.salts, o = (E.chain, U.pk h, salt)}

end Owner

/-- The digest a burn opening `(chain, pk, salt)` derives. -/
def digestOf (o : F × F × F) : F := burnDigest h o.1 o.2.1 o.2.2

/-! ## What each action evaluates -/

/-- The SHA-256 inputs of a hash chain over `cs`, from `c`. -/
def chainCalls : ℕ → List (List ℕ) → Set (ℕ × List ℕ)
  | _, [] => ∅
  | c, x :: cs => {(c, x)} ∪ chainCalls (h.hc c x) cs


def Action.calls (s : State) : Action → Set (List F)
  | .transact req w => JS.calls h req.pub w
  | .merge req ws => Merge.callsAlong h (req.z0 h E) ws
  | .rageExit req w => RE.calls h ⟨req.nf, E.chainId, req.index, 0⟩ w
  | .proveRoot _ ws =>
    let old := s.ledger.rootState
    Root.callsAlong h ⟨old.index, old.chain, old.root⟩ ws
  | _ => ∅

def Action.shaCalls (s : State) : Action → Set (ℕ × List ℕ)
  | .merge req ws => Merge.shaAlong h (req.z0 h E) ws ∪
      chainCalls h 0 (req.nullifiers.map fun nf => [nf.val])
  | .rageExit req _ => chainCalls h req.prev req.commits
  | .checkpointBefore _ prev commits => chainCalls h prev commits
  | .proveRoot _ ws =>
    let old := s.ledger.rootState
    Root.shaAlong h ⟨old.index, old.chain, old.root⟩ ws
  | _ => ∅

/-- The burn openings a spend proves. -/
def Action.openings : Action → Set (F × F × F)
  | .transact req w => if w.in0IsBurn then {(req.pub.chain, w.burnPk, w.burnSalt)} else ∅
  | .merge _ ws => {o | ∃ w ∈ ws, w.isBurn ∧ o = (E.chain, Merge.pk (h := h) w, w.burnSalt)}
  | .rageExit _ w => {(E.chain, RE.pk h w, w.salt)}
  | _ => ∅

/-- The accounts an action takes a balance from. -/
def Action.debits : Action → Set Addr
  | .transfer _ src _ _ => {src}
  | .unwrap _ caller _ _ => {caller}
  | .claimFees _ _ => {E.verifier}
  | _ => ∅

/-! ## A run's values -/

variable {h E} {A : Attest} (R : Run h E A)

def Run.last : State := R.s R.n

/-- The ledger at the end: every state's ledger is a prefix of it. -/
def Run.leaves : List Leaf := R.last.ledger.leaves

def Run.calls : Set (List F) :=
  {x | ∃ i < R.n, x ∈ (R.a i).calls h E (R.s i)} ∪
  {x | ∃ p ≤ R.leaves.length, x ∈ treeCalls h ((R.leaves.take p).map (Leaf.hash h))} ∪
  {x | ∃ l ∈ R.leaves, x = l.words.map (↑)}

def Run.shaCalls : Set (ℕ × List ℕ) :=
  {x | ∃ i < R.n, x ∈ (R.a i).shaCalls h E (R.s i)} ∪
  {x | ∃ m < R.leaves.length, x = (chainOf h (R.leaves.take m), (R.leaves[m]?.map Leaf.words).getD [])}

def Run.openings : Set (F × F × F) := {o | ∃ i < R.n, o ∈ (R.a i).openings h E}

/-- The burn addresses the run opens. -/
def Run.burnAddrs : Set ℕ := {a | ∃ o ∈ R.openings, a = addressOf (digestOf h o)}

/-- The run's hypotheses, with extra Poseidon inputs `S` and burn openings `O` an owner adds. -/
structure RunHyp (S : Set (List F)) (O : Set (F × F × F)) : Prop where
  /-- No Poseidon collision among the run's inputs. -/
  inj : Injective h (R.calls ∪ S)
  /-- No input the run hashes has output zero, the empty slot's value. -/
  ne0 : ∀ x ∈ R.calls ∪ S, h.H x ≠ 0
  /-- No SHA-256 collision among the run's inputs. -/
  sha : ∀ p ∈ R.shaCalls, ∀ q ∈ R.shaCalls, h.hc p.1 p.2 = h.hc q.1 q.2 → p = q
  /-- No two burn openings share an address but not a digest: a 160-bit birthday search on top of
  the proof of work. -/
  burnAddr : ∀ o ∈ R.openings ∪ O, ∀ o' ∈ R.openings ∪ O,
    addressOf (digestOf h o) = addressOf (digestOf h o') → digestOf h o = digestOf h o'
  /-- Nobody holds a key for an address the run opens as a burn address. -/
  frozen : ∀ i < R.n, ∀ a ∈ (R.a i).debits E, a ∉ R.burnAddrs

/-- An owner's hypotheses: the run's, with the owner's own hashes and openings, and no signature
under the owner's key on a merge the owner did not sign first. -/
structure OwnerHyp (U : Owner) : Prop extends RunHyp R (U.calls h E) (U.openings h E) where
  signed : ∀ i < R.n, ∀ req ws, R.a i = .merge req ws → ∀ w ∈ ws, w.ak = U.ak →
    mergeMessage h (Verifier.nullifierChain h req.nullifiers) w.outPk w.outSalt req.fee
      req.feeRecipient ∈ (R.s i).ghost.signed

end

end Zerc20
