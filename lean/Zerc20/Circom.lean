import Zerc20.Spec
import Zerc20.Circomlib
import Zerc20.Poseidon
import Mathlib.Tactic.LinearCombination

/-!
# zERC20's circom templates

One model per template of `zkp/circom/lib/{poseidon,primitives,commitments,merkle,inputs}.circom`
and of the two main circuits `JoinSplit` and `RageExit`. A template's `Rel` has one conjunct per
constraint it emits, over its inputs, its outputs and a witness `W` of its internal signals.

Two kinds of wiring are substituted rather than kept as conjuncts:
- a sub-component's input is the expression wired into it (`c.in <== e`);
- a signal that only copies a sub-component's output (`x <== c.out`) is that output.

An equation `s = e` with `s` a signal only fixes `s`, so substituting `e` for `s` keeps the same
satisfying assignments with `s` dropped. Every other `<==` and `===` is a conjunct.

The models are generic over circomlib's `Poseidon(n)` through `PoseidonGadget`, so they hold for
any model of it that computes the hash `Hashes.H` the protocol statements use. The file ends by
instantiating them with `Circomlib.Poseidon`.
-/

namespace Zerc20.Circom

open Circomlib

/-! ## The Poseidon interface -/

/-- What these templates need of circomlib's `Poseidon(n)`: its constraints over the inputs, the
output and its internal signals pin the output to `hash` of the inputs, and the honest prover can
satisfy them. Both are asked only for the arities 2 to 6 the templates instantiate. -/
structure PoseidonGadget where
  /-- The internal signals of `Poseidon(n)`. -/
  W : ℕ → Type
  Rel : (n : ℕ) → (Fin n → F) → F → W n → Prop
  hash : List F → F
  sound : ∀ {n ins out w}, 2 ≤ n ∧ n ≤ 6 → Rel n ins out w → out = hash (List.ofFn ins)
  complete : ∀ {n}, 2 ≤ n ∧ n ≤ 6 → ∀ ins, ∃ w, Rel n ins (hash (List.ofFn ins)) w

variable {P : PoseidonGadget} {h : Hashes}

/-- The internal signals of circomlib's `IsZero`, or of a `ForceEqualIfEnabled`, whose only
internal signals are those of its `IsZero`. -/
structure IsZeroW where
  out : F
  inv : F

/-- The honest `IsZero` signals of `x`; a `ForceEqualIfEnabled` of `in[0]`, `in[1]` takes those of
`in[1] - in[0]`. -/
def IsZeroW.honest (x : F) : IsZeroW := ⟨if x = 0 then 1 else 0, x⁻¹⟩

/-- The internal signals of our `RangeCheck(n)`: the bits and `recompose.out`. -/
structure RangeCheckW (n : ℕ) where
  bits : Fin n → F
  out : F

/-- The honest `RangeCheck(n)` signals of `x`. -/
def RangeCheckW.honest (n : ℕ) (x : F) : RangeCheckW n := ⟨toBits n x.val, x⟩

/-- The internal signals of our `AddressFromDigest`: the canonical bits of the digest, the
internals of their alias check, and `digest_num.out`. -/
structure AddressFromDigestW where
  bits : Fin 254 → F
  aliasCheck : CompConstant.Witness
  aliasOut : F
  num : F

/-- The honest `AddressFromDigest` signals of `digest`. -/
def AddressFromDigestW.honest (digest : F) : AddressFromDigestW :=
  ⟨toBits 254 digest.val, CompConstant.witness (r - 1) (toBits 254 digest.val), 0, digest⟩

theorem ofFn_vecCons {n : ℕ} (a : F) (v : Fin n → F) :
    List.ofFn (Matrix.vecCons a v) = a :: List.ofFn v := by
  simp [List.ofFn_succ]

/-! ## `poseidon.circom` -/

namespace Hash2

/-- `Hash2`: `Poseidon(2)` of `[left, right]`. -/
def Rel (P : PoseidonGadget) (left right out : F) (w : P.W 2) : Prop :=
  P.Rel 2 ![left, right] out w

theorem sound {left right out : F} {w : P.W 2} (hr : Rel P left right out w) :
    out = P.hash [left, right] := by
  simpa using P.sound (by norm_num) hr

theorem complete (P : PoseidonGadget) (left right : F) :
    ∃ w, Rel P left right (P.hash [left, right]) w := by
  simpa using P.complete (by norm_num) ![left, right]

end Hash2

namespace Hash4

/-- `Hash4`: `Poseidon(4)` of `values`. -/
def Rel (P : PoseidonGadget) (values : Fin 4 → F) (out : F) (w : P.W 4) : Prop :=
  P.Rel 4 values out w

theorem sound {values : Fin 4 → F} {out : F} {w : P.W 4} (hr : Rel P values out w) :
    out = P.hash (List.ofFn values) :=
  P.sound (by norm_num) hr

theorem complete (P : PoseidonGadget) (values : Fin 4 → F) :
    ∃ w, Rel P values (P.hash (List.ofFn values)) w :=
  P.complete (by norm_num) values

end Hash4

namespace DomainHash1

/-- `DomainHash1(domain)`: `Poseidon(2)` of `[domain, value]`. -/
def Rel (P : PoseidonGadget) (domain value out : F) (w : P.W 2) : Prop :=
  P.Rel 2 ![domain, value] out w

theorem sound {domain value out : F} {w : P.W 2} (hr : Rel P domain value out w) :
    out = P.hash [domain, value] := by
  simpa using P.sound (by norm_num) hr

theorem complete (P : PoseidonGadget) (domain value : F) :
    ∃ w, Rel P domain value (P.hash [domain, value]) w := by
  simpa using P.complete (by norm_num) ![domain, value]

end DomainHash1

/-- `DomainHash2`, `DomainHash4` and `DomainHash5` share one shape: `Poseidon(n + 1)` of the domain
followed by the `n` values. -/
theorem domainHash_sound {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 5) {domain out : F}
    {values : Fin n → F} {w : P.W (n + 1)}
    (hr : P.Rel (n + 1) (Matrix.vecCons domain values) out w) :
    out = P.hash (domain :: List.ofFn values) := by
  rw [P.sound (by omega) hr, ofFn_vecCons]

theorem domainHash_complete (P : PoseidonGadget) {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 5)
    (domain : F) (values : Fin n → F) :
    ∃ w, P.Rel (n + 1) (Matrix.vecCons domain values)
      (P.hash (domain :: List.ofFn values)) w := by
  rw [← ofFn_vecCons]
  exact P.complete (by omega) _

namespace DomainHash2

/-- `DomainHash2(domain)`: `Poseidon(3)` of `[domain, values[0], values[1]]`. -/
def Rel (P : PoseidonGadget) (domain : F) (values : Fin 2 → F) (out : F) (w : P.W 3) : Prop :=
  P.Rel 3 (Matrix.vecCons domain values) out w

theorem sound {domain out : F} {values : Fin 2 → F} {w : P.W 3}
    (hr : Rel P domain values out w) : out = P.hash (domain :: List.ofFn values) :=
  domainHash_sound (by norm_num) (by norm_num) hr

theorem complete (P : PoseidonGadget) (domain : F) (values : Fin 2 → F) :
    ∃ w, Rel P domain values (P.hash (domain :: List.ofFn values)) w :=
  domainHash_complete P (by norm_num) (by norm_num) domain values

end DomainHash2

namespace DomainHash4

/-- `DomainHash4(domain)`: `Poseidon(5)` of the domain and `values[0..3]`. -/
def Rel (P : PoseidonGadget) (domain : F) (values : Fin 4 → F) (out : F) (w : P.W 5) : Prop :=
  P.Rel 5 (Matrix.vecCons domain values) out w

theorem sound {domain out : F} {values : Fin 4 → F} {w : P.W 5}
    (hr : Rel P domain values out w) : out = P.hash (domain :: List.ofFn values) :=
  domainHash_sound (by norm_num) (by norm_num) hr

theorem complete (P : PoseidonGadget) (domain : F) (values : Fin 4 → F) :
    ∃ w, Rel P domain values (P.hash (domain :: List.ofFn values)) w :=
  domainHash_complete P (by norm_num) (by norm_num) domain values

end DomainHash4

namespace DomainHash5

/-- `DomainHash5(domain)`: `Poseidon(6)` of the domain and `values[0..4]`. -/
def Rel (P : PoseidonGadget) (domain : F) (values : Fin 5 → F) (out : F) (w : P.W 6) : Prop :=
  P.Rel 6 (Matrix.vecCons domain values) out w

theorem sound {domain out : F} {values : Fin 5 → F} {w : P.W 6}
    (hr : Rel P domain values out w) : out = P.hash (domain :: List.ofFn values) :=
  domainHash_sound (by norm_num) (by norm_num) hr

theorem complete (P : PoseidonGadget) (domain : F) (values : Fin 5 → F) :
    ∃ w, Rel P domain values (P.hash (domain :: List.ofFn values)) w :=
  domainHash_complete P (by norm_num) (by norm_num) domain values

end DomainHash5

/-! ## `primitives.circom` -/

namespace PublicKey

/-- `PublicKey`: `DomainHash2(DOMAIN_PUBLIC_KEY)` of the auth key hash and the nullifying key. -/
def Rel (P : PoseidonGadget) (akh nk pk : F) (w : P.W 3) : Prop :=
  DomainHash2.Rel P DOMAIN_PUBLIC_KEY ![akh, nk] pk w

theorem sound (hP : h.H = P.hash) {akh nk pk : F} {w : P.W 3} (hr : Rel P akh nk pk w) :
    pk = publicKey h akh nk := by
  simpa [publicKey, hP] using DomainHash2.sound hr

theorem complete (hP : h.H = P.hash) (akh nk : F) : ∃ w, Rel P akh nk (publicKey h akh nk) w := by
  simpa [publicKey, hP] using DomainHash2.complete P DOMAIN_PUBLIC_KEY ![akh, nk]

end PublicKey

namespace NullifyingKey

/-- `NullifyingKey`: `DomainHash1(DOMAIN_NULLIFYING_KEY)` of the private key. -/
def Rel (P : PoseidonGadget) (sk nk : F) (w : P.W 2) : Prop :=
  DomainHash1.Rel P DOMAIN_NULLIFYING_KEY sk nk w

theorem sound (hP : h.H = P.hash) {sk nk : F} {w : P.W 2} (hr : Rel P sk nk w) :
    nk = nullifyingKey h sk := by
  simpa [nullifyingKey, hP] using DomainHash1.sound hr

theorem complete (hP : h.H = P.hash) (sk : F) : ∃ w, Rel P sk (nullifyingKey h sk) w := by
  simpa [nullifyingKey, hP] using DomainHash1.complete P DOMAIN_NULLIFYING_KEY sk

end NullifyingKey

namespace Nullifier

/-- `Nullifier`: `DomainHash4(DOMAIN_NULLIFIER)` of the chain, the commitment index, the nullifying
key and 0. -/
def Rel (P : PoseidonGadget) (chain idx nk nf : F) (w : P.W 5) : Prop :=
  DomainHash4.Rel P DOMAIN_NULLIFIER ![chain, idx, nk, 0] nf w

theorem sound (hP : h.H = P.hash) {chain idx nk nf : F} {w : P.W 5}
    (hr : Rel P chain idx nk nf w) : nf = nullifier h chain idx nk := by
  simpa [nullifier, hP] using DomainHash4.sound hr

theorem complete (hP : h.H = P.hash) (chain idx nk : F) :
    ∃ w, Rel P chain idx nk (nullifier h chain idx nk) w := by
  simpa [nullifier, hP] using DomainHash4.complete P DOMAIN_NULLIFIER ![chain, idx, nk, 0]

end Nullifier

namespace DummyNullifier

/-- The internal signals of `DummyNullifier`. -/
structure W (P : PoseidonGadget) where
  indexedEntropy : F
  hash : P.W 3

/-- `DummyNullifier(dummy_index)`: `indexed_entropy <== entropy + dummy_index`, and
`DomainHash2(DOMAIN_DUMMY_NULLIFIER)` of the chain and `indexed_entropy`. -/
def Rel (P : PoseidonGadget) (dummyIndex chain entropy nf : F) (w : W P) : Prop :=
  w.indexedEntropy = entropy + dummyIndex ∧
  DomainHash2.Rel P DOMAIN_DUMMY_NULLIFIER ![chain, w.indexedEntropy] nf w.hash

/-- JoinSplit's one dummy slot is `dummy_index = 1`, which `dummyNullifier` fixes. -/
theorem sound (hP : h.H = P.hash) {chain entropy nf : F} {w : W P}
    (hr : Rel P 1 chain entropy nf w) : nf = dummyNullifier h chain entropy := by
  have := DomainHash2.sound hr.2
  simpa [dummyNullifier, hP, hr.1] using this

theorem complete (hP : h.H = P.hash) (chain entropy : F) :
    ∃ w, Rel P 1 chain entropy (dummyNullifier h chain entropy) w := by
  obtain ⟨w, hw⟩ := DomainHash2.complete P DOMAIN_DUMMY_NULLIFIER ![chain, entropy + 1]
  exact ⟨⟨entropy + 1, w⟩, rfl, by simpa [dummyNullifier, hP] using hw⟩

end DummyNullifier

namespace NoteHash

/-- `NoteHash`: `DomainHash5(DOMAIN_NOTE)` of the chain, the owner, the value, the token and the
salt. -/
def Rel (P : PoseidonGadget) (chain pk value token salt nh : F) (w : P.W 6) : Prop :=
  DomainHash5.Rel P DOMAIN_NOTE ![chain, pk, value, token, salt] nh w

theorem sound (hP : h.H = P.hash) {chain pk value token salt nh : F} {w : P.W 6}
    (hr : Rel P chain pk value token salt nh w) : nh = noteHash h chain pk value token salt := by
  simpa [noteHash, hP] using DomainHash5.sound hr

theorem complete (hP : h.H = P.hash) (chain pk value token salt : F) :
    ∃ w, Rel P chain pk value token salt (noteHash h chain pk value token salt) w := by
  simpa [noteHash, hP] using
    DomainHash5.complete P DOMAIN_NOTE ![chain, pk, value, token, salt]

end NoteHash

namespace BurnDigest

/-- `BurnDigest`: `DomainHash4(DOMAIN_BURN)` of the chain, the owner, the salt and 0. -/
def Rel (P : PoseidonGadget) (chain pk salt digest : F) (w : P.W 5) : Prop :=
  DomainHash4.Rel P DOMAIN_BURN ![chain, pk, salt, 0] digest w

theorem sound (hP : h.H = P.hash) {chain pk salt digest : F} {w : P.W 5}
    (hr : Rel P chain pk salt digest w) : digest = burnDigest h chain pk salt := by
  simpa [burnDigest, hP] using DomainHash4.sound hr

theorem complete (hP : h.H = P.hash) (chain pk salt : F) :
    ∃ w, Rel P chain pk salt (burnDigest h chain pk salt) w := by
  simpa [burnDigest, hP] using DomainHash4.complete P DOMAIN_BURN ![chain, pk, salt, 0]

end BurnDigest

/-! ## `commitments.circom` -/

namespace CommitmentLeaf

/-- `CommitmentLeaf`: `Hash4` of the four fields. -/
def Rel (P : PoseidonGadget) (f0 f1 f2 f3 leaf : F) (w : P.W 4) : Prop :=
  Hash4.Rel P ![f0, f1, f2, f3] leaf w

theorem sound (hP : h.H = P.hash) {f0 f1 f2 f3 leaf : F} {w : P.W 4}
    (hr : Rel P f0 f1 f2 f3 leaf w) : leaf = h.H [f0, f1, f2, f3] := by
  simpa [hP] using Hash4.sound hr

theorem complete (hP : h.H = P.hash) (f0 f1 f2 f3 : F) :
    ∃ w, Rel P f0 f1 f2 f3 (h.H [f0, f1, f2, f3]) w := by
  simpa [hP] using Hash4.complete P ![f0, f1, f2, f3]

end CommitmentLeaf

/-- `TRANSFER_FIELD0_BASE()`: `TRANSFER_TAG << 32`. -/
def TRANSFER_FIELD0_BASE : F := 15992936129728872448

/-- `NOTE_FIELD0_BASE()`: `NOTE_HASH_TAG << 32`. -/
def NOTE_FIELD0_BASE : F := 8691708596607516672

/-- A tag base plus the token in `F` is the leaf's `field0` cast into `F`; the cast is additive, so
this needs no bound on the token. -/
theorem field0_cast (tag : ℕ) (token : F) :
    ((tag * 2 ^ 32 : ℕ) : F) + token = ((field0 tag token.val : ℕ) : F) := by
  simp [field0]

theorem transfer_base : TRANSFER_FIELD0_BASE = ((TRANSFER_TAG * 2 ^ 32 : ℕ) : F) := by
  norm_num [TRANSFER_FIELD0_BASE, TRANSFER_TAG]

theorem note_base : NOTE_FIELD0_BASE = ((NOTE_HASH_TAG * 2 ^ 32 : ℕ) : F) := by
  norm_num [NOTE_FIELD0_BASE, NOTE_HASH_TAG]

/-- The internal signals of `TransferLeaf` and `NoteLeaf`: `field0` and the commitment leaf's. -/
structure LeafW (P : PoseidonGadget) where
  field0 : F
  commitmentLeaf : P.W 4

namespace TransferLeaf

/-- `TransferLeaf`: `field0 <== TRANSFER_FIELD0_BASE + token_id`, and `CommitmentLeaf` of
`[field0, from, to, value]`. -/
def Rel (P : PoseidonGadget) (token src dst value leaf : F) (w : LeafW P) : Prop :=
  w.field0 = TRANSFER_FIELD0_BASE + token ∧
  CommitmentLeaf.Rel P w.field0 src dst value leaf w.commitmentLeaf

theorem sound (hP : h.H = P.hash) {token src dst value leaf : F} {w : LeafW P}
    (hr : Rel P token src dst value leaf w) :
    leaf = h.H [↑(field0 TRANSFER_TAG token.val), src, dst, value] := by
  rw [CommitmentLeaf.sound hP hr.2, hr.1, transfer_base, field0_cast]

theorem complete (hP : h.H = P.hash) (token src dst value : F) :
    ∃ w, Rel P token src dst value (h.H [↑(field0 TRANSFER_TAG token.val), src, dst, value]) w := by
  obtain ⟨w, hw⟩ := CommitmentLeaf.complete hP (TRANSFER_FIELD0_BASE + token) src dst value
  rw [transfer_base, field0_cast] at hw
  exact ⟨⟨_, w⟩, by rw [transfer_base, field0_cast], hw⟩

end TransferLeaf

namespace NoteLeaf

/-- `NoteLeaf`: `field0 <== NOTE_FIELD0_BASE + token_id`, and `CommitmentLeaf` of
`[field0, note_hash, 0, 0]`. -/
def Rel (P : PoseidonGadget) (token nh leaf : F) (w : LeafW P) : Prop :=
  w.field0 = NOTE_FIELD0_BASE + token ∧
  CommitmentLeaf.Rel P w.field0 nh 0 0 leaf w.commitmentLeaf

theorem sound (hP : h.H = P.hash) {token nh leaf : F} {w : LeafW P} (hr : Rel P token nh leaf w) :
    leaf = h.H [↑(field0 NOTE_HASH_TAG token.val), nh, 0, 0] := by
  rw [CommitmentLeaf.sound hP hr.2, hr.1, note_base, field0_cast]

theorem complete (hP : h.H = P.hash) (token nh : F) :
    ∃ w, Rel P token nh (h.H [↑(field0 NOTE_HASH_TAG token.val), nh, 0, 0]) w := by
  obtain ⟨w, hw⟩ := CommitmentLeaf.complete hP (NOTE_FIELD0_BASE + token) nh 0 0
  rw [note_base, field0_cast] at hw
  exact ⟨⟨_, w⟩, by rw [note_base, field0_cast], hw⟩

end NoteLeaf

namespace AspLeaf

/-- `AspLeaf`: `DomainHash1(DOMAIN_ASP_LEAF)` of the commitment index. -/
def Rel (P : PoseidonGadget) (idx leaf : F) (w : P.W 2) : Prop :=
  DomainHash1.Rel P DOMAIN_ASP_LEAF idx leaf w

theorem sound (hP : h.H = P.hash) {idx leaf : F} {w : P.W 2} (hr : Rel P idx leaf w) :
    leaf = aspLeaf h idx := by
  simpa [aspLeaf, hP] using DomainHash1.sound hr

theorem complete (hP : h.H = P.hash) (idx : F) : ∃ w, Rel P idx (aspLeaf h idx) w := by
  simpa [aspLeaf, hP] using DomainHash1.complete P DOMAIN_ASP_LEAF idx

end AspLeaf

/-! ## `merkle.circom` -/

theorem two_pow_depth_le : 2 ^ DEPTH ≤ r := by unfold DEPTH r; norm_num

namespace MerkleRoot

/-- The internal signals of `MerkleRoot(depth)`. `current[level + 1]` is `hashers[level].out`. -/
structure W (P : PoseidonGadget) (depth : ℕ) where
  indexBits : Fin depth → F
  current : Fin (depth + 1) → F
  left : Fin depth → F
  right : Fin depth → F
  hashers : Fin depth → P.W 2

/-- `MerkleRoot(depth)`. -/
structure Rel (P : PoseidonGadget) (depth : ℕ) (leaf index : F) (siblings : Fin depth → F)
    (root : F) (w : W P depth) : Prop where
  indexBits : Num2Bits.Rel depth index w.indexBits
  current0 : w.current 0 = leaf
  left : ∀ l, w.left l =
    w.current l.castSucc + w.indexBits l * (siblings l - w.current l.castSucc)
  right : ∀ l, w.right l =
    siblings l + w.indexBits l * (w.current l.castSucc - siblings l)
  hashers : ∀ l, Hash2.Rel P (w.left l) (w.right l) (w.current l.succ) (w.hashers l)
  rootEq : root = w.current (Fin.last depth)

/-- With bit `k` of the index as selector, the level-`k` muxes feed `Hash2` the pair `pathRoot`
hashes at level `k`. -/
theorem mux (hP : h.H = P.hash) (leaf : F) (idx : ℕ) (sib : Fin DEPTH → F) (k : Fin DEPTH) :
    P.hash [pathRoot h leaf idx sib k + toBits DEPTH idx k * (sib k - pathRoot h leaf idx sib k),
      sib k + toBits DEPTH idx k * (pathRoot h leaf idx sib k - sib k)] =
      pathRoot h leaf idx sib (k + 1) := by
  rw [pathRoot, dif_pos k.isLt, ← hP]
  simp only [toBits, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, Fin.eta]
  split_ifs <;> simp

theorem sound (hP : h.H = P.hash) {leaf index root : F} {sib : Fin DEPTH → F} {w : W P DEPTH}
    (hr : Rel P DEPTH leaf index sib root w) :
    index.val < 2 ^ DEPTH ∧ root = merkleRoot h leaf index.val sib := by
  obtain ⟨hlt, hbits⟩ := Num2Bits.sound two_pow_depth_le hr.indexBits
  have key : ∀ k (hk : k < DEPTH + 1), w.current ⟨k, hk⟩ = pathRoot h leaf index.val sib k := by
    intro k
    induction k with
    | zero => intro _; simpa [pathRoot] using hr.current0
    | succ k ih =>
      intro hk
      have := Hash2.sound (hr.hashers ⟨k, by omega⟩)
      rw [hr.left, hr.right, hbits] at this
      simp only [Fin.castSucc_mk, Fin.succ_mk, ih (by omega)] at this
      rw [this]; exact mux hP leaf _ sib ⟨k, by omega⟩
  exact ⟨hlt, hr.rootEq.trans (key DEPTH (by omega))⟩

theorem complete (hP : h.H = P.hash) (leaf index : F) (sib : Fin DEPTH → F)
    (hidx : index.val < 2 ^ DEPTH) :
    ∃ w, Rel P DEPTH leaf index sib (merkleRoot h leaf index.val sib) w := by
  let c : Fin (DEPTH + 1) → F := fun k => pathRoot h leaf index.val sib k
  let b := toBits DEPTH index.val
  let left := fun l : Fin DEPTH => c l.castSucc + b l * (sib l - c l.castSucc)
  let right := fun l : Fin DEPTH => sib l + b l * (c l.castSucc - sib l)
  have : ∀ l, ∃ w, Hash2.Rel P (left l) (right l) (c l.succ) w := fun l => by
    have := Hash2.complete P (left l) (right l)
    simp only [left, right, c, b, Fin.val_castSucc, mux hP] at this
    exact this
  choose hs hhs using this
  exact ⟨⟨b, c, left, right, hs⟩,
    ⟨Num2Bits.complete hidx, rfl, fun _ => rfl, fun _ => rfl, hhs, rfl⟩⟩

end MerkleRoot

/-! ## `inputs.circom` -/

namespace NoteSpend

/-- The internal signals of `NoteSpend`. `leaf` is `note_leaf.leaf` and `nullifier` is
`nf.nullifier`. -/
structure W (P : PoseidonGadget) where
  disabled : F
  ownerCheck : IsZeroW
  zeroPublicKey : IsZeroW
  zeroValue : IsZeroW
  zeroSalt : IsZeroW
  hash : P.W 6
  noteHash : F
  noteLeaf : LeafW P
  nf : P.W 5

/-- `NoteSpend`, with inputs `enabled`, `chain_id`, `token_id`, `note_public_key`, `note_value`,
`note_salt`, `owner_public_key`, `commitment_index`, `nullifying_key` and outputs `leaf`, `value`,
`nullifier`. -/
structure Rel (P : PoseidonGadget)
    (enabled chain token notePk noteValue noteSalt ownerPk idx nk leaf value nullifier : F)
    (w : W P) : Prop where
  disabled : w.disabled = 1 - enabled
  ownerCheck :
    ForceEqualIfEnabled.Rel enabled notePk ownerPk w.ownerCheck.out w.ownerCheck.inv
  zeroPublicKey :
    ForceEqualIfEnabled.Rel w.disabled notePk 0 w.zeroPublicKey.out w.zeroPublicKey.inv
  zeroValue :
    ForceEqualIfEnabled.Rel w.disabled noteValue 0 w.zeroValue.out w.zeroValue.inv
  zeroSalt :
    ForceEqualIfEnabled.Rel w.disabled noteSalt 0 w.zeroSalt.out w.zeroSalt.inv
  hash : NoteHash.Rel P chain notePk noteValue token noteSalt w.noteHash w.hash
  noteLeaf : NoteLeaf.Rel P token w.noteHash leaf w.noteLeaf
  nf : Nullifier.Rel P chain idx nk nullifier w.nf
  valueEq : value = noteValue

/-- The note's leaf, as the commitment tree holds it. -/
def leafOf (h : Hashes) (chain token pk value salt : F) : F :=
  h.H [↑(field0 NOTE_HASH_TAG token.val), noteHash h chain pk value token salt, 0, 0]

/-- The outputs are the note's leaf, its value and its nullifier; a nonzero `enabled` forces the
owner check, and an `enabled` other than 1 forces the zero opening. -/
theorem sound (hP : h.H = P.hash)
    {enabled chain token notePk noteValue noteSalt ownerPk idx nk leaf value nf : F} {w : W P}
    (hr : Rel P enabled chain token notePk noteValue noteSalt ownerPk idx nk leaf value nf w) :
    leaf = leafOf h chain token notePk noteValue noteSalt ∧ value = noteValue ∧
      nf = nullifier h chain idx nk ∧
      (enabled ≠ 0 → notePk = ownerPk) ∧
      (enabled ≠ 1 → notePk = 0 ∧ noteValue = 0 ∧ noteSalt = 0) := by
  refine ⟨?_, hr.valueEq, Nullifier.sound hP hr.nf,
    fun hen => ForceEqualIfEnabled.sound hr.ownerCheck hen, fun hen => ?_⟩
  · rw [NoteLeaf.sound hP hr.noteLeaf, NoteHash.sound hP hr.hash, leafOf]
  · have hd : w.disabled ≠ 0 := by rw [hr.disabled]; exact sub_ne_zero.2 (Ne.symm hen)
    exact ⟨ForceEqualIfEnabled.sound hr.zeroPublicKey hd,
      ForceEqualIfEnabled.sound hr.zeroValue hd, ForceEqualIfEnabled.sound hr.zeroSalt hd⟩

theorem complete (hP : h.H = P.hash)
    {enabled chain token notePk noteValue noteSalt ownerPk idx nk : F}
    (hon : enabled = 0 ∨ notePk = ownerPk)
    (hoff : enabled = 1 ∨ notePk = 0 ∧ noteValue = 0 ∧ noteSalt = 0) :
    ∃ w, Rel P enabled chain token notePk noteValue noteSalt ownerPk idx nk
      (leafOf h chain token notePk noteValue noteSalt) noteValue (nullifier h chain idx nk) w := by
  obtain ⟨wh, hwh⟩ := NoteHash.complete hP chain notePk noteValue token noteSalt
  obtain ⟨wl, hwl⟩ := NoteLeaf.complete hP token (noteHash h chain notePk noteValue token noteSalt)
  obtain ⟨wn, hwn⟩ := Nullifier.complete hP chain idx nk
  refine ⟨⟨1 - enabled, .honest (ownerPk - notePk), .honest (0 - notePk),
    .honest (0 - noteValue), .honest (0 - noteSalt), wh, _, wl, wn⟩,
    ⟨rfl, ForceEqualIfEnabled.complete hon, ?_, ?_, ?_, hwh, hwl, hwn, rfl⟩⟩
  all_goals refine ForceEqualIfEnabled.complete ?_
  all_goals rcases hoff with rfl | ⟨h1, h2, h3⟩
  all_goals simp_all

end NoteSpend

namespace BurnIntake

/-- The internal signals of `BurnIntake(depth, address_bits, pow_bits)`. `leaf` is
`transfer_leaf.leaf`. -/
structure W (P : PoseidonGadget) (depth : ℕ) where
  disabled : F
  ownerCheck : IsZeroW
  zeroPublicKey : IsZeroW
  zeroSalt : IsZeroW
  zeroFrom : IsZeroW
  zeroValue : IsZeroW
  transferValueIsZero : IsZeroW
  positiveTransferValue : IsZeroW
  digest : P.W 5
  digestOut : F
  address : AddressFromDigestW
  addressOut : F
  transferLeaf : LeafW P
  aspLeaf : P.W 2
  aspLeafOut : F
  aspRootCalc : MerkleRoot.W P depth
  aspRootCalcOut : F
  aspRootCheck : IsZeroW

/-- `BurnIntake(depth, address_bits, pow_bits)`, with inputs `enabled`, `chain_id`, `token_id`,
`owner_public_key`, `burn_public_key`, `burn_salt`, `burn_transfer_from`, `burn_transfer_value`,
`commitment_index`, `asp_root`, `asp_siblings` and outputs `leaf`, `value`. -/
structure Rel (P : PoseidonGadget) (depth addressBits powBits : ℕ)
    (enabled chain token ownerPk burnPk burnSalt burnFrom burnValue idx aspRoot : F)
    (aspSiblings : Fin depth → F) (leaf value : F) (w : W P depth) : Prop where
  disabled : w.disabled = 1 - enabled
  ownerCheck :
    ForceEqualIfEnabled.Rel enabled burnPk ownerPk w.ownerCheck.out w.ownerCheck.inv
  zeroPublicKey :
    ForceEqualIfEnabled.Rel w.disabled burnPk 0 w.zeroPublicKey.out w.zeroPublicKey.inv
  zeroSalt :
    ForceEqualIfEnabled.Rel w.disabled burnSalt 0 w.zeroSalt.out w.zeroSalt.inv
  zeroFrom :
    ForceEqualIfEnabled.Rel w.disabled burnFrom 0 w.zeroFrom.out w.zeroFrom.inv
  zeroValue :
    ForceEqualIfEnabled.Rel w.disabled burnValue 0 w.zeroValue.out w.zeroValue.inv
  transferValueIsZero :
    IsZero.Rel burnValue w.transferValueIsZero.out w.transferValueIsZero.inv
  positiveTransferValue :
    ForceEqualIfEnabled.Rel enabled w.transferValueIsZero.out 0 w.positiveTransferValue.out
      w.positiveTransferValue.inv
  digest : BurnDigest.Rel P chain burnPk burnSalt w.digestOut w.digest
  address : AddressFromDigest.Rel addressBits powBits enabled w.digestOut w.addressOut
    w.address.bits w.address.aliasCheck w.address.aliasOut w.address.num
  transferLeaf : TransferLeaf.Rel P token burnFrom w.addressOut burnValue leaf w.transferLeaf
  aspLeaf : AspLeaf.Rel P idx w.aspLeafOut w.aspLeaf
  aspRootCalc :
    MerkleRoot.Rel P depth w.aspLeafOut idx aspSiblings w.aspRootCalcOut w.aspRootCalc
  aspRootCheck :
    ForceEqualIfEnabled.Rel enabled w.aspRootCalcOut aspRoot w.aspRootCheck.out w.aspRootCheck.inv
  valueEq : value = burnValue

/-- The transfer's leaf, as the commitment tree holds it: it pays the burn address the digest of
`(chain, burnPk, burnSalt)` derives. -/
def leafOf (h : Hashes) (chain token burnPk burnSalt burnFrom burnValue : F) : F :=
  h.H [↑(field0 TRANSFER_TAG token.val), burnFrom,
    ↑(addressOf (burnDigest h chain burnPk burnSalt)), burnValue]

/-- What an enabled branch checks: ownership, a nonzero value, the proof of work, and the ASP's
approval of the position. -/
def Active (h : Hashes) (chain ownerPk burnPk burnSalt burnValue idx aspRoot : F)
    (aspSiblings : Fin DEPTH → F) : Prop :=
  burnPk = ownerPk ∧ burnValue ≠ 0 ∧ (burnDigest h chain burnPk burnSalt).val < POW_BOUND ∧
    merkleRoot h (aspLeaf h idx) idx.val aspSiblings = aspRoot

theorem pow_bits : 2 ^ (254 - 16) = POW_BOUND := by norm_num [POW_BOUND]

/-- The outputs are the transfer's leaf and value, and the ASP path bounds the index whatever
`enabled` is; a nonzero `enabled` forces the branch's checks, and an `enabled` other than 1 forces
the zero burn witness. -/
theorem sound (hP : h.H = P.hash)
    {enabled chain token ownerPk burnPk burnSalt burnFrom burnValue idx aspRoot leaf value : F}
    {aspSiblings : Fin DEPTH → F} {w : W P DEPTH}
    (hr : Rel P DEPTH 160 16 enabled chain token ownerPk burnPk burnSalt burnFrom burnValue idx
      aspRoot aspSiblings leaf value w) :
    leaf = leafOf h chain token burnPk burnSalt burnFrom burnValue ∧ value = burnValue ∧
      idx.val < 2 ^ DEPTH ∧
      (enabled ≠ 0 → Active h chain ownerPk burnPk burnSalt burnValue idx aspRoot aspSiblings) ∧
      (enabled ≠ 1 → burnPk = 0 ∧ burnSalt = 0 ∧ burnFrom = 0 ∧ burnValue = 0) := by
  have hdig := BurnDigest.sound hP hr.digest
  obtain ⟨-, haddr, hpow⟩ := AddressFromDigest.sound hr.address
  obtain ⟨hidx, hasp⟩ := MerkleRoot.sound hP hr.aspRootCalc
  have hasp_leaf := AspLeaf.sound hP hr.aspLeaf
  refine ⟨?_, hr.valueEq, hidx, fun hen => ?_, fun hen => ?_⟩
  · rw [TransferLeaf.sound hP hr.transferLeaf, leafOf, ← hdig, addressOf, ADDRESS_BOUND, ← haddr,
      ZMod.natCast_zmod_val]
  · have hiz := IsZero.sound hr.transferValueIsZero
    rw [ForceEqualIfEnabled.sound hr.positiveTransferValue hen] at hiz
    refine ⟨ForceEqualIfEnabled.sound hr.ownerCheck hen, fun h0 => by simp [h0] at hiz, ?_, ?_⟩
    · rw [← hdig, ← pow_bits]; exact hpow hen
    · rw [← hasp_leaf, ← hasp]; exact ForceEqualIfEnabled.sound hr.aspRootCheck hen
  · have hd : w.disabled ≠ 0 := by rw [hr.disabled]; exact sub_ne_zero.2 (Ne.symm hen)
    exact ⟨ForceEqualIfEnabled.sound hr.zeroPublicKey hd, ForceEqualIfEnabled.sound hr.zeroSalt hd,
      ForceEqualIfEnabled.sound hr.zeroFrom hd, ForceEqualIfEnabled.sound hr.zeroValue hd⟩

theorem complete (hP : h.H = P.hash)
    {enabled chain token ownerPk burnPk burnSalt burnFrom burnValue idx aspRoot : F}
    {aspSiblings : Fin DEPTH → F} (hidx : idx.val < 2 ^ DEPTH)
    (hon : enabled = 0 ∨ Active h chain ownerPk burnPk burnSalt burnValue idx aspRoot aspSiblings)
    (hoff : enabled = 1 ∨ burnPk = 0 ∧ burnSalt = 0 ∧ burnFrom = 0 ∧ burnValue = 0) :
    ∃ w, Rel P DEPTH 160 16 enabled chain token ownerPk burnPk burnSalt burnFrom burnValue idx
      aspRoot aspSiblings (leafOf h chain token burnPk burnSalt burnFrom burnValue) burnValue w := by
  let digest := burnDigest h chain burnPk burnSalt
  let address : F := ↑(addressOf digest)
  obtain ⟨wd, hwd⟩ := BurnDigest.complete hP chain burnPk burnSalt
  obtain ⟨wt, hwt⟩ := TransferLeaf.complete hP token burnFrom address burnValue
  obtain ⟨wa, hwa⟩ := AspLeaf.complete hP idx
  obtain ⟨wm, hwm⟩ := MerkleRoot.complete hP (aspLeaf h idx) idx aspSiblings hidx
  have hafd := AddressFromDigest.complete 160 16 (enabled := enabled) (digest := digest)
    (by rcases hon with h0 | ⟨-, -, hpow, -⟩
        · exact Or.inl h0
        · exact Or.inr (pow_bits ▸ hpow))
  refine ⟨⟨1 - enabled, .honest (ownerPk - burnPk), .honest (0 - burnPk), .honest (0 - burnSalt),
    .honest (0 - burnFrom), .honest (0 - burnValue), .honest burnValue,
    .honest (0 - if burnValue = 0 then 1 else 0), wd, digest, .honest digest, address, wt, wa,
    aspLeaf h idx, wm, merkleRoot h (aspLeaf h idx) idx.val aspSiblings,
    .honest (aspRoot - merkleRoot h (aspLeaf h idx) idx.val aspSiblings)⟩,
    ⟨rfl, ?_, ?_, ?_, ?_, ?_, IsZero.complete burnValue, ?_, hwd, hafd, hwt, hwa, hwm, ?_, rfl⟩⟩
  all_goals refine ForceEqualIfEnabled.complete ?_
  all_goals rcases hon with h0 | ⟨h1, h2, -, h4⟩ <;> simp_all [IsZeroW.honest]

end BurnIntake

/-! ## `main/joinsplit.circom` -/

/-- Two numbers below `r` that agree in `F` are equal. -/
theorem nat_eq_of_cast {m n : ℕ} (hm : m < r) (hn : n < r) (h : (m : F) = n) : m = n := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] at this

/-- A mode flag as its signal. -/
def flag (b : Bool) : F := if b then 1 else 0

theorem flag_bool (b : Bool) : flag b = 0 ∨ flag b = 1 := by cases b <;> simp [flag]

theorem decide_flag (b : Bool) : decide (flag b = 1) = b := by cases b <;> simp [flag]

/-- A boolean signal that reads `false` is 0. -/
theorem eq_zero_of_decide {b : F} (hb : b = 0 ∨ b = 1) (hf : decide (b = 1) = false) : b = 0 :=
  hb.resolve_right (of_decide_eq_false hf)

namespace JoinSplit

/-- Every signal of `main = JoinSplit(MERKLE_DEPTH(), AMOUNT_BITS(), ADDRESS_BITS(),
BURN_POW_BITS())` but the public ones, which `JS.Pub` holds: the private inputs, then the
template's own intermediate signals, then each component's outputs and internal signals. -/
structure Sig (P : PoseidonGadget) where
  entropy : F
  in0IsBurn : F
  in1IsDummy : F
  note0Pk : F
  note0Value : F
  note0Salt : F
  note1Pk : F
  note1Value : F
  note1Salt : F
  burnPk : F
  burnSalt : F
  burnFrom : F
  burnValue : F
  recipientPrivate : F
  amountPrivate : F
  intentPrivate : F
  out1Pk : F
  out1Value : F
  out1Salt : F
  out2Pk : F
  out2Value : F
  out2Salt : F
  sk0 : F
  sk1 : F
  akh0 : F
  akh1 : F
  idx0 : F
  idx1 : F
  sib0 : Fin DEPTH → F
  sib1 : Fin DEPTH → F
  aspSib : Fin DEPTH → F
  in0IsNote : F
  in1IsReal : F
  input0Value : F
  input1Value : F
  selectedIn0Leaf : F
  selectedNullifier1 : F
  amountValues : Fin 6 → F
  addressValues : Fin 2 → F
  tokenRange : RangeCheckW 32
  chainRange : RangeCheckW 64
  amountRange : Fin 6 → RangeCheckW 248
  addressRange : Fin 2 → RangeCheckW 160
  indexRange : Fin 2 → RangeCheckW DEPTH
  nk0 : F
  nk1 : F
  nullifyingKey0 : P.W 2
  nullifyingKey1 : P.W 2
  pk0 : F
  pk1 : F
  publicKey0 : P.W 3
  publicKey1 : P.W 3
  in0NoteLeaf : F
  in0NoteValue : F
  in0Note : NoteSpend.W P
  in0BurnLeaf : F
  in0BurnValue : F
  in0Burn : BurnIntake.W P DEPTH
  in1NoteLeaf : F
  in1NoteValue : F
  in1NoteNullifier : F
  in1Note : NoteSpend.W P
  in0RootOut : F
  in0Root : MerkleRoot.W P DEPTH
  in1RootOut : F
  in1Root : MerkleRoot.W P DEPTH
  in1RootCheck : IsZeroW
  dummyNullifier1Out : F
  dummyNullifier1 : DummyNullifier.W P
  distinctNullifiers : IsZeroW
  outNoteHash1 : P.W 6
  outNoteHash2 : P.W 6
  withdrawInactive : IsZeroW
  zeroWithdrawRecipient : IsZeroW
  zeroWithdrawIntent : IsZeroW

/-- `main` of `joinsplit.circom`, over its public signals `x` and every other signal `a`. The
output `nullifier0` is `in0_note.nullifier`, and `note_hash1`, `note_hash2` are the outputs of
`out_note_hash1`, `out_note_hash2`. -/
structure Rel (P : PoseidonGadget) (x : JS.Pub) (a : Sig P) : Prop where
  in0IsBurnBool : Boolean.Rel a.in0IsBurn
  in1IsDummyBool : Boolean.Rel a.in1IsDummy
  in0IsNote : a.in0IsNote = 1 - a.in0IsBurn
  in1IsReal : a.in1IsReal = 1 - a.in1IsDummy
  tokenRange : RangeCheck.Rel 32 x.token a.tokenRange.bits a.tokenRange.out
  chainRange : RangeCheck.Rel 64 x.chain a.chainRange.bits a.chainRange.out
  amountValues : a.amountValues =
    ![a.amountPrivate, a.burnValue, a.note0Value, a.note1Value, a.out1Value, a.out2Value]
  amountRange : ∀ i,
    RangeCheck.Rel 248 (a.amountValues i) (a.amountRange i).bits (a.amountRange i).out
  addressValues : a.addressValues = ![a.recipientPrivate, a.burnFrom]
  addressRange : ∀ i,
    RangeCheck.Rel 160 (a.addressValues i) (a.addressRange i).bits (a.addressRange i).out
  indexRange0 : RangeCheck.Rel DEPTH a.idx0 (a.indexRange 0).bits (a.indexRange 0).out
  indexRange1 : RangeCheck.Rel DEPTH a.idx1 (a.indexRange 1).bits (a.indexRange 1).out
  publicKey0 : PublicKey.Rel P a.akh0 a.nk0 a.pk0 a.publicKey0
  publicKey1 : PublicKey.Rel P a.akh1 a.nk1 a.pk1 a.publicKey1
  nullifyingKey0 : NullifyingKey.Rel P a.sk0 a.nk0 a.nullifyingKey0
  nullifyingKey1 : NullifyingKey.Rel P a.sk1 a.nk1 a.nullifyingKey1
  in0Note : NoteSpend.Rel P a.in0IsNote x.chain x.token a.note0Pk a.note0Value a.note0Salt a.pk0
    a.idx0 a.nk0 a.in0NoteLeaf a.in0NoteValue x.nf0 a.in0Note
  in0Burn : BurnIntake.Rel P DEPTH 160 16 a.in0IsBurn x.chain x.token a.pk0 a.burnPk a.burnSalt
    a.burnFrom a.burnValue a.idx0 x.asp a.aspSib a.in0BurnLeaf a.in0BurnValue a.in0Burn
  in1Note : NoteSpend.Rel P a.in1IsReal x.chain x.token a.note1Pk a.note1Value a.note1Salt a.pk1
    a.idx1 a.nk1 a.in1NoteLeaf a.in1NoteValue a.in1NoteNullifier a.in1Note
  dummyIndex : a.idx1 * a.in1IsDummy = 0
  dummySiblings : ∀ i, a.sib1 i * a.in1IsDummy = 0
  selectedIn0Leaf :
    a.selectedIn0Leaf = a.in0NoteLeaf + a.in0IsBurn * (a.in0BurnLeaf - a.in0NoteLeaf)
  in0Root : MerkleRoot.Rel P DEPTH a.selectedIn0Leaf a.idx0 a.sib0 a.in0RootOut a.in0Root
  in1Root : MerkleRoot.Rel P DEPTH a.in1NoteLeaf a.idx1 a.sib1 a.in1RootOut a.in1Root
  in0RootEq : a.in0RootOut = x.root
  in1RootCheck : ForceEqualIfEnabled.Rel a.in1IsReal a.in1RootOut x.root a.in1RootCheck.out
    a.in1RootCheck.inv
  dummyNullifier1 :
    DummyNullifier.Rel P 1 x.chain a.entropy a.dummyNullifier1Out a.dummyNullifier1
  selectedNullifier1 : a.selectedNullifier1 =
    a.in1NoteNullifier + a.in1IsDummy * (a.dummyNullifier1Out - a.in1NoteNullifier)
  nullifier1 : x.nf1 = a.selectedNullifier1
  distinctNullifiers :
    IsZero.Rel (x.nf0 - x.nf1) a.distinctNullifiers.out a.distinctNullifiers.inv
  distinctNullifiersOut : a.distinctNullifiers.out = 0
  outNoteHash1 :
    NoteHash.Rel P x.chain a.out1Pk a.out1Value x.token a.out1Salt x.nh1 a.outNoteHash1
  outNoteHash2 :
    NoteHash.Rel P x.chain a.out2Pk a.out2Value x.token a.out2Salt x.nh2 a.outNoteHash2
  input0Value :
    a.input0Value = a.in0NoteValue + a.in0IsBurn * (a.in0BurnValue - a.in0NoteValue)
  input1Value : a.input1Value = a.in1NoteValue * a.in1IsReal
  conservation : a.input0Value + a.input1Value = a.amountPrivate + a.out1Value + a.out2Value
  withdrawInactive : IsZero.Rel a.amountPrivate a.withdrawInactive.out a.withdrawInactive.inv
  zeroWithdrawRecipient : ForceEqualIfEnabled.Rel a.withdrawInactive.out a.recipientPrivate 0
    a.zeroWithdrawRecipient.out a.zeroWithdrawRecipient.inv
  zeroWithdrawIntent : ForceEqualIfEnabled.Rel a.withdrawInactive.out a.intentPrivate 0
    a.zeroWithdrawIntent.out a.zeroWithdrawIntent.inv
  withdrawRecipient : x.recipient = a.recipientPrivate
  withdrawAmount : x.amount = a.amountPrivate
  withdrawIntent : x.intent = a.intentPrivate

/-- The witness parts `JS.Spec` is about. A mode flag reads `true` when its signal is 1. -/
def proj (a : Sig P) : JS.Wit where
  in0IsBurn := decide (a.in0IsBurn = 1)
  in1IsDummy := decide (a.in1IsDummy = 1)
  entropy := a.entropy
  note0 := ⟨a.note0Pk, a.note0Value, a.note0Salt⟩
  note1 := ⟨a.note1Pk, a.note1Value, a.note1Salt⟩
  burnPk := a.burnPk
  burnSalt := a.burnSalt
  burnFrom := a.burnFrom
  burnValue := a.burnValue
  out1 := ⟨a.out1Pk, a.out1Value, a.out1Salt⟩
  out2 := ⟨a.out2Pk, a.out2Value, a.out2Salt⟩
  sk0 := a.sk0
  sk1 := a.sk1
  akh0 := a.akh0
  akh1 := a.akh1
  idx0 := a.idx0
  idx1 := a.idx1
  sib0 := a.sib0
  sib1 := a.sib1
  aspSib := a.aspSib

/-- The constraints imply `JS.Spec`. Conservation lifts from `F` to `ℕ` because the range checks
keep each side below `3·2^248 < r`. -/
theorem sound (hP : h.H = P.hash) {x : JS.Pub} {a : Sig P} (hr : Rel P x a) :
    JS.Spec h x (proj a) := by
  have hb0 := Boolean.sound hr.in0IsBurnBool
  have hb1 := Boolean.sound hr.in1IsDummyBool
  have hamt : ∀ i, (a.amountValues i).val < 2 ^ 248 := fun i =>
    RangeCheck.sound (by norm_num) (hr.amountRange i)
  have haddr : ∀ i, (a.addressValues i).val < 2 ^ 160 := fun i =>
    RangeCheck.sound (by norm_num) (hr.addressRange i)
  rw [hr.amountValues] at hamt
  rw [hr.addressValues] at haddr
  have hnk0 := NullifyingKey.sound hP hr.nullifyingKey0
  have hnk1 := NullifyingKey.sound hP hr.nullifyingKey1
  have hpk0 : a.pk0 = JS.pk0 (h := h) (proj a) := by
    rw [PublicKey.sound hP hr.publicKey0, hnk0]; rfl
  have hpk1 : a.pk1 = JS.pk1 (h := h) (proj a) := by
    rw [PublicKey.sound hP hr.publicKey1, hnk1]; rfl
  obtain ⟨hl0, hv0, hnf0, hown0, hzero0⟩ := NoteSpend.sound hP hr.in0Note
  obtain ⟨hbl, hbv, -, hon, hoff⟩ := BurnIntake.sound hP hr.in0Burn
  obtain ⟨hl1, hv1, hnf1, hown1, hzero1⟩ := NoteSpend.sound hP hr.in1Note
  obtain ⟨-, hroot0⟩ := MerkleRoot.sound hP hr.in0Root
  obtain ⟨-, hroot1⟩ := MerkleRoot.sound hP hr.in1Root
  have hdn := DummyNullifier.sound hP hr.dummyNullifier1
  have hnote : a.in0IsNote = 1 - a.in0IsBurn := hr.in0IsNote
  have hreal : a.in1IsReal = 1 - a.in1IsDummy := hr.in1IsReal
  refine
    { token_lt := RangeCheck.sound (by norm_num) hr.tokenRange
      chain_lt := RangeCheck.sound (by norm_num) hr.chainRange
      amount_lt := by rw [hr.withdrawAmount]; exact hamt 0
      burnValue_lt := hamt 1
      note0_lt := hamt 2
      note1_lt := hamt 3
      out1_lt := hamt 4
      out2_lt := hamt 5
      recipient_lt := by rw [hr.withdrawRecipient]; exact haddr 0
      burnFrom_lt := haddr 1
      idx0_lt := RangeCheck.sound (by norm_num [DEPTH]) hr.indexRange0
      idx1_lt := RangeCheck.sound (by norm_num [DEPTH]) hr.indexRange1
      note0 := fun hf => ?_
      burn0 := fun ht => ?_
      member0 := ?_
      nf0 := by rw [hnf0, hnk0]; rfl
      real1 := fun hf => ?_
      dummy1 := fun ht => ?_
      nf_ne := fun heq => ?_
      nh1 := NoteHash.sound hP hr.outNoteHash1
      nh2 := NoteHash.sound hP hr.outNoteHash2
      conserve := ?_
      noWithdraw := fun h0 => ?_ }
  · have h0 : a.in0IsBurn = 0 := eq_zero_of_decide hb0 hf
    exact ⟨(hown0 (by rw [hnote, h0]; norm_num)).trans hpk0, hoff (by rw [h0]; exact zero_ne_one)⟩
  · have h1 : a.in0IsBurn = 1 := of_decide_eq_true ht
    obtain ⟨hown, hne, hpow, hasp⟩ := hon (by rw [h1]; exact one_ne_zero)
    obtain ⟨z1, z2, z3⟩ := hzero0 (by rw [hnote, h1]; norm_num)
    exact ⟨hown.trans hpk0, hne, hpow, hasp, by simp [proj, JS.Opening.zero, z1, z2, z3]⟩
  · rw [← hr.in0RootEq, hroot0, hr.selectedIn0Leaf, hl0, hbl]
    congr 1
    rcases hb0 with h0 | h0 <;> simp [h0, JS.leaf0, proj, NoteSpend.leafOf, BurnIntake.leafOf]
  · have h0 : a.in1IsDummy = 0 := eq_zero_of_decide hb1 hf
    have hen : a.in1IsReal ≠ 0 := by rw [hreal, h0]; norm_num
    refine ⟨(hown1 hen).trans hpk1, ?_, ?_⟩
    · rw [← ForceEqualIfEnabled.sound hr.in1RootCheck hen, hroot1, hl1]; rfl
    · rw [hr.nullifier1, hr.selectedNullifier1, h0, zero_mul, add_zero, hnf1, hnk1]; rfl
  · have h1 : a.in1IsDummy = 1 := of_decide_eq_true ht
    obtain ⟨z1, z2, z3⟩ := hzero1 (by rw [hreal, h1]; norm_num)
    refine ⟨?_, by simp [proj, JS.Opening.zero, z1, z2, z3], ?_, ?_⟩
    · rw [hr.nullifier1, hr.selectedNullifier1, h1, one_mul, add_sub_cancel, hdn]; rfl
    · simpa [h1] using hr.dummyIndex
    · funext i; simpa [h1] using hr.dummySiblings i
  · have := IsZero.sound hr.distinctNullifiers
    rw [hr.distinctNullifiersOut, heq, sub_self, if_pos rfl] at this
    exact zero_ne_one this
  · have hc := hr.conservation
    rw [hr.input0Value, hr.input1Value, hreal, hv0, hbv, hv1, ← hr.withdrawAmount] at hc
    have hlt0 : JS.value0 (proj a) < 2 ^ 248 := by
      unfold JS.value0; split
      exacts [hamt 1, hamt 2]
    have hlt1 : JS.value1 (proj a) < 2 ^ 248 := by
      unfold JS.value1; split
      exacts [by norm_num, hamt 3]
    have ha : x.amount.val < 2 ^ 248 := by rw [hr.withdrawAmount]; exact hamt 0
    have ho1 : (proj a).out1.value.val < 2 ^ 248 := hamt 4
    have ho2 : (proj a).out2.value.val < 2 ^ 248 := hamt 5
    have := two_pow_253_lt_r
    refine nat_eq_of_cast (by omega) (by omega) ?_
    push_cast [ZMod.natCast_zmod_val]
    rcases hb0 with h0 | h0 <;> rcases hb1 with h1 | h1 <;>
      simp [JS.value0, JS.value1, proj, h0, h1] at hc ⊢ <;>
      linear_combination hc
  · have hiz := IsZero.sound hr.withdrawInactive
    rw [← hr.withdrawAmount, h0, if_pos rfl] at hiz
    have hen : a.withdrawInactive.out ≠ 0 := by rw [hiz]; exact one_ne_zero
    exact ⟨hr.withdrawRecipient.trans (ForceEqualIfEnabled.sound hr.zeroWithdrawRecipient hen),
      hr.withdrawIntent.trans (ForceEqualIfEnabled.sound hr.zeroWithdrawIntent hen)⟩

theorem complete (hP : h.H = P.hash) {x : JS.Pub} {w : JS.Wit} (hs : JS.Spec h x w) :
    ∃ a, Rel P x a ∧ proj a = w := by
  -- The branch preconditions of the per-input templates.
  have hon0 : 1 - flag w.in0IsBurn = 0 ∨ w.note0.pk = JS.pk0 (h := h) w := by
    cases hb : w.in0IsBurn
    · exact Or.inr (hs.note0 hb).1
    · simp [flag]
  have hoff0 : 1 - flag w.in0IsBurn = 1 ∨
      w.note0.pk = 0 ∧ w.note0.value = 0 ∧ w.note0.salt = 0 := by
    cases hb : w.in0IsBurn
    · simp [flag]
    · rw [(hs.burn0 hb).2.2.2.2]; exact Or.inr ⟨rfl, rfl, rfl⟩
  have honB : flag w.in0IsBurn = 0 ∨ BurnIntake.Active h x.chain (JS.pk0 (h := h) w) w.burnPk
      w.burnSalt w.burnValue w.idx0 x.asp w.aspSib := by
    cases hb : w.in0IsBurn
    · simp [flag]
    · obtain ⟨h1, h2, h3, h4, -⟩ := hs.burn0 hb
      exact Or.inr ⟨h1, h2, h3, h4⟩
  have hoffB : flag w.in0IsBurn = 1 ∨
      w.burnPk = 0 ∧ w.burnSalt = 0 ∧ w.burnFrom = 0 ∧ w.burnValue = 0 := by
    cases hb : w.in0IsBurn
    · exact Or.inr (hs.note0 hb).2
    · simp [flag]
  have hon1 : 1 - flag w.in1IsDummy = 0 ∨ w.note1.pk = JS.pk1 (h := h) w := by
    cases hb : w.in1IsDummy
    · exact Or.inr (hs.real1 hb).1
    · simp [flag]
  have hoff1 : 1 - flag w.in1IsDummy = 1 ∨
      w.note1.pk = 0 ∧ w.note1.value = 0 ∧ w.note1.salt = 0 := by
    cases hb : w.in1IsDummy
    · simp [flag]
    · rw [(hs.dummy1 hb).2.1]; exact Or.inr ⟨rfl, rfl, rfl⟩
  -- The components' honest signals.
  obtain ⟨wnk0, hnk0⟩ := NullifyingKey.complete (P := P) hP w.sk0
  obtain ⟨wnk1, hnk1⟩ := NullifyingKey.complete (P := P) hP w.sk1
  obtain ⟨wpk0, hpk0⟩ := PublicKey.complete (P := P) hP w.akh0 (nullifyingKey h w.sk0)
  obtain ⟨wpk1, hpk1⟩ := PublicKey.complete (P := P) hP w.akh1 (nullifyingKey h w.sk1)
  obtain ⟨wn0, hn0⟩ := NoteSpend.complete (P := P) hP (chain := x.chain) (token := x.token)
    (idx := w.idx0) (nk := JS.nk0 (h := h) w) hon0 hoff0
  obtain ⟨wb, hwb⟩ := BurnIntake.complete (P := P) hP (token := x.token) (burnFrom := w.burnFrom)
    hs.idx0_lt honB hoffB
  obtain ⟨wn1, hn1⟩ := NoteSpend.complete (P := P) hP (chain := x.chain) (token := x.token)
    (idx := w.idx1) (nk := JS.nk1 (h := h) w) hon1 hoff1
  obtain ⟨wr0, hr0⟩ := MerkleRoot.complete (P := P) hP (JS.leaf0 h x w) w.idx0 w.sib0 hs.idx0_lt
  obtain ⟨wr1, hr1⟩ := MerkleRoot.complete (P := P) hP (JS.leaf1 h x w) w.idx1 w.sib1 hs.idx1_lt
  obtain ⟨wd, hd⟩ := DummyNullifier.complete (P := P) hP x.chain w.entropy
  obtain ⟨wo1, ho1⟩ := NoteHash.complete (P := P) hP x.chain w.out1.pk w.out1.value x.token
    w.out1.salt
  obtain ⟨wo2, ho2⟩ := NoteHash.complete (P := P) hP x.chain w.out2.pk w.out2.value x.token
    w.out2.salt
  rw [← hs.nf0] at hn0
  rw [hs.member0] at hr0
  rw [← hs.nh1] at ho1
  rw [← hs.nh2] at ho2
  -- The constraints that tie the slots together.
  have hleaf0 : JS.leaf0 h x w =
      NoteSpend.leafOf h x.chain x.token w.note0.pk w.note0.value w.note0.salt +
        flag w.in0IsBurn * (BurnIntake.leafOf h x.chain x.token w.burnPk w.burnSalt w.burnFrom
          w.burnValue - NoteSpend.leafOf h x.chain x.token w.note0.pk w.note0.value w.note0.salt) := by
    cases hb : w.in0IsBurn <;> simp [JS.leaf0, hb, flag, NoteSpend.leafOf, BurnIntake.leafOf]
  have hroot1 : 1 - flag w.in1IsDummy = 0 ∨
      merkleRoot h (JS.leaf1 h x w) w.idx1.val w.sib1 = x.root := by
    cases hb : w.in1IsDummy
    · exact Or.inr (hs.real1 hb).2.1
    · simp [flag]
  have hnf1 : x.nf1 = nullifier h x.chain w.idx1 (JS.nk1 (h := h) w) + flag w.in1IsDummy *
      (dummyNullifier h x.chain w.entropy - nullifier h x.chain w.idx1 (JS.nk1 (h := h) w)) := by
    cases hb : w.in1IsDummy
    · simp [flag, (hs.real1 hb).2.2]
    · simp [flag, (hs.dummy1 hb).1]
  have hidx1 : w.idx1 * flag w.in1IsDummy = 0 := by
    cases hb : w.in1IsDummy
    · simp [flag]
    · simp [flag, (hs.dummy1 hb).2.2.1]
  have hsib1 : ∀ i, w.sib1 i * flag w.in1IsDummy = 0 := fun i => by
    cases hb : w.in1IsDummy
    · simp [flag]
    · simp [flag, (hs.dummy1 hb).2.2.2]
  have hcons : w.note0.value + flag w.in0IsBurn * (w.burnValue - w.note0.value) +
      w.note1.value * (1 - flag w.in1IsDummy) = x.amount + w.out1.value + w.out2.value := by
    have := congrArg (Nat.cast : ℕ → F) hs.conserve
    push_cast [ZMod.natCast_zmod_val] at this
    cases hb0 : w.in0IsBurn <;> cases hb1 : w.in1IsDummy <;>
      simp [JS.value0, JS.value1, flag, hb0, hb1] at this ⊢ <;> linear_combination this
  have hwithdraw : ∀ v : F, (x.amount = 0 → v = 0) →
      (IsZeroW.honest x.amount).out = 0 ∨ v = 0 := fun v hv => by
    by_cases h0 : x.amount = 0
    · exact Or.inr (hv h0)
    · simp [IsZeroW.honest, h0]
  -- The ranges.
  let amounts : Fin 6 → F :=
    ![x.amount, w.burnValue, w.note0.value, w.note1.value, w.out1.value, w.out2.value]
  have hamt : ∀ i, (amounts i).val < 2 ^ 248 := fun i => by
    fin_cases i
    exacts [hs.amount_lt, hs.burnValue_lt, hs.note0_lt, hs.note1_lt, hs.out1_lt, hs.out2_lt]
  have haddr : ∀ i, (![x.recipient, w.burnFrom] i).val < 2 ^ 160 := fun i => by
    fin_cases i
    exacts [hs.recipient_lt, hs.burnFrom_lt]
  refine ⟨
    { entropy := w.entropy
      in0IsBurn := flag w.in0IsBurn
      in1IsDummy := flag w.in1IsDummy
      note0Pk := w.note0.pk
      note0Value := w.note0.value
      note0Salt := w.note0.salt
      note1Pk := w.note1.pk
      note1Value := w.note1.value
      note1Salt := w.note1.salt
      burnPk := w.burnPk
      burnSalt := w.burnSalt
      burnFrom := w.burnFrom
      burnValue := w.burnValue
      recipientPrivate := x.recipient
      amountPrivate := x.amount
      intentPrivate := x.intent
      out1Pk := w.out1.pk
      out1Value := w.out1.value
      out1Salt := w.out1.salt
      out2Pk := w.out2.pk
      out2Value := w.out2.value
      out2Salt := w.out2.salt
      sk0 := w.sk0
      sk1 := w.sk1
      akh0 := w.akh0
      akh1 := w.akh1
      idx0 := w.idx0
      idx1 := w.idx1
      sib0 := w.sib0
      sib1 := w.sib1
      aspSib := w.aspSib
      in0IsNote := 1 - flag w.in0IsBurn
      in1IsReal := 1 - flag w.in1IsDummy
      input0Value := w.note0.value + flag w.in0IsBurn * (w.burnValue - w.note0.value)
      input1Value := w.note1.value * (1 - flag w.in1IsDummy)
      selectedIn0Leaf := JS.leaf0 h x w
      selectedNullifier1 := x.nf1
      amountValues := amounts
      addressValues := ![x.recipient, w.burnFrom]
      tokenRange := .honest 32 x.token
      chainRange := .honest 64 x.chain
      amountRange := fun i => .honest 248 (amounts i)
      addressRange := fun i => .honest 160 (![x.recipient, w.burnFrom] i)
      indexRange := ![.honest DEPTH w.idx0, .honest DEPTH w.idx1]
      nk0 := JS.nk0 (h := h) w
      nk1 := JS.nk1 (h := h) w
      nullifyingKey0 := wnk0
      nullifyingKey1 := wnk1
      pk0 := JS.pk0 (h := h) w
      pk1 := JS.pk1 (h := h) w
      publicKey0 := wpk0
      publicKey1 := wpk1
      in0NoteLeaf := NoteSpend.leafOf h x.chain x.token w.note0.pk w.note0.value w.note0.salt
      in0NoteValue := w.note0.value
      in0Note := wn0
      in0BurnLeaf :=
        BurnIntake.leafOf h x.chain x.token w.burnPk w.burnSalt w.burnFrom w.burnValue
      in0BurnValue := w.burnValue
      in0Burn := wb
      in1NoteLeaf := JS.leaf1 h x w
      in1NoteValue := w.note1.value
      in1NoteNullifier := nullifier h x.chain w.idx1 (JS.nk1 (h := h) w)
      in1Note := wn1
      in0RootOut := x.root
      in0Root := wr0
      in1RootOut := merkleRoot h (JS.leaf1 h x w) w.idx1.val w.sib1
      in1Root := wr1
      in1RootCheck := .honest (x.root - merkleRoot h (JS.leaf1 h x w) w.idx1.val w.sib1)
      dummyNullifier1Out := dummyNullifier h x.chain w.entropy
      dummyNullifier1 := wd
      distinctNullifiers := .honest (x.nf0 - x.nf1)
      outNoteHash1 := wo1
      outNoteHash2 := wo2
      withdrawInactive := .honest x.amount
      zeroWithdrawRecipient := .honest (0 - x.recipient)
      zeroWithdrawIntent := .honest (0 - x.intent) },
    { in0IsBurnBool := Boolean.complete (flag_bool _)
      in1IsDummyBool := Boolean.complete (flag_bool _)
      in0IsNote := rfl
      in1IsReal := rfl
      tokenRange := RangeCheck.complete hs.token_lt
      chainRange := RangeCheck.complete hs.chain_lt
      amountValues := rfl
      amountRange := fun i => RangeCheck.complete (hamt i)
      addressValues := rfl
      addressRange := fun i => RangeCheck.complete (haddr i)
      indexRange0 := RangeCheck.complete hs.idx0_lt
      indexRange1 := RangeCheck.complete hs.idx1_lt
      publicKey0 := hpk0
      publicKey1 := hpk1
      nullifyingKey0 := hnk0
      nullifyingKey1 := hnk1
      in0Note := hn0
      in0Burn := hwb
      in1Note := hn1
      dummyIndex := hidx1
      dummySiblings := hsib1
      selectedIn0Leaf := hleaf0
      in0Root := hr0
      in1Root := hr1
      in0RootEq := rfl
      in1RootCheck := ForceEqualIfEnabled.complete hroot1
      dummyNullifier1 := hd
      selectedNullifier1 := hnf1
      nullifier1 := rfl
      distinctNullifiers := IsZero.complete _
      distinctNullifiersOut := by simp [IsZeroW.honest, sub_eq_zero, hs.nf_ne]
      outNoteHash1 := ho1
      outNoteHash2 := ho2
      input0Value := rfl
      input1Value := rfl
      conservation := hcons
      withdrawInactive := IsZero.complete _
      zeroWithdrawRecipient := ForceEqualIfEnabled.complete
        (by simpa using hwithdraw x.recipient fun h0 => (hs.noWithdraw h0).1)
      zeroWithdrawIntent := ForceEqualIfEnabled.complete
        (by simpa using hwithdraw x.intent fun h0 => (hs.noWithdraw h0).2)
      withdrawRecipient := rfl
      withdrawAmount := rfl
      withdrawIntent := rfl }, ?_⟩
  simp only [proj, decide_flag]

end JoinSplit

/-! ## `main/rageexit.circom` -/

namespace RageExit

/-- Every signal of `main = RageExit(MERKLE_DEPTH(), ADDRESS_BITS(), BURN_POW_BITS())` but the
public ones, which `RE.Pub` holds: the private inputs, then each component's outputs and internal
signals. -/
structure Sig (P : PoseidonGadget) where
  sk : F
  akh : F
  salt : F
  chainRange : RangeCheckW 64
  indexRange : RangeCheckW DEPTH
  nk : F
  nullifyingKey : P.W 2
  pk : F
  publicKey : P.W 3
  digestOut : F
  digest : P.W 5
  addressOut : F
  derivedBurnAddress : AddressFromDigestW
  nf : P.W 5

/-- `main` of `rageexit.circom`, over its public signals `x` and every other signal `a`. The
output `nullifier` is `nf.nullifier`. -/
structure Rel (P : PoseidonGadget) (x : RE.Pub) (a : Sig P) : Prop where
  chainRange : RangeCheck.Rel 64 x.chain a.chainRange.bits a.chainRange.out
  indexRange : RangeCheck.Rel DEPTH x.idx a.indexRange.bits a.indexRange.out
  nullifyingKey : NullifyingKey.Rel P a.sk a.nk a.nullifyingKey
  publicKey : PublicKey.Rel P a.akh a.nk a.pk a.publicKey
  digest : BurnDigest.Rel P x.chain a.pk a.salt a.digestOut a.digest
  derivedBurnAddress : AddressFromDigest.Rel 160 16 1 a.digestOut a.addressOut
    a.derivedBurnAddress.bits a.derivedBurnAddress.aliasCheck a.derivedBurnAddress.aliasOut
    a.derivedBurnAddress.num
  addressEq : a.addressOut = x.address
  nf : Nullifier.Rel P x.chain x.idx a.nk x.nf a.nf

/-- The witness parts `RE.Spec` is about. -/
def proj (a : Sig P) : RE.Wit := ⟨a.sk, a.akh, a.salt⟩

theorem sound (hP : h.H = P.hash) {x : RE.Pub} {a : Sig P} (hr : Rel P x a) :
    RE.Spec h x (proj a) := by
  have hnk := NullifyingKey.sound hP hr.nullifyingKey
  have hdig := BurnDigest.sound hP hr.digest
  rw [PublicKey.sound hP hr.publicKey, hnk] at hdig
  obtain ⟨-, haddr, hpow⟩ := AddressFromDigest.sound hr.derivedBurnAddress
  rw [hdig] at haddr hpow
  refine ⟨RangeCheck.sound (by norm_num) hr.chainRange,
    RangeCheck.sound (by norm_num [DEPTH]) hr.indexRange, ?_, ?_, ?_⟩
  · rw [← BurnIntake.pow_bits]; exact hpow one_ne_zero
  · rw [← hr.addressEq]
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg Nat.cast haddr)
  · rw [Nullifier.sound hP hr.nf, hnk]; rfl

theorem complete (hP : h.H = P.hash) {x : RE.Pub} {w : RE.Wit} (hs : RE.Spec h x w) :
    ∃ a, Rel P x a ∧ proj a = w := by
  let digest := burnDigest h x.chain (RE.pk h w) w.salt
  obtain ⟨wnk, hnk⟩ := NullifyingKey.complete (P := P) hP w.sk
  obtain ⟨wpk, hpk⟩ := PublicKey.complete (P := P) hP w.akh (nullifyingKey h w.sk)
  obtain ⟨wd, hd⟩ := BurnDigest.complete (P := P) hP x.chain (RE.pk h w) w.salt
  obtain ⟨wn, hn⟩ := Nullifier.complete (P := P) hP x.chain x.idx (nullifyingKey h w.sk)
  rw [← hs.nf] at hn
  have hafd := AddressFromDigest.complete 160 16 (enabled := 1) (digest := digest)
    (Or.inr (BurnIntake.pow_bits ▸ hs.pow))
  refine ⟨
    { sk := w.sk
      akh := w.akh
      salt := w.salt
      chainRange := .honest 64 x.chain
      indexRange := .honest DEPTH x.idx
      nk := nullifyingKey h w.sk
      nullifyingKey := wnk
      pk := RE.pk h w
      publicKey := wpk
      digestOut := digest
      digest := wd
      addressOut := x.address
      derivedBurnAddress := .honest digest
      nf := wn },
    ⟨RangeCheck.complete hs.chain_lt, RangeCheck.complete hs.idx_lt, hnk, hpk, hd, ?_, rfl, hn⟩,
    rfl⟩
  rw [hs.address]
  exact hafd

end RageExit

/-! ## circomlib's `Poseidon`

The templates instantiated with circomlib's `Poseidon(n)` as `Circomlib.Poseidon` models it, so the
two circuits prove their statements for the hash that model computes. -/

/-- circomlib's `Poseidon(n)`. -/
def circomlibPoseidon : PoseidonGadget where
  W n := PoseidonEx.Signals (n + 1)
  Rel := Circomlib.Poseidon.Rel
  hash := Zerc20.Poseidon.hash
  sound hn hr := Circomlib.Poseidon.sound hn hr
  complete hn ins := ⟨_, Circomlib.Poseidon.complete hn ins⟩

namespace JoinSplit

/-- Every assignment that satisfies the compiled `JoinSplit` proves `JS.Spec`. -/
theorem main_sound (hP : h.H = Zerc20.Poseidon.hash) {x : JS.Pub}
    {a : Sig circomlibPoseidon} (hr : Rel circomlibPoseidon x a) : JS.Spec h x (proj a) :=
  sound hP hr

/-- Every `JS.Spec` witness extends to an assignment that satisfies the compiled `JoinSplit`. -/
theorem main_complete (hP : h.H = Zerc20.Poseidon.hash) {x : JS.Pub} {w : JS.Wit}
    (hs : JS.Spec h x w) : ∃ a, Rel circomlibPoseidon x a ∧ proj a = w :=
  complete hP hs

end JoinSplit

namespace RageExit

/-- Every assignment that satisfies the compiled `RageExit` proves `RE.Spec`. -/
theorem main_sound (hP : h.H = Zerc20.Poseidon.hash) {x : RE.Pub}
    {a : Sig circomlibPoseidon} (hr : Rel circomlibPoseidon x a) : RE.Spec h x (proj a) :=
  sound hP hr

/-- Every `RE.Spec` witness extends to an assignment that satisfies the compiled `RageExit`. -/
theorem main_complete (hP : h.H = Zerc20.Poseidon.hash) {x : RE.Pub} {w : RE.Wit}
    (hs : RE.Spec h x w) : ∃ a, Rel circomlibPoseidon x a ∧ proj a = w :=
  complete hP hs

end RageExit


end Zerc20.Circom

