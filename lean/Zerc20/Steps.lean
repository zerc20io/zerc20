import Zerc20.Spec
import Zerc20.Ark
import Zerc20.Sha256
import Zerc20.BabyJubJub
import Zerc20.Poseidon

/-!
# The Nova step circuits

Models of the arkworks circuits in `zkp/src`: `tree::merkle_root_var`, `auth::verify_var`, and the
`synthesize_step` of `RootCircuit` and `MergeCircuit`, each proved sound and complete against the
statement `Spec` gives it.

Poseidon enters through `PoseidonVarGadget`, the interface of `poseidon::hash_var`, so the proofs
hold for any gadget that computes a hash function; the end of the file plugs in arkworks'
`PoseidonSpongeVar` with circomlib's parameters. SHA-256 enters through
`primitives.hash_chain_var` and Baby-JubJub through the `AffineVar` gadgets.

The state variables of a step are allocated by the folding scheme, so the models take them as
variables. Every other variable is allocated inside the step and is a witness of its `Rel`.
-/

namespace Zerc20.Zkp

open Ark

/-! ## Poseidon -/

/-- `poseidon::hash_var`, the gadget behind every Poseidon call of the step circuits: `n` inputs,
the config of rate `n`, one output. Its constraints and witnesses stay abstract; only what it
computes matters here. -/
structure PoseidonVarGadget where
  /-- The witnesses of one call on `n` inputs. -/
  W : ℕ → Type
  /-- The variable the call returns. -/
  hash_var : (n : ℕ) → (Fin n → FpVar) → W n → FpVar
  /-- The constraints of one call. -/
  Rel : (n : ℕ) → (Fin n → FpVar) → W n → Prop
  /-- The hash function the gadget computes. -/
  hash : List F → F
  sound : ∀ {n ins w}, Rel n ins w →
    (hash_var n ins w).val = hash (List.ofFn fun i => (ins i).val)
  /-- Every input of the widths the circuits use has satisfying witnesses. -/
  complete : ∀ n ins, 2 ≤ n → n ≤ 6 → ∃ w, Rel n ins w

variable {P : PoseidonVarGadget}

@[simp] theorem val_var (x : F) : (FpVar.var x).val = x := rfl

@[simp] theorem val_const (c : F) : (FpVar.const c).val = c := rfl

namespace primitives

/-- `domain_hash_var`: `hash_var` over the constant domain tag followed by `values`. -/
def domain_hash_var (P : PoseidonVarGadget) (domain : F) {n : ℕ} (values : Fin n → FpVar)
    (w : P.W (n + 1)) : FpVar :=
  P.hash_var (n + 1) (Matrix.vecCons (.const domain) values) w

def domain_hash_var.Rel (P : PoseidonVarGadget) (domain : F) {n : ℕ} (values : Fin n → FpVar)
    (w : P.W (n + 1)) : Prop :=
  P.Rel (n + 1) (Matrix.vecCons (.const domain) values) w

theorem domain_hash_var.sound {domain : F} {n : ℕ} {values : Fin n → FpVar} {w : P.W (n + 1)}
    (h : domain_hash_var.Rel P domain values w) :
    (domain_hash_var P domain values w).val =
      P.hash (domain :: List.ofFn fun i => (values i).val) := by
  rw [domain_hash_var, P.sound h, List.ofFn_succ]
  rfl

theorem domain_hash_var.complete (domain : F) {n : ℕ} (values : Fin n → FpVar) (h1 : 1 ≤ n)
    (h5 : n ≤ 5) : ∃ w, domain_hash_var.Rel P domain values w :=
  P.complete _ _ (by omega) (by omega)

/-- `note_hash_var`: `DomainHash5(NOTE, chain_id, public_key, value, token_id, note_salt)`. -/
def note_hash_var (P : PoseidonVarGadget) (chain pk value token salt : FpVar) (w : P.W 6) : FpVar :=
  domain_hash_var P DOMAIN_NOTE ![chain, pk, value, token, salt] w

/-- The value `hash_chain_var` returns, as a field element. -/
theorem hash_chain_var_val {prev : F} {values : List F} {w : HashChainWit}
    (h : (hash_chain_var prev values w).2) :
    (hash_chain_var prev values w).1.val = ↑(Sha256.hashChain prev.val (values.map ZMod.val)) := by
  rw [← (hash_chain_var.sound h).2, ZMod.natCast_zmod_val]

end primitives

/-! ## `tree::merkle_root_var` -/

namespace tree

/-- The witnesses of one level: the two selections and the hash. -/
structure Level (P : PoseidonVarGadget) where
  left : F
  right : F
  hash : P.W 2

/-- One level of the fold, on the index bit `is_right` and the sibling of the level:
`left = is_right.select(sibling, current)`, `right = is_right.select(current, sibling)`, and
`Poseidon(2)` of the pair. -/
def level (P : PoseidonVarGadget) (pair : Boolean × FpVar) (current : FpVar) (w : Level P) :
    FpVar × Prop :=
  let left := FpVar.conditionally_select pair.1 pair.2 current w.left
  let right := FpVar.conditionally_select pair.1 current pair.2 w.right
  (P.hash_var 2 ![left, right] w.hash,
    FpVar.conditionally_select.Rel pair.1 pair.2 current w.left ∧
      FpVar.conditionally_select.Rel pair.1 current pair.2 w.right ∧ P.Rel 2 ![left, right] w.hash)

/-- `merkle_root_var`: the fold of `level` over the index bits and the siblings, from the leaf.
The step circuits pass the same bits to several calls. -/
def merkle_root_var (P : PoseidonVarGadget) (leaf : FpVar) (bits : Fin DEPTH → Boolean)
    (siblings : Fin DEPTH → FpVar) (w : List (Level P)) : FpVar × Prop :=
  loop (level P) (List.ofFn fun k => (bits k, siblings k)) w leaf

/-- The value a level computes from the bit `j.1` and the sibling `j.2`. -/
def pathStep (H : List F → F) (current : F) (j : Bool × F) : F :=
  if j.1 then H [j.2, current] else H [current, j.2]

theorem pathRoot_eq_foldl (h : Hashes) (leaf : F) (idx : ℕ) (sib : Fin DEPTH → F) :
    ∀ n (hn : n ≤ DEPTH), pathRoot h leaf idx sib n =
      (List.ofFn fun k : Fin n => (idx.testBit k, sib (Fin.castLE hn k))).foldl (pathStep h.H) leaf
  | 0, _ => rfl
  | n + 1, hn => by
    have hk : n < DEPTH := by omega
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat]
    simp only [pathRoot, hk, dite_true, pathRoot_eq_foldl h leaf idx sib n hk.le, pathStep,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
    rfl

theorem merkleRoot_eq_foldl (h : Hashes) (leaf : F) (idx : ℕ) (sib : Fin DEPTH → F) :
    merkleRoot h leaf idx sib =
      (List.ofFn fun k : Fin DEPTH => (idx.testBit k, sib k)).foldl (pathStep h.H) leaf :=
  pathRoot_eq_foldl h leaf idx sib DEPTH le_rfl

theorem ofFn_two (f : Fin 2 → F) : List.ofFn f = [f 0, f 1] := by simp [List.ofFn_succ]

theorem level.sound {pair : Boolean × FpVar} {cur : FpVar} {w : Level P} {p : Bool}
    (hb : pair.1.val = bit p) (h : (level P pair cur w).2) :
    (level P pair cur w).1.val = pathStep P.hash cur.val (p, pair.2.val) := by
  obtain ⟨hl, hr, hh⟩ := h
  simp only [level]
  rw [P.sound hh, ofFn_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    FpVar.conditionally_select.sound hb hl, FpVar.conditionally_select.sound hb hr, pathStep]
  cases p <;> rfl

/-- The pairs the fold reads carry the index bits and the siblings' values. -/
def Carries (pair : Boolean × FpVar) (j : Bool × F) : Prop :=
  pair.1.val = bit j.1 ∧ pair.2.val = j.2

theorem carries {bits : Fin DEPTH → Boolean} {siblings : Fin DEPTH → FpVar} {idx : ℕ}
    (hbits : ∀ k, (bits k).val = bit (idx.testBit k)) :
    List.Forall₂ Carries (List.ofFn fun k => (bits k, siblings k))
      (List.ofFn fun k : Fin DEPTH => (idx.testBit k, (siblings k).val)) :=
  FpVar.forall₂_ofFn fun k => ⟨hbits k, rfl⟩

theorem level.step {i : Boolean × FpVar} {j : Bool × F} {a : FpVar} {b : F} {x : Level P}
    (hq : Carries i j) (hS : a.val = b) (hx : (level P i a x).2) :
    (level P i a x).1.val = pathStep P.hash b j := by
  rw [level.sound hq.1 hx, hS, hq.2]

/-- With the bits of `idx`, the result is the root `merkleRoot` computes: bit `k` set makes the
running value the right child. -/
theorem merkle_root_var.sound (h : Hashes) (hH : h.H = P.hash) {leaf : FpVar}
    {bits : Fin DEPTH → Boolean} {siblings : Fin DEPTH → FpVar} {w : List (Level P)} {idx : ℕ}
    (hbits : ∀ k, (bits k).val = bit (idx.testBit k))
    (hR : (merkle_root_var P leaf bits siblings w).2) :
    (merkle_root_var P leaf bits siblings w).1.val =
      merkleRoot h leaf.val idx fun k => (siblings k).val := by
  rw [merkleRoot_eq_foldl, hH]
  exact loop_sound (step := level P) (spec := pathStep P.hash) (Q := Carries)
    (S := fun a b => FpVar.val a = b)
    (fun i j a b x hq hS hx => level.step hq hS hx) (carries hbits) rfl hR

/-- Completeness: any leaf, bits and siblings have satisfying witnesses. -/
theorem merkle_root_var.complete (h : Hashes) (hH : h.H = P.hash) (leaf : FpVar)
    (bits : Fin DEPTH → Boolean) (siblings : Fin DEPTH → FpVar) {idx : ℕ}
    (hbits : ∀ k, (bits k).val = bit (idx.testBit k)) :
    ∃ w, (merkle_root_var P leaf bits siblings w).2 ∧
      (merkle_root_var P leaf bits siblings w).1.val =
        merkleRoot h leaf.val idx fun k => (siblings k).val := by
  obtain ⟨w, hw⟩ := loop_complete (step := level P) (spec := pathStep P.hash) (Q := Carries)
    (S := fun a b => FpVar.val a = b) (fun i j a b hq hS => by
      obtain ⟨wh, hwh⟩ := P.complete 2 ![FpVar.conditionally_select i.1 i.2 a
        (FpVar.conditionally_select.wit i.1 i.2 a), FpVar.conditionally_select i.1 a i.2
        (FpVar.conditionally_select.wit i.1 a i.2)] le_rfl (by norm_num)
      have hx : (level P i a ⟨_, _, wh⟩).2 :=
        ⟨FpVar.conditionally_select.complete _ _ _, FpVar.conditionally_select.complete _ _ _,
          hwh⟩
      exact ⟨_, hx, level.step hq hS hx⟩) (carries (siblings := siblings) hbits)
    (rfl : FpVar.val leaf = leaf.val)
  exact ⟨w, hw, merkle_root_var.sound h hH hbits hw⟩

end tree

/-! ## `auth::verify_var` -/

namespace auth

open BabyJubJub AffineVar

/-- `DOMAIN_SPEND_AUTH`, the domain tag of a signature's challenge. -/
def DOMAIN_SPEND_AUTH : F :=
  8230886534581055996046092392097874170742872724656370212214393322619803652446

/-- `GENERATOR_POWERS`: `2^i·G` for each of the 251 bits of a scalar, by doubling as arkworks does
natively. Doubling also keeps it cheap to compute: `2^i • G` by repeated addition would take
`2^i` steps. -/
def GENERATOR_POWERS : List Point := List.iterate (fun P => P + P) G 251

/-- `auth_key_hash_var`. -/
def auth_key_hash_var (key : F × F) (w : P.W 3) : FpVar :=
  primitives.domain_hash_var P DOMAIN_AUTH_KEY ![.var key.1, .var key.2] w

/-- `merge_message_var`. -/
def merge_message_var (nfChain outPk outSalt fee feeRecipient : FpVar) (w : P.W 6) : FpVar :=
  primitives.domain_hash_var P DOMAIN_MERGE_AUTH ![nfChain, outPk, outSalt, fee, feeRecipient] w

/-- The challenge of a signature with nonce point `R` on `m`, under a key hashing to `keyHash`, as
the integer below `r` its canonical bits encode. -/
def challenge (H : List F → F) (R : Point) (keyHash m : F) : ℕ :=
  (H [DOMAIN_SPEND_AUTH, R.x, R.y, keyHash, m]).val

/-- What `verify_var` proves of the key `A`: it is not the identity, and a nonce point `R` in
`8·E` and an `s < 2^251` satisfy `s·G = c·A + R`. -/
def Verifies (H : List F → F) (A : Point) (keyHash m : F) : Prop :=
  A ≠ 0 ∧ ∃ R : Point, (∃ Q : Point, R = 8 • Q) ∧
    ∃ s < 2 ^ 251, s • G = challenge H R keyHash m • A + R

/-- A valid owner signature on `m` under the auth key `ak`: `ak` is a point of `8·E`, as its
allocation makes it, and `verify_var`'s check holds with the key hash `authKeyHash`. -/
def schnorrOK (H : List F → F) (ak : F × F) (m : F) : Prop :=
  ∃ A : Point, ofPoint A = ak ∧ (∃ P : Point, A = 8 • P) ∧
    Verifies H A (H [DOMAIN_AUTH_KEY, ak.1, ak.2]) m

/-- The witnesses of `verify_var`: the key's `is_zero`, the nonce point's allocation, the bits of
`s`, the challenge, `s·G`, the challenge's bits, `c·key`, and the sum. -/
structure VerifyWit (P : PoseidonVarGadget) where
  keyIsZero : IsZeroW
  r : NewWitnessW
  s : Fin 251 → F
  c : P.W 5
  sG : List ChunkW
  cBits : FpVar.ToBitsWit
  cKey : List ScalarMulW
  sum : AddW

namespace verify_var

/-- The nonce point `R`, allocated as a witness. -/
def R (w : VerifyWit P) : F × F := new_witness.out w.r

/-- The challenge `DomainHash4(SPEND_AUTH, R.x, R.y, key_hash, message)`. -/
def c (keyHash message : FpVar) (w : VerifyWit P) : FpVar :=
  primitives.domain_hash_var P DOMAIN_SPEND_AUTH ![.var (R w).1, .var (R w).2, keyHash, message] w.c

/-- The bits of `s` paired with `GENERATOR_POWERS`. -/
def sBases (w : VerifyWit P) : List (F × Point) := (List.ofFn w.s).zip GENERATOR_POWERS

/-- The values of `c.to_bits_le()`. -/
def cBits (keyHash message : FpVar) (w : VerifyWit P) : List F :=
  List.ofFn fun i => (FpVar.to_bits_le (c keyHash message w) w.cBits i).val

/-- `verify_var` on the allocated `key`: `key` is not zero; `R` and the 251 bits of `s` are
allocated; `s·G` is `precomputed_base_scalar_mul_le` over `GENERATOR_POWERS` from zero; and
`key.scalar_mul_le(c.to_bits_le()) + R` is enforced equal to it. -/
structure Rel (key : F × F) (keyHash message : FpVar) (w : VerifyWit P) : Prop where
  keyIsZero : is_zero.Rel key w.keyIsZero
  keyNonZero : Boolean.enforce_equal.Rel (.var w.keyIsZero.out) (.const false)
  r : new_witness.Rel w.r
  s : ∀ i, Boolean.new_witness.Rel (w.s i)
  cHash : primitives.domain_hash_var.Rel P DOMAIN_SPEND_AUTH
    ![.var (R w).1, .var (R w).2, keyHash, message] w.c
  sG : precomputed_base_scalar_mul_le.Rel zero (sBases w) w.sG
  cToBits : FpVar.to_bits_le.Rel (c keyHash message w) w.cBits
  cKey : scalar_mul_le.Rel zero key (cBits keyHash message w) w.cKey
  sum : add.Rel (scalar_mul_le.out zero w.cKey) (R w) w.sum
  eq : enforce_equal.Rel (add.out w.sum) (precomputed_base_scalar_mul_le.out zero (sBases w) w.sG)

end verify_var

theorem natOfBitsLE_ofFn : ∀ {n : ℕ} (b : Fin n → Bool), natOfBitsLE (List.ofFn b) = natOfBits b
  | 0, _ => rfl
  | n + 1, b => by
    rw [List.ofFn_succ, natOfBitsLE_cons, natOfBitsLE_ofFn, natOfBits, natOfBits, Fin.sum_univ_succ,
      Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Field bits read as the `Bool`s they carry. -/
theorem ofFn_bits {n : ℕ} {x : Fin n → F} {b : Fin n → Bool} (h : ∀ i, x i = bit (b i)) :
    List.ofFn x = bitVals (List.ofFn b) := by
  rw [bitVals, List.map_ofFn]
  congr 1
  funext i
  simp [h, bit_eq]

theorem zip_bits {n : ℕ} {x : Fin n → F} {b : Fin n → Bool} (h : ∀ i, x i = bit (b i))
    (gs : List Point) : (List.ofFn x).zip gs = pairVals ((List.ofFn b).zip gs) := by
  rw [ofFn_bits h, bitVals, List.zip_map_left, pairVals]
  rfl

theorem length_GENERATOR_POWERS : GENERATOR_POWERS.length = 251 := List.length_iterate _ _ _

theorem GENERATOR_POWERS_getElem (i : ℕ) (hi : i < GENERATOR_POWERS.length) :
    GENERATOR_POWERS[i] = 2 ^ i • G := by
  simp only [GENERATOR_POWERS, List.getElem_iterate]
  clear hi
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih, pow_succ, mul_nsmul, two_nsmul]

theorem natOfBitsLE_testBit {n : ℕ} (x : ℕ) :
    natOfBitsLE (List.ofFn fun i : Fin n => x.testBit i) = x % 2 ^ n := by
  rw [natOfBitsLE_ofFn, natOfBits_testBit]

/-- `c.to_bits_le()` carries the canonical bits of `c`. -/
theorem cBits_eq {keyHash message : FpVar} {w : VerifyWit P}
    (h : FpVar.to_bits_le.Rel (verify_var.c keyHash message w) w.cBits) :
    verify_var.cBits keyHash message w =
      bitVals (List.ofFn fun i : Fin 254 => (verify_var.c keyHash message w).val.val.testBit i) :=
  ofFn_bits fun i => FpVar.to_bits_le.sound h i

theorem natOfBitsLE_val (x : F) :
    natOfBitsLE (List.ofFn fun i : Fin 254 => x.val.testBit i) = x.val := by
  rw [natOfBitsLE_testBit, Nat.mod_eq_of_lt (FpVar.val_lt_two_pow_254 x)]

theorem c_val {keyHash message : FpVar} {w : VerifyWit P} {R : Point}
    (hR : verify_var.R w = ofPoint R)
    (h : primitives.domain_hash_var.Rel P DOMAIN_SPEND_AUTH
      ![.var (verify_var.R w).1, .var (verify_var.R w).2, keyHash, message] w.c) :
    (verify_var.c keyHash message w).val.val = challenge P.hash R keyHash.val message.val := by
  rw [verify_var.c, primitives.domain_hash_var.sound h, challenge, hR]
  simp [List.ofFn_succ, ofPoint]

/-- Soundness: the constraints prove `Verifies` of the key. -/
theorem verify_var.sound {A : Point} {keyHash message : FpVar} {w : VerifyWit P}
    (h : verify_var.Rel (ofPoint A) keyHash message w) :
    Verifies P.hash A keyHash.val message.val := by
  have hA : A ≠ 0 := by
    intro hA0
    have hout : w.keyIsZero.out = 1 := by rw [is_zero.sound h.keyIsZero, if_pos (by rw [hA0]; rfl)]
    have h2 := h.keyNonZero
    simp [Boolean.enforce_equal.Rel, Boolean.conditional_enforce_equal.Rel, Boolean.val, bit,
      hout] at h2
  obtain ⟨Q, -, hR⟩ := new_witness.sound h.r
  have hs : ∀ i, w.s i = bit (decide (w.s i = 1)) := fun i => Boolean.new_witness.sound (h.s i)
  have hsB : verify_var.sBases w = _ := zip_bits hs GENERATOR_POWERS
  have hsG := precomputed_base_scalar_mul_le.sound (G := G)
    (by rw [length_GENERATOR_POWERS, List.length_ofFn]) GENERATOR_POWERS_getElem (hsB ▸ h.sG)
  have hcK := scalar_mul_le.sound (cBits_eq h.cToBits ▸ h.cKey)
  rw [natOfBitsLE_val, c_val hR h.cHash] at hcK
  have hsum := add.sound (P := challenge P.hash (8 • Q) keyHash.val message.val • A)
    (Q := 8 • Q) (w := w.sum) (by rw [← hcK, ← hR]; exact h.sum)
  have heq := enforce_equal.sound h.eq
  rw [hsB, hsum, hsG] at heq
  refine ⟨hA, 8 • Q, ⟨Q, rfl⟩, _, ?_, (ofPoint_injective heq).symm⟩
  rw [natOfBitsLE_ofFn]
  exact natOfBits_lt _

/-! ### Completeness -/

/-- `(k + l·m)·G = k·G`, since `l·G = 0`. -/
theorem smul_add_l (k m : ℕ) : (k + l * m) • G = k • G := by
  rw [add_nsmul, mul_nsmul, l_smul_G, smul_zero, add_zero]

theorem smul_mod_l (n : ℕ) : (n % l) • G = n • G := by
  conv_rhs => rw [← Nat.mod_add_div n l]
  rw [smul_add_l]

/-- `8⁻¹ mod l`: `l ≡ 1 (mod 8)`, so `8` divides `7·l + 1`. -/
def inv8 : ℕ := (7 * l + 1) / 8

theorem eight_mul_inv8 : 8 * inv8 = 7 * l + 1 := by unfold inv8 l; norm_num

/-- Every multiple of `G` lies in `8·E`. -/
theorem smul_G_mem8 (k : ℕ) : k • G = 8 • ((inv8 * k) • G) := by
  rw [← mul_nsmul, show inv8 * k * 8 = k + l * (7 * k) by
    rw [mul_comm inv8 k, mul_assoc, mul_comm inv8, eight_mul_inv8]; ring, smul_add_l]

theorem l_lt : l < 2 ^ 251 := by unfold l; norm_num

/-- An honest signer's `s = (k + c·ask) mod l` satisfies `s·G = c·A + R` for `A = ask·G` and
`R = k·G`. -/
theorem sign_eq (k c ask : ℕ) : ((k + c * ask) % l) • G = c • (ask • G) + k • G := by
  rw [smul_mod_l, add_nsmul, add_comm, mul_comm c ask, mul_nsmul]

theorem is_zero_out {A : Point} (hA : A ≠ 0) : (is_zero.wit (ofPoint A)).out = 0 := by
  have : ofPoint A ≠ zero := fun h => hA (ofPoint_injective (h.trans zero_eq))
  simp [is_zero.wit, this]

/-- Completeness: a key `A ≠ 0` and a signature `(R, s)` with `R ∈ 8·E`, `s < 2^251` and
`s·G = c·A + R` satisfy the constraints, with `R` as the nonce point. -/
theorem verify_var.complete {A R Q : Point} {s : ℕ} (hA : A ≠ 0) (hQ : R = 8 • Q)
    (hs : s < 2 ^ 251) (keyHash message : FpVar)
    (heq : s • G = challenge P.hash R keyHash.val message.val • A + R) :
    ∃ w : VerifyWit P,
      verify_var.Rel (ofPoint A) keyHash message w ∧ verify_var.R w = ofPoint R := by
  obtain ⟨hr, hrOut⟩ := new_witness.complete Q
  rw [← hQ] at hrOut
  obtain ⟨wc, hc⟩ := primitives.domain_hash_var.complete (P := P) DOMAIN_SPEND_AUTH
    ![.var (new_witness.out (new_witness.wit Q)).1, .var (new_witness.out (new_witness.wit Q)).2,
      keyHash, message] (by norm_num) (by norm_num)
  let sb : Fin 251 → Bool := fun i => s.testBit i
  let w : VerifyWit P :=
    { keyIsZero := is_zero.wit (ofPoint A)
      r := new_witness.wit Q
      s := fun i => bit (sb i)
      c := wc
      sG := precomputed_base_scalar_mul_le.wit 0 ((List.ofFn sb).zip GENERATOR_POWERS)
      cBits := FpVar.to_bits_le.wit (primitives.domain_hash_var P DOMAIN_SPEND_AUTH
        ![.var (new_witness.out (new_witness.wit Q)).1, .var (new_witness.out (new_witness.wit Q)).2,
          keyHash, message] wc)
      cKey := scalar_mul_le.wit 0 A (List.ofFn fun i : Fin 254 =>
        (challenge P.hash R keyHash.val message.val).testBit i)
      sum := add.wit (challenge P.hash R keyHash.val message.val • A) R }
  have hR : verify_var.R w = ofPoint R := hrOut
  have hcv : (verify_var.c keyHash message w).val.val = challenge P.hash R keyHash.val message.val :=
    c_val hR hc
  have hcb : FpVar.to_bits_le.Rel (verify_var.c keyHash message w) w.cBits :=
    FpVar.to_bits_le.complete _
  have hsB : verify_var.sBases w = pairVals ((List.ofFn sb).zip GENERATOR_POWERS) :=
    zip_bits (fun _ => rfl) _
  have hcK : scalar_mul_le.Rel zero (ofPoint A) (verify_var.cBits keyHash message w) w.cKey := by
    rw [cBits_eq hcb, hcv]
    exact scalar_mul_le.complete A _
  have hcA := scalar_mul_le.sound (cBits_eq hcb ▸ hcK)
  rw [natOfBitsLE_val, hcv] at hcA
  obtain ⟨hsum, hsumOut⟩ := add.complete (challenge P.hash R keyHash.val message.val • A) R
  refine ⟨w, ⟨is_zero.complete _, ?_, hr, fun _ => Boolean.new_witness.complete _, hc,
    hsB ▸ precomputed_base_scalar_mul_le.complete _, hcb, hcK, ?_, ?_⟩, hR⟩
  · exact Boolean.enforce_equal.complete (p := false) (is_zero_out hA) rfl
  · rw [hcA, hR]; exact hsum
  · have hsG := precomputed_base_scalar_mul_le.sound (G := G)
      (by rw [length_GENERATOR_POWERS, List.length_ofFn]) GENERATOR_POWERS_getElem
      (precomputed_base_scalar_mul_le.complete ((List.ofFn sb).zip GENERATOR_POWERS))
    rw [hsB, hsG, natOfBitsLE_testBit, Nat.mod_eq_of_lt hs, heq]
    exact hsumOut ▸ enforce_equal.complete _

/-- An honest signature satisfies the constraints: the key `A = ask·G ≠ 0`, the nonce point
`R = k·G`, and `s = (k + c·ask) mod l`. -/
theorem verify_var.complete_honest {ask : ℕ} (hA : ask • G ≠ 0) (k : ℕ)
    (keyHash message : FpVar) :
    ∃ w : VerifyWit P,
      verify_var.Rel (ofPoint (ask • G)) keyHash message w ∧ verify_var.R w = ofPoint (k • G) :=
  verify_var.complete hA (smul_G_mem8 k) (lt_trans (Nat.mod_lt _ (by unfold l; norm_num)) l_lt)
    keyHash message (sign_eq k _ ask)

/-- An honest owner's signature is a valid one. -/
theorem schnorrOK_honest (H : List F → F) {ask : ℕ} (hA : ask • G ≠ 0) (k : ℕ) (m : F) :
    schnorrOK H (ofPoint (ask • G)) m :=
  ⟨_, rfl, ⟨_, smul_G_mem8 ask⟩, hA, k • G, ⟨_, smul_G_mem8 k⟩, _,
    lt_trans (Nat.mod_lt _ (by unfold l; norm_num)) l_lt, sign_eq k _ ask⟩

end auth

/-! ## `RootCircuit::synthesize_step` -/

namespace root.RootCircuit.synthesize_step

/-- The witnesses of a root step: the allocated `fields` and `siblings`, and those of the gadgets. -/
structure StepWit (P : PoseidonVarGadget) where
  fields : Fin 4 → F
  siblings : Fin DEPTH → F
  indexBits : FpVar.ToBitsWit
  emptyPath : List (tree.Level P)
  leaf : P.W 4
  newPath : List (tree.Level P)
  chain : primitives.HashChainWit

/-- The witness parts `Root.Spec` is about. -/
def StepWit.spec (w : StepWit P) : Root.Wit := ⟨w.fields, w.siblings⟩

/-- `index.to_bits_le()`. -/
def allBits (z : Root.Z) (w : StepWit P) : Fin 254 → Boolean :=
  FpVar.to_bits_le (.var z.index) w.indexBits

/-- `index_bits[..TREE_HEIGHT]`. -/
def indexBits (z : Root.Z) (w : StepWit P) : Fin DEPTH → Boolean :=
  fun k => allBits z w (Fin.castLE (by decide) k)

/-- The allocated `siblings`. -/
def siblings (w : StepWit P) : Fin DEPTH → FpVar := fun k => .var (w.siblings k)

/-- The allocated `fields`. -/
def fields (w : StepWit P) : Fin 4 → FpVar := fun i => .var (w.fields i)

/-- The root of the path with the empty leaf. -/
def emptyRoot (z : Root.Z) (w : StepWit P) : FpVar × Prop :=
  tree.merkle_root_var P (.const 0) (indexBits z w) (siblings w) w.emptyPath

/-- `Poseidon4(fields)`. -/
def leaf (w : StepWit P) : FpVar := P.hash_var 4 (fields w) w.leaf

/-- The root of the same path with the leaf. -/
def newRoot (z : Root.Z) (w : StepWit P) : FpVar × Prop :=
  tree.merkle_root_var P (leaf w) (indexBits z w) (siblings w) w.newPath

/-- `hash_chain_var(hash_chain, fields)`. -/
def newChain (z : Root.Z) (w : StepWit P) : FpVar × Prop :=
  primitives.hash_chain_var z.chain (List.ofFn w.fields) w.chain

/-- `RootCircuit::synthesize_step` on the state `[index, hash_chain, root]`: the bits of `index`
above `TREE_HEIGHT` are zero, the path of `index` with the empty leaf gives `root`, the same path
with `Poseidon4(fields)` gives the new root, and the hash chain absorbs `fields`. -/
structure Rel (z : Root.Z) (w : StepWit P) : Prop where
  index : FpVar.to_bits_le.Rel (.var z.index) w.indexBits
  index_top : ∀ i : Fin 254, DEPTH ≤ i.val →
    Boolean.enforce_equal.Rel (allBits z w i) (.const false)
  emptyPath : (emptyRoot z w).2
  empty : FpVar.enforce_equal.Rel (emptyRoot z w).1 (.var z.root)
  leaf : P.Rel 4 (fields w) w.leaf
  newPath : (newRoot z w).2
  chain : (newChain z w).2

/-- The state the step returns, `[index + 1, new_hash_chain, new_root]`. -/
def next (z : Root.Z) (w : StepWit P) : Root.Z :=
  ⟨(FpVar.add (.var z.index) (.const 1)).val, (newChain z w).1.val, (newRoot z w).1.val⟩

theorem lt_of_testBit {x : F} {n : ℕ}
    (h : ∀ i : Fin 254, n ≤ i.val → x.val.testBit i = false) :
    x.val < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => if h254 : i < 254 then h ⟨i, h254⟩ hi else
    Nat.testBit_lt_two_pow (lt_of_lt_of_le (FpVar.val_lt_two_pow_254 _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem index_bits {z : Root.Z} {w : StepWit P} (h : Rel z w) :
    z.index.val < 2 ^ DEPTH ∧ ∀ k, (indexBits z w k).val = bit (z.index.val.testBit k) :=
  ⟨lt_of_testBit fun i hi =>
    Boolean.enforce_equal.sound (FpVar.to_bits_le.sound h.index i) rfl (h.index_top i hi),
    fun _ => FpVar.to_bits_le.sound h.index _⟩

/-- Soundness: a satisfying assignment proves `Root.Spec` of the state, the fields and siblings it
allocates, and the state the step returns. -/
theorem sound (h : Hashes) (hH : h.H = P.hash) (hc : h.hc = Sha256.hashChain) {z : Root.Z}
    {w : StepWit P} (hR : Rel z w) : Root.Spec h z w.spec (next z w) := by
  obtain ⟨hlt, hbits⟩ := index_bits hR
  have hleaf : (leaf w).val = Root.leaf h w.spec := by rw [leaf, P.sound hR.leaf, Root.leaf, hH]; rfl
  refine ⟨hlt, (primitives.hash_chain_var.sound hR.chain).1, ?_, ?_⟩
  · have e := FpVar.enforce_equal.sound hR.empty (Bool.and_false _)
    rw [emptyRoot, tree.merkle_root_var.sound h hH hbits hR.emptyPath] at e
    exact e
  · rw [next, Root.next, newChain, newRoot, primitives.hash_chain_var_val hR.chain,
      tree.merkle_root_var.sound h hH hbits hR.newPath, hleaf, hc, List.map_ofFn]
    rfl

/-- Completeness: every `Root.Spec` witness extends to a satisfying assignment whose step returns
the next state. -/
theorem complete (h : Hashes) (hH : h.H = P.hash) (hc : h.hc = Sha256.hashChain) {z z' : Root.Z}
    {w : Root.Wit} (hS : Root.Spec h z w z') :
    ∃ sw : StepWit P, sw.spec = w ∧ Rel z sw ∧ next z sw = z' := by
  have hidx := FpVar.to_bits_le.complete (.var z.index)
  let bits : Fin DEPTH → Boolean := fun k =>
    FpVar.to_bits_le (.var z.index) (FpVar.to_bits_le.wit (.var z.index)) (Fin.castLE (by decide) k)
  have hbits : ∀ k, (bits k).val = bit (z.index.val.testBit k) := fun k =>
    FpVar.to_bits_le.sound hidx _
  obtain ⟨wE, hE, hEv⟩ := tree.merkle_root_var.complete (P := P) h hH (.const 0) bits
    (fun k => .var (w.sib k)) hbits
  obtain ⟨wL, hL⟩ := P.complete 4 (fun i => .var (w.fields i)) (by norm_num) (by norm_num)
  obtain ⟨wN, hN, -⟩ := tree.merkle_root_var.complete h hH
    (P.hash_var 4 (fun i => .var (w.fields i)) wL) bits
    (fun k => .var (w.sib k)) hbits
  obtain ⟨wC, hC⟩ := primitives.hash_chain_var.complete (values := List.ofFn w.fields) hS.chain_lt
  let sw : StepWit P := ⟨w.fields, w.sib, FpVar.to_bits_le.wit (.var z.index), wE, wL, wN, wC⟩
  have hR : Rel z sw := by
    refine ⟨hidx, fun i hi => ?_, hE, FpVar.enforce_equal.complete ?_, hL, hN, hC⟩
    · refine Boolean.enforce_equal.complete (p := false) ?_ rfl
      rw [allBits, FpVar.to_bits_le.sound hidx]
      exact congrArg bit (Nat.testBit_lt_two_pow (lt_of_lt_of_le hS.index_lt
        (Nat.pow_le_pow_right (by norm_num) hi)))
    · exact hEv.trans hS.empty
  exact ⟨sw, rfl, hR, (sound h hH hc hR).next.trans hS.next.symm⟩

end root.RootCircuit.synthesize_step

/-! ## `MergeCircuit::synthesize_step` -/

namespace merge.MergeCircuit.synthesize_step

open BabyJubJub AffineVar primitives

/-- `TRANSFER_FIELD0_BASE`, `TRANSFER_TAG << 32`. -/
def TRANSFER_FIELD0_BASE : F := 15992936129728872448

/-- `NOTE_FIELD0_BASE`, `NOTE_HASH_TAG << 32`. -/
def NOTE_FIELD0_BASE : F := 8691708596607516672

/-- The witnesses of a merge step, in the order the step allocates them: the input's opening and
paths, the output note's opening, the signature's, and those of every gadget. -/
structure StepWit (P : PoseidonVarGadget) where
  isBurn : F
  tokenBits : Fin 32 → F
  chainBits : Fin 64 → F
  authKey : NewWitnessW
  authKeyHash : P.W 3
  nk : F
  publicKey : P.W 3
  noteValue : F
  noteValueBits : Fin 248 → F
  noteSalt : F
  inputNoteHash : P.W 6
  noteLeaf : P.W 4
  burnFrom : F
  burnValue : F
  burnFromBits : Fin 160 → F
  burnValueBits : Fin 248 → F
  burnValueInv : F
  burnSalt : F
  digest : P.W 5
  digestSel : F
  digestBits : Fin 238 → F
  transferLeaf : P.W 4
  idx : F
  idxBits : Fin DEPTH → F
  aspLeaf : P.W 2
  aspSib : Fin DEPTH → F
  aspPath : List (tree.Level P)
  leafSel : F
  valueSel : F
  sib : Fin DEPTH → F
  path : List (tree.Level P)
  nullifier : P.W 5
  nfChain : HashChainWit
  outPk : F
  outSalt : F
  message : P.W 6
  signature : auth.VerifyWit P
  prevSum : F
  isEmpty : F × F
  prevNoteHash : P.W 6
  isLast : F × F
  outSel : F
  outBits : Fin 248 → F
  nextNoteHash : P.W 6

/-! The variables the step computes, one per `let` of the source. -/

def isBurn (w : StepWit P) : Boolean := .var w.isBurn
/-- The auth key, allocated as a witness. -/
def key (w : StepWit P) : F × F := new_witness.out w.authKey
def keyHash (w : StepWit P) : FpVar := auth.auth_key_hash_var (key w) w.authKeyHash
def publicKey (w : StepWit P) : FpVar :=
  domain_hash_var P DOMAIN_PUBLIC_KEY ![keyHash w, .var w.nk] w.publicKey
def inputNoteHash (z : Merge.Z) (w : StepWit P) : FpVar :=
  note_hash_var P (.var z.chain) (publicKey w) (.var w.noteValue) (.var z.token) (.var w.noteSalt)
    w.inputNoteHash
def noteLeafInputs (z : Merge.Z) (w : StepWit P) : Fin 4 → FpVar :=
  ![(FpVar.var z.token).add (.const NOTE_FIELD0_BASE), inputNoteHash z w, .const 0, .const 0]
def noteLeaf (z : Merge.Z) (w : StepWit P) : FpVar := P.hash_var 4 (noteLeafInputs z w) w.noteLeaf
def digest (z : Merge.Z) (w : StepWit P) : FpVar :=
  domain_hash_var P DOMAIN_BURN ![.var z.chain, publicKey w, .var w.burnSalt, .const 0] w.digest
/-- `is_burn.select(digest, zero)`. -/
def digestSel (z : Merge.Z) (w : StepWit P) : FpVar :=
  FpVar.conditionally_select (isBurn w) (digest z w) (.const 0) w.digestSel
def digestBits (z : Merge.Z) (w : StepWit P) : Fin 238 → Boolean :=
  FpVar.to_bits_le_with_top_bits_zero (digestSel z w) 238 w.digestBits
/-- `le_bits_to_fp(digest_bits[..ADDRESS_BITS])`. -/
def burnAddress (z : Merge.Z) (w : StepWit P) : FpVar :=
  Boolean.le_bits_to_fp fun i : Fin 160 => digestBits z w (Fin.castLE (by norm_num) i)
def transferLeafInputs (z : Merge.Z) (w : StepWit P) : Fin 4 → FpVar :=
  ![(FpVar.var z.token).add (.const TRANSFER_FIELD0_BASE), .var w.burnFrom, burnAddress z w,
    .var w.burnValue]
def transferLeaf (z : Merge.Z) (w : StepWit P) : FpVar :=
  P.hash_var 4 (transferLeafInputs z w) w.transferLeaf
/-- `range_check(commitment_index, TREE_HEIGHT)`, shared by both paths. -/
def indexBits (w : StepWit P) : Fin DEPTH → Boolean :=
  FpVar.to_bits_le_with_top_bits_zero (.var w.idx) DEPTH w.idxBits
def aspLeaf (w : StepWit P) : FpVar := domain_hash_var P DOMAIN_ASP_LEAF ![.var w.idx] w.aspLeaf
def aspRoot (w : StepWit P) : FpVar × Prop :=
  tree.merkle_root_var P (aspLeaf w) (indexBits w) (fun k => .var (w.aspSib k)) w.aspPath
def leaf (z : Merge.Z) (w : StepWit P) : FpVar :=
  FpVar.conditionally_select (isBurn w) (transferLeaf z w) (noteLeaf z w) w.leafSel
def value (w : StepWit P) : FpVar :=
  FpVar.conditionally_select (isBurn w) (.var w.burnValue) (.var w.noteValue) w.valueSel
def root (z : Merge.Z) (w : StepWit P) : FpVar × Prop :=
  tree.merkle_root_var P (leaf z w) (indexBits w) (fun k => .var (w.sib k)) w.path
def nullifier (z : Merge.Z) (w : StepWit P) : FpVar :=
  domain_hash_var P DOMAIN_NULLIFIER ![.var z.chain, .var w.idx, .var w.nk, .const 0] w.nullifier
/-- `hash_chain_var(nullifier_chain, [nullifier])`. The nullifier is a variable, as every
Poseidon output with a variable input is, so it enters by its value. -/
def nfChain (z : Merge.Z) (w : StepWit P) : FpVar × Prop :=
  hash_chain_var z.nfChain [(nullifier z w).val] w.nfChain
def message (z : Merge.Z) (w : StepWit P) : FpVar :=
  auth.merge_message_var (.var z.signedChain) (.var w.outPk) (.var w.outSalt) (.var z.fee)
    (.var z.feeRecipient) w.message
/-- `note_hash.is_zero()`. -/
def isEmpty (z : Merge.Z) (w : StepWit P) : Boolean := FpVar.is_zero (.var z.noteHash) w.isEmpty
def prevNoteHash (z : Merge.Z) (w : StepWit P) : FpVar :=
  note_hash_var P (.var z.chain) (.var w.outPk) (.var w.prevSum) (.var z.token) (.var w.outSalt)
    w.prevNoteHash
def sum (w : StepWit P) : FpVar := (FpVar.var w.prevSum).add (value w)
/-- `remaining.is_eq(1)`. -/
def isLast (z : Merge.Z) (w : StepWit P) : Boolean :=
  FpVar.is_eq (.var z.remaining) (.const 1) w.isLast
/-- `is_last.select(sum - fee, sum)`. -/
def out (z : Merge.Z) (w : StepWit P) : FpVar :=
  FpVar.conditionally_select (isLast z w) ((sum w).sub (.var z.fee)) (sum w) w.outSel
def nextNoteHash (z : Merge.Z) (w : StepWit P) : FpVar :=
  note_hash_var P (.var z.chain) (.var w.outPk) (out z w) (.var z.token) (.var w.outSalt)
    w.nextNoteHash

/-- `MergeCircuit::synthesize_step` on the state `[token_id, chain_id, commitment_root, asp_root,
nullifier_chain, signed_chain, note_hash, remaining, fee, fee_recipient]`, in the source's order:
the range checks, the owner's keys, both branches' leaves with the burn checks gated by `is_burn`,
both paths over the same index bits, the nullifier chain, the signature, and the output note. -/
structure Rel (z : Merge.Z) (w : StepWit P) : Prop where
  isBurnBool : Boolean.new_witness.Rel w.isBurn
  tokenRange : FpVar.to_bits_le_with_top_bits_zero.Rel (.var z.token) 32 w.tokenBits
  chainRange : FpVar.to_bits_le_with_top_bits_zero.Rel (.var z.chain) 64 w.chainBits
  keyAlloc : new_witness.Rel w.authKey
  keyHashRel : domain_hash_var.Rel P DOMAIN_AUTH_KEY ![.var (key w).1, .var (key w).2] w.authKeyHash
  publicKeyRel : domain_hash_var.Rel P DOMAIN_PUBLIC_KEY ![keyHash w, .var w.nk] w.publicKey
  noteValueRange : FpVar.to_bits_le_with_top_bits_zero.Rel (.var w.noteValue) 248 w.noteValueBits
  inputNoteHashRel : domain_hash_var.Rel P DOMAIN_NOTE
    ![.var z.chain, publicKey w, .var w.noteValue, .var z.token, .var w.noteSalt] w.inputNoteHash
  noteLeafRel : P.Rel 4 (noteLeafInputs z w) w.noteLeaf
  burnFromRange : FpVar.to_bits_le_with_top_bits_zero.Rel (.var w.burnFrom) 160 w.burnFromBits
  burnValueRange : FpVar.to_bits_le_with_top_bits_zero.Rel (.var w.burnValue) 248 w.burnValueBits
  burnValueNonZero :
    FpVar.conditional_enforce_not_equal.Rel (.var w.burnValue) (.const 0) (isBurn w) w.burnValueInv
  digestRel : domain_hash_var.Rel P DOMAIN_BURN
    ![.var z.chain, publicKey w, .var w.burnSalt, .const 0] w.digest
  digestSelRel : FpVar.conditionally_select.Rel (isBurn w) (digest z w) (.const 0) w.digestSel
  powRange : FpVar.to_bits_le_with_top_bits_zero.Rel (digestSel z w) 238 w.digestBits
  transferLeafRel : P.Rel 4 (transferLeafInputs z w) w.transferLeaf
  indexRange : FpVar.to_bits_le_with_top_bits_zero.Rel (.var w.idx) DEPTH w.idxBits
  aspLeafRel : domain_hash_var.Rel P DOMAIN_ASP_LEAF ![.var w.idx] w.aspLeaf
  aspPathRel : (aspRoot w).2
  aspMember : FpVar.conditional_enforce_equal.Rel (aspRoot w).1 (.var z.asp) (isBurn w)
  leafSelRel : FpVar.conditionally_select.Rel (isBurn w) (transferLeaf z w) (noteLeaf z w) w.leafSel
  valueSelRel :
    FpVar.conditionally_select.Rel (isBurn w) (.var w.burnValue) (.var w.noteValue) w.valueSel
  pathRel : (root z w).2
  member : FpVar.enforce_equal.Rel (root z w).1 (.var z.root)
  nullifierRel : domain_hash_var.Rel P DOMAIN_NULLIFIER
    ![.var z.chain, .var w.idx, .var w.nk, .const 0] w.nullifier
  nfChainRel : (nfChain z w).2
  messageRel : domain_hash_var.Rel P DOMAIN_MERGE_AUTH
    ![.var z.signedChain, .var w.outPk, .var w.outSalt, .var z.fee, .var z.feeRecipient] w.message
  signed : auth.verify_var.Rel (key w) (keyHash w) (message z w) w.signature
  isEmptyRel : FpVar.is_eq.Rel (.var z.noteHash) (.const 0) w.isEmpty
  first : FpVar.conditional_enforce_equal.Rel (.var w.prevSum) (.const 0) (isEmpty z w)
  prevNoteHashRel : domain_hash_var.Rel P DOMAIN_NOTE
    ![.var z.chain, .var w.outPk, .var w.prevSum, .var z.token, .var w.outSalt] w.prevNoteHash
  later : FpVar.conditional_enforce_equal.Rel (prevNoteHash z w) (.var z.noteHash) (isEmpty z w).not
  isLastRel : FpVar.is_eq.Rel (.var z.remaining) (.const 1) w.isLast
  outSelRel :
    FpVar.conditionally_select.Rel (isLast z w) ((sum w).sub (.var z.fee)) (sum w) w.outSel
  outRange : FpVar.to_bits_le_with_top_bits_zero.Rel (out z w) 248 w.outBits
  nextNoteHashRel : domain_hash_var.Rel P DOMAIN_NOTE
    ![.var z.chain, .var w.outPk, out z w, .var z.token, .var w.outSalt] w.nextNoteHash

/-- The witness parts `Merge.Spec` is about. -/
def StepWit.spec (w : StepWit P) : Merge.Wit where
  isBurn := decide (w.isBurn = 1)
  ak := key w
  nk := w.nk
  idx := w.idx
  sib := w.sib
  noteValue := w.noteValue
  noteSalt := w.noteSalt
  burnSalt := w.burnSalt
  burnFrom := w.burnFrom
  burnValue := w.burnValue
  aspSib := w.aspSib
  outPk := w.outPk
  outSalt := w.outSalt
  prevSum := w.prevSum

/-- The state the step returns: the nullifier chain and the output note move on, `remaining` counts
down, and every other word passes through. -/
def next (z : Merge.Z) (w : StepWit P) : Merge.Z :=
  { z with
    nfChain := (nfChain z w).1.val
    noteHash := (nextNoteHash z w).val
    remaining := ((FpVar.var z.remaining).sub (.const 1)).val }

/-! ### What the variables hold -/

/-- The constraints of `Rel` that fix the values of the step's variables: `is_burn`'s booleanity,
the Poseidon calls, and the selections. -/
structure Vals (z : Merge.Z) (w : StepWit P) : Prop where
  isBurnBool : Boolean.new_witness.Rel w.isBurn
  keyHashRel : domain_hash_var.Rel P DOMAIN_AUTH_KEY ![.var (key w).1, .var (key w).2] w.authKeyHash
  publicKeyRel : domain_hash_var.Rel P DOMAIN_PUBLIC_KEY ![keyHash w, .var w.nk] w.publicKey
  inputNoteHashRel : domain_hash_var.Rel P DOMAIN_NOTE
    ![.var z.chain, publicKey w, .var w.noteValue, .var z.token, .var w.noteSalt] w.inputNoteHash
  noteLeafRel : P.Rel 4 (noteLeafInputs z w) w.noteLeaf
  digestRel : domain_hash_var.Rel P DOMAIN_BURN
    ![.var z.chain, publicKey w, .var w.burnSalt, .const 0] w.digest
  digestSelRel : FpVar.conditionally_select.Rel (isBurn w) (digest z w) (.const 0) w.digestSel
  transferLeafRel : P.Rel 4 (transferLeafInputs z w) w.transferLeaf
  aspLeafRel : domain_hash_var.Rel P DOMAIN_ASP_LEAF ![.var w.idx] w.aspLeaf
  leafSelRel : FpVar.conditionally_select.Rel (isBurn w) (transferLeaf z w) (noteLeaf z w) w.leafSel
  valueSelRel :
    FpVar.conditionally_select.Rel (isBurn w) (.var w.burnValue) (.var w.noteValue) w.valueSel
  nullifierRel : domain_hash_var.Rel P DOMAIN_NULLIFIER
    ![.var z.chain, .var w.idx, .var w.nk, .const 0] w.nullifier
  messageRel : domain_hash_var.Rel P DOMAIN_MERGE_AUTH
    ![.var z.signedChain, .var w.outPk, .var w.outSalt, .var z.fee, .var z.feeRecipient] w.message
  prevNoteHashRel : domain_hash_var.Rel P DOMAIN_NOTE
    ![.var z.chain, .var w.outPk, .var w.prevSum, .var z.token, .var w.outSalt] w.prevNoteHash
  isLastRel : FpVar.is_eq.Rel (.var z.remaining) (.const 1) w.isLast
  outSelRel :
    FpVar.conditionally_select.Rel (isLast z w) ((sum w).sub (.var z.fee)) (sum w) w.outSel
  nextNoteHashRel : domain_hash_var.Rel P DOMAIN_NOTE
    ![.var z.chain, .var w.outPk, out z w, .var z.token, .var w.outSalt] w.nextNoteHash

theorem Rel.vals {z : Merge.Z} {w : StepWit P} (hR : Rel z w) : Vals z w :=
  ⟨hR.isBurnBool, hR.keyHashRel, hR.publicKeyRel, hR.inputNoteHashRel, hR.noteLeafRel, hR.digestRel,
    hR.digestSelRel, hR.transferLeafRel, hR.aspLeafRel, hR.leafSelRel, hR.valueSelRel,
    hR.nullifierRel, hR.messageRel, hR.prevNoteHashRel, hR.isLastRel, hR.outSelRel,
    hR.nextNoteHashRel⟩

section values

variable (h : Hashes) (hH : h.H = P.hash) {z : Merge.Z} {w : StepWit P}
include hH

theorem keyHash_val (hV : Vals z w) : (keyHash w).val = authKeyHash h (key w) := by
  rw [keyHash, auth.auth_key_hash_var, domain_hash_var.sound hV.keyHashRel, authKeyHash, hH]
  simp [List.ofFn_succ]

theorem publicKey_val (hV : Vals z w) : (publicKey w).val = Merge.pk (h := h) w.spec := by
  rw [publicKey, domain_hash_var.sound hV.publicKeyRel, Merge.pk, Zerc20.publicKey, hH]
  simp [List.ofFn_succ, keyHash_val h hH hV, StepWit.spec]

omit hH in
theorem field0_cast (tag : ℕ) (x : F) :
    ((field0 tag x.val : ℕ) : F) = x + ((tag * 2 ^ 32 : ℕ) : F) := by
  rw [field0, Nat.cast_add, ZMod.natCast_zmod_val, add_comm]

theorem inputNoteHash_val (hV : Vals z w) :
    (inputNoteHash z w).val =
      noteHash h z.chain (Merge.pk (h := h) w.spec) w.noteValue z.token w.noteSalt := by
  rw [inputNoteHash, note_hash_var, domain_hash_var.sound hV.inputNoteHashRel, noteHash, hH]
  simp [List.ofFn_succ, publicKey_val h hH hV]

theorem noteLeaf_val (hV : Vals z w) :
    (noteLeaf z w).val = h.H [↑(field0 NOTE_HASH_TAG z.token.val),
      noteHash h z.chain (Merge.pk (h := h) w.spec) w.noteValue z.token w.noteSalt, 0, 0] := by
  rw [noteLeaf, P.sound hV.noteLeafRel, hH, field0_cast,
    show ((NOTE_HASH_TAG * 2 ^ 32 : ℕ) : F) = NOTE_FIELD0_BASE by
      unfold NOTE_HASH_TAG NOTE_FIELD0_BASE; norm_num]
  simp [List.ofFn_succ, noteLeafInputs, inputNoteHash_val h hH hV, FpVar.add_val]

theorem digest_val (hV : Vals z w) :
    (digest z w).val = burnDigest h z.chain (Merge.pk (h := h) w.spec) w.burnSalt := by
  rw [digest, domain_hash_var.sound hV.digestRel, burnDigest, hH]
  simp [List.ofFn_succ, publicKey_val h hH hV]

theorem aspLeaf_val (hV : Vals z w) : (aspLeaf w).val = Zerc20.aspLeaf h w.idx := by
  rw [aspLeaf, domain_hash_var.sound hV.aspLeafRel, Zerc20.aspLeaf, hH]
  simp

theorem nullifier_val (hV : Vals z w) : (nullifier z w).val = Merge.nf h z w.spec := by
  rw [nullifier, domain_hash_var.sound hV.nullifierRel, Merge.nf, Zerc20.nullifier, hH]
  simp [List.ofFn_succ, StepWit.spec]

theorem message_val (hV : Vals z w) :
    (message z w).val = mergeMessage h z.signedChain w.outPk w.outSalt z.fee z.feeRecipient := by
  rw [message, auth.merge_message_var, domain_hash_var.sound hV.messageRel, mergeMessage, hH]
  simp [List.ofFn_succ]

theorem prevNoteHash_val (hV : Vals z w) :
    (prevNoteHash z w).val = noteHash h z.chain w.outPk w.prevSum z.token w.outSalt := by
  rw [prevNoteHash, note_hash_var, domain_hash_var.sound hV.prevNoteHashRel, noteHash, hH]
  simp [List.ofFn_succ]

omit hH in
theorem isBurn_val (hV : Vals z w) : (isBurn w).val = bit w.spec.isBurn :=
  Boolean.new_witness.sound hV.isBurnBool

omit hH in
theorem value_val (hV : Vals z w) : (value w).val = Merge.value w.spec := by
  rw [value, FpVar.conditionally_select.sound (isBurn_val hV) hV.valueSelRel, Merge.value]
  rfl

omit hH in
theorem out_eq : out z w = .var w.outSel := rfl

omit hH in
theorem out_val (hV : Vals z w) : (out z w).val = Merge.out z w.spec := by
  have hl : (isLast z w).val = _ := FpVar.is_eq.sound hV.isLastRel
  rw [out, FpVar.conditionally_select.sound hl hV.outSelRel, Merge.out, FpVar.sub_val, sum,
    FpVar.add_val, value_val hV]
  simp only [val_var, val_const, decide_eq_true_eq]
  rfl

theorem nextNoteHash_val (hV : Vals z w) :
    (nextNoteHash z w).val = noteHash h z.chain w.outPk (Merge.out z w.spec) z.token w.outSalt := by
  rw [nextNoteHash, note_hash_var, domain_hash_var.sound hV.nextNoteHashRel, noteHash, hH]
  simp [List.ofFn_succ, out_val hV]

omit hH in
theorem select_var (c : F) (t f : FpVar) (x : F) :
    ∃ y, FpVar.conditionally_select (.var c) t f x = .var y := by
  cases t <;> cases f <;> exact ⟨_, rfl⟩

omit hH in
/-- The selected digest has its top 16 of 254 bits zero, and the burn address is its low 160. -/
theorem pow_address
    (hpow : FpVar.to_bits_le_with_top_bits_zero.Rel (digestSel z w) 238 w.digestBits) :
    (digestSel z w).val.val < 2 ^ 238 ∧
      (burnAddress z w).val = (((digestSel z w).val.val % 2 ^ 160 : ℕ) : F) := by
  obtain ⟨y, hy⟩ : ∃ y, digestSel z w = .var y := select_var _ _ _ _
  have hrel : FpVar.to_bits_le_with_top_bits_zero.Rel (.var y) 238 w.digestBits := by
    rw [← hy]; exact hpow
  obtain ⟨hlt, hbits⟩ := FpVar.to_bits_le_with_top_bits_zero.sound (by norm_num) hrel
  rw [burnAddress, digestBits, hy,
    Boolean.le_bits_to_fp_of_bits (xs := fun i : Fin 160 => y.val.testBit i) fun i => hbits _,
    natOfBits_testBit]
  exact ⟨hlt, rfl⟩

theorem digestSel_val (hV : Vals z w) :
    (digestSel z w).val = if w.spec.isBurn then burnDigest h z.chain (Merge.pk (h := h) w.spec)
      w.burnSalt else 0 := by
  rw [digestSel, FpVar.conditionally_select.sound (isBurn_val hV) hV.digestSelRel, digest_val h hH hV]
  rfl

theorem leaf_val (hV : Vals z w)
    (hpow : FpVar.to_bits_le_with_top_bits_zero.Rel (digestSel z w) 238 w.digestBits) :
    (leaf z w).val = Merge.leaf h z w.spec := by
  rw [leaf, FpVar.conditionally_select.sound (isBurn_val hV) hV.leafSelRel, Merge.leaf]
  cases hb : w.spec.isBurn
  · exact noteLeaf_val h hH hV
  · rw [if_pos rfl, if_pos rfl, transferLeaf, P.sound hV.transferLeafRel, hH, field0_cast,
      show ((TRANSFER_TAG * 2 ^ 32 : ℕ) : F) = TRANSFER_FIELD0_BASE by
        unfold TRANSFER_TAG TRANSFER_FIELD0_BASE; norm_num]
    have ha := (pow_address hpow).2
    rw [digestSel_val h hH hV, hb, if_pos rfl] at ha
    simp [List.ofFn_succ, transferLeafInputs, FpVar.add_val, ha, addressOf, ADDRESS_BOUND,
      StepWit.spec]

end values

/-! ### Soundness -/

/-- Soundness: a satisfying assignment proves `Merge.Spec` of the state, the witness parts it
opens, and the state the step returns, with `sigOK` the Schnorr check `verify_var` proves. -/
theorem sound (h : Hashes) (hH : h.H = P.hash) (hc : h.hc = Sha256.hashChain)
    (hsig : h.sigOK = auth.schnorrOK P.hash) {z : Merge.Z} {w : StepWit P} (hR : Rel z w) :
    Merge.Spec h z w.spec (next z w) := by
  have range {x : F} {size : ℕ} {bits : Fin size → F} (hs : size ≤ 253)
      (hr : FpVar.to_bits_le_with_top_bits_zero.Rel (.var x) size bits) : x.val < 2 ^ size :=
    (FpVar.to_bits_le_with_top_bits_zero.sound hs hr).1
  have hV := hR.vals
  obtain ⟨hidx, hidxBits⟩ := FpVar.to_bits_le_with_top_bits_zero.sound (by decide) hR.indexRange
  replace hidxBits : ∀ k, (indexBits w k).val = bit (w.idx.val.testBit k) := hidxBits
  refine
    { token_lt := range (by norm_num) hR.tokenRange
      chain_lt := range (by norm_num) hR.chainRange
      noteValue_lt := range (by norm_num) hR.noteValueRange
      burnFrom_lt := range (by norm_num) hR.burnFromRange
      burnValue_lt := range (by norm_num) hR.burnValueRange
      idx_lt := hidx
      burn := fun hb => ?_
      member := ?_
      nfChain_lt := (hash_chain_var.sound hR.nfChainRel).1
      signed := ?_
      first := fun h0 => ?_
      later := fun h0 => ?_
      out_lt := ?_
      next := ?_ }
  · have hc1 : (isBurn w).val = 1 := by rw [isBurn_val hV, hb]; rfl
    refine ⟨FpVar.conditional_enforce_not_equal.sound hR.burnValueNonZero hc1 rfl, ?_, ?_⟩
    · have := (pow_address hR.powRange).1
      rwa [digestSel_val h hH hV, hb, if_pos rfl] at this
    · have e := FpVar.conditional_enforce_equal.sound hR.aspMember hc1 (Bool.and_false _)
      rwa [aspRoot, tree.merkle_root_var.sound h hH hidxBits hR.aspPathRel, aspLeaf_val h hH hV] at e
  · have e := FpVar.enforce_equal.sound hR.member (Bool.and_false _)
    rwa [root, tree.merkle_root_var.sound h hH hidxBits hR.pathRel, leaf_val h hH hV hR.powRange] at e
  · obtain ⟨P0, -, hkey⟩ := new_witness.sound hR.keyAlloc
    have hk : key w = ofPoint (8 • P0) := hkey
    have hv := auth.verify_var.sound (hk ▸ hR.signed)
    rw [keyHash_val h hH hV, message_val h hH hV, authKeyHash, hH] at hv
    rw [hsig]
    exact ⟨8 • P0, hk.symm, ⟨P0, rfl⟩, hv⟩
  · have e := FpVar.conditional_enforce_equal.sound hR.first
      (by rw [isEmpty, FpVar.is_zero.sound hR.isEmptyRel]; simp [h0, bit]) rfl
    exact e
  · have e := FpVar.conditional_enforce_equal.sound hR.later
      (by have := Boolean.not_val (FpVar.is_zero.sound hR.isEmptyRel); simpa [h0, bit] using this)
      (Bool.and_false _)
    rw [prevNoteHash_val h hH hV] at e
    exact e
  · rw [← out_val hV]
    exact range (by norm_num) (out_eq ▸ hR.outRange)
  · rw [next, Merge.next, nfChain, hash_chain_var_val hR.nfChainRel, nullifier_val h hH hV,
      nextNoteHash_val h hH hV, hc]
    rfl

/-! ### Completeness -/

theorem decide_bit (b : Bool) : decide (bit b = 1) = b := by cases b <;> simp [bit]

/-- Completeness: every `Merge.Spec` witness, with the signature `sigOK` provides, extends to a
satisfying assignment whose step returns the next state. The inactive branch's witness satisfies
its gated checks as `Merge.Spec` leaves it: in range, and muxed out. -/
theorem complete (h : Hashes) (hH : h.H = P.hash) (hc : h.hc = Sha256.hashChain)
    (hsig : h.sigOK = auth.schnorrOK P.hash) {z z' : Merge.Z} {w : Merge.Wit}
    (hS : Merge.Spec h z w z') : ∃ sw : StepWit P, sw.spec = w ∧ Rel z sw ∧ next z sw = z' := by
  have hsigned := hS.signed
  rw [hsig] at hsigned
  obtain ⟨_, hAk, ⟨P0, rfl⟩, hA0, R, ⟨Q, hQ⟩, s, hs, heq⟩ := hsigned
  obtain ⟨hkey, hk0⟩ := new_witness.complete P0
  have hkeyOut := hk0.trans hAk
  -- the owner's keys
  let key0 := new_witness.out (new_witness.wit P0)
  obtain ⟨wKH, hKH⟩ := domain_hash_var.complete (P := P) DOMAIN_AUTH_KEY
    ![.var key0.1, .var key0.2] (by norm_num) (by norm_num)
  let kh := domain_hash_var P DOMAIN_AUTH_KEY ![.var key0.1, .var key0.2] wKH
  obtain ⟨wPK, hPK⟩ := domain_hash_var.complete (P := P) DOMAIN_PUBLIC_KEY ![kh, .var w.nk]
    (by norm_num) (by norm_num)
  let pk := domain_hash_var P DOMAIN_PUBLIC_KEY ![kh, .var w.nk] wPK
  -- the note branch
  obtain ⟨wINH, hINH⟩ := domain_hash_var.complete (P := P) DOMAIN_NOTE
    ![.var z.chain, pk, .var w.noteValue, .var z.token, .var w.noteSalt] (by norm_num) (by norm_num)
  let inh := note_hash_var P (.var z.chain) pk (.var w.noteValue) (.var z.token) (.var w.noteSalt)
    wINH
  obtain ⟨wNL, hNL⟩ := P.complete 4
    ![(FpVar.var z.token).add (.const NOTE_FIELD0_BASE), inh, .const 0, .const 0]
    (by norm_num) (by norm_num)
  let nl := P.hash_var 4 ![(FpVar.var z.token).add (.const NOTE_FIELD0_BASE), inh, .const 0,
    .const 0] wNL
  -- the burn branch
  obtain ⟨wD, hD⟩ := domain_hash_var.complete (P := P) DOMAIN_BURN
    ![.var z.chain, pk, .var w.burnSalt, .const 0] (by norm_num) (by norm_num)
  let dg := domain_hash_var P DOMAIN_BURN ![.var z.chain, pk, .var w.burnSalt, .const 0] wD
  let ib : Boolean := .var (bit w.isBurn)
  let dsel := FpVar.conditionally_select ib dg (.const 0)
    (FpVar.conditionally_select.wit ib dg (.const 0))
  let dbits := FpVar.to_bits_le_with_top_bits_zero.wit dsel 238
  let addr := Boolean.le_bits_to_fp fun i : Fin 160 =>
    FpVar.to_bits_le_with_top_bits_zero dsel 238 dbits (Fin.castLE (by norm_num) i)
  obtain ⟨wTL, hTL⟩ := P.complete 4
    ![(FpVar.var z.token).add (.const TRANSFER_FIELD0_BASE), .var w.burnFrom, addr, .var w.burnValue]
    (by norm_num) (by norm_num)
  let tl := P.hash_var 4
    ![(FpVar.var z.token).add (.const TRANSFER_FIELD0_BASE), .var w.burnFrom, addr, .var w.burnValue]
    wTL
  -- both paths
  let idxBits := FpVar.to_bits_le_with_top_bits_zero.wit (.var w.idx) DEPTH
  have hidx := FpVar.to_bits_le_with_top_bits_zero.complete (size := DEPTH) hS.idx_lt
  have hbits : ∀ k, (FpVar.to_bits_le_with_top_bits_zero (.var w.idx) DEPTH idxBits k).val =
      bit (w.idx.val.testBit k) :=
    (FpVar.to_bits_le_with_top_bits_zero.sound (by decide) hidx).2
  obtain ⟨wAL, hAL⟩ := domain_hash_var.complete (P := P) DOMAIN_ASP_LEAF ![.var w.idx] le_rfl
    (by norm_num)
  obtain ⟨wAP, hAP, hAPv⟩ := tree.merkle_root_var.complete h hH
    (domain_hash_var P DOMAIN_ASP_LEAF ![.var w.idx] wAL) _ (fun k => .var (w.aspSib k)) hbits
  let lf := FpVar.conditionally_select ib tl nl (FpVar.conditionally_select.wit ib tl nl)
  obtain ⟨wPath, hPath, hPathv⟩ := tree.merkle_root_var.complete h hH lf _
    (fun k => .var (w.sib k)) hbits
  -- the nullifier chain
  obtain ⟨wNF, hNF⟩ := domain_hash_var.complete (P := P) DOMAIN_NULLIFIER
    ![.var z.chain, .var w.idx, .var w.nk, .const 0] (by norm_num) (by norm_num)
  obtain ⟨wCH, hCH⟩ := hash_chain_var.complete (values :=
    [(domain_hash_var P DOMAIN_NULLIFIER ![.var z.chain, .var w.idx, .var w.nk, .const 0] wNF).val])
    hS.nfChain_lt
  -- the signature
  obtain ⟨wM, hM⟩ := domain_hash_var.complete (P := P) DOMAIN_MERGE_AUTH
    ![.var z.signedChain, .var w.outPk, .var w.outSalt, .var z.fee, .var z.feeRecipient]
    (by norm_num) (by norm_num)
  let msg := domain_hash_var P DOMAIN_MERGE_AUTH
    ![.var z.signedChain, .var w.outPk, .var w.outSalt, .var z.fee, .var z.feeRecipient] wM
  have hkh : kh.val = P.hash [DOMAIN_AUTH_KEY, w.ak.1, w.ak.2] := by
    rw [domain_hash_var.sound hKH, ← hkeyOut]; simp [List.ofFn_succ, key0]
  have hmsg : msg.val = mergeMessage h z.signedChain w.outPk w.outSalt z.fee z.feeRecipient := by
    rw [domain_hash_var.sound hM, mergeMessage, hH]; simp [List.ofFn_succ]
  obtain ⟨wSig, hSig, -⟩ := auth.verify_var.complete hA0 hQ hs kh msg
    (by rw [hkh, hmsg]; exact heq)
  -- the output note
  obtain ⟨wPNH, hPNH⟩ := domain_hash_var.complete (P := P) DOMAIN_NOTE
    ![.var z.chain, .var w.outPk, .var w.prevSum, .var z.token, .var w.outSalt]
    (by norm_num) (by norm_num)
  let vsel := FpVar.conditionally_select.wit ib (.var w.burnValue) (.var w.noteValue)
  let lastW := FpVar.is_eq.wit (.var z.remaining) (.const 1)
  let sumV : FpVar := (FpVar.var w.prevSum).add (.var vsel)
  let outW := FpVar.conditionally_select.wit (.var (1 - lastW.1)) (sumV.sub (.var z.fee)) sumV
  obtain ⟨wNNH, hNNH⟩ := domain_hash_var.complete (P := P) DOMAIN_NOTE
    ![.var z.chain, .var w.outPk, .var outW, .var z.token, .var w.outSalt]
    (by norm_num) (by norm_num)
  let sw : StepWit P :=
    { isBurn := bit w.isBurn
      tokenBits := FpVar.to_bits_le_with_top_bits_zero.wit (.var z.token) 32
      chainBits := FpVar.to_bits_le_with_top_bits_zero.wit (.var z.chain) 64
      authKey := new_witness.wit P0
      authKeyHash := wKH
      nk := w.nk
      publicKey := wPK
      noteValue := w.noteValue
      noteValueBits := FpVar.to_bits_le_with_top_bits_zero.wit (.var w.noteValue) 248
      noteSalt := w.noteSalt
      inputNoteHash := wINH
      noteLeaf := wNL
      burnFrom := w.burnFrom
      burnValue := w.burnValue
      burnFromBits := FpVar.to_bits_le_with_top_bits_zero.wit (.var w.burnFrom) 160
      burnValueBits := FpVar.to_bits_le_with_top_bits_zero.wit (.var w.burnValue) 248
      burnValueInv := FpVar.conditional_enforce_not_equal.wit (.var w.burnValue) (.const 0) ib
      burnSalt := w.burnSalt
      digest := wD
      digestSel := FpVar.conditionally_select.wit ib dg (.const 0)
      digestBits := dbits
      transferLeaf := wTL
      idx := w.idx
      idxBits := idxBits
      aspLeaf := wAL
      aspSib := w.aspSib
      aspPath := wAP
      leafSel := FpVar.conditionally_select.wit ib tl nl
      valueSel := vsel
      sib := w.sib
      path := wPath
      nullifier := wNF
      nfChain := wCH
      outPk := w.outPk
      outSalt := w.outSalt
      message := wM
      signature := wSig
      prevSum := w.prevSum
      isEmpty := FpVar.is_eq.wit (.var z.noteHash) (.const 0)
      prevNoteHash := wPNH
      isLast := lastW
      outSel := outW
      outBits := FpVar.to_bits_le_with_top_bits_zero.wit (.var outW) 248
      nextNoteHash := wNNH }
  have hspec : sw.spec = w := by
    simp only [StepWit.spec, sw, decide_bit, key, hkeyOut]
  have hV : Vals z sw :=
    ⟨Boolean.new_witness.complete _, hKH, hPK, hINH, hNL, hD,
      FpVar.conditionally_select.complete _ _ _, hTL, hAL, FpVar.conditionally_select.complete _ _ _,
      FpVar.conditionally_select.complete _ _ _, hNF, hM, hPNH, FpVar.is_eq.complete _ _,
      FpVar.conditionally_select.complete _ _ _, hNNH⟩
  have hb : (isBurn sw).val = bit w.isBurn := rfl
  -- the proof of work, on the selected digest
  have hpow : FpVar.to_bits_le_with_top_bits_zero.Rel (digestSel z sw) 238 sw.digestBits := by
    obtain ⟨y, hy⟩ : ∃ y, digestSel z sw = .var y := select_var _ _ _ _
    have hyv : y = if w.isBurn then burnDigest h z.chain (Merge.pk (h := h) w) w.burnSalt else 0 := by
      have := digestSel_val h hH hV
      rw [hy, val_var, hspec] at this
      exact this
    have hdb : sw.digestBits = FpVar.to_bits_le_with_top_bits_zero.wit (.var y) 238 := by
      show FpVar.to_bits_le_with_top_bits_zero.wit (digestSel z sw) 238 = _
      rw [hy]
    rw [hy, hdb]
    apply FpVar.to_bits_le_with_top_bits_zero.complete
    rw [hyv]
    cases hw : w.isBurn
    · simp
    · exact (hS.burn hw).2.1
  have hE := FpVar.is_eq.complete (.var z.noteHash) (.const 0)
  have hEv : (isEmpty z sw).val = bit (decide (z.noteHash = 0)) := FpVar.is_zero.sound hE
  have hR : Rel z sw :=
    { isBurnBool := hV.isBurnBool
      tokenRange := FpVar.to_bits_le_with_top_bits_zero.complete hS.token_lt
      chainRange := FpVar.to_bits_le_with_top_bits_zero.complete hS.chain_lt
      keyAlloc := hkey
      keyHashRel := hKH
      publicKeyRel := hPK
      noteValueRange := FpVar.to_bits_le_with_top_bits_zero.complete hS.noteValue_lt
      inputNoteHashRel := hINH
      noteLeafRel := hNL
      burnFromRange := FpVar.to_bits_le_with_top_bits_zero.complete hS.burnFrom_lt
      burnValueRange := FpVar.to_bits_le_with_top_bits_zero.complete hS.burnValue_lt
      burnValueNonZero := FpVar.conditional_enforce_not_equal.complete hb fun hw =>
        (hS.burn hw).1
      digestRel := hD
      digestSelRel := hV.digestSelRel
      powRange := hpow
      transferLeafRel := hTL
      indexRange := hidx
      aspLeafRel := hAL
      aspPathRel := hAP
      aspMember := FpVar.conditional_enforce_equal.complete (by
        cases hw : w.isBurn
        · left; rw [hb, hw]; rfl
        · right
          have e : (aspRoot sw).1.val = _ := hAPv
          have ea : (domain_hash_var P DOMAIN_ASP_LEAF ![.var w.idx] wAL).val =
              Zerc20.aspLeaf h w.idx := aspLeaf_val h hH hV
          rw [e, ea]
          exact (hS.burn hw).2.2)
      leafSelRel := hV.leafSelRel
      valueSelRel := hV.valueSelRel
      pathRel := hPath
      member := FpVar.enforce_equal.complete (by
        have e : (root z sw).1.val = _ := hPathv
        have el := leaf_val h hH hV hpow
        rw [hspec] at el
        rw [e, show lf.val = Merge.leaf h z w from el]
        exact hS.member)
      nullifierRel := hNF
      nfChainRel := hCH
      messageRel := hM
      signed := by rw [show key sw = ofPoint (8 • P0) from hk0]; exact hSig
      isEmptyRel := hE
      first := FpVar.conditional_enforce_equal.complete (by
        rw [hEv]
        by_cases h0 : z.noteHash = 0
        · right; exact hS.first h0
        · left; simp [h0, bit])
      prevNoteHashRel := hPNH
      later := FpVar.conditional_enforce_equal.complete (by
        rw [Boolean.not_val hEv]
        by_cases h0 : z.noteHash = 0
        · left; simp [h0, bit]
        · right
          exact (prevNoteHash_val h hH hV).trans (hS.later h0))
      isLastRel := hV.isLastRel
      outSelRel := hV.outSelRel
      outRange := by
        have e := out_val (z := z) hV
        rw [hspec] at e
        rw [out_eq]
        apply FpVar.to_bits_le_with_top_bits_zero.complete
        rw [show sw.outSel = Merge.out z w from e]
        exact hS.out_lt
      nextNoteHashRel := hNNH }
  refine ⟨sw, hspec, hR, ?_⟩
  rw [(sound h hH hc hsig hR).next, hspec, hS.next]

end merge.MergeCircuit.synthesize_step

/-! ## The circuits with arkworks' Poseidon -/

namespace poseidon

open Ark.PoseidonSpongeVar

/-- `poseidon::hash_var` with the configs `POSEIDON2..6`: arkworks' `PoseidonSpongeVar` over
circomlib's parameters. -/
def hash_var : PoseidonVarGadget where
  W n := ℕ → Fin (n + 1) → F × F × F
  hash_var n ins w := Ark.hash_var (Poseidon.params (n + 1)) ins w
  Rel n ins w := Ark.hash_var.Rel (Poseidon.params (n + 1)) ins w
  hash := Poseidon.hash
  sound h := Ark.hash_var.sound h
  complete _ ins _ _ := ⟨_, Ark.hash_var.complete _ ins⟩

theorem hash_var_hash : hash_var.hash = Poseidon.hash := rfl

/-! The step models feed a Poseidon output to `hash_chain_var`, which takes variables, by its
value. That output is a variable: one variable lane spreads to every lane through a matrix with no
zero entry. -/

theorem add_isConst {x : FpVar} (hx : x.isConst = false) (y : FpVar) :
    (x.add y).isConst = false := by
  cases x <;> cases y <;> simp_all [FpVar.add, FpVar.isConst]

theorem foldl_add_isConst {t : ℕ} {g : Fin t → FpVar} :
    ∀ (l : List (Fin t)) (init : FpVar),
      (init.isConst = false ∨ ∃ j ∈ l, (g j).isConst = false) →
      (l.foldl (fun cur j => cur.add (g j)) init).isConst = false
  | [], _, h => by simpa using h
  | j :: l, init, h => by
    apply foldl_add_isConst l
    rcases h with h | ⟨k, hk, hg⟩
    · exact .inl (add_isConst h _)
    · rcases List.mem_cons.mp hk with rfl | hk
      · left; cases init <;> cases hgk : g k <;> simp_all [FpVar.add, FpVar.isConst]
      · right; exact ⟨k, hk, hg⟩

theorem mulConst_isConst {x : FpVar} (hx : x.isConst = false) {c : F} (hc : c ≠ 0) :
    (mulConst x c).isConst = false := by
  cases x <;> simp_all [mulConst, FpVar.mul, FpVar.isConst]

theorem pow_isConst {x : FpVar} (hx : x.isConst = false) (w : F × F × F) :
    (pow_by_constant x w).2.isConst = false := by
  cases x <;> simp_all [pow_by_constant, FpVar.mul, FpVar.isConst]

/-- A round whose matrix has no zero entry turns one variable lane into all. -/
theorem round_isConst {t : ℕ} [NeZero t] {p : Poseidon.Params t} (hmds : ∀ i j, p.mds i j ≠ 0)
    (i : ℕ) (w : Fin t → F × F × F) {s : Fin t → FpVar} {j : Fin t}
    (hj : (s j).isConst = false) (k : Fin t) : ((round p i w s).2 k).isConst = false := by
  have ha : (apply_ark p i s j).isConst = false := add_isConst hj _
  have hb : ((apply_s_box (p.isFull i) (apply_ark p i s) w).2 j).isConst = false := by
    unfold apply_s_box
    split
    · exact pow_isConst ha _
    · by_cases hj0 : j = 0
      · subst hj0; simp only [Function.update_self]; exact pow_isConst ha _
      · simp only [Function.update_of_ne hj0]; exact ha
  exact foldl_add_isConst _ _ (.inr ⟨j, List.mem_finRange j, mulConst_isConst hb (hmds k j)⟩)

theorem rounds_isConst {t : ℕ} [NeZero t] {p : Poseidon.Params t} (hmds : ∀ i j, p.mds i j ≠ 0)
    (w : ℕ → Fin t → F × F × F) {s : Fin t → FpVar} {j : Fin t}
    (hj : (s j).isConst = false) :
    ∀ k, ∃ j, ((rounds p w k s).2 j).isConst = false
  | 0 => ⟨j, hj⟩
  | k + 1 => by
    obtain ⟨j', hj'⟩ := rounds_isConst hmds w hj k
    rw [rounds_succ]
    exact ⟨j', round_isConst hmds k (w k) hj' j'⟩

/-- circomlib's matrices have no zero entry. -/
theorem mds_ne_zero : ∀ t, 3 ≤ t → t ≤ 7 → ∀ i j : Fin t, (Poseidon.params t).mds i j ≠ 0
  | 3, _, _ => by decide +kernel
  | 4, _, _ => by decide +kernel
  | 5, _, _ => by decide +kernel
  | 6, _, _ => by decide +kernel
  | 7, _, _ => by decide +kernel

theorem fullRounds_params : ∀ t, 3 ≤ t → t ≤ 7 → (Poseidon.params t).fullRounds = 8
  | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ => rfl

/-- A call with a variable input returns a variable. -/
theorem hash_var_isConst {n : ℕ} (h2 : 2 ≤ n) (h6 : n ≤ 6) {ins : Fin n → FpVar}
    {w : hash_var.W n} {i : Fin n} (hi : (ins i).isConst = false) :
    (hash_var.hash_var n ins w).isConst = false := by
  set p := Poseidon.params (n + 1)
  have hmds : ∀ i j, p.mds i j ≠ 0 := mds_ne_zero (n + 1) (by omega) (by omega)
  have h8 : p.fullRounds = 8 := fullRounds_params (n + 1) (by omega) (by omega)
  obtain ⟨k, hk⟩ : ∃ k, p.fullRounds + p.partialRounds = k + 1 :=
    ⟨7 + p.partialRounds, by omega⟩
  have hs : ((Matrix.vecCons (FpVar.const 0) fun i => (FpVar.const 0).add (ins i)) i.succ).isConst =
      false := by
    simp only [Matrix.cons_val_succ]; cases h : ins i <;> simp_all [FpVar.add, FpVar.isConst]
  obtain ⟨j, hj⟩ := rounds_isConst hmds w hs k
  show ((permute p w _).2 0).isConst = false
  rw [permute, hk, rounds_succ]
  exact round_isConst hmds _ _ hj 0

end poseidon

/-- The hash functions of the circuits: Poseidon, the SHA-256 hash chain, and the Schnorr check
`verify_var` proves. -/
def hashes : Hashes where
  H := Poseidon.hash
  hc := Sha256.hashChain
  hc_lt := Sha256.hashChain_lt
  sigOK := auth.schnorrOK Poseidon.hash

namespace root.RootCircuit.synthesize_step

/-- With arkworks' Poseidon, a satisfying assignment proves `Root.Spec` under any hashes that are
Poseidon and the SHA-256 hash chain. -/
theorem sound_poseidon (h : Hashes) (hH : h.H = Poseidon.hash) (hc : h.hc = Sha256.hashChain)
    {z : Root.Z} {w : StepWit poseidon.hash_var} (hR : Rel z w) : Root.Spec h z w.spec (next z w) :=
  sound h (hH.trans poseidon.hash_var_hash.symm) hc hR

theorem complete_poseidon (h : Hashes) (hH : h.H = Poseidon.hash) (hc : h.hc = Sha256.hashChain)
    {z z' : Root.Z} {w : Root.Wit} (hS : Root.Spec h z w z') :
    ∃ sw : StepWit poseidon.hash_var, sw.spec = w ∧ Rel z sw ∧ next z sw = z' :=
  complete h (hH.trans poseidon.hash_var_hash.symm) hc hS

end root.RootCircuit.synthesize_step

namespace merge.MergeCircuit.synthesize_step

/-- With arkworks' Poseidon, a satisfying assignment proves `Merge.Spec` under any hashes that are
Poseidon, the SHA-256 hash chain, and the Schnorr check over Poseidon. -/
theorem sound_poseidon (h : Hashes) (hH : h.H = Poseidon.hash) (hc : h.hc = Sha256.hashChain)
    (hsig : h.sigOK = auth.schnorrOK Poseidon.hash) {z : Merge.Z} {w : StepWit poseidon.hash_var}
    (hR : Rel z w) : Merge.Spec h z w.spec (next z w) :=
  sound h (hH.trans poseidon.hash_var_hash.symm) hc (poseidon.hash_var_hash ▸ hsig) hR

theorem complete_poseidon (h : Hashes) (hH : h.H = Poseidon.hash) (hc : h.hc = Sha256.hashChain)
    (hsig : h.sigOK = auth.schnorrOK Poseidon.hash) {z z' : Merge.Z} {w : Merge.Wit}
    (hS : Merge.Spec h z w z') :
    ∃ sw : StepWit poseidon.hash_var, sw.spec = w ∧ Rel z sw ∧ next z sw = z' :=
  complete h (hH.trans poseidon.hash_var_hash.symm) hc (poseidon.hash_var_hash ▸ hsig) hS

/-- The nullifier `hash_chain_var` takes by value is a variable. -/
theorem nullifier_isConst {z : Merge.Z} {w : StepWit poseidon.hash_var} :
    (nullifier z w).isConst = false :=
  poseidon.hash_var_isConst (i := 1) (by norm_num) (by norm_num) rfl

end merge.MergeCircuit.synthesize_step

end Zerc20.Zkp

