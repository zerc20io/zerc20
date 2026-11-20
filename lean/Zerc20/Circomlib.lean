import Zerc20.Field

/-!
# circomlib's bit gadgets, and the range gadgets built on them

Each template is a relation `Rel` over its signals (inputs, outputs and internal witnesses) with
one conjunct per constraint the template emits. `sound` derives what the constraints pin down,
and `complete` shows that the honest witness satisfies them. Bits are field elements,
`Fin n → F`, as in circom, so their booleanity is a constraint of `Rel` rather than a type.
-/

namespace Zerc20

open Finset

namespace Circomlib

/-! ## Binary digits -/

/-- The number whose binary digits, least significant first, are the values of `b`. A circom
bit sum `Σ b[i]·2ⁱ` is this number cast into `F`. -/
def natVal {n : ℕ} (b : Fin n → F) : ℕ := ∑ i, (b i).val * 2 ^ (i : ℕ)

/-- The low `n` binary digits of `m`, which the honest prover computes as `(m >> i) & 1`. -/
def toBits (n m : ℕ) : Fin n → F := fun i => if m.testBit i then 1 else 0

/-- A sum `Σ dᵢ·2ⁱ` of digits `dᵢ ≤ 1` is below `2ⁿ`, and its bit `i` is `dᵢ`. -/
theorem digits_sum {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, d i ≤ 1) :
    ∑ i, d i * 2 ^ (i : ℕ) < 2 ^ n ∧
      ∀ i : Fin n, ((∑ i, d i * 2 ^ (i : ℕ)).testBit i).toNat = d i := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hlt, hbit⟩ := ih (fun i => d i.castSucc) (fun i => hd _)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last] at hlt hbit ⊢
    generalize ∑ i : Fin n, d i.castSucc * 2 ^ (i : ℕ) = S at hlt hbit ⊢
    have hS : S.testBit n = false := Nat.testBit_lt_two_pow hlt
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rcases (by have := hd (Fin.last n); omega : d (Fin.last n) = 0 ∨ d (Fin.last n) = 1)
      with h | h
    · rw [h, zero_mul, add_zero]
      refine ⟨by omega, fun i => Fin.lastCases ?_ (fun j => ?_) i⟩
      · simp [hS, h]
      · simpa using hbit j
    · rw [h, one_mul, add_comm]
      refine ⟨by omega, fun i => Fin.lastCases ?_ (fun j => ?_) i⟩
      · simp [Nat.testBit_two_pow_add_eq, hS, h]
      · simp [Nat.testBit_two_pow_add_gt j.isLt, hbit j]

/-- The low `n` binary digits of `m < 2ⁿ` sum back to `m`. -/
theorem sum_testBit {n m : ℕ} (hm : m < 2 ^ n) :
    ∑ i : Fin n, (m.testBit i).toNat * 2 ^ (i : ℕ) = m := by
  induction n generalizing m with
  | zero => simp_all
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlow : ∀ i : Fin n, m.testBit i = (m % 2 ^ n).testBit i := fun i => by
      simp [Nat.testBit_mod_two_pow, i.isLt]
    simp only [hlow]
    rw [ih (Nat.mod_lt _ (by positivity)), Nat.toNat_testBit]
    have hq : m / 2 ^ n < 2 := Nat.div_lt_of_lt_mul (by rw [pow_succ] at hm; linarith)
    have := Nat.mod_add_div m (2 ^ n)
    rw [Nat.mod_eq_of_lt hq, mul_comm]
    omega

@[simp] theorem val_one : (1 : F).val = 1 :=
  haveI : Fact (1 < r) := ⟨r_prime.one_lt⟩
  ZMod.val_one r

theorem bool_iff {x : F} : x * (x - 1) = 0 ↔ x = 0 ∨ x = 1 := by
  rw [mul_eq_zero, sub_eq_zero]

theorem val_le_one {x : F} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  rcases h with rfl | rfl <;> simp

/-- The circom bit sum is `natVal` cast into `F`, whether or not the bits are boolean. -/
theorem natVal_cast {n : ℕ} (b : Fin n → F) : (natVal b : F) = ∑ i, b i * 2 ^ (i : ℕ) := by
  simp only [natVal, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ZMod.natCast_zmod_val]

theorem natVal_lt {n : ℕ} {b : Fin n → F} (hb : ∀ i, b i = 0 ∨ b i = 1) :
    natVal b < 2 ^ n :=
  (digits_sum _ fun i => val_le_one (hb i)).1

/-- Boolean bits are the binary digits of their `natVal`. -/
theorem toBits_natVal {n : ℕ} {b : Fin n → F} (hb : ∀ i, b i = 0 ∨ b i = 1) :
    toBits n (natVal b) = b := by
  funext i
  have h : ((natVal b).testBit i).toNat = (b i).val :=
    (digits_sum _ fun i => val_le_one (hb i)).2 i
  unfold toBits
  cases hbit : (natVal b).testBit i <;> rw [hbit] at h <;> rcases hb i with h' | h' <;>
    simp_all

theorem natVal_toBits {n m : ℕ} (hm : m < 2 ^ n) : natVal (toBits n m) = m := by
  conv_rhs => rw [← sum_testBit hm]
  refine sum_congr rfl fun i _ => ?_
  unfold toBits
  cases m.testBit i <;> simp

theorem toBits_bool (n m : ℕ) (i : Fin n) : toBits n m i = 0 ∨ toBits n m i = 1 := by
  unfold toBits
  split <;> simp

theorem two_pow_253_lt_r : 2 ^ 253 < r := by unfold r; norm_num

theorem r_lt_two_pow_254 : r < 2 ^ 254 := by unfold r; norm_num

/-! ## Bitify -/

namespace Num2Bits

/-- circomlib `Num2Bits(n)`: each `out[i] * (out[i] - 1) === 0`, and `Σ out[i]·2ⁱ === in`.
The prover's `out[i] <-- (in >> i) & 1` is a hint and emits no constraint. -/
def Rel (n : ℕ) (x : F) (out : Fin n → F) : Prop :=
  (∀ i, out i * (out i - 1) = 0) ∧ ∑ i, out i * 2 ^ (i : ℕ) = x

/-- For any `n` the bits are boolean and sum to `x` modulo `r`. At `n ≥ 254` this is all the
constraints say: two bit patterns can sum to the same field element. -/
theorem sound_mod {n : ℕ} {x : F} {out : Fin n → F} (h : Rel n x out) :
    (∀ i, out i = 0 ∨ out i = 1) ∧ (natVal out : F) = x :=
  ⟨fun i => bool_iff.1 (h.1 i), (natVal_cast out).trans h.2⟩

/-- With `2ⁿ ≤ r` the bit sum cannot wrap, so `x < 2ⁿ` and `out` is the binary expansion of
`x`. -/
theorem sound {n : ℕ} {x : F} {out : Fin n → F} (hn : 2 ^ n ≤ r) (h : Rel n x out) :
    x.val < 2 ^ n ∧ out = toBits n x.val := by
  obtain ⟨hb, hx⟩ := sound_mod h
  have hlt := natVal_lt hb
  have hval : x.val = natVal out := by rw [← hx]; exact ZMod.val_natCast_of_lt (by omega)
  rw [hval, toBits_natVal hb]
  exact ⟨hlt, rfl⟩

theorem complete {n : ℕ} {x : F} (hx : x.val < 2 ^ n) : Rel n x (toBits n x.val) :=
  ⟨fun i => bool_iff.2 (toBits_bool n _ i),
    by rw [← natVal_cast, natVal_toBits hx, ZMod.natCast_zmod_val]⟩

end Num2Bits

namespace Bits2Num

/-- circomlib `Bits2Num(n)`: `out === Σ in[i]·2ⁱ`. It emits no booleanity constraint. -/
def Rel (n : ℕ) (inp : Fin n → F) (out : F) : Prop :=
  ∑ i, inp i * 2 ^ (i : ℕ) = out

theorem sound {n : ℕ} {inp : Fin n → F} {out : F} (h : Rel n inp out) :
    out = (natVal inp : F) :=
  h.symm.trans (natVal_cast inp).symm

theorem complete {n : ℕ} (inp : Fin n → F) : Rel n inp (natVal inp : F) :=
  (natVal_cast inp).symm

end Bits2Num

/-! ## CompConstant -/

/-- `b` read at index `j`, zero past its end. -/
def getD {n : ℕ} (b : Fin n → F) (j : ℕ) : F := if h : j < n then b ⟨j, h⟩ else 0

theorem natVal_eq_range {n : ℕ} (b : Fin n → F) :
    natVal b = ∑ j ∈ range n, (getD b j).val * 2 ^ j := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => (getD b j).val * 2 ^ j)]
  simp [natVal, getD]

/-- Binary digits read two at a time are base-4 digits. -/
theorem sum_range_pairs (e : ℕ → ℕ) (k : ℕ) :
    ∑ j ∈ range (2 * k), e j * 2 ^ j =
      ∑ i ∈ range k, (e (2 * i) + 2 * e (2 * i + 1)) * 4 ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, pow_succ, pow_mul]
    ring

/-- Comparing two numbers whose low base-`B` digits `x`, `y` are below `B` compares the high
digits first. -/
theorem lex_lt {B x y u t : ℕ} (hx : x < B) (hy : y < B) :
    x + u * B < y + t * B ↔ u < t ∨ u = t ∧ x < y := by
  constructor
  · intro h
    rcases lt_trichotomy u t with h1 | rfl | h1
    · exact Or.inl h1
    · exact Or.inr ⟨rfl, by omega⟩
    · have : (t + 1) * B ≤ u * B := Nat.mul_le_mul_right B h1
      rw [add_one_mul] at this
      omega
  · rintro (h1 | ⟨rfl, h1⟩)
    · have : (u + 1) * B ≤ t * B := Nat.mul_le_mul_right B h1
      rw [add_one_mul] at this
      omega
    · omega

namespace CompConstant

/-- Part `i` of circomlib `CompConstant(ct)`, over the input pair `slsb = in[2i]`,
`smsb = in[2i+1]`. `b = 2¹²⁸ - 2ⁱ` and `a = 2ⁱ` are the values the template's loop variables
`b` and `a` hold at iteration `i`. -/
def part (ct i : ℕ) (slsb smsb : F) : F :=
  let clsb := (ct >>> (i * 2)) &&& 1
  let cmsb := (ct >>> (i * 2 + 1)) &&& 1
  let b : F := 2 ^ 128 - 2 ^ i
  let a : F := 2 ^ i
  if cmsb = 0 ∧ clsb = 0 then -b * smsb * slsb + b * smsb + b * slsb
  else if cmsb = 0 ∧ clsb = 1 then a * smsb * slsb - a * slsb + b * smsb - a * smsb + a
  else if cmsb = 1 ∧ clsb = 0 then b * smsb * slsb - a * smsb + a
  else -a * smsb * slsb + a

/-- The value part `i` takes for an input pair `s` against the constant's pair `c`, both base-4
digits: `2¹²⁸ - 2ⁱ` when `s > c`, `2ⁱ` when `s < c`, and 0 when they are equal. -/
def partVal (i c s : ℕ) : ℕ := if c < s then 2 ^ 128 - 2 ^ i else if s < c then 2 ^ i else 0

theorem partVal_cast {i : ℕ} (c s : ℕ) (hi : i ≤ 128) :
    (partVal i c s : F) = if c < s then 2 ^ 128 - 2 ^ i else if s < c then 2 ^ i else 0 := by
  have hpow : 2 ^ i ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) hi
  unfold partVal
  split_ifs <;> simp only [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero]

/-- On boolean inputs each of the template's four polynomials is `partVal` of the pairs. -/
theorem part_eq (ct i : ℕ) (hi : i ≤ 128) {l h : F} (hl : l = 0 ∨ l = 1)
    (hh : h = 0 ∨ h = 1) :
    part ct i l h = (partVal i (ct / 4 ^ i % 4) (l.val + 2 * h.val) : F) := by
  obtain ⟨c0, hc0, h0⟩ : ∃ c, (ct >>> (i * 2)) &&& 1 = c ∧ c < 2 :=
    ⟨_, rfl, by rw [Nat.and_one_is_mod]; omega⟩
  obtain ⟨c1, hc1, h1⟩ : ∃ c, (ct >>> (i * 2 + 1)) &&& 1 = c ∧ c < 2 :=
    ⟨_, rfl, by rw [Nat.and_one_is_mod]; omega⟩
  have hq : ct / 4 ^ i % 4 = c0 + 2 * c1 := by
    have e4 : 4 ^ i = 2 ^ (i * 2) := by rw [mul_comm, pow_mul]; norm_num
    rw [← hc0, ← hc1, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
      Nat.and_one_is_mod, pow_succ, ← Nat.div_div_eq_div_mul, e4]
    omega
  rw [partVal_cast _ _ hi, hq]
  simp only [part, hc0, hc1]
  interval_cases c0 <;> interval_cases c1 <;> rcases hl with rfl | rfl <;>
    rcases hh with rfl | rfl <;> (simp; try ring)

/-- The arithmetic of `CompConstant` over base-4 digits `s i` of the input against those of `ct`.
`X` is the input's low `k` digits and `S` the sum of the first `k` parts. Step `k` adds
`2¹²⁸ - 2ᵏ` when the input digit is larger, `2ᵏ` when it is smaller, and nothing when they are
equal. So modulo `2¹²⁸` the sum sits within `2ᵏ` below `2¹²⁸` when the low digits compare
greater, and below `2ᵏ` otherwise: the most significant differing digit decides. -/
theorem partSum (ct : ℕ) (s : ℕ → ℕ) (hs : ∀ i, s i < 4) (k : ℕ) (hk : k ≤ 127) :
    ∑ i ∈ range k, s i * 4 ^ i < 4 ^ k ∧
      ∑ i ∈ range k, partVal i (ct / 4 ^ i % 4) (s i) ≤ k * 2 ^ 128 ∧
      (ct % 4 ^ k < ∑ i ∈ range k, s i * 4 ^ i →
        2 ^ 128 - 2 ^ k < (∑ i ∈ range k, partVal i (ct / 4 ^ i % 4) (s i)) % 2 ^ 128) ∧
      (∑ i ∈ range k, s i * 4 ^ i ≤ ct % 4 ^ k →
        (∑ i ∈ range k, partVal i (ct / 4 ^ i % 4) (s i)) % 2 ^ 128 < 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hX, hS, hgt, hle⟩ := ih (by omega)
    simp only [sum_range_succ]
    generalize ∑ i ∈ range k, s i * 4 ^ i = X at hX hS hgt hle ⊢
    generalize ∑ i ∈ range k, partVal i (ct / 4 ^ i % 4) (s i) = S at hX hS hgt hle ⊢
    have hC : ct % 4 ^ k < 4 ^ k := Nat.mod_lt _ (by positivity)
    have hcp : ct / 4 ^ k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hsk := hs k
    have hA : 2 ^ k ≤ 2 ^ 126 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have h4 : 4 ^ (k + 1) = 4 * 4 ^ k := by ring
    have hsB : s k * 4 ^ k ≤ 3 * 4 ^ k := Nat.mul_le_mul_right _ (by omega)
    have key1 := lex_lt (u := ct / 4 ^ k % 4) (t := s k) hC hX
    have key2 := lex_lt (u := s k) (t := ct / 4 ^ k % 4) hX hC
    rw [Nat.mod_pow_succ, mul_comm (4 ^ k) (ct / 4 ^ k % 4)]
    unfold partVal
    split_ifs with c1 c2
    · refine ⟨by omega, by omega, fun _ => by omega, fun h => by omega⟩
    · refine ⟨by omega, by omega, fun h => by omega, fun _ => by omega⟩
    · have : ct / 4 ^ k % 4 = s k := by omega
      rw [this] at key1 key2 ⊢
      rw [add_zero]
      exact ⟨by omega, hS.trans (Nat.mul_le_mul_right _ (by omega)), fun h => by omega,
        fun h => by omega⟩

/-- The input pair `in[2i] + 2·in[2i+1]` as a base-4 digit. -/
def pair (inp : Fin 254 → F) (i : ℕ) : ℕ :=
  (getD inp (2 * i)).val + 2 * (getD inp (2 * i + 1)).val

theorem getD_bool {n : ℕ} {b : Fin n → F} (hb : ∀ i, b i = 0 ∨ b i = 1) (j : ℕ) :
    getD b j = 0 ∨ getD b j = 1 := by
  unfold getD
  split
  · exact hb _
  · exact Or.inl rfl

theorem pair_lt {inp : Fin 254 → F} (hb : ∀ i, inp i = 0 ∨ inp i = 1) (i : ℕ) :
    pair inp i < 4 := by
  have := val_le_one (getD_bool hb (2 * i))
  have := val_le_one (getD_bool hb (2 * i + 1))
  unfold pair
  omega

theorem natVal_eq_pairs (inp : Fin 254 → F) :
    natVal inp = ∑ i ∈ range 127, pair inp i * 4 ^ i := by
  rw [natVal_eq_range]
  exact sum_range_pairs (fun j => (getD inp j).val) 127

/-- The internal signals of `CompConstant`: `parts`, `sout`, and the bits of `num2bits`. -/
structure Witness where
  parts : Fin 127 → F
  sout : F
  bits : Fin 135 → F

/-- circomlib `CompConstant(ct)`: `parts[i] <== part i`, `sout <== Σ parts`,
`Num2Bits(135)` of `sout`, and `out <== bits[127]`. `ct` is a natural number: circom's shifts read
the canonical representative of a field constant, so `CompConstant(-1)` has `ct = r - 1`. -/
def Rel (ct : ℕ) (inp : Fin 254 → F) (w : Witness) (out : F) : Prop :=
  (∀ i : Fin 127,
    w.parts i = part ct i (inp ⟨2 * i, by omega⟩) (inp ⟨2 * i + 1, by omega⟩)) ∧
  w.sout = ∑ i, w.parts i ∧
  Num2Bits.Rel 135 w.sout w.bits ∧
  out = w.bits ⟨127, by norm_num⟩

/-- What the parts pin down: their sum fits in 135 bits, and its bit 127 says whether the input
exceeds `ct`. -/
theorem sum_parts {ct : ℕ} (hct : ct < 2 ^ 254) {inp : Fin 254 → F}
    (hb : ∀ i, inp i = 0 ∨ inp i = 1) {parts : Fin 127 → F}
    (hparts : ∀ i : Fin 127,
      parts i = part ct i (inp ⟨2 * i, by omega⟩) (inp ⟨2 * i + 1, by omega⟩)) :
    (∑ i, parts i).val < 2 ^ 135 ∧ ((∑ i, parts i).val.testBit 127 ↔ ct < natVal inp) := by
  obtain ⟨-, hS, hgt, hle⟩ := partSum ct (pair inp) (pair_lt hb) 127 le_rfl
  have hct' : ct % 4 ^ 127 = ct := Nat.mod_eq_of_lt (by norm_num at hct ⊢; omega)
  rw [hct', ← natVal_eq_pairs] at hgt hle
  have hsum : ∑ i, parts i =
      ((∑ i ∈ range 127, partVal i (ct / 4 ^ i % 4) (pair inp i) : ℕ) : F) := by
    rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
      (fun i => ((partVal i (ct / 4 ^ i % 4) (pair inp i) : ℕ) : F))]
    refine sum_congr rfl fun i _ => ?_
    rw [hparts i, part_eq ct i (by omega) (hb _) (hb _)]
    simp [pair, getD, show 2 * (i : ℕ) < 254 by omega, show 2 * (i : ℕ) + 1 < 254 by omega]
  generalize ∑ i ∈ range 127, partVal i (ct / 4 ^ i % 4) (pair inp i) = S at hS hgt hle hsum
  have hlt : S < r := lt_of_le_of_lt hS (lt_trans (by norm_num) two_pow_253_lt_r)
  rw [hsum, ZMod.val_natCast_of_lt hlt, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  constructor
  · omega
  · by_cases h : ct < natVal inp
    · have := hgt h
      omega
    · have := hle (by omega)
      omega

theorem sound {ct : ℕ} {inp : Fin 254 → F} {w : Witness} {out : F} (hct : ct < 2 ^ 254)
    (hb : ∀ i, inp i = 0 ∨ inp i = 1) (h : Rel ct inp w out) :
    out = if ct < natVal inp then 1 else 0 := by
  obtain ⟨hparts, hsout, hbits, hout⟩ := h
  obtain ⟨-, hbit⟩ := sum_parts hct hb hparts
  have := (Num2Bits.sound (le_trans (by norm_num) two_pow_253_lt_r.le) hbits).2
  rw [hout, this, hsout]
  simp only [toBits, ← hbit]

/-- The honest internal signals. -/
def witness (ct : ℕ) (inp : Fin 254 → F) : Witness :=
  let parts := fun i : Fin 127 =>
    part ct i (inp ⟨2 * i, by omega⟩) (inp ⟨2 * i + 1, by omega⟩)
  { parts, sout := ∑ i, parts i, bits := toBits 135 (∑ i, parts i).val }

theorem complete {ct : ℕ} {inp : Fin 254 → F} (hct : ct < 2 ^ 254)
    (hb : ∀ i, inp i = 0 ∨ inp i = 1) :
    Rel ct inp (witness ct inp) (if ct < natVal inp then 1 else 0) := by
  have h : Rel ct inp (witness ct inp) ((witness ct inp).bits ⟨127, by norm_num⟩) :=
    ⟨fun _ => rfl, rfl, Num2Bits.complete (sum_parts hct hb fun _ => rfl).1, rfl⟩
  rwa [← sound hct hb h]

end CompConstant

namespace AliasCheck

/-- circomlib `AliasCheck`: `CompConstant(-1)` of the bits, and `compConstant.out === 0`. -/
def Rel (inp : Fin 254 → F) (w : CompConstant.Witness) (out : F) : Prop :=
  CompConstant.Rel (r - 1) inp w out ∧ out = 0

theorem r_sub_one_lt : r - 1 < 2 ^ 254 := by unfold r; norm_num

/-- Boolean bits that pass the check are the digits of a number below `r`. -/
theorem sound {inp : Fin 254 → F} {w : CompConstant.Witness} {out : F}
    (hb : ∀ i, inp i = 0 ∨ inp i = 1) (h : Rel inp w out) : natVal inp < r := by
  have := CompConstant.sound r_sub_one_lt hb h.1
  rw [h.2] at this
  split_ifs at this with hlt
  · exact absurd this.symm one_ne_zero
  · have := r_prime.pos
    omega

theorem complete {inp : Fin 254 → F} (hb : ∀ i, inp i = 0 ∨ inp i = 1)
    (hlt : natVal inp < r) :
    Rel inp (CompConstant.witness (r - 1) inp) 0 := by
  have := CompConstant.complete r_sub_one_lt hb
  rw [if_neg (by omega)] at this
  exact ⟨this, rfl⟩

end AliasCheck

namespace Num2Bits_strict

/-- circomlib `Num2Bits_strict`: `Num2Bits(254)` of `in`, and `AliasCheck` of its bits. -/
def Rel (x : F) (out : Fin 254 → F) (w : CompConstant.Witness) (aliasOut : F) : Prop :=
  Num2Bits.Rel 254 x out ∧ AliasCheck.Rel out w aliasOut

/-- The bits are the canonical binary expansion of `x`: the alias check rules out the second
expansion `x + r` that `Num2Bits(254)` alone admits. -/
theorem sound {x : F} {out : Fin 254 → F} {w : CompConstant.Witness} {aliasOut : F}
    (h : Rel x out w aliasOut) : out = toBits 254 x.val := by
  obtain ⟨hb, hx⟩ := Num2Bits.sound_mod h.1
  have hval : x.val = natVal out := by
    rw [← hx]; exact ZMod.val_natCast_of_lt (AliasCheck.sound hb h.2)
  rw [hval, toBits_natVal hb]

theorem complete (x : F) :
    Rel x (toBits 254 x.val) (CompConstant.witness (r - 1) (toBits 254 x.val)) 0 := by
  have hx : x.val < 2 ^ 254 := lt_trans (ZMod.val_lt x) r_lt_two_pow_254
  refine ⟨Num2Bits.complete hx, AliasCheck.complete (toBits_bool 254 _) ?_⟩
  rw [natVal_toBits hx]
  exact ZMod.val_lt x

end Num2Bits_strict

/-! ## Comparators -/

namespace IsZero

/-- circomlib `IsZero`: `out <== -in·inv + 1` and `in·out === 0`, with the witness `inv`. -/
def Rel (x out inv : F) : Prop :=
  out = -x * inv + 1 ∧ x * out = 0

theorem sound {x out inv : F} (h : Rel x out inv) : out = if x = 0 then 1 else 0 := by
  obtain ⟨hout, hx⟩ := h
  split_ifs with h0
  · rw [hout, h0]; ring
  · exact (mul_eq_zero.1 hx).resolve_left h0

/-- The honest `inv` is `in⁻¹`, which is 0 at `in = 0`. -/
theorem complete (x : F) : Rel x (if x = 0 then 1 else 0) x⁻¹ := by
  by_cases h0 : x = 0 <;> simp [Rel, h0]

end IsZero

namespace ForceEqualIfEnabled

/-- circomlib `ForceEqualIfEnabled`: `IsZero` of `in[1] - in[0]`, and
`(1 - isz.out)·enabled === 0`. -/
def Rel (enabled in0 in1 iszOut iszInv : F) : Prop :=
  IsZero.Rel (in1 - in0) iszOut iszInv ∧ (1 - iszOut) * enabled = 0

/-- Any nonzero `enabled`, not only 1, forces the inputs equal. -/
theorem sound {enabled in0 in1 iszOut iszInv : F} (h : Rel enabled in0 in1 iszOut iszInv)
    (hen : enabled ≠ 0) : in0 = in1 := by
  have hout := IsZero.sound h.1
  have := (mul_eq_zero.1 h.2).resolve_right hen
  split_ifs at hout with h0
  · exact (sub_eq_zero.1 h0).symm
  · rw [hout] at this; simp at this

theorem complete {enabled in0 in1 : F} (h : enabled = 0 ∨ in0 = in1) :
    Rel enabled in0 in1 (if in1 - in0 = 0 then 1 else 0) (in1 - in0)⁻¹ := by
  refine ⟨IsZero.complete _, ?_⟩
  rcases h with h | h
  · rw [h, mul_zero]
  · simp [h]

end ForceEqualIfEnabled

end Circomlib

/-! ## Our range gadgets -/

namespace Circom

open Circomlib

namespace Boolean

/-- Our `Boolean`: `in * (in - 1) === 0`. -/
def Rel (x : F) : Prop := x * (x - 1) = 0

theorem sound {x : F} (h : Rel x) : x = 0 ∨ x = 1 := bool_iff.1 h

theorem complete {x : F} (h : x = 0 ∨ x = 1) : Rel x := bool_iff.2 h

end Boolean

namespace RangeCheck

/-- Our `RangeCheck(bits)`: `Num2Bits(bits)` of `in`, `Bits2Num(bits)` of those bits, and
`recompose.out === in`. The template's asserts `0 < bits < 254` emit no constraint; `sound`
takes `n < 254` as its hypothesis. -/
def Rel (n : ℕ) (x : F) (bits : Fin n → F) (out : F) : Prop :=
  Num2Bits.Rel n x bits ∧ Bits2Num.Rel n bits out ∧ out = x

/-- Below 254 bits the decomposition cannot wrap the field, so `x < 2ⁿ`. -/
theorem sound {n : ℕ} {x : F} {bits : Fin n → F} {out : F} (hn : n < 254)
    (h : Rel n x bits out) : x.val < 2 ^ n :=
  (Num2Bits.sound ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans
    two_pow_253_lt_r.le) h.1).1

theorem complete {n : ℕ} {x : F} (hx : x.val < 2 ^ n) : Rel n x (toBits n x.val) x :=
  ⟨Num2Bits.complete hx, by
    rw [Bits2Num.Rel, ← natVal_cast, natVal_toBits hx, ZMod.natCast_zmod_val], rfl⟩

end RangeCheck

namespace AddressFromDigest

/-- Our `AddressFromDigest(address_bits, pow_bits)`, over the signals `enabled`, `digest`,
`address`, the canonical bits of `digest` with the internals of their alias check, and
`digest_num.out`. The constraints: `Num2Bits_strict` of `digest`, `Bits2Num(254)` of its bits,
`digest_num.out === digest`, `address <== Σ_{i < address_bits} bits[i]·2ⁱ`, and
`bits[j] * enabled === 0` for each `j` in `254 - pow_bits ≤ j < 254`. -/
def Rel (addressBits powBits : ℕ) (enabled digest address : F) (bits : Fin 254 → F)
    (w : CompConstant.Witness) (aliasOut num : F) : Prop :=
  Num2Bits_strict.Rel digest bits w aliasOut ∧
  Bits2Num.Rel 254 bits num ∧
  num = digest ∧
  address = (∑ i : Fin 254, if (i : ℕ) < addressBits then bits i * 2 ^ (i : ℕ) else 0) ∧
  ∀ j : Fin 254, 254 - powBits ≤ (j : ℕ) → bits j * enabled = 0

/-- The address sum over the canonical bits of `d` is `d mod 2^addressBits`. -/
theorem address_sum (addressBits : ℕ) {d : ℕ} (hd : d < 2 ^ 254) :
    (∑ i : Fin 254, if (i : ℕ) < addressBits then toBits 254 d i * 2 ^ (i : ℕ) else 0) =
      ((d % 2 ^ addressBits : ℕ) : F) := by
  rw [← natVal_toBits (lt_of_le_of_lt (Nat.mod_le _ _) hd), natVal_cast]
  refine sum_congr rfl fun i _ => ?_
  simp only [toBits, Nat.testBit_mod_two_pow]
  split_ifs <;> simp_all
  omega

/-- `address` is the low `addressBits` bits of `digest`, and any nonzero `enabled` forces the
top `powBits` of its 254 canonical bits to zero, that is `digest < 2^(254 - powBits)`. -/
theorem sound {addressBits powBits : ℕ} {enabled digest address : F} {bits : Fin 254 → F}
    {w : CompConstant.Witness} {aliasOut num : F}
    (h : Rel addressBits powBits enabled digest address bits w aliasOut num) :
    bits = toBits 254 digest.val ∧ address.val = digest.val % 2 ^ addressBits ∧
      (enabled ≠ 0 → digest.val < 2 ^ (254 - powBits)) := by
  obtain ⟨hstrict, -, -, haddr, hpow⟩ := h
  have hbits := Num2Bits_strict.sound hstrict
  have hd := ZMod.val_lt digest
  refine ⟨hbits, ?_, fun hen => Nat.lt_pow_two_of_testBit _ fun j hj => ?_⟩
  · rw [haddr, hbits, address_sum _ (hd.trans r_lt_two_pow_254)]
    exact ZMod.val_natCast_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) hd)
  · by_cases hj' : j < 254
    · have h0 := (mul_eq_zero.1 (hpow ⟨j, hj'⟩ hj)).resolve_right hen
      rw [hbits] at h0
      simpa [toBits] using h0
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hd.trans r_lt_two_pow_254)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- With `enabled = 0` every digest passes, and with any other `enabled` every digest below
`2^(254 - powBits)` does. -/
theorem complete (addressBits powBits : ℕ) {enabled digest : F}
    (h : enabled = 0 ∨ digest.val < 2 ^ (254 - powBits)) :
    Rel addressBits powBits enabled digest ((digest.val % 2 ^ addressBits : ℕ) : F)
      (toBits 254 digest.val) (CompConstant.witness (r - 1) (toBits 254 digest.val)) 0
      digest := by
  have hd := (ZMod.val_lt digest).trans r_lt_two_pow_254
  have hstrict := Num2Bits_strict.complete digest
  refine ⟨hstrict, hstrict.1.2, rfl, (address_sum _ hd).symm, fun j hj => ?_⟩
  rcases h with h | h
  · rw [h, mul_zero]
  · have : digest.val.testBit j = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hj))
    simp [toBits, this]

end AddressFromDigest

end Circom

end Zerc20
