import Zerc20.Field
import Zerc20.BabyJubJub.Group
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Baby-JubJub and its arkworks gadgets

`ark-ed-on-bn254`'s curve over `F`: `x² + y² = 1 + d·x²·y²` with `d = 168696/168700`. Euler's
criterion shows `d` is not a square in `F`, so `Edwards.Point d` is a group under the complete
addition law.

The gadgets are `ark-r1cs-std`'s `AffineVar` over this curve, the `EdwardsVar` with which the
spend-authorization circuit checks Schnorr signatures. An `AffineVar` is modelled by its
coordinate pair. Each `Rel` states the
gadget's constraints between the values of the linear combinations involved. A product with a
constant operand is folded by arkworks into a linear combination and emits no constraint; its
value still satisfies the equation the model states for it, so one relation covers constant and
variable operands. Bits are `Bool`s, entering a relation as the field values `0` and `1`; their
booleanity is enforced where they are allocated, outside these gadgets.
-/

namespace Zerc20.BabyJubJub

/-- `EdwardsConfig::COEFF_D`, `168696/168700`. -/
def d : F := 9706598848417545097372247223557719406784115219466060233080913168975159366771

theorem d_spec : d * 168700 = 168696 := by
  unfold d F r
  reduce_mod_char

/-- Euler's criterion: `d^((r - 1)/2) = -1`. -/
theorem d_not_square : ¬IsSquare d := by
  have h0 : d ≠ 0 := by unfold d F r; decide
  rw [ZMod.euler_criterion r h0]
  have : d ^ (r / 2) = -1 := by unfold d F r; reduce_mod_char
  rw [this]
  unfold F r
  decide

instance : Fact (¬IsSquare d) := ⟨d_not_square⟩

instance : NeZero (2 : F) := ⟨by unfold F r; decide⟩

/-- A point of Baby-JubJub. -/
abbrev Point := Edwards.Point d

/-- `EdwardsConfig::GENERATOR`, `(GENERATOR_X, GENERATOR_Y)`. -/
def G : Point where
  x := 19698561148652590122159747500897617769866003486955115824547446575314762165298
  y := 19298250018296453272277890825869354524455968081175474282777126169995084727839
  on_curve := by unfold d F r; reduce_mod_char

/-- The order of the prime-order subgroup, `ark-ed-on-bn254`'s scalar field. -/
def l : ℕ := 2736030358979909402780800718157159386076813972158567259200215660948447373041

/-! ### The order of `G`

The kernel checks `l • G = 0` by double-and-add in projective coordinates over `ℕ`, reduced
mod `r`: projective addition needs no inversion, so every step is a few multiplications of
numbers below `r²`. -/

/-- `d` as a natural number. -/
def dN : ℕ := 9706598848417545097372247223557719406784115219466060233080913168975159366771

/-- `a − b` mod `r`. -/
def subN (a b : ℕ) : ℕ := (a + (r - b % r)) % r

/-- Projective addition with `a = 1`, mod `r`: with `A = Z₁Z₂`, `B = A²`, `C = X₁X₂`, `D = Y₁Y₂`
and `E = d·C·D`, the sum is `(A·(B − E)·((X₁ + Y₁)(X₂ + Y₂) − C − D), A·(B + E)·(D − C),
(B − E)·(B + E))`. -/
def paddN (P Q : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let A := P.2.2 * Q.2.2 % r
  let B := A * A % r
  let C := P.1 * Q.1 % r
  let D := P.2.1 * Q.2.1 % r
  let E := dN * C % r * D % r
  let H := subN (subN ((P.1 + P.2.1) * (Q.1 + Q.2.1) % r) C) D
  (A * subN B E % r * H % r, A * ((B + E) % r) % r * subN D C % r, subN B E * ((B + E) % r) % r)

/-- Little-endian double-and-add over the low `n` bits of `k`, from the base `P` and the
accumulator `acc`. -/
def smulN : ℕ → ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | 0, _, _, acc => acc
  | n + 1, k, P, acc => smulN n (k / 2) (paddN P P) (if k % 2 = 1 then paddN acc P else acc)

/-- `(X : Y : Z)` represents `Q`: `Z ≠ 0`, `X = x·Z` and `Y = y·Z` in `F`. -/
def Rep (p : ℕ × ℕ × ℕ) (Q : Point) : Prop :=
  (p.2.2 : F) ≠ 0 ∧ (p.1 : F) = Q.x * p.2.2 ∧ (p.2.1 : F) = Q.y * p.2.2

theorem cast_mod (a : ℕ) : ((a % r : ℕ) : F) = a := ZMod.natCast_mod a r

theorem cast_subN (a b : ℕ) : (subN a b : F) = a - b := by
  rw [subN, cast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ r_prime.pos).le, ZMod.natCast_self,
    cast_mod]
  ring

theorem cast_dN : (dN : F) = d := by
  unfold dN d
  exact Nat.cast_ofNat

theorem paddN_rep {p q : ℕ × ℕ × ℕ} {P Q : Point} (hp : Rep p P) (hq : Rep q Q) :
    Rep (paddN p q) (P + Q) := by
  obtain ⟨hz1, hx1, hy1⟩ := hp
  obtain ⟨hz2, hx2, hy2⟩ := hq
  have hD1 := Edwards.one_add_ne_zero P Q
  have hD2 := Edwards.one_sub_ne_zero P Q
  simp only [Rep, paddN, cast_mod, cast_subN, Nat.cast_mul, Nat.cast_add, cast_dN]
  rw [hx1, hy1, hx2, hy2]
  have hZ : ((p.2.2 : F) * q.2.2) ^ 2 * ((p.2.2 : F) * q.2.2) ^ 2 *
      (1 - d * P.x * Q.x * P.y * Q.y) * (1 + d * P.x * Q.x * P.y * Q.y) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by simp [hz1, hz2]) hD2) hD1
  refine ⟨?_, ?_, ?_⟩
  · convert hZ using 1
    ring
  · simp only [Edwards.Point.add_x]
    rw [div_mul_eq_mul_div, eq_div_iff hD1]
    ring
  · simp only [Edwards.Point.add_y]
    rw [div_mul_eq_mul_div, eq_div_iff hD2]
    ring

theorem smulN_rep : ∀ (n k : ℕ) (p acc : ℕ × ℕ × ℕ) (P A : Point), Rep p P → Rep acc A →
    Rep (smulN n k p acc) (A + (k % 2 ^ n) • P)
  | 0, k, p, acc, P, A, _, ha => by simpa [smulN, Nat.mod_one] using ha
  | n + 1, k, p, acc, P, A, hp, ha => by
    have hacc : Rep (if k % 2 = 1 then paddN acc p else acc) (A + (k % 2) • P) := by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · simpa [h] using ha
      · simpa [h] using paddN_rep ha hp
    have e : A + (k % 2 ^ (n + 1)) • P = A + (k % 2) • P + (k / 2 % 2 ^ n) • (P + P) := by
      rw [pow_succ', Nat.mod_mul, add_nsmul, mul_nsmul, two_nsmul, add_assoc]
    rw [smulN, e]
    exact smulN_rep n (k / 2) (paddN p p) _ (P + P) _ (paddN_rep hp hp) hacc

/-- `G` in projective coordinates. -/
def Gp : ℕ × ℕ × ℕ :=
  (19698561148652590122159747500897617769866003486955115824547446575314762165298,
    19298250018296453272277890825869354524455968081175474282777126169995084727839, 1)

theorem smulN_l : (smulN 251 l Gp (0, 1, 1)).1 % r = 0 ∧
    (smulN 251 l Gp (0, 1, 1)).2.1 % r = (smulN 251 l Gp (0, 1, 1)).2.2 % r := by
  decide +kernel

/-- `G` has order `l`. -/
theorem l_smul_G : l • G = 0 := by
  have hG : Rep Gp G := by simp [Rep, Gp, G]
  have h0 : Rep (0, 1, 1) (0 : Point) := by simp [Rep]
  have h := smulN_rep 251 l _ _ G 0 hG h0
  rw [Nat.mod_eq_of_lt (by unfold l; norm_num), zero_add] at h
  obtain ⟨hz, hx, hy⟩ := h
  obtain ⟨e1, e2⟩ := smulN_l
  rw [← cast_mod, e1, Nat.cast_zero] at hx
  rw [← cast_mod, e2, cast_mod] at hy
  generalize l • G = Q at hx hy ⊢
  refine Edwards.Point.ext ?_ (mul_right_cancel₀ hz (hy.symm.trans (one_mul _).symm))
  exact (mul_eq_zero.mp hx.symm).resolve_right hz

end Zerc20.BabyJubJub

namespace Zerc20.Ark

open BabyJubJub

namespace FpVar

/-- `TwoBitLookupGadget::two_bit_lookup` for `FpVar` with variable bits `b = (b₀, b₁)` and
constant table `c`: the witness `r` with
`(b₁·(c₃ − c₂ − c₁ + c₀) + (c₁ − c₀))·b₀ = r − c₀ + b₁·(c₀ − c₂)`. -/
def two_bit_lookup.Rel (b : F × F) (c : Fin 4 → F) (r : F) : Prop :=
  (b.2 * (c 3 - c 2 - c 1 + c 0) + (c 1 - c 0)) * b.1 = r - c 0 + b.2 * (c 0 - c 2)

/-- The entry at index `b₀ + 2·b₁`. -/
def two_bit_lookup.spec (b0 b1 : Bool) (c : Fin 4 → F) : F :=
  if b1 then (if b0 then c 3 else c 2) else (if b0 then c 1 else c 0)

theorem two_bit_lookup.sound {b0 b1 : Bool} {c : Fin 4 → F} {r : F}
    (h : two_bit_lookup.Rel ((b0.toNat : F), (b1.toNat : F)) c r) :
    r = two_bit_lookup.spec b0 b1 c := by
  unfold two_bit_lookup.Rel at h
  cases b0 <;> cases b1 <;> simp [two_bit_lookup.spec] at h ⊢ <;> linear_combination -h

theorem two_bit_lookup.complete (b0 b1 : Bool) (c : Fin 4 → F) :
    two_bit_lookup.Rel ((b0.toNat : F), (b1.toNat : F)) c (two_bit_lookup.spec b0 b1 c) := by
  unfold two_bit_lookup.Rel two_bit_lookup.spec
  cases b0 <;> cases b1 <;> simp

end FpVar

namespace AffineVar

/-- The coordinates of an `AffineVar` holding `P`. -/
def ofPoint (P : Point) : F × F := (P.x, P.y)

theorem ofPoint_injective : Function.Injective ofPoint := fun _ _ h =>
  Edwards.Point.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- `CurveVar::zero`: the constant `(0, 1)`; no constraints. -/
def zero : F × F := (0, 1)

theorem zero_eq : zero = ofPoint 0 := rfl

/-! ### Addition -/

/-- The witnesses of one addition. -/
structure AddW where
  u : F
  v0 : F
  v1 : F
  v0v1 : F
  x3 : F
  y3 : F

/-- `impl Add for AffineVar` (`impl_bounded_ops!`), with `a = 1`: `u = (−x₁ + y₁)·(x₂ + y₂)`,
`v₀ = y₂·x₁`, `v₁ = x₂·y₁`, `v₀v₁ = v₀·v₁`, and the witnesses `x₃, y₃` with
`x₃·(d·v₀v₁ + 1) = v₀ + v₁` and `y₃·(−(d·v₀v₁ − 1)) = u + a·v₀ − v₁`. -/
def add.Rel (p q : F × F) (w : AddW) : Prop :=
  (-p.1 + p.2) * (q.1 + q.2) = w.u ∧ q.2 * p.1 = w.v0 ∧ q.1 * p.2 = w.v1 ∧
    w.v0 * w.v1 = w.v0v1 ∧ w.x3 * (d * w.v0v1 + 1) = w.v0 + w.v1 ∧
    w.y3 * -(d * w.v0v1 - 1) = w.u + w.v0 - w.v1

/-- The sum, `(x₃, y₃)`. -/
def add.out (w : AddW) : F × F := (w.x3, w.y3)

/-- The witnesses arkworks assigns. -/
def add.wit (P Q : Point) : AddW where
  u := (-P.x + P.y) * (Q.x + Q.y)
  v0 := Q.y * P.x
  v1 := Q.x * P.y
  v0v1 := Q.y * P.x * (Q.x * P.y)
  x3 := (P + Q).x
  y3 := (P + Q).y

/-- On curve points the constraints determine the sum: neither `1 ± d·x₁x₂y₁y₂` vanishes. -/
theorem add.sound {P Q : Point} {w : AddW} (h : add.Rel (ofPoint P) (ofPoint Q) w) :
    add.out w = ofPoint (P + Q) := by
  obtain ⟨hu, h0, h1, h01, hx, hy⟩ := h
  simp only [ofPoint] at hu h0 h1
  rw [← h01, ← h0, ← h1] at hx hy
  rw [← hu] at hy
  simp only [add.out, ofPoint, Edwards.Point.add_x, Edwards.Point.add_y, Prod.mk.injEq]
  constructor
  · rw [eq_div_iff (Edwards.one_add_ne_zero P Q)]
    linear_combination hx
  · rw [eq_div_iff (Edwards.one_sub_ne_zero P Q)]
    linear_combination hy

theorem add.complete (P Q : Point) :
    add.Rel (ofPoint P) (ofPoint Q) (add.wit P Q) ∧ add.out (add.wit P Q) = ofPoint (P + Q) := by
  have hp := Edwards.one_add_ne_zero P Q
  have hm := Edwards.one_sub_ne_zero P Q
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_, ?_⟩, rfl⟩
  · simp only [add.wit, Edwards.Point.add_x]
    rw [div_mul_eq_mul_div, div_eq_iff hp]
    ring
  · simp only [add.wit, Edwards.Point.add_y]
    rw [div_mul_eq_mul_div, div_eq_iff hm]
    ring

/-! ### Doubling -/

/-- The witnesses of one doubling. -/
structure DoubleW where
  xy : F
  xx : F
  yy : F
  x3 : F
  y3 : F

/-- `CurveVar::double_in_place` for a variable point, with `a = 1`: `xy = x·y`, `xx = x²`,
`yy = y²`, and the witnesses `x₃, y₃` with `x₃·(a·xx + yy) = 2·xy` and
`y₃·(−(a·xx + yy) + 2) = yy − a·xx`. -/
def double_in_place.Rel (p : F × F) (w : DoubleW) : Prop :=
  p.1 * p.2 = w.xy ∧ p.1 * p.1 = w.xx ∧ p.2 * p.2 = w.yy ∧
    w.x3 * (w.xx + w.yy) = 2 * w.xy ∧ w.y3 * (-(w.xx + w.yy) + 2) = w.yy - w.xx

/-- The double, `(x₃, y₃)`. -/
def double_in_place.out (w : DoubleW) : F × F := (w.x3, w.y3)

/-- The witnesses arkworks assigns. -/
def double_in_place.wit (P : Point) : DoubleW where
  xy := P.x * P.y
  xx := P.x * P.x
  yy := P.y * P.y
  x3 := (P + P).x
  y3 := (P + P).y

/-- On the curve `x² + y² = 1 + d·x²y²` and `2 − x² − y² = 1 − d·x²y²`, both nonzero. -/
theorem double_in_place.sound {P : Point} {w : DoubleW}
    (h : double_in_place.Rel (ofPoint P) w) : double_in_place.out w = ofPoint (P + P) := by
  obtain ⟨hxy, hxx, hyy, hx, hy⟩ := h
  simp only [ofPoint] at hxy hxx hyy
  rw [← hxy, ← hxx, ← hyy] at hx
  rw [← hxx, ← hyy] at hy
  simp only [double_in_place.out, ofPoint, Edwards.Point.add_x, Edwards.Point.add_y,
    Prod.mk.injEq]
  constructor
  · rw [eq_div_iff (Edwards.one_add_ne_zero P P)]
    linear_combination hx - w.x3 * P.on_curve
  · rw [eq_div_iff (Edwards.one_sub_ne_zero P P)]
    linear_combination hy + w.y3 * P.on_curve

theorem double_in_place.complete (P : Point) :
    double_in_place.Rel (ofPoint P) (double_in_place.wit P) ∧
      double_in_place.out (double_in_place.wit P) = ofPoint (P + P) := by
  have hp := Edwards.one_add_ne_zero P P
  have hm := Edwards.one_sub_ne_zero P P
  refine ⟨⟨rfl, rfl, rfl, ?_, ?_⟩, rfl⟩
  · simp only [double_in_place.wit, Edwards.Point.add_x]
    rw [div_mul_eq_mul_div, div_eq_iff hp]
    linear_combination (P.x * P.y + P.y * P.x) * P.on_curve
  · simp only [double_in_place.wit, Edwards.Point.add_y]
    rw [div_mul_eq_mul_div, div_eq_iff hm]
    linear_combination (-(P.y * P.y - P.x * P.x)) * P.on_curve

/-! ### Selection, equality, `is_zero` -/

/-- `CondSelectGadget::conditionally_select` for `AffineVar`: per coordinate, `FpVar`'s
`c·(t − f) = r − f`. -/
def conditionally_select.Rel (c : F) (t f r : F × F) : Prop :=
  c * (t.1 - f.1) = r.1 - f.1 ∧ c * (t.2 - f.2) = r.2 - f.2

theorem conditionally_select.sound {b : Bool} {t f r : F × F}
    (h : conditionally_select.Rel (b.toNat : F) t f r) : r = if b then t else f := by
  obtain ⟨h1, h2⟩ := h
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one,
    if_false, if_true, Bool.false_eq_true] at h1 h2 ⊢ <;>
    exact Prod.ext (by linear_combination -h1) (by linear_combination -h2)

theorem conditionally_select.complete (b : Bool) (t f : F × F) :
    conditionally_select.Rel (b.toNat : F) t f (if b then t else f) := by
  cases b <;> simp [conditionally_select.Rel]

/-- `EqGadget::enforce_equal` for `AffineVar`: `(x₁ − x₂)·1 = 0` and `(y₁ − y₂)·1 = 0`. -/
def enforce_equal.Rel (p q : F × F) : Prop := (p.1 - q.1) * 1 = 0 ∧ (p.2 - q.2) * 1 = 0

theorem enforce_equal.sound {p q : F × F} (h : enforce_equal.Rel p q) : p = q :=
  Prod.ext (by linear_combination h.1) (by linear_combination h.2)

theorem enforce_equal.complete (p : F × F) : enforce_equal.Rel p p := by
  simp [enforce_equal.Rel]

/-- The witnesses of `is_zero`. -/
structure IsZeroW where
  ne_x : F
  m_x : F
  ne_y : F
  m_y : F
  out : F

/-- `CurveVar::is_zero` for `AffineVar`, `x.is_zero() & y.is_one()`. `FpVar::is_eq` against the
constant `c` allocates `ne, m` with `(c − v)·m = ne` and `(c − v)·(1 − ne) = 0` and returns
`1 − ne`; `&` allocates `out` with `(1 − ne_x)·(1 − ne_y) = out`. -/
def is_zero.Rel (p : F × F) (w : IsZeroW) : Prop :=
  (0 - p.1) * w.m_x = w.ne_x ∧ (0 - p.1) * (1 - w.ne_x) = 0 ∧
    (1 - p.2) * w.m_y = w.ne_y ∧ (1 - p.2) * (1 - w.ne_y) = 0 ∧
    (1 - w.ne_x) * (1 - w.ne_y) = w.out

/-- The witnesses arkworks assigns: whether `c ≠ v`, and `(c − v)⁻¹` or `1`. -/
def is_zero.wit (p : F × F) : IsZeroW where
  ne_x := if p.1 = 0 then 0 else 1
  m_x := if p.1 = 0 then 1 else (0 - p.1)⁻¹
  ne_y := if p.2 = 1 then 0 else 1
  m_y := if p.2 = 1 then 1 else (1 - p.2)⁻¹
  out := if p = zero then 1 else 0

/-- `is_eq`'s two constraints force `ne` to `0` when `c = v` and to `1` otherwise. -/
private theorem ne_of_rel {c v m ne : F} (h1 : (c - v) * m = ne) (h2 : (c - v) * (1 - ne) = 0) :
    ne = if v = c then 0 else 1 := by
  split_ifs with hv
  · rw [← h1, hv, sub_self, zero_mul]
  · have := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hv))
    linear_combination -this

theorem is_zero.sound {p : F × F} {w : IsZeroW} (h : is_zero.Rel p w) :
    w.out = if p = zero then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [← h5, ne_of_rel h1 h2, ne_of_rel h3 h4]
  by_cases hx : p.1 = 0 <;> by_cases hy : p.2 = 1 <;> simp [zero, Prod.ext_iff, hx, hy]

theorem is_zero.complete (p : F × F) : is_zero.Rel p (is_zero.wit p) := by
  obtain ⟨x, y⟩ := p
  simp only [is_zero.Rel, is_zero.wit, zero, Prod.mk.injEq]
  by_cases hx : x = 0 <;> by_cases hy : y = 1
  · simp [hx, hy]
  · have : (1 : F) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    simp [hx, hy, this]
  · simp [hx, hy]
  · have : (1 : F) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    simp [hx, hy, this]

/-! ### Allocation -/

/-- `AffineVar::new_variable_omit_prime_order_check` for a witness `(x, y)`: `xx = x²`, `yy = y²`
and `(d·xx − 1)·yy = a·xx − 1`, the curve equation. -/
def new_variable_omit_prime_order_check.Rel (p : F × F) (sq : F × F) : Prop :=
  p.1 * p.1 = sq.1 ∧ p.2 * p.2 = sq.2 ∧ (sq.1 * d - 1) * sq.2 = sq.1 - 1

theorem new_variable_omit_prime_order_check.sound {p sq : F × F}
    (h : new_variable_omit_prime_order_check.Rel p sq) : ∃ P : Point, p = ofPoint P := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [← h1, ← h2] at h3
  exact ⟨⟨p.1, p.2, by linear_combination -h3⟩, rfl⟩

theorem new_variable_omit_prime_order_check.complete (P : Point) :
    new_variable_omit_prime_order_check.Rel (ofPoint P) (P.x * P.x, P.y * P.y) :=
  ⟨rfl, rfl, by linear_combination -P.on_curve⟩

/-- The witnesses of `new_witness`. -/
structure NewWitnessW where
  /-- The allocated point `w`. -/
  g : F × F
  /-- `(x², y²)` of `w`. -/
  sq : F × F
  dbl1 : DoubleW
  dbl2 : DoubleW
  dbl3 : DoubleW
  sum : AddW

/-- `AllocVar::new_variable` for `AffineVar` in `AllocationMode::Witness`. The cofactor `8 = 2³`
has Hamming weight `1`, below that of the scalar field's `r − 1`, so arkworks allocates `w` with
the curve check, doubles it three times, and returns `0 + 8w` (its loop over the bits of the odd
part `1` doubles the constant `0`, which emits nothing, then adds). -/
def new_witness.Rel (w : NewWitnessW) : Prop :=
  new_variable_omit_prime_order_check.Rel w.g w.sq ∧ double_in_place.Rel w.g w.dbl1 ∧
    double_in_place.Rel (double_in_place.out w.dbl1) w.dbl2 ∧
    double_in_place.Rel (double_in_place.out w.dbl2) w.dbl3 ∧
    add.Rel zero (double_in_place.out w.dbl3) w.sum

/-- The allocated variable, `8w`. -/
def new_witness.out (w : NewWitnessW) : F × F := add.out w.sum

/-- The witnesses arkworks assigns for `8·P`: `w = P` (it takes `P = 8⁻¹·Q` for the `Q` it is
given). -/
def new_witness.wit (P : Point) : NewWitnessW where
  g := ofPoint P
  sq := (P.x * P.x, P.y * P.y)
  dbl1 := double_in_place.wit P
  dbl2 := double_in_place.wit (P + P)
  dbl3 := double_in_place.wit (P + P + (P + P))
  sum := add.wit 0 (P + P + (P + P) + (P + P + (P + P)))

private theorem eight_nsmul (P : Point) : 0 + (P + P + (P + P) + (P + P + (P + P))) = 8 • P := by
  rw [zero_add, show (8 : ℕ) = 2 * (2 * 2) from rfl, mul_nsmul, mul_nsmul, two_nsmul, two_nsmul,
    two_nsmul]

/-- The allocated variable is a multiple of `8` of a curve point. -/
theorem new_witness.sound {w : NewWitnessW} (h : new_witness.Rel w) :
    ∃ P : Point, w.g = ofPoint P ∧ new_witness.out w = ofPoint (8 • P) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  obtain ⟨P, hP⟩ := new_variable_omit_prime_order_check.sound h0
  rw [hP] at h1
  rw [double_in_place.sound h1] at h2
  rw [double_in_place.sound h2] at h3
  rw [double_in_place.sound h3, zero_eq] at h4
  exact ⟨P, hP, by rw [new_witness.out, add.sound h4, eight_nsmul]⟩

theorem new_witness.complete (P : Point) :
    new_witness.Rel (new_witness.wit P) ∧
      new_witness.out (new_witness.wit P) = ofPoint (8 • P) := by
  obtain ⟨h1, e1⟩ := double_in_place.complete P
  obtain ⟨h2, e2⟩ := double_in_place.complete (P + P)
  obtain ⟨h3, e3⟩ := double_in_place.complete (P + P + (P + P))
  obtain ⟨h4, e4⟩ := add.complete 0 (P + P + (P + P) + (P + P + (P + P)))
  refine ⟨⟨new_variable_omit_prime_order_check.complete P, h1, ?_, ?_, ?_⟩, ?_⟩
  · simp only [new_witness.wit, e1]; exact h2
  · simp only [new_witness.wit, e2]; exact h3
  · simp only [new_witness.wit, e3, zero_eq]; exact h4
  · simp only [new_witness.out, new_witness.wit, e4, eight_nsmul]

/-! ### Scalar multiplication -/

/-- The number a little-endian bit list encodes. -/
def natOfBitsLE (bits : List Bool) : ℕ := Nat.ofDigits 2 (bits.map Bool.toNat)

theorem natOfBitsLE_cons (b : Bool) (bits : List Bool) :
    natOfBitsLE (b :: bits) = b.toNat + 2 * natOfBitsLE bits := by
  simp [natOfBitsLE, Nat.ofDigits_cons]

/-- The field values of bits. -/
def bitVals (bits : List Bool) : List F := bits.map fun b => (b.toNat : F)

/-- The witnesses of one step of `scalar_mul_le`. -/
structure ScalarMulW where
  sum : AddW
  sel : F × F
  dbl : DoubleW

/-- `CurveVar::scalar_mul_le`, little-endian double-and-add from `res = zero` and
`multiple = self`: per bit, `tmp = res + multiple`, `res = bit.select(tmp, res)`, and
`multiple.double_in_place()`. -/
def scalar_mul_le.Rel : F × F → F × F → List F → List ScalarMulW → Prop
  | _, _, [], [] => True
  | res, m, b :: bs, w :: ws =>
    add.Rel res m w.sum ∧ conditionally_select.Rel b (add.out w.sum) res w.sel ∧
      double_in_place.Rel m w.dbl ∧ scalar_mul_le.Rel w.sel (double_in_place.out w.dbl) bs ws
  | _, _, _, _ => False

/-- The final `res`. -/
def scalar_mul_le.out : F × F → List ScalarMulW → F × F
  | res, [] => res
  | _, w :: ws => scalar_mul_le.out w.sel ws

/-- The witnesses arkworks assigns, from `res = A` and `multiple = P`. -/
def scalar_mul_le.wit : Point → Point → List Bool → List ScalarMulW
  | _, _, [] => []
  | A, P, b :: bs =>
    { sum := add.wit A P, sel := ofPoint (if b then A + P else A), dbl := double_in_place.wit P } ::
      scalar_mul_le.wit (if b then A + P else A) (P + P) bs

theorem scalar_mul_le.sound_from (A P : Point) (bits : List Bool) (ws : List ScalarMulW)
    (h : scalar_mul_le.Rel (ofPoint A) (ofPoint P) (bitVals bits) ws) :
    scalar_mul_le.out (ofPoint A) ws = ofPoint (A + natOfBitsLE bits • P) := by
  induction bits generalizing A P ws with
  | nil =>
    cases ws with
    | nil => simp [scalar_mul_le.out, natOfBitsLE]
    | cons _ _ => simp [scalar_mul_le.Rel, bitVals] at h
  | cons b bs ih =>
    cases ws with
    | nil => simp [scalar_mul_le.Rel, bitVals] at h
    | cons w ws =>
      obtain ⟨hadd, hsel, hdbl, hrest⟩ := h
      rw [add.sound hadd] at hsel
      have hsel' := conditionally_select.sound hsel
      have hA : w.sel = ofPoint (if b then A + P else A) := by rw [hsel']; cases b <;> rfl
      rw [hA, double_in_place.sound hdbl] at hrest
      rw [scalar_mul_le.out, hA, ih _ _ _ hrest, natOfBitsLE_cons, ← two_nsmul, ← mul_nsmul,
        add_nsmul]
      cases b <;> simp [add_assoc]

/-- `scalar_mul_le` from the constant `zero` multiplies by the number its bits encode. -/
theorem scalar_mul_le.sound {P : Point} {bits : List Bool} {ws : List ScalarMulW}
    (h : scalar_mul_le.Rel zero (ofPoint P) (bitVals bits) ws) :
    scalar_mul_le.out zero ws = ofPoint (natOfBitsLE bits • P) := by
  rw [zero_eq] at h ⊢
  rw [scalar_mul_le.sound_from 0 P bits ws h, zero_add]

theorem scalar_mul_le.complete_from (A P : Point) (bits : List Bool) :
    scalar_mul_le.Rel (ofPoint A) (ofPoint P) (bitVals bits) (scalar_mul_le.wit A P bits) := by
  induction bits generalizing A P with
  | nil => trivial
  | cons b bs ih =>
    obtain ⟨h1, e1⟩ := add.complete A P
    obtain ⟨h2, e2⟩ := double_in_place.complete P
    refine ⟨h1, ?_, h2, ?_⟩
    · rw [e1]
      have := conditionally_select.complete b (ofPoint (A + P)) (ofPoint A)
      cases b <;> exact this
    · rw [e2]
      exact ih _ _

theorem scalar_mul_le.complete (P : Point) (bits : List Bool) :
    scalar_mul_le.Rel zero (ofPoint P) (bitVals bits) (scalar_mul_le.wit 0 P bits) :=
  scalar_mul_le.complete_from 0 P bits

/-! ### Scalar multiplication by a precomputed base -/

/-- The witnesses of one chunk of `precomputed_base_scalar_mul_le`: the looked-up point and the
addition for a pair of bits; the addition and the selection for a last single bit. -/
structure ChunkW where
  x : F
  y : F
  sum : AddW
  sel : F × F

/-- The table of a pair of bases: `0`, `g₀`, `g₁`, `g₀ + g₁`, the last added natively. -/
def table (g0 g1 : Point) : Fin 4 → Point := ![0, g0, g1, g0 + g1]

/-- `AffineVar::precomputed_base_scalar_mul_le`, the twisted Edwards override. The bits pair up
with the bases; per pair of pairs, each coordinate of the table entry at `b₀ + 2·b₁` is looked up
by `two_bit_lookup` and added to `self`; a last single pair adds its base and selects by its bit,
as `CurveVar`'s default does. -/
def precomputed_base_scalar_mul_le.Rel : F × F → List (F × Point) → List ChunkW → Prop
  | _, [], [] => True
  | acc, [(b, g)], [w] =>
    add.Rel acc (ofPoint g) w.sum ∧ conditionally_select.Rel b (add.out w.sum) acc w.sel
  | acc, (b0, g0) :: (b1, g1) :: rest, w :: ws =>
    FpVar.two_bit_lookup.Rel (b0, b1) (fun i => (table g0 g1 i).x) w.x ∧
      FpVar.two_bit_lookup.Rel (b0, b1) (fun i => (table g0 g1 i).y) w.y ∧
      add.Rel acc (w.x, w.y) w.sum ∧ precomputed_base_scalar_mul_le.Rel (add.out w.sum) rest ws
  | _, _, _ => False

/-- The final `self`. -/
def precomputed_base_scalar_mul_le.out : F × F → List (F × Point) → List ChunkW → F × F
  | _, [_], [w] => w.sel
  | _, _ :: _ :: rest, w :: ws => precomputed_base_scalar_mul_le.out (add.out w.sum) rest ws
  | acc, _, _ => acc

/-- The witnesses arkworks assigns, from `self = A`. -/
def precomputed_base_scalar_mul_le.wit : Point → List (Bool × Point) → List ChunkW
  | _, [] => []
  | A, [(b, g)] => [{ x := 0, y := 0, sum := add.wit A g, sel := ofPoint (if b then A + g else A) }]
  | A, (b0, g0) :: (b1, g1) :: rest =>
    { x := (b0.toNat • g0 + b1.toNat • g1).x, y := (b0.toNat • g0 + b1.toNat • g1).y,
      sum := add.wit A (b0.toNat • g0 + b1.toNat • g1), sel := (0, 0) } ::
      precomputed_base_scalar_mul_le.wit (A + (b0.toNat • g0 + b1.toNat • g1)) rest

/-- The field values of bit-base pairs. -/
def pairVals (ps : List (Bool × Point)) : List (F × Point) :=
  ps.map fun p => ((p.1.toNat : F), p.2)

theorem pairVals_nil : pairVals [] = [] := rfl

theorem pairVals_cons (p : Bool × Point) (ps : List (Bool × Point)) :
    pairVals (p :: ps) = ((p.1.toNat : F), p.2) :: pairVals ps := rfl

/-- `Σ bᵢ·gᵢ`. -/
def pairSum (ps : List (Bool × Point)) : Point := (ps.map fun p => p.1.toNat • p.2).sum

/-- The table entry a pair of bits selects. -/
theorem table_spec (b0 b1 : Bool) (g0 g1 : Point) (f : Point → F) :
    FpVar.two_bit_lookup.spec b0 b1 (fun i => f (table g0 g1 i)) =
      f (b0.toNat • g0 + b1.toNat • g1) := by
  cases b0 <;> cases b1 <;> simp [FpVar.two_bit_lookup.spec, table]

theorem precomputed_base_scalar_mul_le.sound_from :
    ∀ (A : Point) (ps : List (Bool × Point)) (ws : List ChunkW),
      precomputed_base_scalar_mul_le.Rel (ofPoint A) (pairVals ps) ws →
        precomputed_base_scalar_mul_le.out (ofPoint A) (pairVals ps) ws =
          ofPoint (A + pairSum ps)
  | A, [], [], _ => by
    simp only [pairVals_nil, pairSum, List.map_nil, List.sum_nil, add_zero]
    rfl
  | A, [(b, g)], [w], h => by
    obtain ⟨hadd, hsel⟩ := h
    rw [add.sound hadd] at hsel
    simp only [pairVals_cons, pairVals_nil, precomputed_base_scalar_mul_le.out,
      conditionally_select.sound hsel, pairSum, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    cases b <;> simp
  | A, (b0, g0) :: (b1, g1) :: rest, w :: ws, h => by
    obtain ⟨hx, hy, hadd, hrest⟩ := h
    rw [FpVar.two_bit_lookup.sound hx, FpVar.two_bit_lookup.sound hy,
      table_spec b0 b1 g0 g1 Edwards.Point.x, table_spec b0 b1 g0 g1 Edwards.Point.y] at hadd
    have hsum := add.sound (P := A) (Q := b0.toNat • g0 + b1.toNat • g1) hadd
    rw [hsum] at hrest
    simp only [pairVals_cons, precomputed_base_scalar_mul_le.out, hsum]
    rw [precomputed_base_scalar_mul_le.sound_from _ rest ws hrest]
    simp [pairSum, add_assoc]
  | A, [], _ :: _, h => h.elim
  | A, [_], [], h => h.elim
  | A, [_], _ :: _ :: _, h => h.elim
  | A, _ :: _ :: _, [], h => h.elim

theorem precomputed_base_scalar_mul_le.complete_from :
    ∀ (A : Point) (ps : List (Bool × Point)),
      precomputed_base_scalar_mul_le.Rel (ofPoint A) (pairVals ps)
        (precomputed_base_scalar_mul_le.wit A ps)
  | A, [] => trivial
  | A, [(b, g)] => by
    obtain ⟨h1, e1⟩ := add.complete A g
    refine ⟨h1, ?_⟩
    rw [e1]
    have := conditionally_select.complete b (ofPoint (A + g)) (ofPoint A)
    cases b <;> exact this
  | A, (b0, g0) :: (b1, g1) :: rest => by
    obtain ⟨h1, e1⟩ := add.complete A (b0.toNat • g0 + b1.toNat • g1)
    refine ⟨?_, ?_, h1, ?_⟩
    · have := FpVar.two_bit_lookup.complete b0 b1 (fun i => (table g0 g1 i).x)
      rwa [table_spec] at this
    · have := FpVar.two_bit_lookup.complete b0 b1 (fun i => (table g0 g1 i).y)
      rwa [table_spec] at this
    · rw [e1]
      exact precomputed_base_scalar_mul_le.complete_from _ rest

/-- With bases `gᵢ = 2ⁱ·G`, `Σ bᵢ·gᵢ` is the number the bits encode times `G`. -/
theorem pairSum_powers (bits : List Bool) :
    ∀ (G : Point) (gs : List Point), gs.length = bits.length →
      (∀ i (hi : i < gs.length), gs[i] = 2 ^ i • G) →
        pairSum (bits.zip gs) = natOfBitsLE bits • G := by
  induction bits with
  | nil => intro G gs _ _; simp [pairSum, natOfBitsLE]
  | cons b bs ih =>
    intro G gs hlen hgs
    cases gs with
    | nil => simp at hlen
    | cons g gs =>
      have hg : g = G := by simpa using hgs 0 (by simp)
      have ih' := ih (2 • G) gs (by simpa using hlen) fun i hi => by
        have := hgs (i + 1) (by simpa using hi)
        rwa [List.getElem_cons_succ, pow_succ, mul_nsmul'] at this
      simp only [List.zip_cons_cons, pairSum, List.map_cons, List.sum_cons] at ih' ⊢
      rw [ih', hg, natOfBitsLE_cons, add_nsmul, mul_nsmul]

/-- `precomputed_base_scalar_mul_le` from the constant `zero`, over bases `gᵢ = 2ⁱ·G` paired with
the bits, multiplies `G` by the number the bits encode. -/
theorem precomputed_base_scalar_mul_le.sound {G : Point} {bits : List Bool} {gs : List Point}
    (hlen : gs.length = bits.length) (hgs : ∀ i (hi : i < gs.length), gs[i] = 2 ^ i • G)
    {ws : List ChunkW} (h : precomputed_base_scalar_mul_le.Rel zero (pairVals (bits.zip gs)) ws) :
    precomputed_base_scalar_mul_le.out zero (pairVals (bits.zip gs)) ws =
      ofPoint (natOfBitsLE bits • G) := by
  rw [zero_eq] at h ⊢
  rw [precomputed_base_scalar_mul_le.sound_from 0 _ ws h, zero_add,
    pairSum_powers bits G gs hlen hgs]

theorem precomputed_base_scalar_mul_le.complete (ps : List (Bool × Point)) :
    precomputed_base_scalar_mul_le.Rel zero (pairVals ps)
      (precomputed_base_scalar_mul_le.wit 0 ps) :=
  precomputed_base_scalar_mul_le.complete_from 0 ps

end AffineVar

end Zerc20.Ark
