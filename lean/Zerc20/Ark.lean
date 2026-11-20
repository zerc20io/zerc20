import Zerc20.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Fin

/-!
# arkworks R1CS gadgets

Models of the `ark-r1cs-std` 0.6.0 gadgets that zERC20's step circuits use. A gadget's model
computes what the gadget returns from its inputs and the witnesses it allocates, and its `Rel` is
the conjunction of the constraints it emits. Every linear combination arkworks builds is tracked by
its value, so a constraint `A · B = C` becomes an equation between the values of `A`, `B` and `C`.

arkworks folds constants: an operation on constants returns a constant and emits nothing, and an
operation between a constant and a variable often reduces to the variable or its negation. The
models keep the `Constant`/`Var` split of `Boolean` and `FpVar`, so the same folding happens here
and the same constraints remain.
-/

namespace Zerc20.Ark

/-! ## Bits and numbers -/

/-- A bit as a field element. -/
def bit (b : Bool) : F := if b then 1 else 0

theorem bit_eq (b : Bool) : bit b = (b.toNat : F) := by cases b <;> simp [bit]

theorem bit_inj {a b : Bool} (h : bit a = bit b) : a = b := by
  cases a <;> cases b <;> simp_all [bit]

/-- The number whose little-endian binary digits are `b`. -/
def natOfBits {n : ℕ} (b : Fin n → Bool) : ℕ := ∑ i, (b i).toNat * 2 ^ (i : ℕ)

theorem natOfBits_succ {n : ℕ} (b : Fin (n + 1) → Bool) :
    natOfBits b = 2 ^ n * (b (Fin.last n)).toNat + natOfBits (fun i => b i.castSucc) := by
  simp [natOfBits, Fin.sum_univ_castSucc]; ring

theorem natOfBits_lt {n : ℕ} (b : Fin n → Bool) : natOfBits b < 2 ^ n := by
  induction n with
  | zero => simp [natOfBits]
  | succ n ih =>
    rw [natOfBits_succ, pow_succ]
    have := ih (fun i => b i.castSucc)
    have : (b (Fin.last n)).toNat ≤ 1 := Bool.toNat_le _
    nlinarith

theorem testBit_natOfBits {n : ℕ} (b : Fin n → Bool) (i : ℕ) :
    (natOfBits b).testBit i = if h : i < n then b ⟨i, h⟩ else false := by
  induction n generalizing i with
  | zero => simp [natOfBits]
  | succ n ih =>
    rw [natOfBits_succ, Nat.testBit_two_pow_mul_add _ (natOfBits_lt _), ih]
    by_cases hi : i < n
    · simp [hi, Nat.lt_succ_of_lt hi]
    · by_cases hin : i = n
      · subst hin
        simp only [Fin.last, hi, lt_add_one, dite_true, dite_false, Nat.sub_self, Nat.testBit_zero]
        cases b ⟨i, Nat.lt_add_one i⟩ <;> rfl
      · have : ¬ i < n + 1 := by omega
        simp [hi, this, Nat.testBit_bool_toNat]; omega

theorem natOfBits_testBit {n : ℕ} (x : ℕ) :
    natOfBits (fun i : Fin n => x.testBit i) = x % 2 ^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_natOfBits, Nat.testBit_mod_two_pow]
  by_cases h : i < n <;> simp [h]

theorem sum_bit {n : ℕ} (b : Fin n → Bool) :
    ∑ i : Fin n, bit (b i) * 2 ^ (i : ℕ) = (natOfBits b : F) := by
  simp [natOfBits, bit_eq]

theorem two_pow_253_lt_r : 2 ^ 253 < r := by unfold r; norm_num

theorem natCast_inj {a b : ℕ} (ha : a < r) (hb : b < r) (h : (a : F) = b) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem val_natCast_of_lt {a : ℕ} (ha : a < r) : (a : F).val = a := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]

/-! ## `Boolean` -/

/-- `Boolean<F>`: a constant, or a variable whose linear combination has value `x`. -/
inductive Boolean where
  | const (b : Bool)
  | var (x : F)

namespace Boolean

/-- The value of `Boolean::lc()`. -/
def val : Boolean → F
  | const b => bit b
  | var x => x

def isConst : Boolean → Bool
  | const _ => true
  | var _ => false

/-- `GR1CSVar::value`: the bit a constant holds or an assignment encodes. -/
def value : Boolean → Bool
  | const b => b
  | var x => decide (x = 1)

theorem value_eq {a : Boolean} {b : Bool} (h : a.val = bit b) : a.value = b := by
  cases a with
  | const c => exact bit_inj h
  | var x => simp only [val] at h; subst h; cases b <;> simp [value, bit]

/-- `Boolean::new_witness`, whose value `x` is a fresh witness. -/
def new_witness (x : F) : Boolean := var x

/-- `(1 - a) · a = 0`. -/
def new_witness.Rel (x : F) : Prop := (1 - x) * x = 0

theorem new_witness.sound {x : F} (h : new_witness.Rel x) : x = bit (decide (x = 1)) := by
  unfold new_witness.Rel at h
  rcases mul_eq_zero.mp h with h | h
  · have : x = 1 := by linear_combination -h
    simp [this, bit]
  · simp [h, bit]

theorem new_witness.complete (b : Bool) : new_witness.Rel (bit b) := by
  cases b <;> simp [new_witness.Rel, bit]

/-- `Boolean::not`: a constant flips, a variable becomes the linear combination `1 - a`. -/
def not : Boolean → Boolean
  | const b => const (!b)
  | var x => var (1 - x)

theorem not_val {a : Boolean} {b : Bool} (h : a.val = bit b) : a.not.val = bit (!b) := by
  cases a <;> cases b <;> simp_all [not, val, bit]

/-- `Boolean::xor`; `z` is the result's witness when both sides are variables. -/
def xor : Boolean → Boolean → F → Boolean
  | const false, x, _ => x
  | x, const false, _ => x
  | const true, x, _ => x.not
  | x, const true, _ => x.not
  | var _, var _, z => var z

/-- `(a + a) · b = a + b - c` between two variables. -/
def xor.Rel : Boolean → Boolean → F → Prop
  | var x, var y, z => (2 * x) * y = x + y - z
  | _, _, _ => True

/-- The witness arkworks assigns: `a ⊕ b`, here as a polynomial in the inputs. -/
def xor.wit (a b : Boolean) : F := a.val + b.val - 2 * a.val * b.val

theorem xor.sound {a b : Boolean} {p q : Bool} {z : F} (ha : a.val = bit p) (hb : b.val = bit q)
    (h : xor.Rel a b z) : (xor a b z).val = bit (p ^^ q) := by
  rcases a with (_ | _) | x <;> rcases b with (_ | _) | y <;>
    simp_all [xor, xor.Rel, val, not, bit] <;> cases p <;> cases q <;> simp_all <;>
    linear_combination h

theorem xor.complete (a b : Boolean) : xor.Rel a b (xor.wit a b) := by
  rcases a with (_ | _) | x <;> rcases b with (_ | _) | y <;> simp [xor.Rel, xor.wit, val]

/-- `Boolean::and`; `z` is the result's witness when both sides are variables. -/
def and : Boolean → Boolean → F → Boolean
  | const false, _, _ => const false
  | _, const false, _ => const false
  | const true, x, _ => x
  | x, const true, _ => x
  | var _, var _, z => var z

/-- `a · b = c` between two variables. -/
def and.Rel : Boolean → Boolean → F → Prop
  | var x, var y, z => x * y = z
  | _, _, _ => True

def and.wit (a b : Boolean) : F := a.val * b.val

theorem and.sound {a b : Boolean} {p q : Bool} {z : F} (ha : a.val = bit p) (hb : b.val = bit q)
    (h : and.Rel a b z) : (and a b z).val = bit (p && q) := by
  rcases a with (_ | _) | x <;> rcases b with (_ | _) | y <;> cases p <;> cases q <;>
    simp_all [and, and.Rel, val, bit]

theorem and.complete (a b : Boolean) : and.Rel a b (and.wit a b) := by
  rcases a with (_ | _) | x <;> rcases b with (_ | _) | y <;> trivial

/-- `Boolean::conditional_enforce_equal`. Unequal constants make synthesis fail, which is `False`. -/
def conditional_enforce_equal.Rel (a b cond : Boolean) : Prop :=
  match cond with
  | const false => True
  | _ =>
    match a, b with
    | const x, const y => x = y
    | const true, var x | var x, const true => (1 - x) * cond.val = 0
    | const false, var x | var x, const false => x * cond.val = 0
    | var x, var y => (y - x) * cond.val = 0

/-- `EqGadget::enforce_equal`: `conditional_enforce_equal` under `Boolean::TRUE`. -/
def enforce_equal.Rel (a b : Boolean) : Prop := conditional_enforce_equal.Rel a b (const true)

theorem enforce_equal.sound {a b : Boolean} {p q : Bool} (ha : a.val = bit p) (hb : b.val = bit q)
    (h : enforce_equal.Rel a b) : p = q := by
  rcases a with (_ | _) | x <;> rcases b with (_ | _) | y <;>
    simp_all [enforce_equal.Rel, conditional_enforce_equal.Rel, val, bit] <;>
    cases p <;> cases q <;> simp_all

theorem enforce_equal.complete {a b : Boolean} {p : Bool} (ha : a.val = bit p) (hb : b.val = bit p) :
    enforce_equal.Rel a b := by
  rcases a with (_ | _) | x <;> rcases b with (_ | _) | y <;>
    simp_all [enforce_equal.Rel, conditional_enforce_equal.Rel, val, bit]

end Boolean

/-! ## `FpVar` -/

/-- `FpVar<F>`: a constant, or a variable whose linear combination has value `x`. -/
inductive FpVar where
  | const (c : F)
  | var (x : F)

namespace FpVar

def val : FpVar → F
  | const c => c
  | var x => x

def isConst : FpVar → Bool
  | const _ => true
  | var _ => false

/-- `From<Boolean<F>> for FpVar<F>`: the bit's linear combination. -/
def ofBoolean : Boolean → FpVar
  | .const b => const (bit b)
  | .var x => var x

theorem ofBoolean_val (a : Boolean) : (ofBoolean a).val = a.val := by cases a <;> rfl

/-- `FpVar + FpVar`, a linear combination. -/
def add : FpVar → FpVar → FpVar
  | const a, const b => const (a + b)
  | const c, var v | var v, const c => var (v + c)
  | var x, var y => var (x + y)

/-- `FpVar - FpVar`, a linear combination. -/
def sub : FpVar → FpVar → FpVar
  | const a, const b => const (a - b)
  | var v, const c => var (v - c)
  | const c, var v => var (-(v - c))
  | var x, var y => var (x - y)

theorem add_val (a b : FpVar) : (add a b).val = a.val + b.val := by
  cases a <;> cases b <;> simp [add, val, add_comm]

theorem sub_val (a b : FpVar) : (sub a b).val = a.val - b.val := by
  cases a <;> cases b <;> simp [sub, val]

/-- `FpVar * FpVar`; `z` is the product's witness when both sides are variables. -/
def mul : FpVar → FpVar → F → FpVar
  | const a, const b, _ => const (a * b)
  | const c, var v, _ | var v, const c, _ => var (v * c)
  | var _, var _, z => var z

/-- `a · b = c` between two variables. -/
def mul.Rel : FpVar → FpVar → F → Prop
  | var x, var y, z => x * y = z
  | _, _, _ => True

theorem mul.sound {a b : FpVar} {z : F} (h : mul.Rel a b z) : (mul a b z).val = a.val * b.val := by
  cases a <;> cases b <;> simp_all [mul, mul.Rel, val, mul_comm]

theorem mul.complete (a b : FpVar) : mul.Rel a b (a.val * b.val) := by
  cases a <;> cases b <;> simp [mul.Rel, val]

/-- `Sum for FpVar`: the constants and the variables add up separately, and the result is a
variable unless every term is constant. -/
def sum (l : List FpVar) : FpVar :=
  if l.all isConst then const (l.map val).sum else var (l.map val).sum

theorem sum_val (l : List FpVar) : (sum l).val = (l.map val).sum := by
  unfold sum; split <;> rfl

/-- `AllocatedFp::is_neq`'s constraints on the difference `d`, with witnesses `w = (c, m)`:
`d · m = c` and `d · (1 - c) = 0`. -/
def isNeqRel (d : F) (w : F × F) : Prop := d * w.2 = w.1 ∧ d * (1 - w.1) = 0

/-- The witnesses `AllocatedFp::is_neq` assigns: whether `d ≠ 0`, and `d⁻¹` or `1`. -/
def isNeqWit (d : F) : F × F := if d = 0 then (0, 1) else (1, d⁻¹)

theorem isNeqRel_sound {d : F} {w : F × F} (h : isNeqRel d w) : w.1 = bit (decide (d ≠ 0)) := by
  obtain ⟨h1, h2⟩ := h
  by_cases hd : d = 0
  · simp_all [bit]
  · have : 1 - w.1 = 0 := (mul_eq_zero.mp h2).resolve_left hd
    simp [hd, bit]; linear_combination -this

theorem isNeqRel_complete (d : F) : isNeqRel d (isNeqWit d) := by
  unfold isNeqRel isNeqWit; split <;> simp_all

/-- The difference `AllocatedFp::is_neq` constrains: a constant side is allocated and becomes the
receiver. -/
def is_eq.diff : FpVar → FpVar → F
  | const c, var v | var v, const c => c - v
  | a, b => a.val - b.val

/-- `FpVar::is_eq`: constants compare natively; otherwise `!is_neq`, with `w` as `is_neq`'s
witnesses. -/
def is_eq : FpVar → FpVar → F × F → Boolean
  | const a, const b, _ => .const (decide (a = b))
  | _, _, w => .var (1 - w.1)

def is_eq.Rel : FpVar → FpVar → F × F → Prop
  | const _, const _, _ => True
  | a, b, w => isNeqRel (is_eq.diff a b) w

def is_eq.wit (a b : FpVar) : F × F := isNeqWit (is_eq.diff a b)

theorem is_eq.diff_eq_zero (a b : FpVar) : is_eq.diff a b = 0 ↔ a.val = b.val := by
  cases a <;> cases b <;> simp [is_eq.diff, val, sub_eq_zero, eq_comm]

theorem is_eq.sound {a b : FpVar} {w : F × F} (h : is_eq.Rel a b w) :
    (is_eq a b w).val = bit (decide (a.val = b.val)) := by
  have key : ∀ d, isNeqRel d w → (d = 0 ↔ a.val = b.val) →
      (Boolean.var (1 - w.1)).val = bit (decide (a.val = b.val)) := by
    intro d hd hiff
    rw [Boolean.val, isNeqRel_sound hd]
    by_cases hab : a.val = b.val <;> simp [hiff, hab, bit]
  cases a <;> cases b
  · rfl
  all_goals exact key _ h (is_eq.diff_eq_zero _ _)

theorem is_eq.complete (a b : FpVar) : is_eq.Rel a b (is_eq.wit a b) := by
  cases a <;> cases b <;> first | trivial | exact isNeqRel_complete _

/-- `EqGadget::is_neq`: `!is_eq`. -/
def is_neq (a b : FpVar) (w : F × F) : Boolean := (is_eq a b w).not

/-- `FieldVar::is_zero`: `is_eq` against the constant zero. -/
def is_zero (a : FpVar) (w : F × F) : Boolean := is_eq a (const 0) w

theorem is_neq.sound {a b : FpVar} {w : F × F} (h : is_eq.Rel a b w) :
    (is_neq a b w).val = bit (decide (a.val ≠ b.val)) := by
  rw [is_neq, Boolean.not_val (is_eq.sound h), decide_not]

theorem is_zero.sound {a : FpVar} {w : F × F} (h : is_eq.Rel a (const 0) w) :
    (is_zero a w).val = bit (decide (a.val = 0)) :=
  is_eq.sound h

/-- `FpVar::conditional_enforce_equal`: `(a - b) · cond = 0`, nothing between two constants. -/
def conditional_enforce_equal.Rel (a b : FpVar) (cond : Boolean) : Prop :=
  match a, b with
  | const _, const _ => True
  | const c, var v | var v, const c => (c - v) * cond.val = 0
  | var x, var y => (x - y) * cond.val = 0

/-- `EqGadget::enforce_equal`: `conditional_enforce_equal` under `Boolean::TRUE`. -/
def enforce_equal.Rel (a b : FpVar) : Prop := conditional_enforce_equal.Rel a b (.const true)

theorem conditional_enforce_equal.sound {a b : FpVar} {cond : Boolean}
    (h : conditional_enforce_equal.Rel a b cond) (hc : cond.val = 1)
    (hv : (a.isConst && b.isConst) = false) : a.val = b.val := by
  cases a <;> cases b <;>
    simp only [conditional_enforce_equal.Rel, isConst, val, hc, mul_one, sub_eq_zero] at h hv ⊢ <;>
    first | exact h | exact h.symm | simp at hv

theorem conditional_enforce_equal.complete {a b : FpVar} {cond : Boolean}
    (h : cond.val = 0 ∨ a.val = b.val) : conditional_enforce_equal.Rel a b cond := by
  cases a <;> cases b <;> rcases h with h | h <;> simp_all [conditional_enforce_equal.Rel, val]

theorem enforce_equal.sound {a b : FpVar} (h : enforce_equal.Rel a b)
    (hv : (a.isConst && b.isConst) = false) : a.val = b.val :=
  conditional_enforce_equal.sound h (by simp [Boolean.val, bit]) hv

theorem enforce_equal.complete {a b : FpVar} (h : a.val = b.val) : enforce_equal.Rel a b :=
  conditional_enforce_equal.complete (.inr h)

/-- `FpVar::conditional_enforce_not_equal`: `(a - b) · m = cond`, nothing between two constants. -/
def conditional_enforce_not_equal.Rel (a b : FpVar) (cond : Boolean) (m : F) : Prop :=
  match a, b with
  | const _, const _ => True
  | const c, var v | var v, const c => (c - v) * m = cond.val
  | var x, var y => (x - y) * m = cond.val

/-- The witness arkworks assigns: `(a - b)⁻¹` when enforcing, else `0`. -/
def conditional_enforce_not_equal.wit (a b : FpVar) (cond : Boolean) : F :=
  cond.val * (is_eq.diff a b)⁻¹

theorem conditional_enforce_not_equal.sound {a b : FpVar} {cond : Boolean} {m : F}
    (h : conditional_enforce_not_equal.Rel a b cond m) (hc : cond.val = 1)
    (hv : (a.isConst && b.isConst) = false) : a.val ≠ b.val := by
  intro hab
  cases a <;> cases b <;> simp only [conditional_enforce_not_equal.Rel, isConst, val] at h hv hab <;>
    first | (rw [hab, sub_self, zero_mul, hc] at h; exact zero_ne_one h) | simp at hv

theorem conditional_enforce_not_equal.complete {a b : FpVar} {cond : Boolean} {p : Bool}
    (hc : cond.val = bit p) (h : p = true → a.val ≠ b.val) :
    conditional_enforce_not_equal.Rel a b cond (conditional_enforce_not_equal.wit a b cond) := by
  cases p <;> simp only [bit] at hc <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc
  · cases a <;> cases b <;>
      simp_all [conditional_enforce_not_equal.Rel, conditional_enforce_not_equal.wit]
  · have hd : is_eq.diff a b ≠ 0 := fun h0 => h rfl ((is_eq.diff_eq_zero a b).mp h0)
    simp only [conditional_enforce_not_equal.wit, hc, one_mul]
    cases a <;> cases b <;> simp_all [conditional_enforce_not_equal.Rel, is_eq.diff, val]

/-- `FpVar::conditionally_select`, which `Boolean::select` calls; `z` is the result's witness. -/
def conditionally_select : Boolean → FpVar → FpVar → F → FpVar
  | .const true, t, _, _ => t
  | .const false, _, f, _ => f
  | .var c, const t, const f, _ => var (c * t + (1 - c) * f)
  | .var _, _, _, z => var z

/-- `cond · (t - f) = r - f`, unless the condition is constant or both branches are. -/
def conditionally_select.Rel : Boolean → FpVar → FpVar → F → Prop
  | .var _, const _, const _, _ => True
  | .var c, t, f, z => c * (t.val - f.val) = z - f.val
  | .const _, _, _, _ => True

def conditionally_select.wit (cond : Boolean) (t f : FpVar) : F := f.val + cond.val * (t.val - f.val)

theorem conditionally_select.sound {cond : Boolean} {p : Bool} {t f : FpVar} {z : F}
    (hc : cond.val = bit p) (h : conditionally_select.Rel cond t f z) :
    (conditionally_select cond t f z).val = if p then t.val else f.val := by
  rcases cond with (_ | _) | c <;> cases p <;> cases t <;> cases f <;>
    simp_all [conditionally_select, conditionally_select.Rel, Boolean.val, val, bit] <;>
    linear_combination -h

theorem conditionally_select.complete (cond : Boolean) (t f : FpVar) :
    conditionally_select.Rel cond t f (conditionally_select.wit cond t f) := by
  rcases cond with (_ | _) | c <;> cases t <;> cases f <;>
    simp [conditionally_select.Rel, conditionally_select.wit, Boolean.val, val]

end FpVar

/-! ## `kary_and` and the comparison with a constant -/

namespace Boolean

/-- `Boolean::kary_and`. Up to three bits chain `&`; more are summed and compared with their count
by `FpVar::is_eq`. `w` holds the two `&` witnesses, or `is_eq`'s. -/
def kary_and : List Boolean → F × F → Boolean
  | [a], _ => a
  | [a, b], w => a.and b w.1
  | [a, b, c], w => (a.and b w.1).and c w.2
  | bits, w => FpVar.is_eq (FpVar.sum (bits.map FpVar.ofBoolean)) (.const bits.length) w

def kary_and.Rel : List Boolean → F × F → Prop
  | [_], _ => True
  | [a, b], w => and.Rel a b w.1
  | [a, b, c], w => and.Rel a b w.1 ∧ and.Rel (a.and b w.1) c w.2
  | bits, w => FpVar.is_eq.Rel (FpVar.sum (bits.map FpVar.ofBoolean)) (.const bits.length) w

def kary_and.wit : List Boolean → F × F
  | [a, b] => (and.wit a b, 0)
  | [a, b, c] => (and.wit a b, and.wit (a.and b (and.wit a b)) c)
  | bits => FpVar.is_eq.wit (FpVar.sum (bits.map FpVar.ofBoolean)) (.const bits.length)

/-- A list of `Boolean`s carries a list of bits. -/
abbrev Carry (bits : List Boolean) (xs : List Bool) : Prop :=
  List.Forall₂ (fun a x => a.val = bit x) bits xs

theorem toNat_sum_le (xs : List Bool) : (xs.map Bool.toNat).sum ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ihy => have := Bool.toNat_le y; simp; omega

theorem toNat_sum_eq_length {xs : List Bool} :
    (xs.map Bool.toNat).sum = xs.length ↔ xs.all id = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have := toNat_sum_le xs
    cases x
    · simp; omega
    · simp only [List.map_cons, Bool.toNat_true, List.sum_cons, List.length_cons, List.all_cons,
        id, Bool.true_and]
      rw [← ih]; omega

theorem kary_and_sum {bits : List Boolean} {xs : List Bool} {w : F × F} (hb : Carry bits xs)
    (hlen : bits.length < r)
    (h : FpVar.is_eq.Rel (FpVar.sum (bits.map FpVar.ofBoolean)) (.const bits.length) w) :
    (FpVar.is_eq (FpVar.sum (bits.map FpVar.ofBoolean)) (.const bits.length) w).val =
      bit (xs.all id) := by
  rw [FpVar.is_eq.sound h, FpVar.sum_val]
  have hv : ((bits.map FpVar.ofBoolean).map FpVar.val).sum = ((xs.map Bool.toNat).sum : F) := by
    simp only [List.map_map, Nat.cast_list_sum, Function.comp_def, FpVar.ofBoolean_val]
    clear hlen h; induction hb with
    | nil => rfl
    | cons hax _ ih => simp [hax, ih, bit_eq]
  have hle := toNat_sum_le xs
  have hl := hb.length_eq
  rw [hv, FpVar.val]
  congr 1
  by_cases ha : xs.all id = true
  · rw [ha, toNat_sum_eq_length.mpr ha, hl]; simp
  · rw [Bool.not_eq_true] at ha
    rw [ha, decide_eq_false_iff_not]
    intro h'
    have := toNat_sum_eq_length.mp (natCast_inj (by omega) (by omega) (h'.trans (by rw [hl])))
    simp [ha] at this

theorem kary_and.sound {bits : List Boolean} {xs : List Bool} {w : F × F} (hb : Carry bits xs)
    (hlen : bits.length < r) (h : kary_and.Rel bits w) : (kary_and bits w).val = bit (xs.all id) := by
  match bits, xs, hb with
  | [], [], _ => rfl
  | [a], [x], .cons ha .nil => simpa [kary_and] using ha
  | [a, b], [x, y], .cons ha (.cons hb .nil) =>
    simpa [kary_and] using and.sound ha hb h
  | [a, b, c], [x, y, z], .cons ha (.cons hb (.cons hc .nil)) =>
    simpa [kary_and, Bool.and_assoc] using and.sound (and.sound ha hb h.1) hc h.2
  | a :: b :: c :: d :: rest, xs, hb => exact kary_and_sum hb hlen h

theorem kary_and.complete (bits : List Boolean) : kary_and.Rel bits (kary_and.wit bits) := by
  match bits with
  | [] => unfold kary_and.Rel kary_and.wit; exact FpVar.is_eq.complete _ _
  | [_] => trivial
  | [a, b] => exact and.complete a b
  | [a, b, c] => exact ⟨and.complete a b, and.complete _ c⟩
  | _ :: _ :: _ :: _ :: _ => exact FpVar.is_eq.complete _ _

/-- `Boolean::enforce_kary_nand`: `kary_and(bits)` is enforced equal to `false`. -/
def enforce_kary_nand.Rel (bits : List Boolean) (w : F × F) : Prop :=
  kary_and.Rel bits w ∧ enforce_equal.Rel (kary_and bits w) (const false)

/-- The state of `enforce_smaller_or_equal_than_le`'s loop. -/
structure RunState where
  last_run : Boolean
  current_run : List Boolean

/-- The witnesses one position of that loop may allocate: the `kary_and` closing a run of ones, and
the one inside `enforce_kary_nand`. -/
structure CmpWit where
  run : F × F
  nand : F × F

/-- `last_run` once a `0` of the element is reached: a pending run of ones is closed by `kary_and`
over its bits followed by the previous `last_run`. -/
def closeRun (s : RunState) (w : F × F) : Boolean :=
  match s.current_run with
  | [] => s.last_run
  | run => kary_and (run ++ [s.last_run]) w

def closeRun.Rel (s : RunState) (w : F × F) : Prop :=
  match s.current_run with
  | [] => True
  | run => kary_and.Rel (run ++ [s.last_run]) w

/-- One position of the loop, where `b` is the element's bit and `a` the compared bit: a `1` extends
the current run; a `0` closes it and enforces `!(last_run ∧ a)`. -/
def cmpStep (s : RunState) (b : Bool) (a : Boolean) (w : CmpWit) : RunState × Prop :=
  if b then (⟨s.last_run, s.current_run ++ [a]⟩, True)
  else (⟨closeRun s w.run, []⟩,
    closeRun.Rel s w.run ∧ enforce_kary_nand.Rel [closeRun s w.run, a] w.nand)

/-- The loop over the positions, most significant first; the `k`-th position uses the `k`-th
witness. -/
def cmpLoop : List (Bool × Boolean) → List CmpWit → RunState → RunState × Prop
  | [], _, s => (s, True)
  | (b, a) :: ps, ws, s =>
    let step := cmpStep s b a (ws.headD ⟨(0, 0), (0, 0)⟩)
    ((cmpLoop ps ws.tail step.1).1, step.2 ∧ (cmpLoop ps ws.tail step.1).2)

/-- `Boolean::enforce_smaller_or_equal_than_le` for `n` bits against an `element` with exactly `n`
significant bits, so no bit lies above the element's top bit: the loop walks the element's bits
from the top beside the compared ones, starting from `last_run = TRUE`. Returns the final run and
the constraints. -/
def enforce_smaller_or_equal_than_le {n : ℕ} (bits : Fin n → Boolean) (element : ℕ)
    (ws : List CmpWit) : List Boolean × Prop :=
  let loop := cmpLoop ((List.finRange n).reverse.map fun j : Fin n => (element.testBit j, bits j)) ws
    ⟨const true, []⟩
  (loop.1.current_run, loop.2)

/-- `Boolean::enforce_in_field_le` for the 254 bits of a field element: `bits ≤ r - 1`. The final
run it asserts empty is a property of `r - 1`, whose low bit is `0`, and emits nothing. -/
def enforce_in_field_le (bits : Fin 254 → Boolean) (ws : List CmpWit) : Prop :=
  (enforce_smaller_or_equal_than_le bits (r - 1) ws).2

/-! ### Soundness of the comparison -/

/-- The number whose big-endian binary digits are `l`, after the digits of `acc`. -/
def ofBE (acc : ℕ) (l : List Bool) : ℕ := l.foldl (fun a b => 2 * a + b.toNat) acc

theorem ofBE_cons (acc : ℕ) (b : Bool) (l : List Bool) :
    ofBE acc (b :: l) = ofBE (2 * acc + b.toNat) l := rfl

theorem ofBE_append (acc : ℕ) (l₁ l₂ : List Bool) : ofBE acc (l₁ ++ l₂) = ofBE (ofBE acc l₁) l₂ :=
  List.foldl_append

theorem ofBE_eq (acc : ℕ) (l : List Bool) : ofBE acc l = acc * 2 ^ l.length + ofBE 0 l := by
  induction l generalizing acc with
  | nil => simp [ofBE]
  | cons b l ih => rw [ofBE_cons, ofBE_cons, ih, ih (2 * 0 + _)]; simp [pow_succ]; ring

theorem ofBE_lt (l : List Bool) : ofBE 0 l + 1 ≤ 2 ^ l.length := by
  induction l with
  | nil => simp [ofBE]
  | cons b l ih => rw [ofBE_cons, ofBE_eq]; have := Bool.toNat_le b; simp [pow_succ]; nlinarith

theorem ofBE_eq_ones {l : List Bool} : ofBE 0 l + 1 = 2 ^ l.length ↔ l.all id = true := by
  induction l with
  | nil => simp [ofBE]
  | cons b l ih =>
    rw [ofBE_cons, ofBE_eq]; have := ofBE_lt l; have := Nat.one_le_two_pow (n := l.length)
    cases b
    · simp [pow_succ]; omega
    · simp only [Bool.toNat_true, List.all_cons, id, Bool.true_and, List.length_cons, pow_succ]
      rw [← ih]; omega

theorem ofBE_replicate (acc k : ℕ) : ofBE acc (List.replicate k true) + 1 = (acc + 1) * 2 ^ k := by
  rw [ofBE_eq]
  have := (ofBE_eq_ones (l := List.replicate k true)).mpr (by simp)
  simp only [List.length_replicate] at this ⊢; nlinarith

/-- The invariant of the loop: while `last_run` holds, the compared prefix equals the element's;
once it fails, the prefix is below the element's. -/
def CmpInv : Bool → ℕ → ℕ → Prop
  | true, A, C => A = C
  | false, A, C => A < C

theorem CmpInv.le {l : Bool} {A C : ℕ} (h : CmpInv l A C) : A ≤ C := by
  cases l <;> simp only [CmpInv] at h <;> omega

theorem CmpInv.run {l : Bool} {A C : ℕ} (rs : List Bool) (h : CmpInv l A C) :
    CmpInv (rs.all id && l) (ofBE A rs) (ofBE C (List.replicate rs.length true)) := by
  have hC := ofBE_replicate C rs.length
  rw [ofBE_eq A rs]
  have hr := ofBE_lt rs
  have hp : 0 < 2 ^ rs.length := by positivity
  cases l
  · simp only [CmpInv, Bool.and_false] at h ⊢; nlinarith
  · simp only [CmpInv] at h; subst h
    by_cases ha : rs.all id = true
    · have := ofBE_eq_ones.mpr ha; simp only [ha, Bool.and_self, CmpInv]; nlinarith
    · have := mt ofBE_eq_ones.mp ha; simp only [ha, Bool.false_and, CmpInv]
      have : ofBE 0 rs + 1 < 2 ^ rs.length := lt_of_le_of_ne hr this
      nlinarith

theorem CmpInv.bit {l x : Bool} {A C : ℕ} (h : CmpInv l A C) (hx : (l && x) = false) :
    CmpInv l (2 * A + x.toNat) (2 * C + (false).toNat) := by
  cases l <;> cases x <;>
    simp only [CmpInv, Bool.toNat_false, Bool.toNat_true, Bool.and_self, Bool.true_eq_false] at h hx ⊢ <;>
    omega

theorem all_pair (p x : Bool) : [p, x].all id = (p && x) := by cases p <;> cases x <;> rfl

theorem closeRun.sound {s : RunState} {w : F × F} {l : Bool} {rs : List Bool}
    (hl : s.last_run.val = bit l) (hr : Carry s.current_run rs) (hlen : rs.length + 1 < r)
    (h : closeRun.Rel s w) : (closeRun s w).val = bit (rs.all id && l) := by
  unfold closeRun closeRun.Rel at *
  split
  · next he => rw [he] at hr; cases hr; simpa using hl
  · next he =>
    have := kary_and.sound (List.rel_append hr (.cons hl .nil)) (by simp [hr.length_eq]; omega)
      (by simpa [he] using h)
    simpa using this

theorem cmpLoop_sound : ∀ (ps : List (Bool × Boolean)) (ws : List CmpWit) (s : RunState) (l : Bool)
    (rs as : List Bool) (A C : ℕ),
    s.last_run.val = bit l → Carry s.current_run rs →
    List.Forall₂ (fun p x => p.2.val = bit x) ps as → CmpInv l A C →
    rs.length + ps.length < r → (cmpLoop ps ws s).2 →
    ofBE A (rs ++ as) ≤ ofBE C (List.replicate rs.length true ++ ps.map Prod.fst)
  | [], _, s, l, rs, as, A, C, _, _, has, hinv, _, _ => by
    cases has; simpa using (hinv.run rs).le
  | (b, a) :: ps, ws, s, l, rs, as, A, C, hl, hr, has, hinv, hlen, h => by
    obtain ⟨x, as, rfl⟩ : ∃ x as', as = x :: as' := by cases has; exact ⟨_, _, rfl⟩
    obtain ⟨hax, has'⟩ := List.forall₂_cons.mp has
    clear has
    obtain ⟨hstep, hrest⟩ := h
    cases b
    · simp only [cmpStep, Bool.false_eq_true, ↓reduceIte] at hstep hrest
      obtain ⟨hclose, hnand1, hnand2⟩ := hstep
      have hL := closeRun.sound hl hr (by simp at hlen; omega) hclose
      have hand := kary_and.sound (.cons hL (.cons hax .nil)) (by simp; unfold r; omega) hnand1
      rw [all_pair] at hand
      have hx : (rs.all id && l && x) = false := enforce_equal.sound hand rfl hnand2
      have := cmpLoop_sound ps ws.tail _ _ [] as _ _ hL .nil has' ((hinv.run rs).bit hx)
        (by simp at hlen ⊢; omega) hrest
      simpa [ofBE_append, ofBE_cons] using this
    · simp only [cmpStep, ↓reduceIte] at hrest
      have := cmpLoop_sound ps ws.tail ⟨s.last_run, s.current_run ++ [a]⟩ l (rs ++ [x]) as A C hl
        (List.rel_append hr (.cons hax .nil)) has' hinv (by simp at hlen ⊢; omega) hrest
      simpa [List.replicate_succ', List.append_assoc] using this

/-! ### Completeness of the comparison -/

/-- The witnesses arkworks assigns at one position of the loop. -/
def cmpStep.wit (s : RunState) (a : Boolean) : CmpWit :=
  let run := kary_and.wit (s.current_run ++ [s.last_run])
  ⟨run, kary_and.wit [closeRun s run, a]⟩

/-- The witnesses arkworks assigns along the loop. -/
def cmpHonest : List (Bool × Boolean) → RunState → List CmpWit
  | [], _ => []
  | (b, a) :: ps, s => cmpStep.wit s a :: cmpHonest ps (cmpStep s b a (cmpStep.wit s a)).1

theorem closeRun.complete (s : RunState) :
    closeRun.Rel s (kary_and.wit (s.current_run ++ [s.last_run])) := by
  unfold closeRun.Rel; split
  · trivial
  · exact kary_and.complete _

theorem cmpLoop_complete : ∀ (ps : List (Bool × Boolean)) (s : RunState) (l : Bool)
    (rs as : List Bool) (A C : ℕ),
    s.last_run.val = bit l → Carry s.current_run rs →
    List.Forall₂ (fun p x => p.2.val = bit x) ps as → CmpInv l A C →
    rs.length + ps.length < r →
    ofBE A (rs ++ as) ≤ ofBE C (List.replicate rs.length true ++ ps.map Prod.fst) →
    (cmpLoop ps (cmpHonest ps s) s).2
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | (b, a) :: ps, s, l, rs, as, A, C, hl, hr, has, hinv, hlen, hle => by
    obtain ⟨x, as, rfl⟩ : ∃ x as', as = x :: as' := by cases has; exact ⟨_, _, rfl⟩
    obtain ⟨hax, has'⟩ := List.forall₂_cons.mp has
    clear has
    simp only [cmpLoop, cmpHonest, List.headD_cons, List.tail_cons]
    cases b
    · simp only [cmpStep, Bool.false_eq_true, ↓reduceIte]
      have hclose := closeRun.complete s
      have hL := closeRun.sound hl hr (by simp at hlen; omega) hclose
      have hand := kary_and.sound (.cons hL (.cons hax .nil)) (by simp; unfold r; omega)
        (kary_and.complete _)
      rw [all_pair] at hand
      have hinv1 := hinv.run rs
      have hm := has'.length_eq
      have hx : (rs.all id && l && x) = false := by
        by_contra hcon
        have hp : (rs.all id && l) = true := by revert hcon; cases (rs.all id && l) <;> simp
        have hxt : x = true := by revert hcon; cases x <;> simp
        rw [hp] at hinv1
        simp only [CmpInv] at hinv1
        subst hxt
        simp only [List.map_cons, ofBE_append, ofBE_cons, Bool.toNat_true, Bool.toNat_false] at hle
        rw [ofBE_eq _ as, ofBE_eq _ (List.map Prod.fst ps), hinv1] at hle
        have := ofBE_lt (ps.map Prod.fst)
        simp only [List.length_map] at hle this
        rw [hm] at hle this
        nlinarith
      have hand' : (kary_and [closeRun s (cmpStep.wit s a).run, a] (cmpStep.wit s a).nand).val =
          bit false := by rw [← hx]; exact hand
      refine ⟨⟨hclose, kary_and.complete _, enforce_equal.complete hand' rfl⟩, ?_⟩
      apply cmpLoop_complete ps _ _ [] as _ _ hL .nil has' (hinv1.bit hx) (by simp at hlen ⊢; omega)
      simpa [ofBE_append, ofBE_cons] using hle
    · simp only [cmpStep, ↓reduceIte]
      refine ⟨trivial, ?_⟩
      apply cmpLoop_complete ps ⟨s.last_run, s.current_run ++ [a]⟩ l (rs ++ [x]) as A C hl
        (List.rel_append hr (.cons hax .nil)) has' hinv (by simp at hlen ⊢; omega)
      simpa [List.replicate_succ', List.append_assoc] using hle

theorem ofBE_finRange {n : ℕ} (f : Fin n → Bool) :
    ofBE 0 ((List.finRange n).reverse.map f) = natOfBits f := by
  induction n with
  | zero => simp [ofBE, natOfBits]
  | succ n ih =>
    rw [List.finRange_succ_last, List.reverse_append, List.map_append, ← List.map_reverse]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append, List.map_map]
    rw [ofBE_cons, ofBE_eq, natOfBits_succ, ← ih]
    simp [Function.comp_def]; ring

theorem forall₂_map {α γ δ : Type} {R : γ → δ → Prop} (l : List α) {f : α → γ} {g : α → δ}
    (h : ∀ a, R (f a) (g a)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (h a) ih

/-- The positions `enforce_in_field_le` walks, most significant first. -/
def inFieldPositions (bits : Fin 254 → Boolean) : List (Bool × Boolean) :=
  (List.finRange 254).reverse.map fun j : Fin 254 => ((r - 1).testBit j, bits j)

theorem natOfBits_r_sub_one : natOfBits (fun j : Fin 254 => (r - 1).testBit j) = r - 1 := by
  rw [natOfBits_testBit, Nat.mod_eq_of_lt]; unfold r; norm_num

theorem inFieldPositions_length (bits : Fin 254 → Boolean) :
    ([] : List Bool).length + (inFieldPositions bits).length < r := by
  simp only [inFieldPositions, List.length_map, List.length_reverse, List.length_finRange,
    List.length_nil]
  unfold r; norm_num

theorem inFieldPositions_fst (bits : Fin 254 → Boolean) :
    (inFieldPositions bits).map Prod.fst =
      (List.finRange 254).reverse.map fun j : Fin 254 => (r - 1).testBit j := by
  simp only [inFieldPositions, List.map_map]; rfl

theorem enforce_in_field_le.sound {bits : Fin 254 → Boolean} {xs : Fin 254 → Bool}
    {ws : List CmpWit} (hb : ∀ i, (bits i).val = bit (xs i)) (h : enforce_in_field_le bits ws) :
    natOfBits xs ≤ r - 1 := by
  have := cmpLoop_sound (inFieldPositions bits) ws ⟨const true, []⟩ true []
    ((List.finRange 254).reverse.map xs) 0 0 rfl .nil (forall₂_map _ hb) rfl
    (inFieldPositions_length bits) h
  rwa [List.nil_append, List.length_nil, List.replicate_zero, List.nil_append,
    inFieldPositions_fst, ofBE_finRange, ofBE_finRange, natOfBits_r_sub_one] at this

theorem enforce_in_field_le.complete {bits : Fin 254 → Boolean} {xs : Fin 254 → Bool}
    (hb : ∀ i, (bits i).val = bit (xs i)) (hle : natOfBits xs ≤ r - 1) :
    enforce_in_field_le bits (cmpHonest (inFieldPositions bits) ⟨const true, []⟩) := by
  apply cmpLoop_complete (inFieldPositions bits) ⟨const true, []⟩ true []
    ((List.finRange 254).reverse.map xs) 0 0 rfl .nil (forall₂_map _ hb) rfl
    (inFieldPositions_length bits)
  rwa [List.nil_append, List.length_nil, List.replicate_zero, List.nil_append,
    inFieldPositions_fst, ofBE_finRange, ofBE_finRange, natOfBits_r_sub_one]

end Boolean

/-! ## `UInt` -/

/-- `UInt<N, T, F>`: `N` little-endian `Boolean`s; `UInt8` is `UInt 8` and `UInt32` is `UInt 32`.
A `UInt` is its bits, so `to_bits_le` and `from_bits_le` are the identity. -/
abbrev UInt (n : ℕ) := Fin n → Boolean

namespace UInt

variable {n : ℕ}

/-- `u` carries the word `x`: each bit's value is the matching bit of `x`. -/
def Encodes (u : UInt n) (x : BitVec n) : Prop := ∀ i : Fin n, (u i).val = bit (x.getLsbD i)

/-- `GR1CSVar::is_constant`: every bit is a constant. -/
def isConst (u : UInt n) : Bool := (List.finRange n).all fun i => (u i).isConst

/-- `GR1CSVar::value`. -/
def value (u : UInt n) : BitVec n := BitVec.ofNat n (natOfBits fun i => (u i).value)

theorem Encodes.value_eq {u : UInt n} {x : BitVec n} (h : Encodes u x) : value u = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [value, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, testBit_natOfBits,
    dite_true]
  exact Boolean.value_eq (h ⟨i, hi⟩)

/-- `UInt::constant`. -/
def constant (x : BitVec n) : UInt n := fun i => .const (x.getLsbD i)

theorem constant_encodes (x : BitVec n) : Encodes (constant x) x := fun _ => rfl

theorem Encodes.of_eq {u : UInt n} {x y : BitVec n} (h : Encodes u x) (e : x = y) : Encodes u y :=
  e ▸ h

/-- `UInt::rotate_right`: `[T]::rotate_left` of the little-endian bits. -/
def rotate_right (u : UInt n) (k : ℕ) : UInt n :=
  fun i => u ⟨(i + k) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

theorem rotate_right_encodes {u : UInt n} {x : BitVec n} (h : Encodes u x) (k : ℕ) :
    Encodes (rotate_right u k) (x.rotateRight k) := by
  intro i
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hk := Nat.mod_lt k hn
  rw [rotate_right, h, BitVec.getLsbD_rotateRight]
  congr 1
  have hi := i.isLt
  by_cases hlt : (i : ℕ) < n - k % n
  · have : ((i : ℕ) + k) % n = k % n + i := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega)]; omega
    simp [hlt, this]
  · have : ((i : ℕ) + k) % n = i - (n - k % n) := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [hlt, this, hi]

/-- `UInt >> k` for `k < N`: the bits move down and constant `false` fills the top. -/
def shr (u : UInt n) (k : ℕ) : UInt n :=
  fun i => if h : (i : ℕ) + k < n then u ⟨i + k, h⟩ else .const false

theorem shr_encodes {u : UInt n} {x : BitVec n} (h : Encodes u x) (k : ℕ) :
    Encodes (shr u k) (x >>> k) := by
  intro i
  rw [shr, BitVec.getLsbD_ushiftRight]
  split
  · refine (h _).trans ?_; simp [Nat.add_comm]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; rfl

/-- `UInt ^ UInt`, bitwise `Boolean::xor`. -/
def xor (a b : UInt n) (w : Fin n → F) : UInt n := fun i => (a i).xor (b i) (w i)

def xor.Rel (a b : UInt n) (w : Fin n → F) : Prop := ∀ i, Boolean.xor.Rel (a i) (b i) (w i)

def xor.wit (a b : UInt n) : Fin n → F := fun i => Boolean.xor.wit (a i) (b i)

theorem xor.sound {a b : UInt n} {x y : BitVec n} {w : Fin n → F} (ha : Encodes a x)
    (hb : Encodes b y) (h : xor.Rel a b w) : Encodes (xor a b w) (x ^^^ y) := fun i => by
  rw [BitVec.getLsbD_xor]; exact Boolean.xor.sound (ha i) (hb i) (h i)

theorem xor.complete (a b : UInt n) : xor.Rel a b (xor.wit a b) := fun _ => Boolean.xor.complete _ _

/-- `UInt & UInt`, bitwise `Boolean::and`. -/
def and (a b : UInt n) (w : Fin n → F) : UInt n := fun i => (a i).and (b i) (w i)

def and.Rel (a b : UInt n) (w : Fin n → F) : Prop := ∀ i, Boolean.and.Rel (a i) (b i) (w i)

def and.wit (a b : UInt n) : Fin n → F := fun i => Boolean.and.wit (a i) (b i)

theorem and.sound {a b : UInt n} {x y : BitVec n} {w : Fin n → F} (ha : Encodes a x)
    (hb : Encodes b y) (h : and.Rel a b w) : Encodes (and a b w) (x &&& y) := fun i => by
  rw [BitVec.getLsbD_and]; exact Boolean.and.sound (ha i) (hb i) (h i)

theorem and.complete (a b : UInt n) : and.Rel a b (and.wit a b) := fun _ => Boolean.and.complete _ _

/-- `!UInt`, bitwise `Boolean::not`. -/
def not (u : UInt n) : UInt n := fun i => (u i).not

theorem not_encodes {u : UInt n} {x : BitVec n} (h : Encodes u x) : Encodes (not u) (~~~x) :=
  fun i => by rw [BitVec.getLsbD_not]; simpa using Boolean.not_val (h i)

end UInt

/-! ## Bit decompositions -/

/-- `Boolean::le_bits_to_fp` for fewer bits than the field's 254, where it emits no constraint: the
linear combination `Σ b_i · 2^i`, a constant when every bit is. -/
def Boolean.le_bits_to_fp {n : ℕ} (bits : Fin n → Boolean) : FpVar :=
  if UInt.isConst bits then .const (∑ i, (bits i).val * 2 ^ (i : ℕ))
  else .var (∑ i, (bits i).val * 2 ^ (i : ℕ))

theorem Boolean.le_bits_to_fp_val {n : ℕ} (bits : Fin n → Boolean) :
    (le_bits_to_fp bits).val = ∑ i, (bits i).val * 2 ^ (i : ℕ) := by
  unfold le_bits_to_fp; split <;> rfl

theorem Boolean.le_bits_to_fp_isConst {n : ℕ} (bits : Fin n → Boolean) :
    (le_bits_to_fp bits).isConst = UInt.isConst bits := by
  unfold le_bits_to_fp; split <;> simp_all [FpVar.isConst]

theorem Boolean.le_bits_to_fp_of_bits {n : ℕ} {bits : Fin n → Boolean} {xs : Fin n → Bool}
    (h : ∀ i, (bits i).val = bit (xs i)) : (le_bits_to_fp bits).val = (natOfBits xs : F) := by
  rw [le_bits_to_fp_val, ← sum_bit]; simp [h]

theorem UInt.Encodes.le_bits_to_fp {n : ℕ} {u : UInt n} {x : BitVec n} (h : Encodes u x) :
    (Boolean.le_bits_to_fp u).val = (x.toNat : F) := by
  rw [Boolean.le_bits_to_fp_of_bits h]
  congr 1
  rw [show (fun i : Fin n => x.getLsbD i) = fun i : Fin n => x.toNat.testBit i from rfl,
    natOfBits_testBit, Nat.mod_eq_of_lt x.isLt]

theorem new_witness_bits {n : ℕ} {z : Fin n → F} (h : ∀ i, Boolean.new_witness.Rel (z i)) :
    ∀ i, z i = bit (decide (z i = 1)) := fun i => Boolean.new_witness.sound (h i)

namespace FpVar

/-- `to_non_unique_bits_le`: 254 fresh boolean witnesses `z` whose weighted sum is the value,
`0 · 0 = Σ 2^i·z_i - x`. A constant gives the bits of its canonical value and emits nothing. -/
def to_non_unique_bits_le : FpVar → (Fin 254 → F) → Fin 254 → Boolean
  | const c, _ => fun i => .const (c.val.testBit i)
  | var _, z => fun i => .var (z i)

def to_non_unique_bits_le.Rel : FpVar → (Fin 254 → F) → Prop
  | const _, _ => True
  | var x, z => (∀ i, Boolean.new_witness.Rel (z i)) ∧ 0 * 0 = (∑ i : Fin 254, 2 ^ (i : ℕ) * z i) - x

/-- The bits are binary digits of the value, read as a number below `2^254`, which may exceed `r`. -/
theorem to_non_unique_bits_le.sound {x : F} {z : Fin 254 → F}
    (h : to_non_unique_bits_le.Rel (var x) z) :
    (∀ i, (to_non_unique_bits_le (var x) z i).val = bit (decide (z i = 1))) ∧
      x = (natOfBits fun i => decide (z i = 1) : F) := by
  obtain ⟨hbool, hsum⟩ := h
  have hb := new_witness_bits hbool
  refine ⟨hb, ?_⟩
  rw [← sum_bit]
  have : ∑ i : Fin 254, 2 ^ (i : ℕ) * z i = x := by linear_combination -hsum
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by
    rw [mul_comm]; exact congrArg (· * (2 : F) ^ (i : ℕ)) (hb i)

theorem val_lt_two_pow_254 (x : F) : x.val < 2 ^ 254 :=
  lt_of_lt_of_le (ZMod.val_lt x) (by unfold r; norm_num)

theorem to_non_unique_bits_le.complete (x : F) :
    to_non_unique_bits_le.Rel (var x) fun i => bit (x.val.testBit i) := by
  refine ⟨fun i => Boolean.new_witness.complete _, ?_⟩
  rw [show (∑ i : Fin 254, 2 ^ (i : ℕ) * bit (x.val.testBit i)) =
    ∑ i : Fin 254, bit (x.val.testBit i) * 2 ^ (i : ℕ) from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _, sum_bit, natOfBits_testBit,
    Nat.mod_eq_of_lt (val_lt_two_pow_254 x), ZMod.natCast_zmod_val]
  ring

/-- The witnesses of `to_bits_le`: the bits, and those of the comparison with `r - 1`. -/
structure ToBitsWit where
  bits : Fin 254 → F
  cmp : List Boolean.CmpWit

/-- `ToBitsGadget::to_bits_le`: `to_non_unique_bits_le`, then `Boolean::enforce_in_field_le`. -/
def to_bits_le (a : FpVar) (w : ToBitsWit) : Fin 254 → Boolean := to_non_unique_bits_le a w.bits

def to_bits_le.Rel : FpVar → ToBitsWit → Prop
  | const _, _ => True
  | var x, w => to_non_unique_bits_le.Rel (var x) w.bits ∧
      Boolean.enforce_in_field_le (to_non_unique_bits_le (var x) w.bits) w.cmp

/-- The witnesses arkworks assigns: the canonical bits, then the loop's. -/
def to_bits_le.wit (a : FpVar) : ToBitsWit :=
  let bits := fun i : Fin 254 => bit (a.val.val.testBit i)
  ⟨bits, Boolean.cmpHonest (Boolean.inFieldPositions fun i => .var (bits i)) ⟨.const true, []⟩⟩

/-- The bits are the canonical binary digits of the value. -/
theorem to_bits_le.sound {a : FpVar} {w : ToBitsWit} (h : to_bits_le.Rel a w) (i : Fin 254) :
    (to_bits_le a w i).val = bit (a.val.val.testBit i) := by
  cases a with
  | const c => rfl
  | var x =>
    obtain ⟨hbits, hcmp⟩ := h
    obtain ⟨hb, hx⟩ := to_non_unique_bits_le.sound hbits
    have hle := Boolean.enforce_in_field_le.sound hb hcmp
    have hr : 0 < r := by unfold r; norm_num
    have hval : x.val = natOfBits fun i => decide (w.bits i = 1) := by
      rw [hx]; exact val_natCast_of_lt (by omega)
    rw [val, hval, testBit_natOfBits, dif_pos i.isLt]
    exact hb i

theorem to_bits_le.complete (a : FpVar) : to_bits_le.Rel a (to_bits_le.wit a) := by
  cases a with
  | const c => trivial
  | var x =>
    refine ⟨to_non_unique_bits_le.complete x, ?_⟩
    apply Boolean.enforce_in_field_le.complete (xs := fun i : Fin 254 => x.val.testBit i)
      (fun i => rfl)
    rw [natOfBits_testBit, Nat.mod_eq_of_lt (val_lt_two_pow_254 x)]
    have := ZMod.val_lt x; omega

theorem sub_var_isConst (x : F) (b : FpVar) : (sub (var x) b).isConst = false := by
  cases b <;> rfl

/-- `to_bits_le_with_top_bits_zero`: `size` fresh boolean witnesses whose weighted sum is enforced
equal to the value, through `(value - Σ b_i·2^i).enforce_equal(0)`. A constant gives its bits and
emits nothing. The difference arkworks also returns is zero under the constraint. -/
def to_bits_le_with_top_bits_zero (a : FpVar) (size : ℕ) (z : Fin size → F) : Fin size → Boolean :=
  match a with
  | const c => fun i => .const (c.val.testBit i)
  | var _ => fun i => .var (z i)

def to_bits_le_with_top_bits_zero.Rel (a : FpVar) (size : ℕ) (z : Fin size → F) : Prop :=
  match a with
  | const _ => True
  | var _ => (∀ i, Boolean.new_witness.Rel (z i)) ∧
      enforce_equal.Rel (sub a (Boolean.le_bits_to_fp (to_bits_le_with_top_bits_zero a size z)))
        (const 0)

def to_bits_le_with_top_bits_zero.wit (a : FpVar) (size : ℕ) : Fin size → F :=
  fun i => bit (a.val.val.testBit i)

theorem to_bits_le_with_top_bits_zero.sound {x : F} {size : ℕ} {z : Fin size → F}
    (hsize : size ≤ 253) (h : to_bits_le_with_top_bits_zero.Rel (var x) size z) :
    x.val < 2 ^ size ∧
      ∀ i, (to_bits_le_with_top_bits_zero (var x) size z i).val = bit (x.val.testBit i) := by
  obtain ⟨hbool, heq⟩ := h
  have hb := new_witness_bits hbool
  set xs := fun i => decide (z i = 1)
  have := enforce_equal.sound heq (by rw [sub_var_isConst]; rfl)
  rw [sub_val, Boolean.le_bits_to_fp_of_bits (bits := to_bits_le_with_top_bits_zero (var x) size z)
    (xs := xs) hb, val, val, sub_eq_zero] at this
  have hlt := natOfBits_lt xs
  have h253 : 2 ^ size ≤ 2 ^ 253 := Nat.pow_le_pow_right (by norm_num) hsize
  have hval : x.val = natOfBits xs := by
    rw [this, val_natCast_of_lt (by have := two_pow_253_lt_r; omega)]
  refine ⟨hval ▸ hlt, fun i => ?_⟩
  simp only [to_bits_le_with_top_bits_zero, Boolean.val, hval, testBit_natOfBits, i.isLt,
    dite_true]
  exact hb i

theorem to_bits_le_with_top_bits_zero.complete {x : F} {size : ℕ} (hx : x.val < 2 ^ size) :
    to_bits_le_with_top_bits_zero.Rel (var x) size (to_bits_le_with_top_bits_zero.wit (var x) size) := by
  refine ⟨fun i => Boolean.new_witness.complete _, enforce_equal.complete ?_⟩
  rw [sub_val, Boolean.le_bits_to_fp_of_bits (xs := fun i : Fin size => x.val.testBit i)
    (fun i => rfl), natOfBits_testBit, Nat.mod_eq_of_lt hx, ZMod.natCast_zmod_val]
  simp [val]

theorem forall₂_ofFn {α β : Type} {R : α → β → Prop} {n : ℕ} {f : Fin n → α} {g : Fin n → β}
    (h : ∀ i, R (f i) (g i)) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]; exact Boolean.forall₂_map _ h

/-- `ToBytesGadget::to_bytes_le`: the bits of `to_bits_le`, padded with constant `false` to 256 and
cut into 32 bytes, least significant first. A constant's bytes are the constant bytes of its
canonical value, which this also gives. -/
def to_bytes_le (a : FpVar) (w : ToBitsWit) : List (UInt 8) :=
  List.ofFn fun j : Fin 32 => fun k : Fin 8 =>
    if h : 8 * (j : ℕ) + k < 254 then to_bits_le a w ⟨_, h⟩ else .const false

/-- Byte `j` is the value's `j`-th little-endian byte. -/
theorem to_bytes_le.sound {a : FpVar} {w : ToBitsWit} (h : to_bits_le.Rel a w) :
    List.Forall₂ UInt.Encodes (to_bytes_le a w)
      (List.ofFn fun j : Fin 32 => BitVec.ofNat 8 (a.val.val / 256 ^ (j : ℕ))) := by
  apply forall₂_ofFn; intro j k
  have h256 : (256 : ℕ) ^ (j : ℕ) = 2 ^ (8 * (j : ℕ)) := by rw [pow_mul]; norm_num
  rw [BitVec.getLsbD_ofNat, h256, Nat.testBit_div_two_pow]
  simp only [k.isLt, decide_true, Bool.true_and]
  split
  · refine (to_bits_le.sound h _).trans ?_; simp [Nat.add_comm]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (val_lt_two_pow_254 _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl

end FpVar

namespace UInt

variable {n : ℕ}

/-- `ark_std::log2`: the ceiling of the base-2 logarithm, `0` below `2`. -/
def log2 (x : ℕ) : ℕ := if x ≤ 1 then 0 else Nat.log2 (x - 1) + 1

theorem log2_le_self (x : ℕ) : log2 x ≤ x := by
  unfold log2; split
  · omega
  · have := (Nat.log2_lt (n := x - 1) (k := x - 1) (by omega)).mpr Nat.lt_two_pow_self; omega

/-- The sums of the SHA-256 gadget, of up to five 32-bit words, fit `to_bits_le_with_top_bits_zero`'s
bound with room to spare. -/
theorem size_le {α : Type} (l : List α) (hl : l.length ≤ 221) : 32 + log2 l.length ≤ 253 := by
  have := log2_le_self l.length; omega

theorem le_two_pow_log2 (x : ℕ) : x ≤ 2 ^ log2 x := by
  unfold log2; split
  · simp; omega
  · have := Nat.lt_log2_self (n := x - 1); omega

/-- `UInt::wrapping_add_many`. A single operand comes back as it is, and constants add natively.
Otherwise `add_many_helper` sums the operands' `le_bits_to_fp` as field elements and splits the sum
into `n + log2 len` bits with `to_bits_le_with_top_bits_zero`; the low `n` are the result. -/
def wrapping_add_many (ops : List (UInt n)) (z : Fin (n + log2 ops.length) → F) : UInt n :=
  if h : ops.length = 1 then ops[0]
  else if ops.all isConst then constant ((ops.map value).foldl (· + ·) 0)
  else fun i => FpVar.to_bits_le_with_top_bits_zero (FpVar.sum (ops.map Boolean.le_bits_to_fp))
    (n + log2 ops.length) z (Fin.castLE (Nat.le_add_right _ _) i)

def wrapping_add_many.Rel (ops : List (UInt n)) (z : Fin (n + log2 ops.length) → F) : Prop :=
  if ops.length = 1 ∨ ops.all isConst = true then True
  else FpVar.to_bits_le_with_top_bits_zero.Rel (FpVar.sum (ops.map Boolean.le_bits_to_fp)) _ z

def wrapping_add_many.wit (ops : List (UInt n)) : Fin (n + log2 ops.length) → F :=
  FpVar.to_bits_le_with_top_bits_zero.wit (FpVar.sum (ops.map Boolean.le_bits_to_fp)) _

/-- `UInt::wrapping_add`: `wrapping_add_many` of the two. -/
def wrapping_add (a b : UInt n) (z : Fin (n + log2 2) → F) : UInt n := wrapping_add_many [a, b] z

theorem foldl_add_toNat (xs : List (BitVec n)) (acc : BitVec n) :
    (xs.foldl (· + ·) acc).toNat = (acc.toNat + (xs.map BitVec.toNat).sum) % 2 ^ n := by
  induction xs generalizing acc with
  | nil => simp [Nat.mod_eq_of_lt acc.isLt]
  | cons x xs ih => simp [ih, BitVec.toNat_add, Nat.add_assoc]

theorem sum_toNat_le (xs : List (BitVec n)) :
    (xs.map BitVec.toNat).sum + xs.length ≤ xs.length * 2 ^ n := by
  induction xs with
  | nil => simp
  | cons x xs ih => have := x.isLt; simp [Nat.succ_mul]; omega

theorem sum_toNat_lt (xs : List (BitVec n)) :
    (xs.map BitVec.toNat).sum < 2 ^ (n + log2 xs.length) := by
  have h1 := sum_toNat_le xs
  have h3 : xs.length * 2 ^ n ≤ 2 ^ (n + log2 xs.length) := by
    rw [pow_add, mul_comm]; exact Nat.mul_le_mul_left _ (le_two_pow_log2 _)
  rcases xs with _ | ⟨x, xs⟩
  · simp
  · simp only [List.length_cons] at h1 h3 ⊢; omega

theorem two_pow_lt_r {k : ℕ} (h : k ≤ 253) : 2 ^ k < r :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) h) two_pow_253_lt_r

theorem sum_le_bits_to_fp {ops : List (UInt n)} {xs : List (BitVec n)}
    (hops : List.Forall₂ Encodes ops xs) :
    ((ops.map Boolean.le_bits_to_fp).map FpVar.val).sum = ((xs.map BitVec.toNat).sum : F) := by
  induction hops with
  | nil => simp
  | cons hx _ ih => simp only [List.map_cons, List.sum_cons, ih, hx.le_bits_to_fp]; push_cast; rfl

theorem sum_isConst {ops : List (UInt n)} :
    (FpVar.sum (ops.map Boolean.le_bits_to_fp)) =
      if ops.all isConst then .const ((ops.map Boolean.le_bits_to_fp).map FpVar.val).sum
      else .var ((ops.map Boolean.le_bits_to_fp).map FpVar.val).sum := by
  simp [FpVar.sum, List.all_map, Function.comp_def, Boolean.le_bits_to_fp_isConst]

theorem map_value {ops : List (UInt n)} {xs : List (BitVec n)} (hops : List.Forall₂ Encodes ops xs) :
    ops.map value = xs := by
  induction hops with
  | nil => rfl
  | cons hx _ ih => simp [hx.value_eq, ih]

theorem wrapping_add_many.sound {ops : List (UInt n)} {xs : List (BitVec n)}
    {z : Fin (n + log2 ops.length) → F} (hops : List.Forall₂ Encodes ops xs)
    (hsize : n + log2 ops.length ≤ 253) (h : wrapping_add_many.Rel ops z) :
    Encodes (wrapping_add_many ops z) (xs.foldl (· + ·) 0) := by
  have hl := hops.length_eq
  unfold wrapping_add_many
  split
  · next h1 =>
    obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp h1
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (hl ▸ h1)
    simpa using (List.forall₂_cons.mp hops).1
  · next h1 =>
    split
    · rw [map_value hops]; exact constant_encodes _
    · next hc =>
      have hrel : FpVar.to_bits_le_with_top_bits_zero.Rel
          (FpVar.sum (ops.map Boolean.le_bits_to_fp)) _ z := by
        simpa [wrapping_add_many.Rel, h1, hc] using h
      rw [sum_isConst, if_neg hc, sum_le_bits_to_fp hops] at hrel ⊢
      obtain ⟨hlt, hbits⟩ := FpVar.to_bits_le_with_top_bits_zero.sound hsize hrel
      have hval : (((xs.map BitVec.toNat).sum : ℕ) : F).val = (xs.map BitVec.toNat).sum :=
        val_natCast_of_lt (lt_trans (sum_toNat_lt xs) (two_pow_lt_r (hl ▸ hsize)))
      intro i
      rw [hbits, hval]
      simp [BitVec.getLsbD, foldl_add_toNat, Nat.testBit_mod_two_pow, i.isLt]

theorem wrapping_add_many.complete {ops : List (UInt n)} {xs : List (BitVec n)}
    (hops : List.Forall₂ Encodes ops xs) (hsize : n + log2 ops.length ≤ 253) :
    wrapping_add_many.Rel ops (wrapping_add_many.wit ops) := by
  unfold wrapping_add_many.Rel
  split
  · trivial
  · next hc =>
    simp only [not_or, Bool.not_eq_true] at hc
    unfold wrapping_add_many.wit
    rw [sum_isConst, if_neg (by simp [hc.2]), sum_le_bits_to_fp hops]
    apply FpVar.to_bits_le_with_top_bits_zero.complete
    have hl := hops.length_eq
    rw [val_natCast_of_lt (lt_trans (sum_toNat_lt xs) (two_pow_lt_r (hl ▸ hsize))), hl]
    exact sum_toNat_lt xs

/-- `UInt32::from_bytes_be`: the bytes reversed, each contributing its little-endian bits. -/
def from_bytes_be (bytes : List (UInt 8)) : UInt 32 :=
  fun i => (bytes.reverse.getD (i / 8) (constant 0)) ⟨i % 8, Nat.mod_lt _ (by norm_num)⟩

theorem Encodes.bit_eq {u : UInt n} {x : BitVec n} (h : Encodes u x) {k : Fin n} {j : ℕ}
    (hj : (k : ℕ) = j) : (u k).val = bit (x.getLsbD j) := hj ▸ h k

theorem from_bytes_be_encodes {b₀ b₁ b₂ b₃ : UInt 8} {x₀ x₁ x₂ x₃ : BitVec 8}
    (h₀ : Encodes b₀ x₀) (h₁ : Encodes b₁ x₁) (h₂ : Encodes b₂ x₂) (h₃ : Encodes b₃ x₃) :
    Encodes (from_bytes_be [b₀, b₁, b₂, b₃]) (x₀ ++ x₁ ++ x₂ ++ x₃) := by
  intro i
  have hi := i.isLt
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp only [from_bytes_be, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  rcases (by omega : (i : ℕ) / 8 = 0 ∨ (i : ℕ) / 8 = 1 ∨ (i : ℕ) / 8 = 2 ∨ (i : ℕ) / 8 = 3)
    with h' | h' | h' | h' <;> simp only [h', List.getD_cons_zero, List.getD_cons_succ] <;>
    split_ifs <;>
    first
    | omega
    | exact h₀.bit_eq (by simp; omega)
    | exact h₁.bit_eq (by simp; omega)
    | exact h₂.bit_eq (by simp; omega)
    | exact h₃.bit_eq (by simp; omega)

/-- `UInt::to_bytes_le`: the bits cut into bytes, least significant first. -/
def to_bytes_le (u : UInt 32) : List (UInt 8) :=
  List.ofFn fun j : Fin 4 => fun k : Fin 8 => u ⟨8 * j + k, by omega⟩

/-- `UInt::to_bytes_be`: `to_bytes_le` reversed. -/
def to_bytes_be (u : UInt 32) : List (UInt 8) := (to_bytes_le u).reverse

theorem to_bytes_be_encodes {u : UInt 32} {x : BitVec 32} (h : Encodes u x) :
    List.Forall₂ Encodes (to_bytes_be u)
      [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] := by
  simp only [to_bytes_be, to_bytes_le, List.ofFn_succ, List.ofFn_zero, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append]
  unfold Encodes at *
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))) <;> intro k <;>
    simp [h, k.isLt, Nat.add_comm]

/-- `UInt::conditional_enforce_equal` under `TRUE` for at most 253 bits, which form one chunk:
the two `le_bits_to_fp` sums are enforced equal. -/
def enforce_equal.Rel (a b : UInt n) : Prop :=
  FpVar.enforce_equal.Rel (Boolean.le_bits_to_fp a) (Boolean.le_bits_to_fp b)

theorem enforce_equal.sound {a b : UInt n} {x y : BitVec n} (hn : n ≤ 253) (ha : Encodes a x)
    (hb : Encodes b y) (hc : isConst a = false) (h : enforce_equal.Rel a b) : x = y := by
  have := FpVar.enforce_equal.sound h (by simp [Boolean.le_bits_to_fp_isConst, hc])
  rw [ha.le_bits_to_fp, hb.le_bits_to_fp] at this
  have hr := two_pow_253_lt_r
  have hp : 2 ^ n ≤ 2 ^ 253 := Nat.pow_le_pow_right (by norm_num) hn
  exact BitVec.eq_of_toNat_eq (natCast_inj (by have := x.isLt; omega) (by have := y.isLt; omega) this)

theorem enforce_equal.complete {a b : UInt n} {x : BitVec n} (ha : Encodes a x)
    (hb : Encodes b x) : enforce_equal.Rel a b :=
  FpVar.enforce_equal.complete (by rw [ha.le_bits_to_fp, hb.le_bits_to_fp])

end UInt

end Zerc20.Ark
