import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-!
# The BN254 scalar field

Every circuit and every contract word lives in `F = ZMod r`, where `r` is the order of BN254's
G1. `r` is proved prime by a Pratt certificate: Lucas's test at each node, with the powers
evaluated by `reduce_mod_char`, so the kernel only multiplies and reduces numbers below `r²`.
-/

namespace Zerc20

/-- Lucas's test with the factorization of `p - 1` spelled out. -/
theorem prime_of_pratt (p : ℕ) (a : ZMod p) (fs : List (ℕ × ℕ))
    (hprime : ∀ f ∈ fs, f.1.Prime) (hprod : (fs.map fun f => f.1 ^ f.2).prod = p - 1)
    (ha : a ^ (p - 1) = 1) (hd : ∀ f ∈ fs, a ^ ((p - 1) / f.1) ≠ 1) : p.Prime := by
  refine lucas_primality p a ha fun q hq hqd => ?_
  rw [← hprod, (Nat.prime_iff.mp hq).dvd_prod_iff] at hqd
  obtain ⟨_, hm, hdvd⟩ := hqd
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hm
  rw [(Nat.prime_dvd_prime_iff_eq hq (hprime f hf)).mp (hq.dvd_of_dvd_pow hdvd)]
  exact hd f hf

/-- One certificate node: the witness, then the factorization of `p - 1`. Factors below `10⁶`
are left to `norm_num`; larger ones need their own node. -/
macro "pratt " a:term " with " fs:term " using " ps:term,* : tactic =>
  `(tactic| (
    refine prime_of_pratt _ $a $fs ?_ (by norm_num) (by reduce_mod_char) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      $[have := $ps];*
      and_intros <;> first | assumption | norm_num
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      norm_num
      and_intros <;> reduce_mod_char <;> decide))

theorem prime_639533339 : Nat.Prime 639533339 := by
  pratt 2 with [(2, 1), (229, 1), (853, 1), (1637, 1)] using Nat.prime_two

theorem prime_65865678001877903 : Nat.Prime 65865678001877903 := by
  pratt 5 with [(2, 1), (83, 1), (379, 1), (1637, 1), (639533339, 1)] using prime_639533339

theorem prime_1593227 : Nat.Prime 1593227 := by
  pratt 2 with [(2, 1), (19, 1), (41927, 1)] using Nat.prime_two

theorem prime_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 := by
  pratt 3 with [(2, 5), (5, 1), (823, 1), (1593227, 1), (65865678001877903, 1)]
    using prime_1593227, prime_65865678001877903

theorem prime_12048837557 : Nat.Prime 12048837557 := by
  pratt 2 with [(2, 2), (7, 2), (661, 1), (93001, 1)] using Nat.prime_two

theorem prime_5156902474397 : Nat.Prime 5156902474397 := by
  pratt 2 with [(2, 2), (107, 1), (12048837557, 1)] using prime_12048837557

theorem prime_1670836401704629 : Nat.Prime 1670836401704629 := by
  pratt 2 with [(2, 2), (3, 4), (5156902474397, 1)] using prime_5156902474397

theorem prime_405928799 : Nat.Prime 405928799 := by
  pratt 22 with [(2, 1), (11, 1), (3691, 1), (4999, 1)] using Nat.prime_two

/-- The order of BN254's G1, the field of every circuit. -/
def r : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

theorem r_prime : r.Prime := by
  unfold r
  pratt 5 with [(2, 28), (3, 2), (13, 1), (29, 1), (983, 1), (11003, 1), (237073, 1),
      (405928799, 1), (1670836401704629, 1), (13818364434197438864469338081, 1)]
    using prime_405928799, prime_1670836401704629, prime_13818364434197438864469338081

instance : Fact r.Prime := ⟨r_prime⟩

/-- The circuit field. -/
abbrev F := ZMod r

end Zerc20

