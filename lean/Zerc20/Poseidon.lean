import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Zerc20.Field
import Zerc20.Ark
import Zerc20.PoseidonConstants3
import Zerc20.PoseidonConstants4
import Zerc20.PoseidonConstants5
import Zerc20.PoseidonConstants6
import Zerc20.PoseidonConstants7

/-!
# Poseidon

The spec is the standard Poseidon permutation as arkworks' `PoseidonSponge::permute` runs it,
with the standard constants of circomlib's `poseidon_constants_old.circom`. `Poseidon.hash` is
lane 0 after one permutation of `[0, x₁, …, xₙ]`.

Two implementations are proved against it:
- `Ark.hash_var`, the arkworks sponge gadget behind `zkp/src/poseidon.rs`, follows the spec round
  by round, so its proof is direct.
- circomlib's `Poseidon(n)` runs an optimized schedule with other constants and a sparse matrix
  in the partial rounds. `Circomlib.PoseidonEx.opt_eq_std` proves that schedule equal to the
  spec for all inputs, from finite identities among the constants that the kernel checks in `ℕ`.
-/

namespace Zerc20

open Matrix

/-! ## The spec -/

namespace Poseidon

/-- arkworks' `PoseidonConfig` with `alpha = 5` and capacity 1, for a state of `t` lanes. -/
structure Params (t : ℕ) where
  fullRounds : ℕ
  partialRounds : ℕ
  /-- `ark[i][j]`: the constant added to lane `j` in round `i`. -/
  ark : ℕ → Fin t → F
  /-- `mds[i][j]`: `apply_mds` sets lane `i` to the sum of `mds[i][j]·state[j]`. -/
  mds : Matrix (Fin t) (Fin t) F

variable {t : ℕ}

/-- `apply_s_box`: `x⁵` on every lane in a full round, on lane 0 alone in a partial round. -/
def sbox (full : Bool) (s : Fin t → F) : Fin t → F :=
  fun i => if full || i.val = 0 then s i ^ 5 else s i

namespace Params

/-- `permute` runs `fullRounds / 2` full rounds, then the partial rounds, then the other full
rounds. -/
def isFull (p : Params t) (i : ℕ) : Bool :=
  i < p.fullRounds / 2 || p.fullRounds / 2 + p.partialRounds ≤ i

/-- Round `i` of `permute`: `apply_ark`, `apply_s_box`, `apply_mds`. -/
def round (p : Params t) (i : ℕ) (s : Fin t → F) : Fin t → F :=
  p.mds *ᵥ sbox (p.isFull i) (s + p.ark i)

/-- The state after the first `k` rounds. -/
def rounds (p : Params t) (k : ℕ) (s : Fin t → F) : Fin t → F :=
  (List.range k).foldl (fun s i => p.round i s) s

/-- `PoseidonSponge::permute`. Its three loops (full, partial, full rounds) are one loop over all
rounds here, with `isFull` telling the kinds apart. -/
def perm (p : Params t) (s : Fin t → F) : Fin t → F :=
  p.rounds (p.fullRounds + p.partialRounds) s

theorem rounds_zero (p : Params t) (s : Fin t → F) : p.rounds 0 s = s := rfl

theorem rounds_succ (p : Params t) (k : ℕ) (s : Fin t → F) :
    p.rounds (k + 1) s = p.round k (p.rounds k s) := by
  simp [rounds, List.range_succ, List.foldl_append]

end Params

/-- A vector given as a list; lanes past its end are 0. -/
def castVec (v : List ℕ) : Fin t → F := fun i => (v.getD i 0 : F)

/-- A matrix given row by row; entries past the lists' ends are 0. -/
def castMat (m : List (List ℕ)) : Matrix (Fin t) (Fin t) F :=
  Matrix.of fun i j => ((m.getD i []).getD j 0 : F)

/-- Standard parameters from the generated lists: 8 full rounds, `ark` flat with `t` constants per
round, `mds` row by row. -/
def ofLists (partialRounds : ℕ) (ark : List ℕ) (mds : List (List ℕ)) : Params t where
  fullRounds := 8
  partialRounds := partialRounds
  ark i j := (ark.getD (i * t + j) 0 : F)
  mds := castMat mds

/-- circomlib's standard parameters for the widths zERC20 uses, `t = 3..7`. Other widths get no
rounds, so their permutation is the identity. -/
def params : (t : ℕ) → Params t
  | 3 => ofLists PoseidonConstants.T3.partialRounds PoseidonConstants.T3.ark
      PoseidonConstants.T3.mds
  | 4 => ofLists PoseidonConstants.T4.partialRounds PoseidonConstants.T4.ark
      PoseidonConstants.T4.mds
  | 5 => ofLists PoseidonConstants.T5.partialRounds PoseidonConstants.T5.ark
      PoseidonConstants.T5.mds
  | 6 => ofLists PoseidonConstants.T6.partialRounds PoseidonConstants.T6.ark
      PoseidonConstants.T6.mds
  | 7 => ofLists PoseidonConstants.T7.partialRounds PoseidonConstants.T7.ark
      PoseidonConstants.T7.mds
  | _ => ⟨0, 0, 0, 0⟩

/-- The Poseidon permutation of width `t`. -/
def perm (t : ℕ) : (Fin t → F) → Fin t → F := (params t).perm

/-- circomlib's `Poseidon(n)` of `xs`, `n = xs.length`: lane 0 of the permutation of
`[0, x₁, …, xₙ]`. It is meant for `n = 2..6`; other lengths have no rounds and give 0. -/
def hash (xs : List F) : F := perm (xs.length + 1) (vecCons 0 xs.get) 0

/-- `hash` of a list read as a vector of length `n`. -/
theorem hash_eq {n : ℕ} (xs : List F) (x : Fin n → F) (hlen : xs.length = n)
    (hx : ∀ i : Fin n, xs.get (Fin.cast hlen.symm i) = x i) :
    hash xs = perm (n + 1) (vecCons 0 x) 0 := by
  subst hlen
  have : xs.get = x := funext hx
  simp [hash, this]

theorem hash_ofFn {n : ℕ} (x : Fin n → F) : hash (List.ofFn x) = perm (n + 1) (vecCons 0 x) 0 :=
  hash_eq _ x (List.length_ofFn) (fun i => by simp)

end Poseidon

/-! ## circomlib's templates -/

namespace Circomlib

variable {t : ℕ}

/-- The signals of one `Sigma()`. -/
structure Sigma.Signals where
  in2 : F
  in4 : F
  out : F

/-- `Sigma()`: `in2 <== in*in; in4 <== in2*in2; out <== in4*in`. -/
def Sigma.Rel (inp : F) (s : Sigma.Signals) : Prop :=
  s.in2 = inp * inp ∧ s.in4 = s.in2 * s.in2 ∧ s.out = s.in4 * inp

/-- The signals witness generation assigns a `Sigma()` on `inp`. -/
def Sigma.signals (inp : F) : Sigma.Signals :=
  ⟨inp * inp, inp * inp * (inp * inp), inp * inp * (inp * inp) * inp⟩

theorem Sigma.sound {inp : F} {s : Sigma.Signals} (h : Sigma.Rel inp s) : s.out = inp ^ 5 := by
  obtain ⟨h2, h4, h5⟩ := h
  rw [h5, h4, h2]
  ring

theorem Sigma.signals_out (inp : F) : (Sigma.signals inp).out = inp ^ 5 := by
  simp only [Sigma.signals]
  ring

theorem Sigma.complete (inp : F) : Sigma.Rel inp (Sigma.signals inp) := ⟨rfl, rfl, rfl⟩

/-- `Ark(t, C, r)`'s output. -/
def Ark.spec (C : ℕ → F) (r : ℕ) (inp : Fin t → F) : Fin t → F := fun i => inp i + C (i + r)

/-- `Ark(t, C, r)`: `out[i] <== in[i] + C[i + r]`. -/
def Ark.Rel (C : ℕ → F) (r : ℕ) (inp out : Fin t → F) : Prop :=
  ∀ i : Fin t, out i = inp i + C (i + r)

theorem Ark.sound {C : ℕ → F} {r : ℕ} {inp out : Fin t → F} (h : Ark.Rel C r inp out) :
    out = Ark.spec C r inp := funext h

theorem Ark.complete (C : ℕ → F) (r : ℕ) (inp : Fin t → F) : Ark.Rel C r inp (Ark.spec C r inp) :=
  fun _ => rfl

/-- `Mix(t, M)`'s output. -/
def Mix.spec (M : Fin t → Fin t → F) (inp : Fin t → F) : Fin t → F := fun i => ∑ j, M j i * inp j

/-- `Mix(t, M)`: `out[i] <== Σⱼ M[j][i]·in[j]`. -/
def Mix.Rel (M : Fin t → Fin t → F) (inp out : Fin t → F) : Prop :=
  ∀ i, out i = ∑ j, M j i * inp j

theorem Mix.sound {M : Fin t → Fin t → F} {inp out : Fin t → F} (h : Mix.Rel M inp out) :
    out = Mix.spec M inp := funext h

theorem Mix.complete (M : Fin t → Fin t → F) (inp : Fin t → F) : Mix.Rel M inp (Mix.spec M inp) :=
  fun _ => rfl

/-- `MixLast(t, M, s)`'s output. -/
def MixLast.spec (M : Fin t → Fin t → F) (s : Fin t) (inp : Fin t → F) : F := ∑ j, M j s * inp j

/-- `MixLast(t, M, s)`: `out <== Σⱼ M[j][s]·in[j]`. -/
def MixLast.Rel (M : Fin t → Fin t → F) (s : Fin t) (inp : Fin t → F) (out : F) : Prop :=
  out = ∑ j, M j s * inp j

theorem MixLast.sound {M : Fin t → Fin t → F} {s : Fin t} {inp : Fin t → F} {out : F}
    (h : MixLast.Rel M s inp out) : out = MixLast.spec M s inp := h

theorem MixLast.complete (M : Fin t → Fin t → F) (s : Fin t) (inp : Fin t → F) :
    MixLast.Rel M s inp (MixLast.spec M s inp) := rfl

/-- `MixS(t, S, r)`'s output. -/
def MixS.spec [NeZero t] (S : ℕ → F) (r : ℕ) (inp : Fin t → F) : Fin t → F := fun i =>
  if i = 0 then ∑ j : Fin t, S ((t * 2 - 1) * r + j) * inp j
  else inp i + inp 0 * S ((t * 2 - 1) * r + t + i - 1)

/-- `MixS(t, S, r)`: `out[0] <== Σᵢ S[(t*2-1)*r + i]·in[i]`, and
`out[i] <== in[i] + in[0]·S[(t*2-1)*r + t + i - 1]` for `i = 1..t-1`. -/
def MixS.Rel [NeZero t] (S : ℕ → F) (r : ℕ) (inp out : Fin t → F) : Prop :=
  out 0 = (∑ i : Fin t, S ((t * 2 - 1) * r + i) * inp i) ∧
    ∀ i : Fin t, i ≠ 0 → out i = inp i + inp 0 * S ((t * 2 - 1) * r + t + i - 1)

theorem MixS.sound [NeZero t] {S : ℕ → F} {r : ℕ} {inp out : Fin t → F}
    (h : MixS.Rel S r inp out) : out = MixS.spec S r inp := by
  funext i
  by_cases hi : i = 0
  · subst hi; simpa [MixS.spec] using h.1
  · simpa [MixS.spec, hi] using h.2 i hi

theorem MixS.complete [NeZero t] (S : ℕ → F) (r : ℕ) (inp : Fin t → F) :
    MixS.Rel S r inp (MixS.spec S r inp) :=
  ⟨by simp [MixS.spec], fun i hi => by simp [MixS.spec, hi]⟩

theorem MixS.rel_of_eq [NeZero t] {S : ℕ → F} {r : ℕ} {inp out : Fin t → F}
    (h : out = MixS.spec S r inp) : MixS.Rel S r inp out :=
  h ▸ MixS.complete S r inp

/-! ### `PoseidonEx(nInputs, 1)` and `Poseidon(nInputs)` -/

/-- The constants `PoseidonEx` reads for width `t`: `N_ROUNDS_P[t-2]` and the arrays
`POSEIDON_C(t)`, `POSEIDON_S(t)`, `POSEIDON_M(t)`, `POSEIDON_P(t)`, with `M j i` for `M[j][i]`. -/
structure PoseidonEx.Constants (t : ℕ) where
  nRoundsP : ℕ
  C : ℕ → F
  S : ℕ → F
  M : Fin t → Fin t → F
  P : Fin t → Fin t → F

namespace PoseidonEx

/-- The constants from the generated lists. -/
def ofLists (nRoundsP : ℕ) (C S : List ℕ) (M P : List (List ℕ)) : Constants t :=
  ⟨nRoundsP, fun k => (C.getD k 0 : F), fun k => (S.getD k 0 : F), Poseidon.castMat M,
    Poseidon.castMat P⟩

/-- circomlib's constants for the widths zERC20 uses, `t = 3..7`. -/
def constants : (t : ℕ) → Constants t
  | 3 => ofLists PoseidonConstants.T3.partialRounds PoseidonConstants.T3.C PoseidonConstants.T3.S
      PoseidonConstants.T3.M PoseidonConstants.T3.P
  | 4 => ofLists PoseidonConstants.T4.partialRounds PoseidonConstants.T4.C PoseidonConstants.T4.S
      PoseidonConstants.T4.M PoseidonConstants.T4.P
  | 5 => ofLists PoseidonConstants.T5.partialRounds PoseidonConstants.T5.C PoseidonConstants.T5.S
      PoseidonConstants.T5.M PoseidonConstants.T5.P
  | 6 => ofLists PoseidonConstants.T6.partialRounds PoseidonConstants.T6.C PoseidonConstants.T6.S
      PoseidonConstants.T6.M PoseidonConstants.T6.P
  | 7 => ofLists PoseidonConstants.T7.partialRounds PoseidonConstants.T7.C PoseidonConstants.T7.S
      PoseidonConstants.T7.M PoseidonConstants.T7.P
  | _ => ⟨0, 0, 0, 0, 0⟩

/-- A row of `Sigma()`s: `x⁵` on every lane. -/
def sigma (x : Fin t → F) : Fin t → F := fun j => x j ^ 5

/-- A round of either full-round loop: `Sigma` on every lane, `Ark` from offset `off`, `Mix` with
`M`. -/
def fullRound (c : Constants t) (off : ℕ) (x : Fin t → F) : Fin t → F :=
  Mix.spec c.M (Ark.spec c.C off (sigma x))

/-- Partial round `r`: `Sigma` on lane 0, plus `C[(nRoundsF\2+1)*t + r]`, then `MixS`. -/
def partialRound [NeZero t] (c : Constants t) (r : ℕ) (x : Fin t → F) : Fin t → F :=
  MixS.spec c.S r fun j => if j = 0 then x 0 ^ 5 + c.C (5 * t + r) else x j

/-- The first `k` rounds of the first full-round loop, from `ark[0].out = x`. -/
def firstRounds (c : Constants t) (k : ℕ) (x : Fin t → F) : Fin t → F :=
  (List.range k).foldl (fun x r => fullRound c ((r + 1) * t) x) x

/-- The first `k` partial rounds, from `mix[nRoundsF\2-1].out = x`. -/
def partialRounds [NeZero t] (c : Constants t) (k : ℕ) (x : Fin t → F) : Fin t → F :=
  (List.range k).foldl (fun x r => partialRound c r x) x

/-- The first `k` rounds of the last full-round loop, from `mixS[nRoundsP-1].out = x`. -/
def lastRounds (c : Constants t) (k : ℕ) (x : Fin t → F) : Fin t → F :=
  (List.range k).foldl (fun x r => fullRound c (5 * t + c.nRoundsP + r * t) x) x

theorem firstRounds_succ (c : Constants t) (k : ℕ) (x : Fin t → F) :
    firstRounds c (k + 1) x = fullRound c ((k + 1) * t) (firstRounds c k x) := by
  simp [firstRounds, List.range_succ, List.foldl_append]

theorem partialRounds_succ [NeZero t] (c : Constants t) (k : ℕ) (x : Fin t → F) :
    partialRounds c (k + 1) x = partialRound c k (partialRounds c k x) := by
  simp [partialRounds, List.range_succ, List.foldl_append]

theorem lastRounds_succ (c : Constants t) (k : ℕ) (x : Fin t → F) :
    lastRounds c (k + 1) x = fullRound c (5 * t + c.nRoundsP + k * t) (lastRounds c k x) := by
  simp [lastRounds, List.range_succ, List.foldl_append]

/-- `PoseidonEx(nInputs, 1)`'s `out[0]` from the state `[initialState, inputs…]`, with
`nRoundsF = 8`. -/
def output [NeZero t] (c : Constants t) (s : Fin t → F) : F :=
  let x := firstRounds c 3 (Ark.spec c.C 0 s)
  let y := Mix.spec c.P (Ark.spec c.C (4 * t) (sigma x))
  MixLast.spec c.M 0 (sigma (lastRounds c 3 (partialRounds c c.nRoundsP y)))

/-- `PoseidonEx(nInputs, 1)`'s `out[0]`. -/
def spec {n : ℕ} (c : Constants (n + 1)) (inputs : Fin n → F) (initialState : F) : F :=
  output c (vecCons initialState inputs)

/-- The signals of `PoseidonEx(nInputs, 1)` by component: `ark[r].out`, `sigmaF[r][j]`,
`mix[r].out`, `sigmaP[r]`, `mixS[r].out` and `mixLast[0].out`. -/
structure Signals (t : ℕ) where
  ark : ℕ → Fin t → F
  sigmaF : ℕ → Fin t → Sigma.Signals
  mix : ℕ → Fin t → F
  sigmaP : ℕ → Sigma.Signals
  mixS : ℕ → Fin t → F
  mixLast : F

/-- `PoseidonEx(nInputs, 1)` with constants `c`, `t = nInputs + 1` and `nRoundsF = 8`, so
`nRoundsF\2 = 4`. A component input wired with `<==` equals the wired expression, so the model
passes that expression as the input. -/
def Rel {n : ℕ} (c : Constants (n + 1)) (inputs : Fin n → F) (initialState out : F)
    (w : Signals (n + 1)) : Prop :=
  Ark.Rel c.C 0 (vecCons initialState inputs) (w.ark 0) ∧
  (∀ r < 3,
    (∀ j, Sigma.Rel (if r = 0 then w.ark 0 j else w.mix (r - 1) j) (w.sigmaF r j)) ∧
    Ark.Rel c.C ((r + 1) * (n + 1)) (fun j => (w.sigmaF r j).out) (w.ark (r + 1)) ∧
    Mix.Rel c.M (w.ark (r + 1)) (w.mix r)) ∧
  (∀ j, Sigma.Rel (w.mix 2 j) (w.sigmaF 3 j)) ∧
  Ark.Rel c.C (4 * (n + 1)) (fun j => (w.sigmaF 3 j).out) (w.ark 4) ∧
  Mix.Rel c.P (w.ark 4) (w.mix 3) ∧
  (∀ r < c.nRoundsP,
    Sigma.Rel (if r = 0 then w.mix 3 0 else w.mixS (r - 1) 0) (w.sigmaP r) ∧
    MixS.Rel c.S r
      (fun j => if j = 0 then (w.sigmaP r).out + c.C (5 * (n + 1) + r)
        else if r = 0 then w.mix 3 j else w.mixS (r - 1) j)
      (w.mixS r)) ∧
  (∀ r < 3,
    (∀ j, Sigma.Rel (if r = 0 then w.mixS (c.nRoundsP - 1) j else w.mix (4 + r - 1) j)
      (w.sigmaF (4 + r) j)) ∧
    Ark.Rel c.C (5 * (n + 1) + c.nRoundsP + r * (n + 1)) (fun j => (w.sigmaF (4 + r) j).out)
      (w.ark (4 + r + 1)) ∧
    Mix.Rel c.M (w.ark (4 + r + 1)) (w.mix (4 + r))) ∧
  (∀ j, Sigma.Rel (w.mix 6 j) (w.sigmaF 7 j)) ∧
  MixLast.Rel c.M 0 (fun j => (w.sigmaF 7 j).out) w.mixLast ∧
  out = w.mixLast

/-- A loop whose round `r` reads `x₀` for `r = 0` and round `r - 1`'s output otherwise. -/
theorem loop_eq {α : Type*} (step : ℕ → α → α) (x₀ : α) (out : ℕ → α) (K : ℕ)
    (h : ∀ r < K, out r = step r (if r = 0 then x₀ else out (r - 1))) :
    ∀ r < K, out r = (List.range (r + 1)).foldl (fun x r => step r x) x₀ := by
  intro r hr
  induction r with
  | zero => simpa using h 0 hr
  | succ r ih =>
    rw [h (r + 1) hr, List.range_succ, List.foldl_append, ← ih (by omega)]
    simp

theorem sigma_of_rel {inp : Fin t → F} {s : Fin t → Sigma.Signals}
    (h : ∀ j, Sigma.Rel (inp j) (s j)) : (fun j => (s j).out) = sigma inp :=
  funext fun j => Sigma.sound (h j)

theorem sigma_signals (inp : Fin t → F) : (fun j => (Sigma.signals (inp j)).out) = sigma inp :=
  funext fun j => Sigma.signals_out (inp j)

theorem sound {n : ℕ} {c : Constants (n + 1)} {inputs : Fin n → F} {initialState out : F}
    {w : Signals (n + 1)} (hRP : 0 < c.nRoundsP) (h : Rel c inputs initialState out w) :
    out = spec c inputs initialState := by
  obtain ⟨h0, h1, hσ3, ha4, hm3, hp, h2, hσ7, hlast, hout⟩ := h
  have ha0 := Ark.sound h0
  have first := loop_eq (fun r x => fullRound c ((r + 1) * (n + 1)) x) (w.ark 0) w.mix 3
    fun r hr => by
      obtain ⟨hσ, ha, hm⟩ := h1 r hr
      rw [Mix.sound hm, Ark.sound ha, sigma_of_rel hσ]
      split_ifs <;> rfl
  have hy : w.mix 3 = Mix.spec c.P (Ark.spec c.C (4 * (n + 1)) (sigma (w.mix 2))) := by
    rw [Mix.sound hm3, Ark.sound ha4, sigma_of_rel hσ3]
  have part := loop_eq (fun r x => partialRound c r x) (w.mix 3) w.mixS c.nRoundsP
    fun r hr => by
      obtain ⟨hσ, hs⟩ := hp r hr
      rw [MixS.sound hs, Sigma.sound hσ]
      simp only [partialRound]
      congr 1
      funext j
      split_ifs <;> simp_all
  have last := loop_eq (fun r x => fullRound c (5 * (n + 1) + c.nRoundsP + r * (n + 1)) x)
    (w.mixS (c.nRoundsP - 1)) (fun r => w.mix (4 + r)) 3
    fun r hr => by
      obtain ⟨hσ, ha, hm⟩ := h2 r hr
      dsimp only
      rw [Mix.sound hm, Ark.sound ha, sigma_of_rel hσ]
      rcases r with _ | r
      · rfl
      · simp [show 4 + (r + 1) - 1 = 4 + r by omega]; rfl
  have l2 : w.mix 6 = _ := last 2 (by norm_num)
  have p' : w.mixS (c.nRoundsP - 1) = _ := part (c.nRoundsP - 1) (by omega)
  have f2 : w.mix 2 = _ := first 2 (by norm_num)
  rw [Nat.sub_add_cancel hRP] at p'
  rw [hout, MixLast.sound hlast, sigma_of_rel hσ7, l2, p', hy, f2, ha0]
  rfl

/-- The signals witness generation assigns from the state `s = [initialState, inputs…]`. -/
def signals {n : ℕ} (c : Constants (n + 1)) (s : Fin (n + 1) → F) : Signals (n + 1) :=
  let x := fun r => firstRounds c r (Ark.spec c.C 0 s)
  let y := Mix.spec c.P (Ark.spec c.C (4 * (n + 1)) (sigma (x 3)))
  let z := fun r => partialRounds c r y
  let u := fun r => lastRounds c r (z c.nRoundsP)
  { ark := fun r =>
      if r = 0 then x 0
      else if r ≤ 4 then Ark.spec c.C (r * (n + 1)) (sigma (x (r - 1)))
      else Ark.spec c.C (5 * (n + 1) + c.nRoundsP + (r - 5) * (n + 1)) (sigma (u (r - 5)))
    sigmaF := fun r j => Sigma.signals (if r < 4 then x r j else u (r - 4) j)
    mix := fun r => if r < 3 then x (r + 1) else if r = 3 then y else u (r - 3)
    sigmaP := fun r => Sigma.signals (z r 0)
    mixS := fun r => z (r + 1)
    mixLast := output c s }

theorem complete {n : ℕ} (c : Constants (n + 1)) (inputs : Fin n → F) (initialState : F)
    (hRP : 0 < c.nRoundsP) :
    Rel c inputs initialState (spec c inputs initialState)
      (signals c (vecCons initialState inputs)) := by
  set s := vecCons initialState inputs
  refine ⟨Ark.complete _ _ _, fun r hr => ⟨fun j => ?_, ?_, ?_⟩, fun j => ?_, ?_, ?_,
    fun r hr => ⟨?_, ?_⟩, fun r hr => ⟨fun j => ?_, ?_, ?_⟩, fun j => ?_, ?_, rfl⟩
  · simp only [signals]
    rcases r with _ | r
    · simpa using Sigma.complete _
    · simpa [show r < 3 by omega, show r + 1 < 4 by omega] using Sigma.complete _
  · simp only [signals]
    rw [sigma_signals]
    simp [show r < 4 by omega, show r + 1 ≤ 4 by omega]
    exact Ark.complete _ _ _
  · simp only [signals]
    simp [hr, show r + 1 ≤ 4 by omega, firstRounds_succ, fullRound]
    exact Mix.complete _ _
  · simpa [signals] using Sigma.complete _
  · simp only [signals]
    rw [sigma_signals]
    simpa using Ark.complete _ _ _
  · simpa [signals] using Mix.complete _ _
  · simp only [signals]
    rcases r with _ | r
    · simpa using Sigma.complete _
    · simpa using Sigma.complete _
  · simp only [signals]
    refine MixS.rel_of_eq ?_
    rw [partialRounds_succ, partialRound, Sigma.signals_out]
    congr 1
    funext j
    rcases r with _ | r <;> by_cases hj : j = 0 <;> simp [hj, partialRounds]
  · simp only [signals]
    rcases r with _ | r
    · simpa [Nat.sub_add_cancel hRP, lastRounds] using Sigma.complete _
    · simpa [show ¬ 4 + r < 3 by omega, show 4 + r ≠ 3 by omega, show 4 + r - 3 = r + 1 by omega]
        using Sigma.complete _
  · simp only [signals]
    rw [sigma_signals]
    simpa [show ¬ 4 + r + 1 ≤ 4 by omega] using Ark.complete _ _ _
  · simp only [signals]
    simp [show ¬ 4 + r < 3 by omega, show 4 + r ≠ 3 by omega, show ¬ 4 + r + 1 ≤ 4 by omega,
      show 4 + r - 3 = r + 1 by omega, lastRounds_succ, fullRound]
    exact Mix.complete _ _
  · simpa [signals] using Sigma.complete _
  · simp only [signals]
    rw [sigma_signals]
    rfl

/-! ### The optimized schedule computes the standard permutation

circomlib folds the round constants of each partial round into lane 0 and the matrix of each
partial round into a sparse one. Before partial round `k`'s S-box the standard state is
`L k *ᵥ w + d k`, where `w` is `PoseidonEx`'s state there. The S-box of a partial round only
touches lane 0, and `L k` fixes lane 0 and keeps it apart from the others while `d k` vanishes
on it, so the S-box commutes with this change of variables (`sbox_affine`). The rest is linear
algebra on the constants, collected in `Compatible`. -/

theorem mix_eq {M : Fin t → Fin t → F} {A : Matrix (Fin t) (Fin t) F}
    (h : ∀ i j, M j i = A i j) (x : Fin t → F) : Mix.spec M x = A *ᵥ x := by
  funext i
  simp [Mix.spec, mulVec, dotProduct, h]

theorem ark_eq (C : ℕ → F) (off : ℕ) (x : Fin t → F) :
    Ark.spec C off x = x + fun i : Fin t => C (i + off) := rfl

theorem mixLast_eq (M : Fin t → Fin t → F) (s : Fin t) (x : Fin t → F) :
    MixLast.spec M s x = Mix.spec M x s := rfl

theorem sigma_eq (x : Fin t → F) : sigma x = Poseidon.sbox true x := by
  funext i
  simp [sigma, Poseidon.sbox]

variable [NeZero t]

/-- `MixS(t, S, r)` as a matrix. -/
def mixSMatrix (S : ℕ → F) (r : ℕ) : Matrix (Fin t) (Fin t) F :=
  Matrix.of fun i j =>
    if i = 0 then S ((t * 2 - 1) * r + j)
    else if j = 0 then S ((t * 2 - 1) * r + t + i - 1) else if i = j then 1 else 0

theorem mixS_eq (S : ℕ → F) (r : ℕ) (x : Fin t → F) :
    MixS.spec S r x = mixSMatrix S r *ᵥ x := by
  funext i
  by_cases hi : i = 0
  · simp [MixS.spec, mixSMatrix, mulVec, dotProduct, hi]
  · simp only [MixS.spec, hi, if_false, mulVec, dotProduct, mixSMatrix, of_apply]
    rw [Fintype.sum_eq_add 0 i (Ne.symm hi) fun j hj => by simp [hj.1, Ne.symm hj.2]]
    simp [hi]
    ring

theorem sbox_false (x : Fin t → F) : Poseidon.sbox false x = x + Pi.single 0 (x 0 ^ 5 - x 0) := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp [Poseidon.sbox]
  · simp [Poseidon.sbox, hi, Fin.val_eq_zero_iff]

theorem mulVec_single_zero {L : Matrix (Fin t) (Fin t) F}
    (hcol : ∀ i, L i 0 = if i = 0 then 1 else 0) (a : F) :
    L *ᵥ Pi.single 0 a = Pi.single 0 a := by
  funext i
  simp [mulVec, dotProduct, Pi.single_apply, hcol]

theorem mulVec_zero_lane {L : Matrix (Fin t) (Fin t) F}
    (hrow : ∀ j, L 0 j = if j = 0 then 1 else 0) (y : Fin t → F) : (L *ᵥ y) 0 = y 0 := by
  simp [mulVec, dotProduct, hrow]

/-- The S-box of a partial round commutes with `y ↦ L *ᵥ y + d` when `L` is `diag(1, L̂)` and
`d` vanishes on lane 0. -/
theorem sbox_affine {L : Matrix (Fin t) (Fin t) F} {d : Fin t → F}
    (hrow : ∀ j, L 0 j = if j = 0 then 1 else 0) (hcol : ∀ i, L i 0 = if i = 0 then 1 else 0)
    (hd : d 0 = 0) (y : Fin t → F) :
    Poseidon.sbox false (L *ᵥ y + d) = L *ᵥ Poseidon.sbox false y + d := by
  have h0 : (L *ᵥ y + d) 0 = y 0 := by simp [mulVec_zero_lane hrow, hd]
  rw [sbox_false, sbox_false, h0, mulVec_add, mulVec_single_zero hcol]
  abel

/-- The identities between the standard parameters `p` and circomlib's constants `c` under which
`PoseidonEx` computes `p.perm`, with `L k`, `d k` the change of variables before partial round
`k`. -/
structure Compatible (p : Poseidon.Params t) (c : Constants t) (L : ℕ → Matrix (Fin t) (Fin t) F)
    (d : ℕ → Fin t → F) : Prop where
  fullRounds : p.fullRounds = 8
  partialRounds : p.partialRounds = c.nRoundsP
  /-- `Mix` reads `M[j][i]`, so `M` is the MDS matrix transposed. -/
  M : ∀ i j, c.M j i = p.mds i j
  /-- `ark[0]` adds round 0's constants. -/
  ark_zero : ∀ i : Fin t, c.C i = p.ark 0 i
  /-- The next three `Ark`s of the first loop add `mds⁻¹·ark` ahead of `Mix`. -/
  first : ∀ q < 3, p.mds *ᵥ (fun i : Fin t => c.C (i + (q + 1) * t)) = p.ark (q + 1)
  /-- `Mix(t, P)` ends the first loop: `mds = L 0 · Pᵀ`. -/
  P : L 0 * Matrix.of (fun i j => c.P j i) = p.mds
  ark_four : p.mds *ᵥ (fun i : Fin t => c.C (i + 4 * t)) + d 0 = p.ark 4
  L_row : ∀ k < c.nRoundsP, ∀ j, L k 0 j = if j = 0 then 1 else 0
  L_col : ∀ k < c.nRoundsP, ∀ i, L k i 0 = if i = 0 then 1 else 0
  d_zero : ∀ k < c.nRoundsP, d k 0 = 0
  L_step : ∀ k < c.nRoundsP, p.mds * L k = L (k + 1) * mixSMatrix c.S k
  d_step : ∀ k < c.nRoundsP,
    p.mds *ᵥ (d k - Pi.single 0 (c.C (5 * t + k))) + p.ark (5 + k) = d (k + 1)
  L_last : L c.nRoundsP = 1
  d_last : d c.nRoundsP = 0
  /-- The `Ark`s of the last loop add `mds⁻¹·ark` ahead of `Mix`. -/
  last : ∀ q < 3, p.mds *ᵥ (fun i : Fin t => c.C (i + (5 * t + c.nRoundsP + q * t))) =
    p.ark (5 + c.nRoundsP + q)

theorem partialRound_eq (c : Constants t) (k : ℕ) (x : Fin t → F) :
    partialRound c k x =
      mixSMatrix c.S k *ᵥ (Poseidon.sbox false x + Pi.single 0 (c.C (5 * t + k))) := by
  rw [partialRound, mixS_eq, sbox_false]
  congr 1
  funext j
  by_cases hj : j = 0
  · subst hj; simp
  · simp [hj]

/-- The optimized schedule computes lane 0 of the standard permutation, for every state. -/
theorem output_eq_perm {p : Poseidon.Params t} {c : Constants t} {L : ℕ → Matrix (Fin t) (Fin t) F}
    {d : ℕ → Fin t → F} (h : Compatible p c L d) (s : Fin t → F) : output c s = p.perm s 0 := by
  set RP := c.nRoundsP
  have isFull : ∀ k, p.isFull k = decide (k < 4 ∨ 4 + RP ≤ k) := by
    intro k; simp [Poseidon.Params.isFull, h.fullRounds, h.partialRounds, RP]
  have hM := mix_eq h.M
  have std : ∀ k, p.rounds (k + 1) s =
      p.mds *ᵥ Poseidon.sbox (p.isFull k) (p.rounds k s + p.ark k) :=
    fun k => p.rounds_succ k s
  have full : ∀ off k (x : Fin t → F), (k < 4 ∨ 4 + RP ≤ k) → x = p.rounds k s + p.ark k →
      p.mds *ᵥ (fun i : Fin t => c.C (i + off)) = p.ark (k + 1) →
      fullRound c off x = p.rounds (k + 1) s + p.ark (k + 1) := by
    intro off k x hk hx hc
    rw [fullRound, hM, ark_eq c.C off, sigma_eq, mulVec_add, hc, hx, std, isFull, decide_eq_true hk]
  have first : ∀ k ≤ 3, firstRounds c k (Ark.spec c.C 0 s) = p.rounds k s + p.ark k := by
    intro k hk
    induction k with
    | zero => funext i; simp [firstRounds, Ark.spec, h.ark_zero, p.rounds_zero]
    | succ k ih =>
      rw [firstRounds_succ]
      exact full _ k _ (by omega) (ih (by omega)) (h.first k (by omega))
  set y := Mix.spec c.P (Ark.spec c.C (4 * t) (sigma (firstRounds c 3 (Ark.spec c.C 0 s)))) with hy
  have part : ∀ k ≤ RP, p.rounds (4 + k) s + p.ark (4 + k) = L k *ᵥ partialRounds c k y + d k := by
    intro k hk
    induction k with
    | zero =>
      have e4 : p.rounds 4 s = p.mds *ᵥ Poseidon.sbox (p.isFull 3) (p.rounds 3 s + p.ark 3) := std 3
      have hP : ∀ x, Mix.spec c.P x = Matrix.of (fun i j => c.P j i) *ᵥ x := mix_eq fun _ _ => rfl
      rw [Nat.add_zero, e4, isFull, decide_eq_true (by omega), ← first 3 le_rfl, ← sigma_eq,
        show partialRounds c 0 y = y from rfl, hy, hP, mulVec_mulVec, h.P, ark_eq c.C (4 * t),
        mulVec_add, add_assoc, h.ark_four]
    | succ k ih =>
      have hk' : k < RP := by omega
      have e : p.rounds (4 + (k + 1)) s =
          p.mds *ᵥ Poseidon.sbox false (p.rounds (4 + k) s + p.ark (4 + k)) := by
        rw [show 4 + (k + 1) = 4 + k + 1 by omega, std, isFull, decide_eq_false (by omega)]
      rw [e, ih (by omega), sbox_affine (h.L_row k hk') (h.L_col k hk') (h.d_zero k hk'),
        partialRounds_succ, partialRound_eq, mulVec_mulVec, ← h.L_step k hk', ← mulVec_mulVec,
        ← h.d_step k hk', show 4 + (k + 1) = 5 + k by omega, mulVec_add (L k),
        mulVec_single_zero (h.L_col k hk'), ← add_assoc, ← mulVec_add]
      congr 2
      abel
  have last : ∀ k ≤ 3, lastRounds c k (partialRounds c RP y) =
      p.rounds (4 + RP + k) s + p.ark (4 + RP + k) := by
    intro k hk
    induction k with
    | zero => rw [lastRounds, List.range_zero, List.foldl_nil, add_zero, part RP le_rfl, h.L_last,
        h.d_last, one_mulVec, add_zero]
    | succ k ih =>
      rw [lastRounds_succ, show 4 + RP + (k + 1) = 4 + RP + k + 1 by omega]
      refine full _ _ _ (by omega) (ih (by omega)) ?_
      rw [h.last k (by omega)]
      congr 1
      omega
  have e : p.perm s =
      p.mds *ᵥ Poseidon.sbox true (p.rounds (4 + RP + 3) s + p.ark (4 + RP + 3)) := by
    rw [Poseidon.Params.perm, h.fullRounds, h.partialRounds, show 8 + RP = 4 + RP + 3 + 1 by omega,
      std, isFull, decide_eq_true (by omega)]
  simp only [output]
  rw [mixLast_eq, hM, last 3 le_rfl, e, sigma_eq]

end PoseidonEx

end Circomlib

/-! ### The identities, checked by the kernel

The kernel decides them over `ℕ`, whose arithmetic it runs on GMP, reducing every result mod `r`;
`Poseidon.castVec` and `Poseidon.castMat` carry them to `F`. Vectors and matrices are built with
`tab`, so their length is `t` by construction. -/

namespace Poseidon.Check

/-- `[f 0, …, f (t-1)]`. -/
def tab {α : Type} (t : ℕ) (f : ℕ → α) : List α := (List.range t).map f

def dot (a b : List ℕ) : ℕ := (List.zipWith (· * ·) a b).sum

/-- `m·v` mod `r`. -/
def mulVec (t : ℕ) (m : List (List ℕ)) (v : List ℕ) : List ℕ :=
  tab t fun i => dot (m.getD i []) (tab t fun k => v.getD k 0) % r

/-- `a·b` mod `r`. -/
def mul (t : ℕ) (a b : List (List ℕ)) : List (List ℕ) :=
  tab t fun i => tab t fun j => dot (a.getD i []) (tab t fun k => (b.getD k []).getD j 0) % r

/-- `diag(1, L̂)`. -/
def block (t : ℕ) (Lhat : List (List ℕ)) : List (List ℕ) :=
  tab t fun i => tab t fun j =>
    if i = 0 ∨ j = 0 then (if i = j then 1 else 0) else (Lhat.getD (i - 1) []).getD (j - 1) 0

/-- `MixS(t, S, k)` as a matrix. Dropping to row `k` of `S` first keeps the lookups short. -/
def sparse (t : ℕ) (S : List ℕ) (k : ℕ) : List (List ℕ) :=
  let s := S.drop ((t * 2 - 1) * k)
  tab t fun i => tab t fun j =>
    if i = 0 then s.getD j 0 else if j = 0 then s.getD (t + i - 1) 0 else if i = j then 1 else 0

/-- `L k`: the certificate's `diag(1, L̂ k)` for a partial round, the identity after the last. -/
def L (t RP : ℕ) (Lhat : List (List (List ℕ))) (k : ℕ) : List (List ℕ) :=
  if k < RP then block t (Lhat.getD k []) else tab t fun i => tab t fun j => if i = j then 1 else 0

/-- `d k`: `[0, d̂ k…]` for a partial round, zero after the last. -/
def d (t RP : ℕ) (dhat : List (List ℕ)) (k : ℕ) : List ℕ :=
  if k < RP then tab t fun i => if i = 0 then 0 else (dhat.getD k []).getD (i - 1) 0 else []

/-- `d k - C[5t + k]·e₀`. -/
def dSub (t RP : ℕ) (C : List ℕ) (dhat : List (List ℕ)) (k : ℕ) : List ℕ :=
  tab t fun i => if i = 0 then r - C.getD (5 * t + k) 0 % r else (d t RP dhat k).getD i 0

/-- The fields of `Compatible`, over `ℕ` mod `r`, for the generated lists of one width. -/
abbrev Checks (t RP : ℕ) (ark : List ℕ) (mds : List (List ℕ)) (C S : List ℕ)
    (M P : List (List ℕ)) (Lhat : List (List (List ℕ))) (dhat : List (List ℕ)) : Prop :=
  (∀ i < t, C.getD i 0 % r = ark.getD i 0 % r) ∧
  (∀ i < t, ∀ j < t, (M.getD j []).getD i 0 % r = (mds.getD i []).getD j 0 % r) ∧
  (∀ q < 3, ∀ i < t, (mulVec t mds (tab t fun k => C.getD (k + (q + 1) * t) 0)).getD i 0 =
    ark.getD ((q + 1) * t + i) 0 % r) ∧
  (∀ i < t, ∀ j < t,
    ((mul t (L t RP Lhat 0) (tab t fun i => tab t fun j => (P.getD j []).getD i 0)).getD i []).getD
      j 0 = (mds.getD i []).getD j 0 % r) ∧
  (∀ i < t, ((mulVec t mds (tab t fun k => C.getD (k + 4 * t) 0)).getD i 0 +
    (d t RP dhat 0).getD i 0) % r = ark.getD (4 * t + i) 0 % r) ∧
  (∀ k < RP, mul t mds (L t RP Lhat k) = mul t (L t RP Lhat (k + 1)) (sparse t S k)) ∧
  (∀ k < RP, ∀ i < t, ((mulVec t mds (dSub t RP C dhat k)).getD i 0 +
    ark.getD ((5 + k) * t + i) 0) % r = (d t RP dhat (k + 1)).getD i 0 % r) ∧
  (∀ q < 3, ∀ i < t, (mulVec t mds (tab t fun k => C.getD (k + (5 * t + RP + q * t)) 0)).getD i 0 =
    ark.getD ((5 + RP + q) * t + i) 0 % r)

theorem getD_tab {α : Type} {t i : ℕ} {f : ℕ → α} {x : α} (h : i < t) :
    (tab t f).getD i x = f i := by
  simp [tab, List.getD_eq_getElem?_getD, h]

theorem length_tab {α : Type} (t : ℕ) (f : ℕ → α) : (tab t f).length = t := by simp [tab]

theorem getD_drop (l : List ℕ) (n m : ℕ) : (l.drop n).getD m 0 = l.getD (n + m) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem cast_mod (a : ℕ) : ((a % r : ℕ) : F) = a := ZMod.natCast_mod a r

theorem cast_eq_of_mod {a b : ℕ} (h : a % r = b % r) : (a : F) = b :=
  (ZMod.natCast_eq_natCast_iff' a b r).mpr h

theorem cast_dot {t : ℕ} (a b : List ℕ) (hb : b.length ≤ t) :
    ((dot a b : ℕ) : F) = ∑ j : Fin t, (a.getD j 0 : F) * (b.getD j 0 : F) := by
  induction t generalizing a b with
  | zero => simp_all [dot]
  | succ t ih =>
    rw [Fin.sum_univ_succ]
    rcases a with _ | ⟨x, a⟩
    · simp [dot]
    rcases b with _ | ⟨y, b⟩
    · simp [dot]
    simp only [List.length_cons] at hb
    rw [show dot (x :: a) (y :: b) = x * y + dot a b by simp [dot], Nat.cast_add, Nat.cast_mul,
      ih a b (by omega)]
    simp

theorem castVec_tab {t : ℕ} (f : ℕ → ℕ) :
    (castVec (tab t f) : Fin t → F) = fun i : Fin t => (f i : F) := by
  funext i
  simp only [castVec]
  rw [getD_tab i.2]

theorem castVec_mulVec {t : ℕ} (m : List (List ℕ)) (v : List ℕ) :
    (castVec (mulVec t m v) : Fin t → F) = castMat m *ᵥ castVec v := by
  funext i
  simp only [castVec, mulVec]
  rw [getD_tab i.2, cast_mod, cast_dot (t := t) _ _ (by rw [length_tab])]
  simp only [Matrix.mulVec, dotProduct, castMat, of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [getD_tab j.2]
  rfl

theorem castMat_mul {t : ℕ} (a b : List (List ℕ)) :
    (castMat (mul t a b) : Matrix (Fin t) (Fin t) F) = castMat a * castMat b := by
  ext i j
  simp only [castMat, mul, of_apply]
  rw [getD_tab i.2, getD_tab j.2, cast_mod, cast_dot (t := t) _ _ (by rw [length_tab]),
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [getD_tab k.2]
  rfl

theorem castMat_ident {t : ℕ} :
    (castMat (tab t fun i => tab t fun j => if i = j then 1 else 0) : Matrix (Fin t) (Fin t) F) =
      1 := by
  ext i j
  simp only [castMat, of_apply]
  rw [getD_tab i.2, getD_tab j.2, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Fin.val_ne_of_ne h]

theorem castMat_transpose {t : ℕ} (P : List (List ℕ)) :
    (castMat (tab t fun i => tab t fun j => (P.getD j []).getD i 0) : Matrix (Fin t) (Fin t) F) =
      Matrix.of fun i j => (castMat P : Matrix (Fin t) (Fin t) F) j i := by
  ext i j
  simp only [castMat, of_apply]
  rw [getD_tab i.2, getD_tab j.2]

variable {t : ℕ} [NeZero t]

theorem castMat_sparse (S : List ℕ) (k : ℕ) :
    (castMat (sparse t S k) : Matrix (Fin t) (Fin t) F) =
      Circomlib.PoseidonEx.mixSMatrix (fun m => (S.getD m 0 : F)) k := by
  have ht := NeZero.ne t
  ext i j
  simp only [castMat, sparse, of_apply]
  rw [getD_tab i.2, getD_tab j.2]
  simp only [Circomlib.PoseidonEx.mixSMatrix, of_apply, getD_drop]
  have hi0 : (i : ℕ) = 0 ↔ i = 0 := Fin.val_eq_zero_iff
  have hj0 : (j : ℕ) = 0 ↔ j = 0 := Fin.val_eq_zero_iff
  by_cases h1 : i = 0
  · simp [h1]
  by_cases h2 : j = 0
  · subst h2
    have : (i : ℕ) ≠ 0 := fun h => h1 (hi0.mp h)
    simp only [h1, this, Fin.val_zero, if_false, if_true]
    congr 2
    omega
  · simp [h1, h2, hi0, hj0, Fin.val_inj]

theorem castMat_block_row (Lhat : List (List ℕ)) (j : Fin t) :
    (castMat (block t Lhat) : Matrix (Fin t) (Fin t) F) 0 j = if j = 0 then 1 else 0 := by
  simp only [castMat, block, of_apply, Fin.val_zero]
  rw [getD_tab (NeZero.pos t), getD_tab j.2]
  by_cases hj : j = 0
  · simp [hj]
  · have : (j : ℕ) ≠ 0 := fun h => hj (Fin.val_eq_zero_iff.mp h)
    simp [hj, this, Ne.symm this]

theorem castMat_block_col (Lhat : List (List ℕ)) (i : Fin t) :
    (castMat (block t Lhat) : Matrix (Fin t) (Fin t) F) i 0 = if i = 0 then 1 else 0 := by
  simp only [castMat, block, of_apply, Fin.val_zero]
  rw [getD_tab i.2, getD_tab (NeZero.pos t)]
  by_cases hi : i = 0
  · simp [hi]
  · have : (i : ℕ) ≠ 0 := fun h => hi (Fin.val_eq_zero_iff.mp h)
    simp [hi, this]

theorem compatible_of_checks {RP : ℕ} {ark : List ℕ} {mds : List (List ℕ)} {C S : List ℕ}
    {M P : List (List ℕ)} {Lhat : List (List (List ℕ))} {dhat : List (List ℕ)}
    (h : Checks t RP ark mds C S M P Lhat dhat) :
    Circomlib.PoseidonEx.Compatible (t := t) (ofLists RP ark mds)
      (Circomlib.PoseidonEx.ofLists RP C S M P)
      (fun k => castMat (L t RP Lhat k)) (fun k => castVec (d t RP dhat k)) := by
  obtain ⟨h0, hM, hfirst, hP, h4, hL, hd, hlast⟩ := h
  have vec : ∀ off : ℕ, (fun i : Fin t => ((C.getD (i + off) 0 : ℕ) : F)) =
      castVec (tab t fun k => C.getD (k + off) 0) := fun off =>
    (castVec_tab (t := t) fun k => C.getD (k + off) 0).symm
  constructor
  · rfl
  · rfl
  · intro i j; exact cast_eq_of_mod (hM i i.2 j j.2)
  · intro i; simpa [ofLists] using cast_eq_of_mod (h0 i i.2)
  · intro q hq
    funext i
    simp only [ofLists, Circomlib.PoseidonEx.ofLists]
    rw [vec, ← castVec_mulVec]
    simp only [castVec]
    rw [hfirst q hq i i.2, cast_mod]
  · show castMat (L t RP Lhat 0) *
        Matrix.of (fun i j => (castMat P : Matrix (Fin t) (Fin t) F) j i) = castMat mds
    rw [← castMat_transpose, ← castMat_mul]
    ext i j
    simp only [castMat, of_apply]
    rw [hP i i.2 j j.2, cast_mod]
  · funext i
    simp only [ofLists, Circomlib.PoseidonEx.ofLists, Pi.add_apply]
    rw [vec, ← castVec_mulVec]
    simp only [castVec]
    rw [← Nat.cast_add, ← cast_mod, h4 i i.2, cast_mod]
  · intro k hk j
    change k < RP at hk
    rw [L, if_pos hk]
    exact castMat_block_row _ j
  · intro k hk i
    change k < RP at hk
    rw [L, if_pos hk]
    exact castMat_block_col _ i
  · intro k hk
    change k < RP at hk
    simp only [castVec, d, if_pos hk, Fin.val_zero]
    rw [getD_tab (NeZero.pos t)]
    simp
  · intro k hk
    change k < RP at hk
    have := congrArg (castMat (t := t)) (hL k hk)
    rwa [castMat_mul, castMat_mul, castMat_sparse] at this
  · intro k hk
    change k < RP at hk
    have hsub : castVec (dSub t RP C dhat k) =
        (castVec (d t RP dhat k) : Fin t → F) - Pi.single 0 ((C.getD (5 * t + k) 0 : ℕ) : F) := by
      funext i
      simp only [Pi.sub_apply, castVec]
      by_cases hi : i = 0
      · subst hi
        have hlt : C.getD (5 * t + k) 0 % r ≤ r := (Nat.mod_lt _ (by unfold r; norm_num)).le
        simp only [dSub, d, if_pos hk, Fin.val_zero]
        rw [getD_tab (NeZero.pos t), getD_tab (NeZero.pos t)]
        simp only [↓reduceIte, Nat.cast_sub hlt, cast_mod, ZMod.natCast_self, Pi.single_eq_same,
          Nat.cast_zero, zero_sub]
      · have : i.val ≠ 0 := fun h => hi (Fin.val_eq_zero_iff.mp h)
        simp only [dSub]
        rw [getD_tab i.2]
        simp [this, hi]
    funext i
    simp only [ofLists, Circomlib.PoseidonEx.ofLists, Pi.add_apply]
    rw [← hsub, ← castVec_mulVec]
    simp only [castVec]
    rw [← Nat.cast_add, ← cast_mod, hd k hk i i.2, cast_mod]
  · show castMat (L t RP Lhat RP) = 1
    rw [L, if_neg (lt_irrefl _)]
    exact castMat_ident
  · show castVec (d t RP dhat RP) = 0
    funext i
    simp [castVec, d]
  · intro q hq
    funext i
    simp only [ofLists, Circomlib.PoseidonEx.ofLists]
    rw [vec, ← castVec_mulVec]
    simp only [castVec]
    rw [hlast q hq i i.2, cast_mod]

/-- `Params.round i` of `ofLists RP ark mds` on a state given as a list, mod `r`. -/
def roundN (t RP : ℕ) (ark : List ℕ) (mds : List (List ℕ)) (i : ℕ) (s : List ℕ) : List ℕ :=
  mulVec t mds (tab t fun j =>
    let x := (s.getD j 0 + ark.getD (i * t + j) 0) % r
    if i < 4 ∨ 4 + RP ≤ i ∨ j = 0 then x ^ 5 % r else x)

/-- `Params.perm` of `ofLists RP ark mds` on a state given as a list, mod `r`. -/
def permN (t RP : ℕ) (ark : List ℕ) (mds : List (List ℕ)) (s : List ℕ) : List ℕ :=
  (List.range (8 + RP)).foldl (fun s i => roundN t RP ark mds i s) s

theorem castVec_roundN (RP : ℕ) (ark : List ℕ) (mds : List (List ℕ)) (i : ℕ) (s : List ℕ) :
    (castVec (roundN t RP ark mds i s) : Fin t → F) =
      (ofLists RP ark mds : Params t).round i (castVec s) := by
  rw [roundN, castVec_mulVec, castVec_tab]
  simp only [Params.round]
  congr 1
  funext j
  have hfull : ((ofLists RP ark mds : Params t).isFull i || decide ((j : ℕ) = 0)) =
      decide (i < 4 ∨ 4 + RP ≤ i ∨ (j : ℕ) = 0) := by
    simp [Params.isFull, ofLists, Bool.or_assoc]
  simp only [sbox, Pi.add_apply, castVec]
  simp only [hfull, decide_eq_true_eq]
  split_ifs <;> simp only [ofLists, cast_mod, Nat.cast_pow, Nat.cast_add]

theorem castVec_permN (RP : ℕ) (ark : List ℕ) (mds : List (List ℕ)) (s : List ℕ) :
    (castVec (permN t RP ark mds s) : Fin t → F) =
      (ofLists RP ark mds : Params t).perm (castVec s) := by
  simp only [permN, Params.perm, Params.rounds]
  rw [show (ofLists RP ark mds : Params t).fullRounds + (ofLists RP ark mds).partialRounds = 8 + RP
    from rfl]
  generalize List.range (8 + RP) = l
  induction l generalizing s with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ih, castVec_roundN]

end Poseidon.Check

/-- circomlib's `Poseidon([1, 2])`, evaluated by the kernel. -/
theorem Poseidon.hash_one_two :
    Poseidon.hash [1, 2] =
      7853200120776062878684798364095072458815029376092732009249414926327459813530 := by
  have h : (Poseidon.Check.permN 3 PoseidonConstants.T3.partialRounds PoseidonConstants.T3.ark
      PoseidonConstants.T3.mds [0, 1, 2]).getD 0 0 =
      7853200120776062878684798364095072458815029376092732009249414926327459813530 := by
    decide +kernel
  have hs : (vecCons (0 : F) [(1 : F), 2].get : Fin 3 → F) = Poseidon.castVec [0, 1, 2] := by
    funext i; fin_cases i <;> rfl
  change Poseidon.perm 3 (vecCons (0 : F) [(1 : F), 2].get) 0 = _
  rw [hs]
  show (Poseidon.ofLists PoseidonConstants.T3.partialRounds PoseidonConstants.T3.ark
    PoseidonConstants.T3.mds : Poseidon.Params 3).perm (Poseidon.castVec [0, 1, 2]) 0 = _
  rw [← Poseidon.Check.castVec_permN]
  simp only [Poseidon.castVec, Fin.val_zero]
  rw [h]
  norm_num

namespace Circomlib

namespace PoseidonEx

open Poseidon.Check PoseidonConstants

/-! Each width's identities, decided by the kernel. -/

theorem compatible3 : Compatible (Poseidon.params 3) (constants 3)
    (fun k => Poseidon.castMat (L 3 T3.partialRounds T3.Lhat k))
    (fun k => Poseidon.castVec (d 3 T3.partialRounds T3.dhat k)) :=
  compatible_of_checks (by decide +kernel)

theorem compatible4 : Compatible (Poseidon.params 4) (constants 4)
    (fun k => Poseidon.castMat (L 4 T4.partialRounds T4.Lhat k))
    (fun k => Poseidon.castVec (d 4 T4.partialRounds T4.dhat k)) :=
  compatible_of_checks (by decide +kernel)

theorem compatible5 : Compatible (Poseidon.params 5) (constants 5)
    (fun k => Poseidon.castMat (L 5 T5.partialRounds T5.Lhat k))
    (fun k => Poseidon.castVec (d 5 T5.partialRounds T5.dhat k)) :=
  compatible_of_checks (by decide +kernel)

theorem compatible6 : Compatible (Poseidon.params 6) (constants 6)
    (fun k => Poseidon.castMat (L 6 T6.partialRounds T6.Lhat k))
    (fun k => Poseidon.castVec (d 6 T6.partialRounds T6.dhat k)) :=
  compatible_of_checks (by decide +kernel)

theorem compatible7 : Compatible (Poseidon.params 7) (constants 7)
    (fun k => Poseidon.castMat (L 7 T7.partialRounds T7.Lhat k))
    (fun k => Poseidon.castVec (d 7 T7.partialRounds T7.dhat k)) :=
  compatible_of_checks (by decide +kernel)

/-- circomlib's optimized `PoseidonEx(n, 1)` computes the standard permutation's lane 0, for every
input and initial state, for `n = 2..6`. -/
theorem opt_eq_std {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 6) (inputs : Fin n → F) (initialState : F) :
    spec (constants (n + 1)) inputs initialState =
      Poseidon.perm (n + 1) (vecCons initialState inputs) 0 := by
  obtain ⟨h2, h6⟩ := hn
  interval_cases n
  · exact output_eq_perm compatible3 _
  · exact output_eq_perm compatible4 _
  · exact output_eq_perm compatible5 _
  · exact output_eq_perm compatible6 _
  · exact output_eq_perm compatible7 _

theorem nRoundsP_pos {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 6) : 0 < (constants (n + 1)).nRoundsP := by
  obtain ⟨h2, h6⟩ := hn
  interval_cases n <;> decide

end PoseidonEx

/-- `Poseidon(nInputs)`: `PoseidonEx(nInputs, 1)` with `initialState <== 0`, and
`out <== pEx.out[0]`. -/
def Poseidon.Rel (n : ℕ) (inputs : Fin n → F) (out : F) (w : PoseidonEx.Signals (n + 1)) : Prop :=
  PoseidonEx.Rel (PoseidonEx.constants (n + 1)) inputs 0 out w

theorem Poseidon.sound {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 6) {inputs : Fin n → F} {out : F}
    {w : PoseidonEx.Signals (n + 1)} (h : Poseidon.Rel n inputs out w) :
    out = Zerc20.Poseidon.hash (List.ofFn inputs) := by
  rw [PoseidonEx.sound (PoseidonEx.nRoundsP_pos hn) h, PoseidonEx.opt_eq_std hn,
    Zerc20.Poseidon.hash_ofFn]

theorem Poseidon.complete {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 6) (inputs : Fin n → F) :
    Poseidon.Rel n inputs (Zerc20.Poseidon.hash (List.ofFn inputs))
      (PoseidonEx.signals (PoseidonEx.constants (n + 1)) (vecCons 0 inputs)) := by
  rw [Zerc20.Poseidon.hash_ofFn, ← PoseidonEx.opt_eq_std hn]
  exact PoseidonEx.complete _ _ _ (PoseidonEx.nRoundsP_pos hn)

end Circomlib

/-! ## arkworks' `PoseidonSpongeVar` -/

namespace Ark


namespace PoseidonSpongeVar

variable {t : ℕ}

/-- `FpVar * F`: a zero constant gives `FpVar::zero()`; any other constant folds into the linear
combination, with no constraint. -/
def mulConst (x : FpVar) (c : F) : FpVar := if c = 0 then .const 0 else x.mul (.const c) 0

theorem mulConst_val (x : FpVar) (c : F) : (mulConst x c).val = x.val * c := by
  unfold mulConst
  split_ifs with h
  · simp [FpVar.val, h]
  · cases x <;> simp [FpVar.mul, FpVar.val]

/-- `FpVar::pow_by_constant(&[5])`: from `res = one()`, over the bits `1, 0, 1` of 5, `square`,
then `*= self` on a set bit. `square` is `mul` of `res` with itself. The first two steps fold,
since `one()` is a constant; each later product of two variables allocates its witness from
`w`. -/
def pow_by_constant (x : FpVar) (w : F × F × F) : Prop × FpVar :=
  let one := FpVar.const 1
  let r₁ := one.mul one 0
  let r₂ := r₁.mul x 0
  let r₃ := r₂.mul r₂ w.1
  let r₄ := r₃.mul r₃ w.2.1
  let r₅ := r₄.mul x w.2.2
  (FpVar.mul.Rel one one 0 ∧ FpVar.mul.Rel r₁ x 0 ∧ FpVar.mul.Rel r₂ r₂ w.1 ∧
    FpVar.mul.Rel r₃ r₃ w.2.1 ∧ FpVar.mul.Rel r₄ x w.2.2, r₅)

/-- The witnesses `pow_by_constant(&[5])` assigns on a value `v`: `v²`, `v⁴`, `v⁵`. -/
def pow_by_constant.wit (v : F) : F × F × F := (v * v, v * v * (v * v), v * v * (v * v) * v)

theorem pow_by_constant.sound {x : FpVar} {w : F × F × F} (h : (pow_by_constant x w).1) :
    (pow_by_constant x w).2.val = x.val ^ 5 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  simp only [pow_by_constant] at *
  rw [FpVar.mul.sound h₅, FpVar.mul.sound h₄, FpVar.mul.sound h₃, FpVar.mul.sound h₂,
    FpVar.mul.sound h₁]
  simp only [FpVar.val]
  ring

theorem pow_by_constant.complete (x : FpVar) : (pow_by_constant x (wit x.val)).1 := by
  cases x <;> simp [pow_by_constant, wit, FpVar.mul, FpVar.mul.Rel, FpVar.val]

/-- `apply_s_box`: `pow_by_constant(&[5])` on every lane in a full round, on lane 0 in a partial
round, with `w j` the witnesses of lane `j`. -/
def apply_s_box [NeZero t] (full : Bool) (s : Fin t → FpVar) (w : Fin t → F × F × F) :
    Prop × (Fin t → FpVar) :=
  if full then (∀ j, (pow_by_constant (s j) (w j)).1, fun j => (pow_by_constant (s j) (w j)).2)
  else ((pow_by_constant (s 0) (w 0)).1, Function.update s 0 (pow_by_constant (s 0) (w 0)).2)

/-- `apply_ark`: `state[j] += ark[i][j]`, a linear combination. -/
def apply_ark (p : Poseidon.Params t) (i : ℕ) (s : Fin t → FpVar) : Fin t → FpVar :=
  fun j => (s j).add (.const (p.ark i j))

/-- `apply_mds`: lane `i` is `cur += state[j] * mds[i][j]` over `j`, from `cur = zero()`; all
linear combinations. -/
def apply_mds (p : Poseidon.Params t) (s : Fin t → FpVar) : Fin t → FpVar := fun i =>
  (List.finRange t).foldl (fun cur j => cur.add (mulConst (s j) (p.mds i j))) (.const 0)

/-- Round `i` of `permute`, with `w` the S-box witnesses of its lanes. -/
def round [NeZero t] (p : Poseidon.Params t) (i : ℕ) (w : Fin t → F × F × F) (s : Fin t → FpVar) :
    Prop × (Fin t → FpVar) :=
  let b := apply_s_box (p.isFull i) (apply_ark p i s) w
  (b.1, apply_mds p b.2)

/-- The constraints of the first `k` rounds of `permute` and the state after them, with `w i` the
S-box witnesses of round `i`. -/
def rounds [NeZero t] (p : Poseidon.Params t) (w : ℕ → Fin t → F × F × F) (k : ℕ)
    (s : Fin t → FpVar) : Prop × (Fin t → FpVar) :=
  (List.range k).foldl (fun acc i => (acc.1 ∧ (round p i (w i) acc.2).1, (round p i (w i) acc.2).2))
    (True, s)

/-- `permute`. Its three loops (full, partial, full rounds) are one loop over all rounds here, as
in `Poseidon.Params.perm`. -/
def permute [NeZero t] (p : Poseidon.Params t) (w : ℕ → Fin t → F × F × F) (s : Fin t → FpVar) :
    Prop × (Fin t → FpVar) :=
  rounds p w (p.fullRounds + p.partialRounds) s

/-- The values of a state. -/
def vals (s : Fin t → FpVar) : Fin t → F := fun j => (s j).val

theorem apply_ark_vals (p : Poseidon.Params t) (i : ℕ) (s : Fin t → FpVar) :
    vals (apply_ark p i s) = vals s + p.ark i :=
  funext fun _ => FpVar.add_val _ _

theorem foldl_mulConst_val (s : Fin t → FpVar) (m : Fin t → F) (l : List (Fin t)) (init : FpVar) :
    (l.foldl (fun cur j => cur.add (mulConst (s j) (m j))) init).val =
      init.val + (l.map fun j => (s j).val * m j).sum := by
  induction l generalizing init with
  | nil => simp
  | cons j l ih => simp [ih, FpVar.add_val, mulConst_val, add_assoc]

theorem apply_mds_vals (p : Poseidon.Params t) (s : Fin t → FpVar) :
    vals (apply_mds p s) = p.mds *ᵥ vals s := by
  funext i
  simp only [vals, apply_mds, foldl_mulConst_val, mulVec, dotProduct, Fin.sum_univ_def]
  simp [FpVar.val, mul_comm]

variable [NeZero t]

theorem apply_s_box.sound {full : Bool} {s : Fin t → FpVar} {w : Fin t → F × F × F}
    (h : (apply_s_box full s w).1) :
    vals (apply_s_box full s w).2 = Poseidon.sbox full (vals s) := by
  funext j
  cases full
  · simp only [apply_s_box, Bool.false_eq_true, if_false] at h ⊢
    by_cases hj : j = 0
    · subst hj; simp [vals, Poseidon.sbox, pow_by_constant.sound h]
    · simp [vals, Poseidon.sbox, hj, Fin.val_eq_zero_iff]
  · simp only [apply_s_box, if_true] at h ⊢
    simp [vals, Poseidon.sbox, pow_by_constant.sound (h j)]

theorem apply_s_box.complete (full : Bool) (s : Fin t → FpVar) :
    (apply_s_box full s fun j => pow_by_constant.wit (s j).val).1 := by
  cases full
  · exact pow_by_constant.complete _
  · exact fun j => pow_by_constant.complete _

theorem round.sound {p : Poseidon.Params t} {i : ℕ} {w : Fin t → F × F × F} {s : Fin t → FpVar}
    (h : (round p i w s).1) : vals (round p i w s).2 = p.round i (vals s) := by
  simp only [round] at h ⊢
  rw [apply_mds_vals, apply_s_box.sound h, apply_ark_vals]
  rfl

theorem rounds_succ (p : Poseidon.Params t) (w : ℕ → Fin t → F × F × F) (k : ℕ)
    (s : Fin t → FpVar) :
    rounds p w (k + 1) s = ((rounds p w k s).1 ∧ (round p k (w k) (rounds p w k s).2).1,
      (round p k (w k) (rounds p w k s).2).2) := by
  simp [rounds, List.range_succ, List.foldl_append]

theorem rounds.sound {p : Poseidon.Params t} {w : ℕ → Fin t → F × F × F} {k : ℕ}
    {s : Fin t → FpVar} (h : (rounds p w k s).1) :
    vals (rounds p w k s).2 = p.rounds k (vals s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rounds_succ] at h ⊢
    rw [round.sound h.2, ih h.1, p.rounds_succ]

/-- The S-box witnesses of every round, from the values `v` of the initial state. -/
def wit (p : Poseidon.Params t) (v : Fin t → F) : ℕ → Fin t → F × F × F :=
  fun i j => pow_by_constant.wit ((p.rounds i v + p.ark i) j)

theorem rounds.complete (p : Poseidon.Params t) (k : ℕ) (s : Fin t → FpVar) :
    (rounds p (wit p (vals s)) k s).1 := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [rounds_succ]
    refine ⟨ih, ?_⟩
    have hv := rounds.sound ih
    have : wit p (vals s) k =
        fun j => pow_by_constant.wit ((apply_ark p k (rounds p (wit p (vals s)) k s).2) j).val := by
      funext j
      rw [show ((apply_ark p k _) j).val = vals (apply_ark p k _) j from rfl, apply_ark_vals, hv]
      rfl
    rw [this]
    exact apply_s_box.complete _ _

end PoseidonSpongeVar

/-- `poseidon::hash_var` with config `p` (rate `n`, capacity 1): `PoseidonSpongeVar::new` sets
every lane to `FpVar::zero()`, `absorb` adds input `i` to lane `1 + i`, and
`squeeze_field_elements(1)` permutes once; the result is lane 0. `w i j` holds the S-box witnesses
of round `i`, lane `j`. -/
def hash_var {n : ℕ} (p : Poseidon.Params (n + 1)) (inputs : Fin n → FpVar)
    (w : ℕ → Fin (n + 1) → F × F × F) : FpVar :=
  (PoseidonSpongeVar.permute p w (vecCons (.const 0) fun i => (FpVar.const 0).add (inputs i))).2 0

/-- The constraints `hash_var` emits: those of the S-boxes of `permute`. -/
def hash_var.Rel {n : ℕ} (p : Poseidon.Params (n + 1)) (inputs : Fin n → FpVar)
    (w : ℕ → Fin (n + 1) → F × F × F) : Prop :=
  (PoseidonSpongeVar.permute p w (vecCons (.const 0) fun i => (FpVar.const 0).add (inputs i))).1

/-- The witnesses `hash_var` assigns. -/
def hash_var.wit {n : ℕ} (p : Poseidon.Params (n + 1)) (inputs : Fin n → FpVar) :
    ℕ → Fin (n + 1) → F × F × F :=
  PoseidonSpongeVar.wit p (vecCons 0 fun i => (inputs i).val)

theorem hash_var.vals_init {n : ℕ} (inputs : Fin n → FpVar) :
    PoseidonSpongeVar.vals (vecCons (.const 0) fun i => (FpVar.const 0).add (inputs i)) =
      vecCons 0 fun i => (inputs i).val := by
  funext j
  refine Fin.cases rfl (fun i => ?_) j
  simp only [PoseidonSpongeVar.vals, Matrix.cons_val_succ]
  rw [FpVar.add_val]
  simp [FpVar.val]

theorem hash_var.sound_perm {n : ℕ} {p : Poseidon.Params (n + 1)} {inputs : Fin n → FpVar}
    {w : ℕ → Fin (n + 1) → F × F × F} (h : hash_var.Rel p inputs w) :
    (hash_var p inputs w).val = p.perm (vecCons 0 fun i => (inputs i).val) 0 := by
  have := PoseidonSpongeVar.rounds.sound h
  rw [hash_var.vals_init] at this
  exact congrFun this 0

theorem hash_var.complete {n : ℕ} (p : Poseidon.Params (n + 1)) (inputs : Fin n → FpVar) :
    hash_var.Rel p inputs (hash_var.wit p inputs) := by
  have := PoseidonSpongeVar.rounds.complete p (p.fullRounds + p.partialRounds)
    (vecCons (.const 0) fun i => (FpVar.const 0).add (inputs i))
  rwa [hash_var.vals_init] at this

/-- With circomlib's parameters, the configs `POSEIDON2..6` of `zkp/src/poseidon.rs`, `hash_var`
computes `Poseidon.hash`. -/
theorem hash_var.sound {n : ℕ} {inputs : Fin n → FpVar} {w : ℕ → Fin (n + 1) → F × F × F}
    (h : hash_var.Rel (Poseidon.params (n + 1)) inputs w) :
    (hash_var (Poseidon.params (n + 1)) inputs w).val =
      Poseidon.hash (List.ofFn fun i => (inputs i).val) := by
  rw [hash_var.sound_perm h, Poseidon.hash_ofFn]
  rfl

end Ark


end Zerc20

