import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The group law of an Edwards curve

The curve `x² + y² = 1 + d·x²·y²` over a field `K` in which `2 ≠ 0` and `d` is not a square. The
addition law

  `(x₁, y₁) + (x₂, y₂) = ((x₁y₂ + y₁x₂) / (1 + d·x₁x₂y₁y₂), (y₁y₂ − x₁x₂) / (1 − d·x₁x₂y₁y₂))`

is complete: since `d` is not a square, neither denominator vanishes on the curve. Commutativity,
the identity `(0, 1)` and the inverse `(−x, y)` follow from the formulas. Associativity is
transported from Mathlib's Weierstrass group along the injective map

  `(x, y) ↦ (X, Y) = ((1 − d)·(1 + y)/(1 − y), 2X/x)`,  `(0, 1) ↦ 0`

onto `Y² = X³ + 2(1 + d)·X² + (1 − d)²·X`, which carries the Edwards sum to the Weierstrass sum.
The identities behind that are polynomial; each is checked by `linear_combination` against the
curve equations after clearing denominators, in the coordinates `t = (1 + y)/(1 − y)` and
`w = 1/x`, where the curve reads `(t + 1)² − d·(t − 1)² = 4·t·w²` and the map is
`(X, Y) = ((1 − d)·t, 2·(1 − d)·t·w)`.
-/

namespace Zerc20.Edwards

variable {K : Type*} [Field K]

/-- A point of the Edwards curve `x² + y² = 1 + d·x²·y²`. -/
@[ext]
structure Point (d : K) where
  x : K
  y : K
  on_curve : x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2

variable {d : K}

section NonSquare

variable [hd : Fact (¬IsSquare d)]

theorem d_ne_zero : d ≠ 0 := fun h => hd.out ⟨0, by simp [h]⟩

theorem d_ne_one : d ≠ 1 := fun h => hd.out ⟨1, by simp [h]⟩

theorem one_sub_d_ne_zero : 1 - d ≠ 0 := sub_ne_zero.mpr (Ne.symm d_ne_one)

theorem one_sub_d_mul_sq_ne_zero (y : K) : 1 - d * y ^ 2 ≠ 0 := by
  intro h
  have hy : y ≠ 0 := by rintro rfl; simp at h
  exact hd.out ⟨y⁻¹, by field_simp; linear_combination -h⟩

/-- If `(d·x₁x₂y₁y₂)² = 1` for two points, then `d·x₂²y₂²·(x₁ ± y₁)² = (x₂ ± d·x₁x₂y₁y₂·y₂)²` and
one of `x₁ ± y₁` is nonzero, which makes `d` a square. -/
theorem sq_mul_ne_one [NeZero (2 : K)] (P Q : Point d) : (d * P.x * Q.x * P.y * Q.y) ^ 2 ≠ 1 := by
  obtain ⟨x1, y1, h1⟩ := P
  obtain ⟨x2, y2, h2⟩ := Q
  dsimp only
  intro hD
  have hD0 : d * x1 * x2 * y1 * y2 ≠ 0 := by rintro h; rw [h] at hD; simp at hD
  have hx1 : x1 ≠ 0 := by rintro rfl; simp at hD0
  have hx2 : x2 ≠ 0 := by rintro rfl; simp at hD0
  have hy2 : y2 ≠ 0 := by rintro rfl; simp at hD0
  have key (s : K) (hs : s ^ 2 = 1) (hne : x1 + s * y1 ≠ 0) : IsSquare d := by
    have e : d * (x2 * y2 * (x1 + s * y1)) ^ 2 = (x2 + s * (d * x1 * x2 * y1 * y2) * y2) ^ 2 := by
      linear_combination (d * x2 ^ 2 * y2 ^ 2) * h1 + (1 - s ^ 2 * y2 ^ 2) * hD - h2 +
        (d * x2 ^ 2 * y2 ^ 2 * y1 ^ 2 - y2 ^ 2) * hs
    have hden : x2 * y2 * (x1 + s * y1) ≠ 0 := mul_ne_zero (mul_ne_zero hx2 hy2) hne
    refine ⟨(x2 + s * (d * x1 * x2 * y1 * y2) * y2) / (x2 * y2 * (x1 + s * y1)), ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hden hden)]
    linear_combination e
  by_cases h : x1 + 1 * y1 = 0
  · refine hd.out (key (-1) (by ring) fun h' => hx1 ?_)
    have : (2 : K) * x1 = 0 := by linear_combination h + h'
    simpa [two_ne_zero] using this
  · exact hd.out (key 1 (by ring) h)

theorem one_add_ne_zero [NeZero (2 : K)] (P Q : Point d) :
    1 + d * P.x * Q.x * P.y * Q.y ≠ 0 := fun h =>
  sq_mul_ne_one P Q (by rw [eq_neg_of_add_eq_zero_right h]; ring)

theorem one_sub_ne_zero [NeZero (2 : K)] (P Q : Point d) :
    1 - d * P.x * Q.x * P.y * Q.y ≠ 0 := fun h =>
  sq_mul_ne_one P Q (by rw [← sub_eq_zero.mp h]; ring)

end NonSquare

/-! ### Polynomial identities

Each holds in the ideal of the curve equations once multiplied by the stated factor, nonzero
wherever the identity is used. The multipliers of `linear_combination` in the `t, w` identities
come from pseudo-division by the curve equations. -/

/-- Closure of the addition law, with its denominators cleared. With `aᵢ = xᵢ² + yᵢ²`,
`pᵢ = xᵢ²yᵢ²` and `D = d·x₁x₂y₁y₂`, the difference of the two sides is
`a₁a₂(1 + D²) − (1 − D²)² − d·p₁a₂² − d·p₂a₁²`, which vanishes at `aᵢ = 1 + d·pᵢ`. -/
private theorem add_on_curve_poly {x1 y1 x2 y2 : K}
    (h1 : x1 ^ 2 + y1 ^ 2 = 1 + d * x1 ^ 2 * y1 ^ 2)
    (h2 : x2 ^ 2 + y2 ^ 2 = 1 + d * x2 ^ 2 * y2 ^ 2) :
    (x1 * y2 + y1 * x2) ^ 2 * (1 - d * x1 * x2 * y1 * y2) ^ 2 +
        (y1 * y2 - x1 * x2) ^ 2 * (1 + d * x1 * x2 * y1 * y2) ^ 2 =
      (1 + d * x1 * x2 * y1 * y2) ^ 2 * (1 - d * x1 * x2 * y1 * y2) ^ 2 +
        d * (x1 * y2 + y1 * x2) ^ 2 * (y1 * y2 - x1 * x2) ^ 2 := by
  linear_combination
    ((x2 ^ 2 + y2 ^ 2) * (1 + d ^ 2 * (x1 ^ 2 * y1 ^ 2) * (x2 ^ 2 * y2 ^ 2)) -
        d * (x2 ^ 2 * y2 ^ 2) * (x1 ^ 2 + y1 ^ 2 + 1 + d * x1 ^ 2 * y1 ^ 2)) * h1 +
      ((1 + d * x1 ^ 2 * y1 ^ 2) * (1 + d ^ 2 * (x1 ^ 2 * y1 ^ 2) * (x2 ^ 2 * y2 ^ 2)) -
        d * (x1 ^ 2 * y1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + 1 + d * x2 ^ 2 * y2 ^ 2)) * h2

/-- The `X`-coordinate of the Weierstrass sum of two points with distinct `t`, against the Edwards
sum's `t`-coordinate; `l` is the chord's slope. -/
private theorem add_X_poly {l t1 t2 w1 w2 : K}
    (h1 : (t1 + 1) ^ 2 - d * (t1 - 1) ^ 2 = 4 * t1 * w1 ^ 2)
    (h2 : (t2 + 1) ^ 2 - d * (t2 - 1) ^ 2 = 4 * t2 * w2 ^ 2)
    (hl : l * (t1 - t2) = 2 * (t1 * w1 - t2 * w2)) :
    256 * t1 ^ 2 * t2 ^ 2 * (t1 - t2) ^ 2 *
      ((l ^ 2 - 2 * (1 + d) - (1 - d) * t1 - (1 - d) * t2) *
          (2 * (w1 * w2) * (t1 + t2) + (t1 + 1) * (t2 + 1) - d * (t1 - 1) * (t2 - 1)) -
        (1 - d) * (2 * (w1 * w2) * (t1 * t2 + 1) - (t1 + 1) * (t2 + 1) - d * (t1 - 1) * (t2 - 1))) =
      0 := by
  linear_combination
    (512*l*w1*w2*t1^4*t2^2 - 512*l*w1*w2*t1^2*t2^4 - 256*l*t1^4*t2^3*d + 256*l*t1^4*t2^3 +
    256*l*t1^4*t2^2*d + 256*l*t1^4*t2^2 + 256*l*t1^3*t2^4*d - 256*l*t1^3*t2^4 - 256*l*t1^3*t2^2*d
    + 256*l*t1^3*t2^2 - 256*l*t1^2*t2^4*d - 256*l*t1^2*t2^4 + 256*l*t1^2*t2^3*d - 256*l*t1^2*t2^3
    + 1024*w1^2*w2*t1^4*t2^2 + 1024*w1^2*w2*t1^3*t2^3 - 1024*w1*w2^2*t1^3*t2^3 -
    1024*w1*w2^2*t1^2*t2^4 - 512*w1*t1^4*t2^3*d + 512*w1*t1^4*t2^3 + 512*w1*t1^4*t2^2*d +
    512*w1*t1^4*t2^2 + 512*w1*t1^3*t2^3*d + 512*w1*t1^3*t2^3 - 512*w1*t1^3*t2^2*d +
    512*w1*t1^3*t2^2 + 512*w2*t1^3*t2^4*d - 512*w2*t1^3*t2^4 - 512*w2*t1^3*t2^3*d -
    512*w2*t1^3*t2^3 - 512*w2*t1^2*t2^4*d - 512*w2*t1^2*t2^4 + 512*w2*t1^2*t2^3*d -
    512*w2*t1^2*t2^3) * hl + (-512*w1*w2*t1^4*t2^2 - 512*w1*w2*t1^3*t2^3 + 1024*w2^2*t1^3*t2^3 +
    1024*w2^2*t1^2*t2^4 + 256*t1^4*t2^3*d - 256*t1^4*t2^3 - 256*t1^4*t2^2*d - 256*t1^4*t2^2 -
    256*t1^3*t2^3*d - 256*t1^3*t2^3 + 256*t1^3*t2^2*d - 256*t1^3*t2^2) * h1 +
    (-512*w1*w2*t1^3*t2^3 - 512*w1*w2*t1^2*t2^4 - 256*t1^5*t2^2*d + 256*t1^5*t2^2 -
    256*t1^4*t2^3*d + 256*t1^4*t2^3 + 512*t1^4*t2^2*d + 512*t1^4*t2^2 + 256*t1^3*t2^4*d -
    256*t1^3*t2^4 + 256*t1^3*t2^3*d + 256*t1^3*t2^3 - 256*t1^3*t2^2*d + 256*t1^3*t2^2 -
    256*t1^2*t2^4*d - 256*t1^2*t2^4) * h2

/-- The `Y`-coordinate of the same sum, against the Edwards sum's `x`-coordinate. -/
private theorem add_Y_poly {l t1 t2 w1 w2 : K}
    (h1 : (t1 + 1) ^ 2 - d * (t1 - 1) ^ 2 = 4 * t1 * w1 ^ 2)
    (h2 : (t2 + 1) ^ 2 - d * (t2 - 1) ^ 2 = 4 * t2 * w2 ^ 2)
    (hl : l * (t1 - t2) = 2 * (t1 * w1 - t2 * w2)) :
    4096 * t1 ^ 3 * t2 ^ 3 * (t1 - t2) ^ 3 *
      (-(l * ((l ^ 2 - 2 * (1 + d) - (1 - d) * t1 - (1 - d) * t2) - (1 - d) * t1) +
            2 * (1 - d) * t1 * w1) *
          (w2 * (t1 + 1) * (t2 - 1) + w1 * (t1 - 1) * (t2 + 1)) -
        2 * (l ^ 2 - 2 * (1 + d) - (1 - d) * t1 - (1 - d) * t2) *
          (w1 * w2 * (t1 + 1) * (t2 + 1) + d * (t1 - 1) * (t2 - 1))) = 0 := by
  linear_combination
    (-4096*l^2*w1*t1^6*t2^4 - 4096*l^2*w1*t1^6*t2^3 + 8192*l^2*w1*t1^5*t2^5 +
    12288*l^2*w1*t1^5*t2^4 + 4096*l^2*w1*t1^5*t2^3 - 4096*l^2*w1*t1^4*t2^6 -
    12288*l^2*w1*t1^4*t2^5 - 8192*l^2*w1*t1^4*t2^4 + 4096*l^2*w1*t1^3*t2^6 + 4096*l^2*w1*t1^3*t2^5
    - 4096*l^2*w2*t1^6*t2^4 + 4096*l^2*w2*t1^6*t2^3 + 8192*l^2*w2*t1^5*t2^5 -
    12288*l^2*w2*t1^5*t2^4 + 4096*l^2*w2*t1^5*t2^3 - 4096*l^2*w2*t1^4*t2^6 +
    12288*l^2*w2*t1^4*t2^5 - 8192*l^2*w2*t1^4*t2^4 - 4096*l^2*w2*t1^3*t2^6 + 4096*l^2*w2*t1^3*t2^5
    - 8192*l*w1^2*t1^6*t2^4 - 8192*l*w1^2*t1^6*t2^3 + 8192*l*w1^2*t1^5*t2^5 +
    16384*l*w1^2*t1^5*t2^4 + 8192*l*w1^2*t1^5*t2^3 - 8192*l*w1^2*t1^4*t2^5 - 8192*l*w1^2*t1^4*t2^4
    - 16384*l*w1*w2*t1^6*t2^4 + 32768*l*w1*w2*t1^5*t2^5 - 16384*l*w1*w2*t1^4*t2^6 +
    8192*l*w2^2*t1^5*t2^5 - 8192*l*w2^2*t1^5*t2^4 - 8192*l*w2^2*t1^4*t2^6 + 16384*l*w2^2*t1^4*t2^5
    - 8192*l*w2^2*t1^4*t2^4 - 8192*l*w2^2*t1^3*t2^6 + 8192*l*w2^2*t1^3*t2^5 - 8192*l*t1^6*t2^4*d +
    8192*l*t1^6*t2^3*d + 16384*l*t1^5*t2^5*d - 8192*l*t1^5*t2^4*d - 8192*l*t1^5*t2^3*d -
    8192*l*t1^4*t2^6*d - 8192*l*t1^4*t2^5*d + 16384*l*t1^4*t2^4*d + 8192*l*t1^3*t2^6*d -
    8192*l*t1^3*t2^5*d - 16384*w1^3*t1^6*t2^4 - 16384*w1^3*t1^6*t2^3 + 16384*w1^3*t1^5*t2^4 +
    16384*w1^3*t1^5*t2^3 - 32768*w1^2*w2*t1^6*t2^4 + 49152*w1^2*w2*t1^5*t2^5 +
    16384*w1^2*w2*t1^5*t2^4 - 16384*w1^2*w2*t1^4*t2^5 - 16384*w1^2*w2*t1^4*t2^4 +
    49152*w1*w2^2*t1^5*t2^5 - 16384*w1*w2^2*t1^5*t2^4 - 32768*w1*w2^2*t1^4*t2^6 +
    16384*w1*w2^2*t1^4*t2^5 - 16384*w1*w2^2*t1^4*t2^4 - 8192*w1*t1^7*t2^4*d + 8192*w1*t1^7*t2^4 -
    8192*w1*t1^7*t2^3*d + 8192*w1*t1^7*t2^3 + 12288*w1*t1^6*t2^5*d - 12288*w1*t1^6*t2^5 +
    12288*w1*t1^6*t2^4*d - 12288*w1*t1^6*t2^4 + 32768*w1*t1^6*t2^3*d - 12288*w1*t1^5*t2^5*d -
    4096*w1*t1^5*t2^5 - 36864*w1*t1^5*t2^4*d - 12288*w1*t1^5*t2^4 - 24576*w1*t1^5*t2^3*d -
    8192*w1*t1^5*t2^3 - 4096*w1*t1^4*t2^7*d + 4096*w1*t1^4*t2^7 + 4096*w1*t1^4*t2^6*d +
    12288*w1*t1^4*t2^6 + 8192*w1*t1^4*t2^5*d + 24576*w1*t1^4*t2^5 + 32768*w1*t1^4*t2^4*d +
    16384*w1*t1^4*t2^4 + 4096*w1*t1^3*t2^7*d - 4096*w1*t1^3*t2^7 - 4096*w1*t1^3*t2^6*d -
    12288*w1*t1^3*t2^6 - 8192*w1*t1^3*t2^5*d - 8192*w1*t1^3*t2^5 - 16384*w2^3*t1^4*t2^6 +
    16384*w2^3*t1^4*t2^5 - 16384*w2^3*t1^3*t2^6 + 16384*w2^3*t1^3*t2^5 - 8192*w2*t1^7*t2^4*d +
    8192*w2*t1^7*t2^4 + 8192*w2*t1^7*t2^3*d - 8192*w2*t1^7*t2^3 + 12288*w2*t1^6*t2^5*d -
    12288*w2*t1^6*t2^5 - 12288*w2*t1^6*t2^4*d + 28672*w2*t1^6*t2^4 - 16384*w2*t1^6*t2^3 +
    12288*w2*t1^5*t2^5*d - 28672*w2*t1^5*t2^5 - 4096*w2*t1^5*t2^4*d + 36864*w2*t1^5*t2^4 -
    8192*w2*t1^5*t2^3*d - 8192*w2*t1^5*t2^3 - 4096*w2*t1^4*t2^7*d + 4096*w2*t1^4*t2^7 -
    4096*w2*t1^4*t2^6*d + 4096*w2*t1^4*t2^6 - 24576*w2*t1^4*t2^5*d - 24576*w2*t1^4*t2^5 +
    32768*w2*t1^4*t2^4*d + 16384*w2*t1^4*t2^4 - 4096*w2*t1^3*t2^7*d + 4096*w2*t1^3*t2^7 +
    28672*w2*t1^3*t2^6*d + 4096*w2*t1^3*t2^6 - 24576*w2*t1^3*t2^5*d - 8192*w2*t1^3*t2^5) * hl +
    (8192*w1^2*t1^6*t2^4 + 8192*w1^2*t1^6*t2^3 - 8192*w1^2*t1^5*t2^4 - 8192*w1^2*t1^5*t2^3 +
    16384*w1*w2*t1^6*t2^4 - 32768*w1*w2*t1^5*t2^5 - 16384*w1*w2*t1^5*t2^4 + 16384*w1*w2*t1^4*t2^5
    + 16384*w1*w2*t1^4*t2^4 - 40960*w2^2*t1^5*t2^5 + 8192*w2^2*t1^5*t2^4 + 40960*w2^2*t1^4*t2^6 +
    8192*w2^2*t1^4*t2^4 - 8192*w2^2*t1^3*t2^6 - 8192*w2^2*t1^3*t2^5 + 8192*t1^6*t2^4*d -
    8192*t1^6*t2^3*d - 6144*t1^5*t2^6*d + 6144*t1^5*t2^6 - 6144*t1^5*t2^5*d + 14336*t1^5*t2^5 +
    6144*t1^5*t2^4*d + 10240*t1^5*t2^4 + 6144*t1^5*t2^3*d + 2048*t1^5*t2^3 + 4096*t1^4*t2^7*d -
    4096*t1^4*t2^7 + 6144*t1^4*t2^6*d - 14336*t1^4*t2^6 + 2048*t1^4*t2^5*d - 18432*t1^4*t2^5 -
    14336*t1^4*t2^4*d - 10240*t1^4*t2^4 + 2048*t1^4*t2^3*d - 2048*t1^4*t2^3 - 4096*t1^3*t2^7*d +
    4096*t1^3*t2^7 + 8192*t1^3*t2^6 + 4096*t1^3*t2^5*d + 4096*t1^3*t2^5) * h1 +
    (32768*w1*w2*t1^5*t2^5 - 16384*w1*w2*t1^5*t2^4 - 16384*w1*w2*t1^4*t2^6 + 16384*w1*w2*t1^4*t2^5
    - 16384*w1*w2*t1^4*t2^4 - 8192*w2^2*t1^4*t2^6 + 8192*w2^2*t1^4*t2^5 - 8192*w2^2*t1^3*t2^6 +
    8192*w2^2*t1^3*t2^5 + 6144*t1^7*t2^4*d - 6144*t1^7*t2^4 + 2048*t1^7*t2^3*d - 2048*t1^7*t2^3 -
    4096*t1^6*t2^5*d + 4096*t1^6*t2^5 - 26624*t1^6*t2^4*d - 6144*t1^6*t2^4 + 2048*t1^6*t2^3*d -
    2048*t1^6*t2^3 + 28672*t1^5*t2^5*d + 4096*t1^5*t2^5 + 10240*t1^5*t2^4*d + 6144*t1^5*t2^4 -
    2048*t1^5*t2^3*d + 2048*t1^5*t2^3 - 8192*t1^4*t2^6*d - 20480*t1^4*t2^5*d - 4096*t1^4*t2^5 +
    10240*t1^4*t2^4*d + 6144*t1^4*t2^4 - 2048*t1^4*t2^3*d + 2048*t1^4*t2^3 + 8192*t1^3*t2^6*d -
    4096*t1^3*t2^5*d - 4096*t1^3*t2^5) * h2

/-- `add_X_poly` for a point added to itself; `l` is the tangent's slope. -/
private theorem double_X_poly {l t w : K}
    (h : (t + 1) ^ 2 - d * (t - 1) ^ 2 = 4 * t * w ^ 2)
    (hl : l * 4 * t * w = (1 - d) * (3 * t ^ 2 + 1) + 4 * (1 + d) * t) :
    256 * w ^ 2 * t ^ 4 *
      ((l ^ 2 - 2 * (1 + d) - 2 * (1 - d) * t) *
          (2 * (w * w) * (t + t) + (t + 1) * (t + 1) - d * (t - 1) * (t - 1)) -
        (1 - d) * (2 * (w * w) * (t * t + 1) - (t + 1) * (t + 1) - d * (t - 1) * (t - 1))) = 0 := by
  linear_combination
    (256*l*w^3*t^4 - 64*l*w*t^5*d + 64*l*w*t^5 + 128*l*w*t^4*d + 128*l*w*t^4 - 64*l*w*t^3*d +
    64*l*w*t^3 - 192*w^2*t^5*d + 192*w^2*t^5 + 256*w^2*t^4*d + 256*w^2*t^4 - 64*w^2*t^3*d +
    64*w^2*t^3 + 48*t^6*d^2 - 96*t^6*d + 48*t^6 - 160*t^5*d^2 + 160*t^5 + 192*t^4*d^2 + 128*t^4*d
    + 192*t^4 - 96*t^3*d^2 + 96*t^3 + 16*t^2*d^2 - 32*t^2*d + 16*t^2) * hl + (-640*w^2*t^5*d +
    640*w^2*t^5 + 512*w^2*t^4*d + 512*w^2*t^4 - 128*w^2*t^3*d + 128*w^2*t^3 + 144*t^6*d^2 -
    288*t^6*d + 144*t^6 - 384*t^5*d^2 + 384*t^5 + 352*t^4*d^2 + 320*t^4*d + 352*t^4 - 128*t^3*d^2
    + 128*t^3 + 16*t^2*d^2 - 32*t^2*d + 16*t^2) * h

/-- `add_Y_poly` for a point added to itself. -/
private theorem double_Y_poly {l t w : K}
    (h : (t + 1) ^ 2 - d * (t - 1) ^ 2 = 4 * t * w ^ 2)
    (hl : l * 4 * t * w = (1 - d) * (3 * t ^ 2 + 1) + 4 * (1 + d) * t) :
    1024 * w ^ 3 * t ^ 5 *
      (-(l * ((l ^ 2 - 2 * (1 + d) - 2 * (1 - d) * t) - (1 - d) * t) + 2 * (1 - d) * t * w) *
          (w * (t + 1) * (t - 1) + w * (t - 1) * (t + 1)) -
        2 * (l ^ 2 - 2 * (1 + d) - 2 * (1 - d) * t) *
          (w * w * (t + 1) * (t + 1) + d * (t - 1) * (t - 1))) = 0 := by
  linear_combination
    (-512*l^2*w^3*t^6 + 512*l^2*w^3*t^4 - 512*l*w^4*t^6 - 1024*l*w^4*t^5 - 512*l*w^4*t^4 +
    384*l*w^2*t^7*d - 384*l*w^2*t^7 - 1024*l*w^2*t^6*d - 512*l*w^2*t^6 + 768*l*w^2*t^5*d +
    256*l*w^2*t^5 + 512*l*w^2*t^4 - 128*l*w^2*t^3*d + 128*l*w^2*t^3 - 1152*w^3*t^7*d +
    1152*w^3*t^7 + 1280*w^3*t^6*d - 256*w^3*t^6 + 1024*w^3*t^5*d - 3072*w^3*t^5 - 1280*w^3*t^4*d -
    1792*w^3*t^4 + 128*w^3*t^3*d - 128*w^3*t^3 - 288*w*t^8*d^2 + 576*w*t^8*d - 288*w*t^8 +
    1152*w*t^7*d^2 - 384*w*t^7*d - 768*w*t^7 - 1696*w*t^6*d^2 - 960*w*t^6*d - 416*w*t^6 +
    1024*w*t^5*d^2 + 512*w*t^5*d + 512*w*t^5 - 96*w*t^4*d^2 + 448*w*t^4*d + 672*w*t^4 -
    128*w*t^3*d^2 - 128*w*t^3*d + 256*w*t^3 + 32*w*t^2*d^2 - 64*w*t^2*d + 32*w*t^2) * hl +
    (1024*w^3*t^6*d - 3072*w^3*t^6 - 4096*w^3*t^5 - 1024*w^3*t^4*d - 1024*w^3*t^4 - 864*w*t^8*d^2
    + 1728*w*t^8*d - 864*w*t^8 + 2880*w*t^7*d^2 - 1152*w*t^7*d - 1728*w*t^7 - 3360*w*t^6*d^2 -
    2496*w*t^6*d - 288*w*t^6 + 1408*w*t^5*d^2 + 1280*w*t^5*d + 1408*w*t^5 + 96*w*t^4*d^2 +
    832*w*t^4*d + 1120*w*t^4 - 192*w*t^3*d^2 - 128*w*t^3*d + 320*w*t^3 + 32*w*t^2*d^2 - 64*w*t^2*d
    + 32*w*t^2) * h

variable [hd : Fact (¬IsSquare d)] [NeZero (2 : K)]

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
/-- The curve equation for `(N₁/A, N₂/B)`, from its form with denominators cleared. -/
private theorem on_curve_of_cleared {A B N1 N2 : K} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : N1 ^ 2 * B ^ 2 + N2 ^ 2 * A ^ 2 = A ^ 2 * B ^ 2 + d * N1 ^ 2 * N2 ^ 2) :
    (N1 / A) ^ 2 + (N2 / B) ^ 2 = 1 + d * (N1 / A) ^ 2 * (N2 / B) ^ 2 := by
  field_simp
  linear_combination h

namespace Point

/-- The complete addition law. -/
def add (P Q : Point d) : Point d where
  x := (P.x * Q.y + P.y * Q.x) / (1 + d * P.x * Q.x * P.y * Q.y)
  y := (P.y * Q.y - P.x * Q.x) / (1 - d * P.x * Q.x * P.y * Q.y)
  on_curve := on_curve_of_cleared (one_add_ne_zero P Q) (one_sub_ne_zero P Q)
    (add_on_curve_poly P.on_curve Q.on_curve)

instance : Add (Point d) := ⟨add⟩

instance : Zero (Point d) := ⟨⟨0, 1, by ring⟩⟩

instance : Neg (Point d) := ⟨fun P => ⟨-P.x, P.y, by rw [neg_sq]; exact P.on_curve⟩⟩

@[simp] theorem add_x (P Q : Point d) :
    (P + Q).x = (P.x * Q.y + P.y * Q.x) / (1 + d * P.x * Q.x * P.y * Q.y) := rfl

@[simp] theorem add_y (P Q : Point d) :
    (P + Q).y = (P.y * Q.y - P.x * Q.x) / (1 - d * P.x * Q.x * P.y * Q.y) := rfl

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
@[simp] theorem zero_x : (0 : Point d).x = 0 := rfl

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
@[simp] theorem zero_y : (0 : Point d).y = 1 := rfl

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
@[simp] theorem neg_x (P : Point d) : (-P).x = -P.x := rfl

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
@[simp] theorem neg_y (P : Point d) : (-P).y = P.y := rfl

omit [NeZero (2 : K)] in
/-- A point with `y² = 1` is `(0, ±1)`. -/
theorem x_eq_zero_of_y_sq (P : Point d) (h : P.y ^ 2 = 1) : P.x = 0 := by
  have : P.x ^ 2 * (1 - d) = 0 := by linear_combination P.on_curve + (d * P.x ^ 2 - 1) * h
  simpa [one_sub_d_ne_zero] using this

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
theorem y_sq_of_x_eq_zero (P : Point d) (h : P.x = 0) : P.y ^ 2 = 1 := by
  simpa [h] using P.on_curve

theorem add_comm' (P Q : Point d) : P + Q = Q + P := by
  ext <;> simp only [add_x, add_y] <;> ring

theorem zero_add' (P : Point d) : 0 + P = P := by
  ext <;> simp

theorem neg_add_cancel' (P : Point d) : -P + P = 0 := by
  ext
  · simp only [add_x, neg_x, neg_y, zero_x]
    rw [div_eq_zero_iff]
    left
    ring
  · have h := one_sub_ne_zero (-P) P
    simp only [add_y, neg_x, neg_y, zero_y] at h ⊢
    rw [div_eq_one_iff_eq h]
    linear_combination P.on_curve

end Point

/-! ### The Weierstrass model -/

/-- The Weierstrass curve `Y² = X³ + 2(1 + d)·X² + (1 − d)²·X`. -/
def W (d : K) : WeierstrassCurve.Affine K := ⟨0, 2 * (1 + d), 0, (1 - d) ^ 2, 0⟩

omit [hd : Fact (¬IsSquare d)] in
/-- A power of two, such as a numeral `256 = 2⁸`, is nonzero. -/
private theorem two_pow_ne (n : ℕ) {m : K} (h : (2 : K) ^ n = m) : m ≠ 0 :=
  h ▸ pow_ne_zero n two_ne_zero

theorem W_Δ_ne_zero : (W d).Δ ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have : (W d).Δ = 2 ^ 8 * d * (1 - d) ^ 4 := by
    simp only [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [this]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) d_ne_zero) (pow_ne_zero _ one_sub_d_ne_zero)

/-- `t = (1 + y)/(1 − y)`, the Montgomery `u`-coordinate. -/
def tc (P : Point d) : K := (1 + P.y) / (1 - P.y)

/-- `w = 1/x`. -/
def wc (P : Point d) : K := P.x⁻¹

/-- The Weierstrass `X` of a point other than `(0, 1)`. -/
def toX (P : Point d) : K := (1 - d) * (1 + P.y) / (1 - P.y)

/-- The Weierstrass `Y` of a point other than `(0, 1)`; `(0, −1)` gives `2·0/0 = 0`. -/
def toY (P : Point d) : K := 2 * toX P / P.x

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
theorem toX_eq (P : Point d) : toX P = (1 - d) * tc P := mul_div_assoc _ _ _

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
theorem toY_eq (P : Point d) : toY P = 2 * (1 - d) * tc P * wc P := by
  rw [toY, toX_eq, wc, div_eq_mul_inv]; ring

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
theorem tw_curve (P : Point d) (hx : P.x ≠ 0) (hy : P.y ≠ 1) :
    (tc P + 1) ^ 2 - d * (tc P - 1) ^ 2 = 4 * tc P * wc P ^ 2 := by
  have hy' : 1 - P.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  simp only [tc, wc]
  field_simp
  linear_combination 4 * P.on_curve

omit [NeZero (2 : K)] in
theorem one_add_y_ne_zero (P : Point d) (hx : P.x ≠ 0) : 1 + P.y ≠ 0 := fun h =>
  hx (P.x_eq_zero_of_y_sq (by rw [eq_neg_of_add_eq_zero_right h]; ring))

omit [NeZero (2 : K)] in
theorem tc_ne_zero (P : Point d) (hx : P.x ≠ 0) (hy : P.y ≠ 1) : tc P ≠ 0 :=
  div_ne_zero (one_add_y_ne_zero P hx) (sub_ne_zero.mpr (Ne.symm hy))

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
/-- `(0, −1)` is the only point with `x = 0` other than `(0, 1)`. -/
theorem y_eq_neg_one (P : Point d) (hx : P.x = 0) (hy : P.y ≠ 1) : P.y = -1 := by
  have : (P.y - 1) * (P.y + 1) = 0 := by linear_combination P.y_sq_of_x_eq_zero hx
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hy
  · linear_combination h

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
theorem equation_toW (P : Point d) (hy : P.y ≠ 1) : (W d).Equation (toX P) (toY P) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [W]
  by_cases hx : P.x = 0
  · simp [toY, toX, y_eq_neg_one P hx hy]
  · rw [toX_eq, toY_eq]
    linear_combination (-(1 - d) ^ 2 * tc P) * tw_curve P hx hy

theorem nonsingular_toW (P : Point d) (hy : P.y ≠ 1) : (W d).Nonsingular (toX P) (toY P) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero W_Δ_ne_zero).mp
    (equation_toW P hy)

omit [NeZero (2 : K)] in
theorem toX_ne_zero (P : Point d) (hx : P.x ≠ 0) (hy : P.y ≠ 1) : toX P ≠ 0 := by
  rw [toX_eq]; exact mul_ne_zero one_sub_d_ne_zero (tc_ne_zero P hx hy)

theorem toX_eq_toX (P Q : Point d) (hP : P.y ≠ 1) (hQ : Q.y ≠ 1) (h : toX P = toX Q) :
    P.y = Q.y := by
  have hP' : 1 - P.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hP)
  have hQ' : 1 - Q.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hQ)
  rw [toX, toX, div_eq_div_iff hP' hQ'] at h
  have : (1 - d) * 2 * (P.y - Q.y) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left
    (mul_ne_zero one_sub_d_ne_zero two_ne_zero))

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
private theorem one_sub_div_mul {A B : K} (hB : B ≠ 0) : (1 - A / B) * B = B - A := by
  field_simp

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
private theorem one_add_div_mul {A B : K} (hB : B ≠ 0) : (1 + A / B) * B = B + A := by
  field_simp

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
/-- Cancels a common nonzero factor `c` from `a·(u·c) = b·(v·c)`. -/
private theorem eq_of_cleared {a b c N Dn u v : K} (hc : c ≠ 0) (h : a * N = b * Dn)
    (hN : N = u * c) (hD : Dn = v * c) : a * u = b * v :=
  mul_right_cancel₀ hc (by rw [mul_assoc, mul_assoc, ← hN, ← hD]; exact h)

section SumTW

variable (P Q : Point d) (hPx : P.x ≠ 0) (hQx : Q.x ≠ 0) (hPy : P.y ≠ 1) (hQy : Q.y ≠ 1)
include hPx hQx hPy hQy

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
/-- The numerator and denominator of `t` of the Edwards sum, in `t, w` coordinates and scaled by
`M = w₁w₂(t₁ + 1)(t₂ + 1)`. -/
theorem sum_y_tw :
    2 * (wc P * wc Q) * (tc P + tc Q) + (tc P + 1) * (tc Q + 1) - d * (tc P - 1) * (tc Q - 1) =
      (1 - d * P.x * Q.x * P.y * Q.y - (P.y * Q.y - P.x * Q.x)) *
        (wc P * wc Q * (tc P + 1) * (tc Q + 1)) ∧
    2 * (wc P * wc Q) * (tc P * tc Q + 1) - (tc P + 1) * (tc Q + 1) - d * (tc P - 1) * (tc Q - 1) =
      (1 - d * P.x * Q.x * P.y * Q.y + (P.y * Q.y - P.x * Q.x)) *
        (wc P * wc Q * (tc P + 1) * (tc Q + 1)) := by
  obtain ⟨x1, y1, h1⟩ := P
  obtain ⟨x2, y2, h2⟩ := Q
  simp only [tc, wc] at *
  have h1' : 1 - y1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hPy)
  have h2' : 1 - y2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hQy)
  constructor <;> field_simp <;> ring

omit [hd : Fact (¬IsSquare d)] [NeZero (2 : K)] in
/-- The numerator and denominator of `x` of the Edwards sum, likewise. -/
theorem sum_x_tw :
    wc Q * (tc P + 1) * (tc Q - 1) + wc P * (tc P - 1) * (tc Q + 1) =
      (P.x * Q.y + P.y * Q.x) * (wc P * wc Q * (tc P + 1) * (tc Q + 1)) ∧
    wc P * wc Q * (tc P + 1) * (tc Q + 1) + d * (tc P - 1) * (tc Q - 1) =
      (1 + d * P.x * Q.x * P.y * Q.y) * (wc P * wc Q * (tc P + 1) * (tc Q + 1)) := by
  obtain ⟨x1, y1, h1⟩ := P
  obtain ⟨x2, y2, h2⟩ := Q
  simp only [tc, wc] at *
  have h1' : 1 - y1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hPy)
  have h2' : 1 - y2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hQy)
  constructor <;> field_simp <;> ring

omit [hd : Fact (¬IsSquare d)] in
theorem scale_ne_zero : wc P * wc Q * (tc P + 1) * (tc Q + 1) ≠ 0 := by
  have h1' : 1 - P.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hPy)
  have h2' : 1 - Q.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hQy)
  have e1 : tc P + 1 = 2 / (1 - P.y) := by rw [tc]; field_simp; ring
  have e2 : tc Q + 1 = 2 / (1 - Q.y) := by rw [tc]; field_simp; ring
  rw [e1, e2, wc, wc]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hPx) (inv_ne_zero hQx))
    (div_ne_zero two_ne_zero h1')) (div_ne_zero two_ne_zero h2')

end SumTW

section Map

variable [DecidableEq K]

open WeierstrassCurve.Affine

/-- The map onto the Weierstrass model. -/
def toW (P : Point d) : (W d).Point :=
  if h : P.y = 1 then 0 else .some (toX P) (toY P) (nonsingular_toW P h)

theorem toW_of_ne (P : Point d) (h : P.y ≠ 1) :
    toW P = .some (toX P) (toY P) (nonsingular_toW P h) := dif_neg h

theorem toW_of_eq (P : Point d) (h : P.y = 1) : toW P = 0 := dif_pos h

theorem toW_zero : toW (0 : Point d) = 0 := dif_pos rfl

/-- The image of a point, recognized from coordinates `X, Y` satisfying `X·(1 − y) = (1 − d)(1 + y)`
and `Y·x = 2X`. -/
theorem toW_eq_some (P : Point d) {X Y : K} (h : (W d).Nonsingular X Y)
    (hX : X * (1 - P.y) = (1 - d) * (1 + P.y)) (hY : Y * P.x = 2 * X) :
    toW P = .some X Y h := by
  have hy : P.y ≠ 1 := by
    intro e
    rw [e] at hX
    have : (1 - d) * 2 = 0 := by linear_combination -hX
    exact mul_ne_zero one_sub_d_ne_zero two_ne_zero this
  have hy' : 1 - P.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hXeq : X = toX P := by rw [toX, eq_div_iff hy']; exact hX
  subst hXeq
  have hYeq : Y = toY P := by
    by_cases hx : P.x = 0
    · have hX0 : toX P = 0 := by simp [toX, y_eq_neg_one P hx hy]
      have := (WeierstrassCurve.Affine.equation_iff _ _).mp h.1
      simp only [W, hX0] at this
      simp [toY, hX0, pow_eq_zero_iff] at this ⊢
      simpa using this
    · rw [toY, eq_div_iff hx]; exact hY
  subst hYeq
  exact toW_of_ne P hy

theorem toW_injective : Function.Injective (toW : Point d → (W d).Point) := by
  intro P Q hPQ
  by_cases hP : P.y = 1
  · by_cases hQ : Q.y = 1
    · exact Point.ext (by rw [P.x_eq_zero_of_y_sq (by simp [hP]),
        Q.x_eq_zero_of_y_sq (by simp [hQ])]) (hP.trans hQ.symm)
    · rw [toW_of_eq P hP, toW_of_ne Q hQ] at hPQ
      exact absurd hPQ.symm (Point.some_ne_zero _)
  · by_cases hQ : Q.y = 1
    · rw [toW_of_eq Q hQ, toW_of_ne P hP] at hPQ
      exact absurd hPQ (Point.some_ne_zero _)
    rw [toW_of_ne P hP, toW_of_ne Q hQ, Point.some.injEq] at hPQ
    obtain ⟨hX, hY⟩ := hPQ
    have hP' : 1 - P.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hP)
    have hQ' : 1 - Q.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hQ)
    have hy : P.y = Q.y := by
      rw [toX, toX, div_eq_div_iff hP' hQ'] at hX
      have : (1 - d) * 2 * (P.y - Q.y) = 0 := by linear_combination hX
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left
        (mul_ne_zero one_sub_d_ne_zero two_ne_zero))
    refine Point.ext ?_ hy
    by_cases hPx : P.x = 0
    · have hQx : Q.x = 0 := Q.x_eq_zero_of_y_sq (by rw [← hy]; exact P.y_sq_of_x_eq_zero hPx)
      rw [hPx, hQx]
    · have hQx : Q.x ≠ 0 := fun h =>
        hPx (P.x_eq_zero_of_y_sq (by rw [hy]; exact Q.y_sq_of_x_eq_zero h))
      have hX0 : toX P ≠ 0 :=
        div_ne_zero (mul_ne_zero one_sub_d_ne_zero (one_add_y_ne_zero P hPx)) hP'
      rw [toY, toY, ← hX, div_eq_div_iff hPx hQx] at hY
      exact (mul_left_cancel₀ (mul_ne_zero two_ne_zero hX0) hY).symm



/-- The image of a sum of two points with distinct `y`, neither `(0, ±1)`. -/
theorem toW_add_of_y_ne (P Q : Point d) (hPx : P.x ≠ 0) (hQx : Q.x ≠ 0) (hPy : P.y ≠ 1)
    (hQy : Q.y ≠ 1) (hy : P.y ≠ Q.y) : toW (P + Q) = toW P + toW Q := by
  have hX : toX P ≠ toX Q := fun h => hy (toX_eq_toX P Q hPy hQy h)
  have htP := tw_curve P hPx hPy
  have htQ := tw_curve Q hQx hQy
  have htt : tc P - tc Q ≠ 0 := fun h => hX (by rw [toX_eq, toX_eq, sub_eq_zero.mp h])
  have hl := div_mul_cancel₀ (toY P - toY Q) (sub_ne_zero.mpr hX)
  rw [toW_of_ne P hPy, toW_of_ne Q hQy, Point.add_of_X_ne hX]
  apply toW_eq_some
  all_goals
    simp only [addY, negY, negAddY, addX, slope_of_X_ne hX, W]
    rw [toX_eq, toX_eq, toY_eq, toY_eq] at hl ⊢
    generalize (2 * (1 - d) * tc P * wc P - 2 * (1 - d) * tc Q * wc Q) /
      ((1 - d) * tc P - (1 - d) * tc Q) = l at hl ⊢
    replace hl : l * (tc P - tc Q) = 2 * (tc P * wc P - tc Q * wc Q) :=
      mul_left_cancel₀ (one_sub_d_ne_zero (d := d)) (by linear_combination hl)
    have hne : (256 * tc P ^ 2 * tc Q ^ 2 * (tc P - tc Q) ^ 2 : K) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (two_pow_ne 8 (by norm_num))
        (pow_ne_zero 2 (tc_ne_zero P hPx hPy))) (pow_ne_zero 2 (tc_ne_zero Q hQx hQy)))
        (pow_ne_zero 2 htt)
  · have key := sub_eq_zero.mp ((mul_eq_zero.mp (add_X_poly htP htQ hl)).resolve_left hne)
    obtain ⟨hD, hN⟩ := sum_y_tw P Q hPx hQx hPy hQy
    rw [← one_sub_div_mul (one_sub_ne_zero P Q)] at hD
    rw [← one_add_div_mul (one_sub_ne_zero P Q)] at hN
    have := eq_of_cleared (mul_ne_zero (one_sub_ne_zero P Q) (scale_ne_zero P Q hPx hQx hPy hQy))
      key (hD.trans (mul_assoc _ _ _)) (hN.trans (mul_assoc _ _ _))
    simp only [Point.add_y]
    linear_combination this
  · have hne : (4096 * tc P ^ 3 * tc Q ^ 3 * (tc P - tc Q) ^ 3 : K) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (two_pow_ne 12 (by norm_num))
        (pow_ne_zero 3 (tc_ne_zero P hPx hPy))) (pow_ne_zero 3 (tc_ne_zero Q hQx hQy)))
        (pow_ne_zero 3 htt)
    have key := sub_eq_zero.mp ((mul_eq_zero.mp (add_Y_poly htP htQ hl)).resolve_left hne)
    obtain ⟨hN, hD⟩ := sum_x_tw P Q hPx hQx hPy hQy
    rw [← div_mul_cancel₀ (P.x * Q.y + P.y * Q.x) (one_add_ne_zero P Q)] at hN
    have := eq_of_cleared (mul_ne_zero (one_add_ne_zero P Q) (scale_ne_zero P Q hPx hQx hPy hQy))
      key (hN.trans (mul_assoc _ _ _)) (hD.trans (one_mul _).symm)
    simp only [Point.add_x]
    linear_combination this

/-- The image of a point added to itself, the point not `(0, ±1)`. -/
theorem toW_double (P : Point d) (hPx : P.x ≠ 0) (hPy : P.y ≠ 1) :
    toW (P + P) = toW P + toW P := by
  have ht := tc_ne_zero P hPx hPy
  have hw : wc P ≠ 0 := inv_ne_zero hPx
  have hY : toY P ≠ (W d).negY (toX P) (toY P) := by
    simp only [negY, W, toY_eq]
    intro h
    have : 2 * 2 * (1 - d) * tc P * wc P = 0 := by linear_combination h
    simp [two_ne_zero, one_sub_d_ne_zero, ht, hw] at this
  have htP := tw_curve P hPx hPy
  have hl := div_mul_cancel₀ (3 * toX P ^ 2 + 2 * (W d).a₂ * toX P + (W d).a₄ - (W d).a₁ * toY P)
    (sub_ne_zero.mpr hY)
  rw [← slope_of_Y_ne rfl hY] at hl
  rw [toW_of_ne P hPy, Point.add_self_of_Y_ne hY]
  apply toW_eq_some
  all_goals
    generalize (W d).slope (toX P) (toX P) (toY P) (toY P) = l at hl ⊢
    simp only [addY, negY, negAddY, addX, W, toX_eq, toY_eq] at hl ⊢
    replace hl : l * 4 * tc P * wc P = (1 - d) * (3 * tc P ^ 2 + 1) + 4 * (1 + d) * tc P :=
      mul_left_cancel₀ (one_sub_d_ne_zero (d := d)) (by linear_combination hl)
  · have key := sub_eq_zero.mp ((mul_eq_zero.mp (double_X_poly htP hl)).resolve_left
      (mul_ne_zero (mul_ne_zero (two_pow_ne 8 (by norm_num)) (pow_ne_zero 2 hw))
        (pow_ne_zero 4 ht)))
    obtain ⟨hD, hN⟩ := sum_y_tw P P hPx hPx hPy hPy
    rw [← one_sub_div_mul (one_sub_ne_zero P P)] at hD
    rw [← one_add_div_mul (one_sub_ne_zero P P)] at hN
    have := eq_of_cleared (mul_ne_zero (one_sub_ne_zero P P) (scale_ne_zero P P hPx hPx hPy hPy))
      key (hD.trans (mul_assoc _ _ _)) (hN.trans (mul_assoc _ _ _))
    simp only [Point.add_y]
    linear_combination this
  · have key := sub_eq_zero.mp ((mul_eq_zero.mp (double_Y_poly htP hl)).resolve_left
      (mul_ne_zero (mul_ne_zero (two_pow_ne 10 (by norm_num)) (pow_ne_zero 3 hw))
        (pow_ne_zero 5 ht)))
    obtain ⟨hN, hD⟩ := sum_x_tw P P hPx hPx hPy hPy
    rw [← div_mul_cancel₀ (P.x * P.y + P.y * P.x) (one_add_ne_zero P P)] at hN
    have := eq_of_cleared (mul_ne_zero (one_add_ne_zero P P) (scale_ne_zero P P hPx hPx hPy hPy))
      key (hN.trans (mul_assoc _ _ _)) (hD.trans (one_mul _).symm)
    simp only [Point.add_x]
    linear_combination this

/-- The image of `(0, −1) + Q` for `Q` not `(0, ±1)`. -/
theorem toW_add_of_x_eq_zero (P Q : Point d) (hPx : P.x = 0) (hPy : P.y ≠ 1) (hQx : Q.x ≠ 0) :
    toW (P + Q) = toW P + toW Q := by
  have hP' := y_eq_neg_one P hPx hPy
  have hQy : Q.y ≠ 1 := fun h => hQx (Q.x_eq_zero_of_y_sq (by rw [h]; ring))
  have hX0 : toX P = 0 := by simp [toX, hP']
  have hY0 : toY P = 0 := by simp [toY, hX0]
  have hX : toX P ≠ toX Q := by rw [hX0]; exact (toX_ne_zero Q hQx hQy).symm
  have ht := tc_ne_zero Q hQx hQy
  have htQ := tw_curve Q hQx hQy
  have hty : 1 + Q.y = tc Q * (1 - Q.y) := by
    rw [tc, div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hQy))]
  have hwx : wc Q * Q.x = 1 := inv_mul_cancel₀ hQx
  have hl : (W d).slope (toX P) (toX Q) (toY P) (toY Q) = 2 * wc Q := by
    rw [slope_of_X_ne hX, div_eq_iff (sub_ne_zero.mpr hX), hX0, hY0, toX_eq, toY_eq]
    ring
  rw [toW_of_ne P hPy, toW_of_ne Q hQy, Point.add_of_X_ne hX]
  apply toW_eq_some
  all_goals simp only [hl]
  all_goals simp only [addY, negY, negAddY, addX, W, hX0, hY0, toX_eq, Point.add_x,
    Point.add_y, hPx, hP']
  · simp only [mul_zero, zero_mul, sub_zero, neg_mul, one_mul, add_zero, div_one]
    linear_combination (-(1 - Q.y)) * htQ + (4 * wc Q ^ 2 - 2 * (1 + d) - (1 - d) * tc Q) * hty
  · simp only [mul_zero, zero_mul, sub_zero, neg_mul, one_mul, add_zero, div_one]
    linear_combination (2 * ((2 * wc Q) ^ 2 - 2 * (1 + d) - (1 - d) * tc Q)) * hwx

/-- The image of `P + (−P)`, the point not `(0, ±1)`. -/
theorem toW_add_neg (P : Point d) (hPy : P.y ≠ 1) : toW (P + -P) = toW P + toW (-P) := by
  rw [Point.add_comm', Point.neg_add_cancel', toW_zero, toW_of_ne P hPy, toW_of_ne (-P) hPy]
  exact (Point.add_of_Y_eq rfl (by simp [negY, W, toY, div_neg]; rfl)).symm

theorem toW_add (P Q : Point d) : toW (P + Q) = toW P + toW Q := by
  by_cases hPy : P.y = 1
  · obtain rfl : P = 0 := Point.ext (P.x_eq_zero_of_y_sq (by rw [hPy]; ring)) hPy
    rw [Point.zero_add', toW_zero, zero_add]
  by_cases hQy : Q.y = 1
  · obtain rfl : Q = 0 := Point.ext (Q.x_eq_zero_of_y_sq (by rw [hQy]; ring)) hQy
    rw [Point.add_comm', Point.zero_add', toW_zero, add_zero]
  by_cases hPx : P.x = 0
  · by_cases hQx : Q.x = 0
    · obtain rfl : Q = -P := Point.ext (by simp [hPx, hQx])
        (by simp [y_eq_neg_one P hPx hPy, y_eq_neg_one Q hQx hQy])
      exact toW_add_neg P hPy
    · exact toW_add_of_x_eq_zero P Q hPx hPy hQx
  by_cases hQx : Q.x = 0
  · rw [Point.add_comm', toW_add_of_x_eq_zero Q P hQx hQy hPx, add_comm]
  by_cases hy : P.y = Q.y
  · have : (Q.x - P.x) * (Q.x + P.x) * (1 - d * P.y ^ 2) = 0 := by
      linear_combination Q.on_curve - P.on_curve - (d * Q.x ^ 2 - 1) * (P.y + Q.y) * hy
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · obtain rfl : Q = P := Point.ext (sub_eq_zero.mp h) hy.symm
        exact toW_double Q hQx hQy
      · obtain rfl : Q = -P := Point.ext (eq_neg_of_add_eq_zero_left h) hy.symm
        exact toW_add_neg P hPy
    · exact absurd h (one_sub_d_mul_sq_ne_zero _)
  · exact toW_add_of_y_ne P Q hPx hQx hPy hQy hy

end Map

/-! ### The group -/

instance : AddCommGroup (Point d) where
  add_assoc P Q R := by
    classical
    exact toW_injective (by rw [toW_add, toW_add, toW_add, toW_add, add_assoc])
  zero_add := Point.zero_add'
  add_zero P := by rw [Point.add_comm', Point.zero_add']
  add_comm := Point.add_comm'
  neg_add_cancel := Point.neg_add_cancel'
  nsmul := nsmulRec
  zsmul := zsmulRec

end Zerc20.Edwards
