module

public import Erdos173.Reduction.Plane
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The strip coloring

Color a point of `ℝ²` by the parity of `⌊y / h⌋`, where `y` is its second
coordinate and `h = √3/2`: alternating half-open horizontal strips of width `h`.
No equilateral triangle of side one is monochromatic.

Let the vertices have heights `y₀, y₁, y₂` and put `t₁ = y₁ - y₀`,
`t₂ = y₂ - y₁`. Three points at mutual distance one satisfy
`t₁² + t₂² + t₁ t₂ = 3/4 = h²`, so twice this is the sum of the squares of the
three vertical gaps `t₁, t₂, t₁ + t₂`. Two gaps longer than `h` would make that
sum exceed `2 h²`; three gaps shorter than `h` would make the identity fail.
Two vertices with equal parity lie in one strip, at vertical distance less than
`h`, or in strips at least two apart, at vertical distance more than `h`. If all
three vertices have one parity, either all three lie in one strip or at least
two pairs lie in different strips, and both are impossible.
-/

@[expose] public section

noncomputable section

open Affine
open scoped Congruent

namespace Erdos173.Strips

open Plane

/-- The Euclidean plane, as in `formal-conjectures`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The width `√3/2` of the strips. -/
def stripWidth : ℝ := √3 / 2

/-- The strips have positive width. -/
lemma stripWidth_pos : 0 < stripWidth := by
  unfold stripWidth
  positivity

/-- `(√3/2)² = 3/4`. -/
lemma stripWidth_sq : stripWidth ^ 2 = 3 / 4 := by
  rw [stripWidth, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The coloring by alternating half-open horizontal strips of width `√3/2`. -/
def stripColor (P : ℝ²) : Fin 2 :=
  if Even ⌊P 1 / stripWidth⌋ then 0 else 1

/-- Two points of one color have heights whose floors have equal parity. -/
lemma even_iff_of_stripColor_eq {P Q : ℝ²} (h : stripColor P = stripColor Q) :
    Even ⌊P 1 / stripWidth⌋ ↔ Even ⌊Q 1 / stripWidth⌋ := by
  unfold stripColor at h
  split_ifs at h with hP hQ hQ
  · exact iff_of_true hP hQ
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact iff_of_false hP hQ

/-- The equilateral triangle `(0, 1, ζ)` of side one in `ℂ`. -/
def unitTriangleC : Triangle ℝ ℂ :=
  ⟨![0, 1, ζ], by
    rw [affineIndependent_iff_not_collinear_set]
    intro hcol
    rw [collinear_iff_of_mem (p₀ := (0 : ℂ)) (by simp)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r₁, h₁⟩ := hv 1 (by simp)
    obtain ⟨r₂, h₂⟩ := hv ζ (by simp)
    have h₁re := congrArg Complex.re h₁
    have h₁im := congrArg Complex.im h₁
    have h₂im := congrArg Complex.im h₂
    simp only [vadd_eq_add, add_zero, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, zero_mul,
      sub_zero, add_zero, ζ] at h₁re h₁im h₂im
    have h3 : (0 : ℝ) < √3 / 2 := by positivity
    rcases mul_eq_zero.1 h₁im.symm with h | h
    · simp [h] at h₁re
    · rw [h, mul_zero] at h₂im
      linarith⟩

/-- The equilateral triangle of side one in `ℝ²`. -/
def unitTriangle : Triangle ℝ ℝ² :=
  unitTriangleC.map toC.symm.toLinearEquiv.toLinearMap.toAffineMap toC.symm.injective

/-- The vertices of the unit triangle are at mutual distance one. -/
lemma dist_unitTriangle {i j : Fin 3} (h : i ≠ j) :
    dist (unitTriangle.points i) (unitTriangle.points j) = 1 := by
  change dist (toC.symm (unitTriangleC.points i)) (toC.symm (unitTriangleC.points j)) = 1
  rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
  fin_cases i <;> fin_cases j <;>
    simp_all [unitTriangleC, norm_ζ, norm_one_sub_ζ, norm_ζ_sub_one]

/-- Two points at distance one, in coordinates. -/
lemma sq_add_sq_of_dist_eq_one {P Q : ℝ²} (h : dist P Q = 1) :
    (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 = 1 := by
  rw [EuclideanSpace.dist_eq, Real.sqrt_eq_one, Fin.sum_univ_two] at h
  simpa [Real.dist_eq, sq_abs] using h

/-- For unit vectors `(p, q)` and `(r, s)` at distance one, `q² + s² - q s = 3/4`. -/
lemma vertical_identity {p q r s : ℝ} (h₁ : p ^ 2 + q ^ 2 = 1) (h₂ : r ^ 2 + s ^ 2 = 1)
    (h₃ : (r - p) ^ 2 + (s - q) ^ 2 = 1) : q ^ 2 + s ^ 2 - q * s = 3 / 4 := by
  have h₄ : p * r + q * s = 1 / 2 := by linear_combination (h₁ + h₂ - h₃) / 2
  have hD : (p * s - q * r) ^ 2 = 3 / 4 := by
    linear_combination (r ^ 2 + s ^ 2) * h₁ + h₂ - (p * r + q * s + 1 / 2) * h₄
  have hs : s = q / 2 + (p * s - q * r) * p := by linear_combination (-s) * h₁ + q * h₄
  linear_combination (s - q / 2 + (p * s - q * r) * p) * hs + p ^ 2 * hD + 3 / 4 * h₁

/-- Two heights with floors of equal parity lie in one strip or in strips at least two
apart. -/
lemma strip_pair {h yi yj : ℝ} (hh : 0 < h) {i j : ℤ} (hi : i = ⌊yi / h⌋) (hj : j = ⌊yj / h⌋)
    (hij : Even i ↔ Even j) : (i = j ∧ |yi - yj| < h) ∨ (i ≠ j ∧ h ^ 2 < (yi - yj) ^ 2) := by
  have bi : (i : ℝ) * h ≤ yi := by
    rw [hi, ← le_div_iff₀ hh]
    exact Int.floor_le _
  have bi' : yi < ((i : ℝ) + 1) * h := by
    rw [hi, ← div_lt_iff₀ hh]
    exact Int.lt_floor_add_one _
  have bj : (j : ℝ) * h ≤ yj := by
    rw [hj, ← le_div_iff₀ hh]
    exact Int.floor_le _
  have bj' : yj < ((j : ℝ) + 1) * h := by
    rw [hj, ← div_lt_iff₀ hh]
    exact Int.lt_floor_add_one _
  by_cases e : i = j
  · subst e
    left
    exact ⟨rfl, abs_lt.2 ⟨by nlinarith, by nlinarith⟩⟩
  · right
    refine ⟨e, ?_⟩
    obtain ⟨r, hr⟩ := Int.even_sub.2 hij
    rcases (by omega : i + 2 ≤ j ∨ j + 2 ≤ i) with c | c
    · have c' : (i : ℝ) + 2 ≤ j := by exact_mod_cast c
      have g : h < yj - yi := by nlinarith [mul_le_mul_of_nonneg_right c' hh.le]
      nlinarith
    · have c' : (j : ℝ) + 2 ≤ i := by exact_mod_cast c
      have g : h < yi - yj := by nlinarith [mul_le_mul_of_nonneg_right c' hh.le]
      nlinarith

/-- Three heights with `t₁² + t₂² + t₁ t₂ = h²` do not have floors of one parity. -/
lemma strip_parity {h y₀ y₁ y₂ : ℝ} (hh : 0 < h)
    (hQ : (y₁ - y₀) ^ 2 + (y₂ - y₁) ^ 2 + (y₁ - y₀) * (y₂ - y₁) = h ^ 2)
    (e₁ : Even ⌊y₀ / h⌋ ↔ Even ⌊y₁ / h⌋) (e₂ : Even ⌊y₀ / h⌋ ↔ Even ⌊y₂ / h⌋) : False := by
  rcases strip_pair hh rfl rfl e₁ with ⟨k₀₁, n₀₁⟩ | ⟨k₀₁, f₀₁⟩ <;>
  rcases strip_pair hh rfl rfl (e₁.symm.trans e₂) with ⟨k₁₂, n₁₂⟩ | ⟨k₁₂, f₁₂⟩ <;>
  rcases strip_pair hh rfl rfl e₂ with ⟨k₀₂, n₀₂⟩ | ⟨k₀₂, f₀₂⟩
  · -- all three heights in one strip
    obtain ⟨a₁, a₂⟩ := abs_lt.1 n₀₁
    obtain ⟨b₁, b₂⟩ := abs_lt.1 n₁₂
    obtain ⟨c₁, c₂⟩ := abs_lt.1 n₀₂
    rcases le_or_gt 0 ((y₁ - y₀) * (y₂ - y₁)) with H | H
    · nlinarith
    · rcases le_total (y₁ - y₀) 0 with s | s <;> rcases le_total (y₁ - y₀) (y₀ - y₂) with t | t <;>
        nlinarith
  all_goals first
    | omega
    | nlinarith [sq_nonneg (y₁ - y₀), sq_nonneg (y₂ - y₁), sq_nonneg (y₂ - y₀)]

/-- No equilateral triangle of side one is monochromatic for the strip coloring. -/
theorem not_hasMonochromaticCopy_strip : ¬ HasMonochromaticCopy stripColor unitTriangle := by
  rintro ⟨T, hT, i, hi⟩
  have d : ∀ a b : Fin 3, a ≠ b → dist (T.points a) (T.points b) = 1 := fun a b h =>
    ((congruent_iff_dist_eq.1 hT) a b).trans (dist_unitTriangle h)
  have d₁ := sq_add_sq_of_dist_eq_one (d 0 1 (by decide))
  have d₂ := sq_add_sq_of_dist_eq_one (d 0 2 (by decide))
  have d₃ := sq_add_sq_of_dist_eq_one (d 1 2 (by decide))
  have hv := vertical_identity (p := T.points 1 0 - T.points 0 0)
    (q := T.points 1 1 - T.points 0 1) (r := T.points 2 0 - T.points 0 0)
    (s := T.points 2 1 - T.points 0 1) (by linear_combination d₁) (by linear_combination d₂)
    (by linear_combination d₃)
  exact strip_parity stripWidth_pos (by rw [stripWidth_sq]; linear_combination hv)
    (even_iff_of_stripColor_eq ((hi 0).trans (hi 1).symm))
    (even_iff_of_stripColor_eq ((hi 0).trans (hi 2).symm))

end Erdos173.Strips

end
