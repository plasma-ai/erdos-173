module

public import Erdos173.Bessel.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The shape of `J₀`

Qualitative facts that turn finitely many values of `J₀` and `J₁ = -J₀'` into bounds
on intervals:

* `|J₀''| ≤ 1/2`, since `J₀''` averages `cos² θ cos (x cos θ)` and `cos²` averages
  to `1/2`; hence `J₀'` is `1/2`-Lipschitz, while `J₀` is `1`-Lipschitz;
* `J₁ ≥ 0` on `[0, π]`, since `cos θ sin (t cos θ) ≥ 0` there;
* `J₀` is monotone where `J₀'` has a sign;
* the energy `J₀² + J₀'²` is nonincreasing on `(0, ∞)`, since by Bessel's equation
  its derivative is `-2 J₀'²/t`.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open Real Set

/-- `|J₀''| ≤ 1/2`. -/
theorem abs_besselJ0Deriv2_le_half (x : ℝ) : |besselJ0Deriv2 x| ≤ 1 / 2 := by
  have hπ := two_pi_pos
  have hle : |∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ)| ≤
      ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 := by
    refine (intervalIntegral.abs_integral_le_integral_abs hπ.le).trans
      (intervalIntegral.integral_mono_on hπ.le ?_ ?_ fun θ _ => ?_)
    · exact (by fun_prop : Continuous fun θ =>
        |cos θ ^ 2 * cos (x * cos θ)|).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ => cos θ ^ 2).intervalIntegrable _ _
    · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (sq_nonneg _) (abs_cos_le_one _)
  rw [integral_cos_sq] at hle
  simp only [cos_two_pi, sin_two_pi, cos_zero, sin_zero, mul_zero, sub_zero,
    zero_add] at hle
  rw [besselJ0Deriv2, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hπ)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ)|
      ≤ (2 * π)⁻¹ * ((2 * π) / 2) := by gcongr
    _ = 1 / 2 := by field_simp

/-- `J₀'` is `1/2`-Lipschitz. -/
theorem abs_besselJ0Deriv_sub_le (s t : ℝ) :
    |besselJ0Deriv t - besselJ0Deriv s| ≤ |t - s| / 2 := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (G := ℝ)
    (f := besselJ0Deriv) (s := univ) (x := s) (y := t) (C := 1 / 2)
    (fun x _ => (hasDerivAt_besselJ0Deriv x).hasDerivWithinAt)
    (fun x _ => abs_besselJ0Deriv2_le_half x) convex_univ (mem_univ _) (mem_univ _)
  simp only [Real.norm_eq_abs] at h
  linarith

/-- `J₀` is `1`-Lipschitz. -/
theorem abs_besselJ0_sub_le (s t : ℝ) : |besselJ0 t - besselJ0 s| ≤ |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (G := ℝ)
    (f := besselJ0) (s := univ) (x := s) (y := t) (C := 1)
    (fun x _ => (hasDerivAt_besselJ0 x).hasDerivWithinAt)
    (fun x _ => abs_besselJ0Deriv_le_one x) convex_univ (mem_univ _) (mem_univ _)
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- `J₀' = -J₁ ≤ 0` on `[0, π]`. -/
theorem besselJ0Deriv_nonpos_of_le_pi {t : ℝ} (ht : 0 ≤ t) (htπ : t ≤ π) :
    besselJ0Deriv t ≤ 0 := by
  rw [besselJ0Deriv, neg_nonpos]
  refine mul_nonneg (inv_nonneg.mpr two_pi_pos.le)
    (intervalIntegral.integral_nonneg two_pi_pos.le fun θ _ => ?_)
  have h1 := neg_one_le_cos θ
  have h2 := cos_le_one θ
  rcases le_or_gt 0 (cos θ) with hc | hc
  · exact mul_nonneg hc (sin_nonneg_of_nonneg_of_le_pi (mul_nonneg ht hc) (by nlinarith))
  · exact mul_nonneg_of_nonpos_of_nonpos hc.le
      (sin_nonpos_of_nonpos_of_neg_pi_le (mul_nonpos_of_nonneg_of_nonpos ht hc.le)
        (by nlinarith))

/-- `J₀` decreases where `J₀' ≤ 0`. -/
theorem antitoneOn_besselJ0 {a b : ℝ} (h : ∀ t ∈ Icc a b, besselJ0Deriv t ≤ 0) :
    AntitoneOn besselJ0 (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) continuous_besselJ0.continuousOn
    (fun t _ => (hasDerivAt_besselJ0 t).hasDerivWithinAt) fun t ht => h t (interior_subset ht)

/-- `J₀` increases where `J₀' ≥ 0`. -/
theorem monotoneOn_besselJ0 {a b : ℝ} (h : ∀ t ∈ Icc a b, 0 ≤ besselJ0Deriv t) :
    MonotoneOn besselJ0 (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) continuous_besselJ0.continuousOn
    (fun t _ => (hasDerivAt_besselJ0 t).hasDerivWithinAt) fun t ht => h t (interior_subset ht)

/-- The energy `J₀² + J₀'²`. -/
def besselEnergy (t : ℝ) : ℝ :=
  besselJ0 t ^ 2 + besselJ0Deriv t ^ 2

/-- The energy is nonincreasing on `[s, ∞)` for `s > 0`. -/
theorem antitoneOn_besselEnergy {s : ℝ} (hs : 0 < s) : AntitoneOn besselEnergy (Ici s) := by
  have hd (t : ℝ) : HasDerivAt besselEnergy
      (2 * besselJ0 t * besselJ0Deriv t + 2 * besselJ0Deriv t * besselJ0Deriv2 t) t := by
    convert ((hasDerivAt_besselJ0 t).pow 2).add ((hasDerivAt_besselJ0Deriv t).pow 2) using 1
    · rfl
    · norm_num
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici s)
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).hasDerivWithinAt)
    fun t ht => ?_
  rw [interior_Ici] at ht
  have ht0 : 0 < t := hs.trans ht
  have key : t * (2 * besselJ0 t * besselJ0Deriv t + 2 * besselJ0Deriv t * besselJ0Deriv2 t) =
      -2 * besselJ0Deriv t ^ 2 := by
    linear_combination (2 * besselJ0Deriv t) * besselJ0_ode t
  nlinarith [sq_nonneg (besselJ0Deriv t)]

/-- `J₀(t)² ≤ J₀(s)² + J₀'(s)²` for `0 < s ≤ t`. -/
theorem sq_besselJ0_le_energy {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    besselJ0 t ^ 2 ≤ besselJ0 s ^ 2 + besselJ0Deriv s ^ 2 := by
  have h := antitoneOn_besselEnergy hs self_mem_Ici hst hst
  simp only [besselEnergy] at h
  nlinarith [sq_nonneg (besselJ0Deriv t)]

end Erdos173

end
