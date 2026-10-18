module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Bessel function `J₀`

`J₀(x) = (2π)⁻¹ ∫₀^{2π} cos (x cos θ) dθ`, its first two derivatives as angular
integrals, and the differential equation `x J₀'' + J₀' + x J₀ = 0`.
-/

@[expose] public section

namespace Erdos173

open Real

/-- The Bessel function `J₀(x) = (2π)⁻¹ ∫₀^{2π} cos (x cos θ) dθ`. -/
noncomputable def besselJ0 (x : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)

/-- The derivative `J₀'(x) = -(2π)⁻¹ ∫₀^{2π} cos θ sin (x cos θ) dθ`. -/
noncomputable def besselJ0Deriv (x : ℝ) : ℝ :=
  -((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos θ * sin (x * cos θ))

/-- The second derivative `J₀''(x) = -(2π)⁻¹ ∫₀^{2π} cos² θ cos (x cos θ) dθ`. -/
noncomputable def besselJ0Deriv2 (x : ℝ) : ℝ :=
  -((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ))

/-- An angular average of a function bounded by `1` is bounded by `1`. -/
lemma abs_inv_two_pi_mul_integral_le_one {f : ℝ → ℝ} (hf : ∀ θ, |f θ| ≤ 1) :
    |(2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f θ| ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (C := 1) (f := f) fun θ _ => hf θ
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos two_pi_pos, one_mul] at h
  rw [abs_mul, abs_of_pos (inv_pos.mpr two_pi_pos)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, f θ| ≤ (2 * π)⁻¹ * (2 * π) := by gcongr
    _ = 1 := inv_mul_cancel₀ two_pi_pos.ne'

/-- `|J₀| ≤ 1`. -/
theorem abs_besselJ0_le_one (x : ℝ) : |besselJ0 x| ≤ 1 :=
  abs_inv_two_pi_mul_integral_le_one fun _ => abs_cos_le_one _

/-- `|J₀'| ≤ 1`. -/
theorem abs_besselJ0Deriv_le_one (x : ℝ) : |besselJ0Deriv x| ≤ 1 := by
  rw [besselJ0Deriv, abs_neg]
  refine abs_inv_two_pi_mul_integral_le_one fun θ => ?_
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)).trans (abs_sin_le_one _)

/-- Differentiation under the integral: `J₀'` is the derivative of `J₀`. -/
theorem hasDerivAt_besselJ0 (x : ℝ) : HasDerivAt besselJ0 (besselJ0Deriv x) x := by
  have h := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ => cos (x * cos θ)) (F' := fun x θ => -(cos θ * sin (x * cos θ)))
    (μ := MeasureTheory.volume) (x₀ := x) (bound := fun _ => 1) (a := 0) (b := 2 * π)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (by fun_prop : Continuous fun θ => cos (x * cos θ))
      |>.aestronglyMeasurable)
    ((by fun_prop : Continuous fun θ => cos (x * cos θ)).intervalIntegrable _ _)
    (by fun_prop : Continuous fun θ => -(cos θ * sin (x * cos θ))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ y _ => by
      rw [norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)).trans (abs_sin_le_one _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ y _ => by
      convert ((hasDerivAt_mul_const (cos θ)).cos : HasDerivAt (fun y => cos (y * cos θ)) _ y)
        using 1
      ring)).2.const_mul (2 * π)⁻¹
  rwa [intervalIntegral.integral_neg, mul_neg] at h

/-- Differentiation under the integral: `J₀''` is the derivative of `J₀'`. -/
theorem hasDerivAt_besselJ0Deriv (x : ℝ) : HasDerivAt besselJ0Deriv (besselJ0Deriv2 x) x := by
  exact ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ => cos θ * sin (x * cos θ)) (F' := fun x θ => cos θ ^ 2 * cos (x * cos θ))
    (μ := MeasureTheory.volume) (x₀ := x) (bound := fun _ => 1) (a := 0) (b := 2 * π)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous fun θ => cos θ * sin (x * cos θ)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun θ => cos θ * sin (x * cos θ)).intervalIntegrable _ _)
    (by fun_prop : Continuous fun θ => cos θ ^ 2 * cos (x * cos θ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ y _ => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (abs_nonneg _)
        (pow_le_one₀ (abs_nonneg _) (abs_cos_le_one _))).trans (abs_cos_le_one _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ y _ => by
      convert ((hasDerivAt_mul_const (cos θ)).sin.const_mul (cos θ) :
        HasDerivAt (fun y => cos θ * sin (y * cos θ)) _ y) using 1
      ring)).2.const_mul (2 * π)⁻¹).neg

/-- `J₀` is continuous. -/
theorem continuous_besselJ0 : Continuous besselJ0 :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_besselJ0 x).continuousAt

/-- Bessel's equation of order zero. -/
theorem besselJ0_ode (x : ℝ) : x * besselJ0Deriv2 x + besselJ0Deriv x + x * besselJ0 x = 0 := by
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * π), HasDerivAt (fun θ => sin θ * sin (x * cos θ))
      (cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)) θ := fun θ _ => by
    convert (hasDerivAt_sin θ).mul ((hasDerivAt_cos θ).const_mul x).sin using 1
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun θ =>
      cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)).intervalIntegrable _ _)
  simp only [sin_two_pi, sin_zero, zero_mul, sub_zero] at hint
  have hsplit : (∫ θ in (0 : ℝ)..2 * π,
      cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)) =
      (∫ θ in (0 : ℝ)..2 * π, cos θ * sin (x * cos θ)) -
        x * ((∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)) -
          ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ)) := by
    have hcongr : (fun θ => cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)) =
        fun θ => cos θ * sin (x * cos θ) -
          x * (cos (x * cos θ) - cos θ ^ 2 * cos (x * cos θ)) := by
      ext θ
      rw [sin_sq]
      ring
    rw [hcongr, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub] <;> exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hsplit] at hint
  simp only [besselJ0, besselJ0Deriv, besselJ0Deriv2]
  linear_combination (-(2 * π)⁻¹) * hint

end Erdos173
