module

public import Erdos173.Bessel.Basic
public import Erdos173.Bessel.Taylor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The power series of `J₀` and `J₁`

The moments `∫₀^{2π} cos^{2k} θ dθ = 2π (2k)!/(4^k k!²)` turn the Taylor bounds for
`cos` and `sin` into enclosures of `J₀` and `J₁ = -J₀'` by the partial sums of their
power series:

* `|J₀(x) - ∑_{k<N} (-1)^k (x/2)^{2k}/k!²| ≤ (x/2)^{2N}/N!²`,
* `|J₁(x) - ∑_{k<N} (-1)^k (x/2)^{2k+1}/(k!(k+1)!)| ≤ |x/2|^{2N+1}/(N!(N+1)!)`.

Both errors are the absolute value of the first omitted term of the series.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open Real Finset

/-- The partial sum `∑_{k<N} (-1)^k (x/2)^{2k}/k!²` of the power series of `J₀`. -/
def j0Partial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * (x / 2) ^ (2 * k) / (k.factorial : ℝ) ^ 2

/-- The partial sum `∑_{k<N} (-1)^k (x/2)^{2k+1}/(k!(k+1)!)` of the power series of `J₁`. -/
def j1Partial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range N,
    (-1) ^ k * (x / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))

/-- `∫₀^{2π} cos^{2k} θ dθ = 2π (2k)!/(4^k k!²)`. -/
lemma integral_cos_pow_two_mul (k : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, cos θ ^ (2 * k) =
      2 * π * ((2 * k).factorial : ℝ) / (4 ^ k * (k.factorial : ℝ) ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, integral_cos_pow, ih]
    simp only [sin_zero, sin_two_pi, mul_zero, sub_zero, zero_div, zero_add]
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    push_cast
    field_simp
    ring

/-- The even moment against the coefficient of `y^{2k}` in `cos`. -/
lemma integral_even_term (k : ℕ) (y : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, y ^ (2 * k) / ((2 * k).factorial : ℝ) * cos θ ^ (2 * k) =
      2 * π * ((y / 2) ^ (2 * k) / (k.factorial : ℝ) ^ 2) := by
  rw [intervalIntegral.integral_const_mul, integral_cos_pow_two_mul, div_pow, pow_mul,
    pow_mul 2]
  field_simp
  norm_num

/-- The even moment against the coefficient of `y^{2k+1}` in `sin`, times `cos θ`. -/
lemma integral_odd_term (k : ℕ) (y : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π,
      y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) * cos θ ^ (2 * (k + 1)) =
      2 * π * ((y / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))) := by
  have h2 : (2 : ℝ) ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [intervalIntegral.integral_const_mul, integral_cos_pow_two_mul,
    show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1),
    Nat.factorial_succ k, div_pow, h2, pow_succ (4 : ℝ)]
  push_cast
  field_simp
  ring

/-- `C_N` is continuous. -/
lemma continuous_cosTaylor (N : ℕ) : Continuous (cosTaylor N) := by
  unfold cosTaylor
  fun_prop

/-- `S_N` is continuous. -/
lemma continuous_sinTaylor (N : ℕ) : Continuous (sinTaylor N) := by
  unfold sinTaylor
  fun_prop

/-- The angular average of `C_N(x cos θ)` is the partial sum of `J₀`. -/
lemma integral_cosTaylor (N : ℕ) (x : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, cosTaylor N (x * cos θ) = 2 * π * j0Partial N x := by
  simp only [cosTaylor, j0Partial, mul_sum]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun θ =>
      (-1) ^ k * (x * cos θ) ^ (2 * k) / ((2 * k).factorial : ℝ)).intervalIntegrable _ _]
  refine sum_congr rfl fun k _ => ?_
  have h : (fun θ => (-1) ^ k * (x * cos θ) ^ (2 * k) / ((2 * k).factorial : ℝ)) =
      fun θ => (-1) ^ k * (x ^ (2 * k) / ((2 * k).factorial : ℝ) * cos θ ^ (2 * k)) := by
    ext θ
    ring
  rw [h, intervalIntegral.integral_const_mul, integral_even_term]
  ring

/-- The angular average of `cos θ S_N(x cos θ)` is the partial sum of `J₁`. -/
lemma integral_cos_mul_sinTaylor (N : ℕ) (x : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, cos θ * sinTaylor N (x * cos θ) = 2 * π * j1Partial N x := by
  simp only [sinTaylor, j1Partial, mul_sum]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun θ =>
      cos θ * ((-1) ^ k * (x * cos θ) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ))).intervalIntegrable _ _]
  refine sum_congr rfl fun k _ => ?_
  have h : (fun θ => cos θ * ((-1) ^ k * (x * cos θ) ^ (2 * k + 1) /
      ((2 * k + 1).factorial : ℝ))) = fun θ => (-1) ^ k *
        (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) * cos θ ^ (2 * (k + 1))) := by
    ext θ
    ring
  rw [h, intervalIntegral.integral_const_mul, integral_odd_term]
  ring

/-- `J₀` is enclosed by the partial sums of its power series. -/
theorem abs_besselJ0_sub_j0Partial_le (N : ℕ) (x : ℝ) :
    |besselJ0 x - j0Partial N x| ≤ (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2 := by
  have hπ := two_pi_pos
  have hc := continuous_cosTaylor N
  have hdiff : besselJ0 x - j0Partial N x = (2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, (cos (x * cos θ) - cosTaylor N (x * cos θ)) := by
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun θ =>
      cos (x * cos θ)).intervalIntegrable _ _) ((by fun_prop : Continuous fun θ =>
        cosTaylor N (x * cos θ)).intervalIntegrable _ _), integral_cosTaylor, besselJ0,
      mul_sub, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]
  have hle : |∫ θ in (0 : ℝ)..2 * π, (cos (x * cos θ) - cosTaylor N (x * cos θ))| ≤
      ∫ θ in (0 : ℝ)..2 * π, x ^ (2 * N) / ((2 * N).factorial : ℝ) * cos θ ^ (2 * N) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hπ.le).trans
      (intervalIntegral.integral_mono_on hπ.le ?_ ?_ fun θ _ => ?_)
    · exact (by fun_prop : Continuous fun θ =>
        |cos (x * cos θ) - cosTaylor N (x * cos θ)|).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ =>
        x ^ (2 * N) / ((2 * N).factorial : ℝ) * cos θ ^ (2 * N)).intervalIntegrable _ _
    · have h := abs_cos_sub_cosTaylor_le N (x * cos θ)
      rw [(even_two_mul N).pow_abs, mul_pow] at h
      exact h.trans_eq (by ring)
  rw [integral_even_term] at hle
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.mpr hπ)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, (cos (x * cos θ) - cosTaylor N (x * cos θ))|
      ≤ (2 * π)⁻¹ * (2 * π * ((x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2)) := by gcongr
    _ = (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2 := by field_simp

/-- `J₁ = -J₀'` is enclosed by the partial sums of its power series. -/
theorem abs_besselJ0Deriv_add_j1Partial_le (N : ℕ) (x : ℝ) :
    |besselJ0Deriv x + j1Partial N x| ≤
      |x / 2| ^ (2 * N + 1) / ((N.factorial : ℝ) * ((N + 1).factorial : ℝ)) := by
  have hπ := two_pi_pos
  have hs := continuous_sinTaylor N
  have hdiff : besselJ0Deriv x + j1Partial N x = -((2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun θ =>
      cos θ * sin (x * cos θ)).intervalIntegrable _ _) ((by fun_prop : Continuous fun θ =>
        cos θ * sinTaylor N (x * cos θ)).intervalIntegrable _ _), integral_cos_mul_sinTaylor,
      besselJ0Deriv, mul_sub, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]
    ring
  have hle : |∫ θ in (0 : ℝ)..2 * π, cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))| ≤
      ∫ θ in (0 : ℝ)..2 * π,
        |x| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) * cos θ ^ (2 * (N + 1)) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hπ.le).trans
      (intervalIntegral.integral_mono_on hπ.le ?_ ?_ fun θ _ => ?_)
    · exact (by fun_prop : Continuous fun θ =>
        |cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))|).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ =>
        |x| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) * cos θ ^ (2 * (N + 1))).intervalIntegrable
          _ _
    · have h := abs_sin_sub_sinTaylor_le N (x * cos θ)
      have hcos : cos θ ^ (2 * (N + 1)) = |cos θ| * |cos θ| ^ (2 * N + 1) := by
        rw [← pow_succ', show 2 * N + 1 + 1 = 2 * (N + 1) by ring,
          (even_two_mul (N + 1)).pow_abs]
      rw [hcos, abs_mul (cos θ)]
      calc |cos θ| * |sin (x * cos θ) - sinTaylor N (x * cos θ)|
          ≤ |cos θ| * (|x| ^ (2 * N + 1) * |cos θ| ^ (2 * N + 1) /
            ((2 * N + 1).factorial : ℝ)) := by gcongr; rwa [abs_mul, mul_pow] at h
        _ = _ := by ring
  rw [integral_odd_term] at hle
  rw [hdiff, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hπ), abs_div, abs_two]
  calc (2 * π)⁻¹ *
        |∫ θ in (0 : ℝ)..2 * π, cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))|
      ≤ (2 * π)⁻¹ * (2 * π * ((|x| / 2) ^ (2 * N + 1) /
        ((N.factorial : ℝ) * ((N + 1).factorial : ℝ)))) := by gcongr
    _ = _ := by field_simp

end Erdos173

end
