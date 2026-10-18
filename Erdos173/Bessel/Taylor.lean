module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Taylor bounds for `cos` and `sin`

The Taylor polynomials `C_N(y) = ∑_{k<N} (-1)^k y^{2k}/(2k)!` and
`S_N(y) = ∑_{k<N} (-1)^k y^{2k+1}/(2k+1)!` approximate `cos` and `sin` with
`|cos y - C_N(y)| ≤ |y|^{2N}/(2N)!` and `|sin y - S_N(y)| ≤ |y|^{2N+1}/(2N+1)!` for
every real `y`. Since `S_N' = C_N` and `C_{N+1}' = -S_N`, both follow by induction
from the single step: a function vanishing at `0` whose derivative is bounded by
`|t|^m/m!` is bounded by `|t|^{m+1}/(m+1)!`.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open Real Finset

/-- The Taylor polynomial `∑_{k<N} (-1)^k y^{2k}/(2k)!` of `cos`. -/
def cosTaylor (N : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * y ^ (2 * k) / ((2 * k).factorial : ℝ)

/-- The Taylor polynomial `∑_{k<N} (-1)^k y^{2k+1}/(2k+1)!` of `sin`. -/
def sinTaylor (N : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

/-- The derivative of `y^{m+1}/(m+1)!` is `y^m/m!`. -/
lemma hasDerivAt_pow_div_factorial (m : ℕ) (y : ℝ) :
    HasDerivAt (fun y => y ^ (m + 1) / ((m + 1).factorial : ℝ))
      (y ^ m / (m.factorial : ℝ)) y := by
  convert (hasDerivAt_pow (m + 1) y).div_const ((m + 1).factorial : ℝ) using 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp
  push_cast
  ring

/-- `S_N' = C_N`. -/
lemma hasDerivAt_sinTaylor (N : ℕ) (y : ℝ) :
    HasDerivAt (sinTaylor N) (cosTaylor N y) y := by
  have h := HasDerivAt.fun_sum (u := range N) (x := y)
    (A := fun k y => (-1) ^ k * (y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)))
    (A' := fun k => (-1) ^ k * (y ^ (2 * k) / ((2 * k).factorial : ℝ)))
    fun k _ => (hasDerivAt_pow_div_factorial (2 * k) y).const_mul _
  convert h using 1
  · ext y
    simp only [sinTaylor, mul_div_assoc]
  · simp only [cosTaylor, mul_div_assoc]

/-- `C_{N+1}' = -S_N`. -/
lemma hasDerivAt_cosTaylor_succ (N : ℕ) (y : ℝ) :
    HasDerivAt (cosTaylor (N + 1)) (-sinTaylor N y) y := by
  have h := (HasDerivAt.fun_sum (u := range N) (x := y)
    (A := fun k y => (-1) ^ (k + 1) * (y ^ (2 * k + 1 + 1) / ((2 * k + 1 + 1).factorial : ℝ)))
    (A' := fun k => (-1) ^ (k + 1) * (y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)))
    fun k _ => (hasDerivAt_pow_div_factorial (2 * k + 1) y).const_mul _).add_const 1
  convert h using 1
  · ext y
    simp only [cosTaylor, sum_range_succ', mul_div_assoc]
    norm_num [mul_add, pow_succ]
  · simp only [sinTaylor, ← sum_neg_distrib, mul_div_assoc, pow_succ]
    ring_nf

/-- A function vanishing at `0` with derivative bounded by `|t|^m/m!` is bounded by
`|t|^{m+1}/(m+1)!`. -/
lemma abs_le_of_abs_deriv_le {f f' : ℝ → ℝ} {m : ℕ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) (hb : ∀ t, |f' t| ≤ |t| ^ m / (m.factorial : ℝ)) (y : ℝ) :
    |f y| ≤ |y| ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  wlog hy : 0 ≤ y generalizing f f' y
  · have h := this (f := fun t => f (-t)) (f' := fun t => -f' (-t))
      (fun t => by
        have := (hf (-t)).comp t (hasDerivAt_neg t)
        simpa [Function.comp_def] using this) (by simpa using h0)
      (fun t => by simpa [abs_neg] using hb (-t)) (-y) (by linarith)
    simpa [abs_neg] using h
  set g : ℝ → ℝ := fun y => y ^ (m + 1) / ((m + 1).factorial : ℝ)
  have hg := hasDerivAt_pow_div_factorial m
  have hmono (s : ℝ) (hs : s = 1 ∨ s = -1) : MonotoneOn (fun t => g t + s * f t) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ => ((hg t).add ((hf t).const_mul s)).continuousAt.continuousWithinAt)
      (fun t _ => ((hg t).add ((hf t).const_mul s)).hasDerivWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    have hb' := abs_le.mp (hb t)
    rw [abs_of_pos ht] at hb'
    rcases hs with rfl | rfl <;> linarith
  have h1 := hmono 1 (Or.inl rfl) Set.self_mem_Ici hy hy
  have h2 := hmono (-1) (Or.inr rfl) Set.self_mem_Ici hy hy
  simp only [g, h0, mul_zero, add_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, zero_div] at h1 h2
  rw [abs_of_nonneg hy, abs_le]
  constructor <;> linarith

/-- `|sin y - S_N(y)| ≤ |y|^{2N+1}/(2N+1)!` given the matching bound for `cos`. -/
lemma abs_sin_sub_sinTaylor_le_of_cos {N : ℕ}
    (hc : ∀ y, |cos y - cosTaylor N y| ≤ |y| ^ (2 * N) / ((2 * N).factorial : ℝ)) (y : ℝ) :
    |sin y - sinTaylor N y| ≤ |y| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) :=
  abs_le_of_abs_deriv_le (fun t => (hasDerivAt_sin t).sub (hasDerivAt_sinTaylor N t))
    (by simp [sinTaylor]) hc y

/-- `|cos y - C_N(y)| ≤ |y|^{2N}/(2N)!`. -/
theorem abs_cos_sub_cosTaylor_le (N : ℕ) (y : ℝ) :
    |cos y - cosTaylor N y| ≤ |y| ^ (2 * N) / ((2 * N).factorial : ℝ) := by
  induction N generalizing y with
  | zero => simpa [cosTaylor] using abs_cos_le_one y
  | succ N ih =>
    have h := abs_le_of_abs_deriv_le (m := 2 * N + 1)
      (fun t => (hasDerivAt_cos t).sub (hasDerivAt_cosTaylor_succ N t))
      (by simp [cosTaylor, sum_range_succ']) (fun t => ?_) y
    · simpa [mul_add] using h
    · rw [show -sin t - -sinTaylor N t = -(sin t - sinTaylor N t) by ring, abs_neg]
      exact abs_sin_sub_sinTaylor_le_of_cos ih t

/-- `|sin y - S_N(y)| ≤ |y|^{2N+1}/(2N+1)!`. -/
theorem abs_sin_sub_sinTaylor_le (N : ℕ) (y : ℝ) :
    |sin y - sinTaylor N y| ≤ |y| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) :=
  abs_sin_sub_sinTaylor_le_of_cos (abs_cos_sub_cosTaylor_le N) y

end Erdos173

end
