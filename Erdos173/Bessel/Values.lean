module

public import Erdos173.Bessel.Series
public import Mathlib.Tactic.NormNum.BigOperators

/-!
# Rational enclosures of `J₀` and `J₁` at sample points

Each bound follows from the partial sum of the power series with `N` terms and the
size of the first omitted term (`Erdos173.Bessel.Series`); both are finite sums of
rationals, evaluated by `norm_num`. Bounds on `J₁` are stated for `J₀' = -J₁`. The
number of terms is chosen so that the omitted term is below `10⁻⁶`.

| point | `J₀` | `J₁ = -J₀'` |
| --- | --- | --- |
| `3` | `≥ -0.261` | `≥ 0.33` |
| `16/5` | `≥ -0.321` | |
| `7/2` | | `≥ 0.13` |
| `15/4` | `∈ [-0.4015, 0]` | `∈ [-0.0334, 0.0334]` |
| `9/2` | `≥ -0.321` | `≤ -0.23` |
| `24/5` | `≥ -0.241` | |
| `11/2` | | `≤ -0.34` |
| `13/2` | `≥ 0.25` | |
| `15/2` | `≥ 0.25` | |
| `17/2` | | `≥ 0.27` |
| `9` | | `≥ 0.24` |
| `46/5` | `∈ [-0.137, 0]` | `∈ [-0.218, 0.218]` |
-/

@[expose] public section

noncomputable section

namespace Erdos173

open Finset

/-- A lower bound for `J₀(x)` from the partial sum with `N` terms. -/
lemma le_besselJ0_of_partial {N : ℕ} {x c : ℝ}
    (h : c ≤ j0Partial N x - (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2) : c ≤ besselJ0 x := by
  linarith [(abs_le.mp (abs_besselJ0_sub_j0Partial_le N x)).1]

/-- An upper bound for `J₀(x)` from the partial sum with `N` terms. -/
lemma besselJ0_le_of_partial {N : ℕ} {x c : ℝ}
    (h : j0Partial N x + (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2 ≤ c) : besselJ0 x ≤ c := by
  linarith [(abs_le.mp (abs_besselJ0_sub_j0Partial_le N x)).2]

/-- A lower bound for `J₀'(x)`, `x ≥ 0`, from the partial sum with `N` terms. -/
lemma le_besselJ0Deriv_of_partial {N : ℕ} {x c : ℝ} (hx : 0 ≤ x)
    (h : c ≤ -j1Partial N x -
      (x / 2) ^ (2 * N + 1) / ((N.factorial : ℝ) * ((N + 1).factorial : ℝ))) :
    c ≤ besselJ0Deriv x := by
  have h' := (abs_le.mp (abs_besselJ0Deriv_add_j1Partial_le N x)).1
  rw [abs_of_nonneg (by positivity : 0 ≤ x / 2)] at h'
  linarith

/-- An upper bound for `J₀'(x)`, `x ≥ 0`, from the partial sum with `N` terms. -/
lemma besselJ0Deriv_le_of_partial {N : ℕ} {x c : ℝ} (hx : 0 ≤ x)
    (h : -j1Partial N x +
      (x / 2) ^ (2 * N + 1) / ((N.factorial : ℝ) * ((N + 1).factorial : ℝ)) ≤ c) :
    besselJ0Deriv x ≤ c := by
  have h' := (abs_le.mp (abs_besselJ0Deriv_add_j1Partial_le N x)).2
  rw [abs_of_nonneg (by positivity : 0 ≤ x / 2)] at h'
  linarith

/-- Evaluates a partial-sum inequality at a rational point. -/
local macro "partial_sum_norm_num" : tactic =>
  `(tactic| (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]
             norm_num))

/-- `J₀(3) ≥ -0.261`. -/
theorem besselJ0_three : -261 / 1000 ≤ besselJ0 3 :=
  le_besselJ0_of_partial (N := 8) (by partial_sum_norm_num)

/-- `J₁(3) ≥ 0.33`. -/
theorem besselJ0Deriv_three : besselJ0Deriv 3 ≤ -33 / 100 :=
  besselJ0Deriv_le_of_partial (N := 8) (by norm_num) (by partial_sum_norm_num)

/-- `J₀(16/5) ≥ -0.321`. -/
theorem besselJ0_sixteen_fifths : -321 / 1000 ≤ besselJ0 (16 / 5) :=
  le_besselJ0_of_partial (N := 9) (by partial_sum_norm_num)

/-- `J₁(7/2) ≥ 0.13`. -/
theorem besselJ0Deriv_seven_halves : besselJ0Deriv (7 / 2) ≤ -13 / 100 :=
  besselJ0Deriv_le_of_partial (N := 9) (by norm_num) (by partial_sum_norm_num)

/-- `-0.4015 ≤ J₀(15/4) ≤ 0`. -/
theorem besselJ0_fifteen_quarters :
    -4015 / 10000 ≤ besselJ0 (15 / 4) ∧ besselJ0 (15 / 4) ≤ 0 :=
  ⟨le_besselJ0_of_partial (N := 9) (by partial_sum_norm_num),
    besselJ0_le_of_partial (N := 9) (by partial_sum_norm_num)⟩

/-- `|J₁(15/4)| ≤ 0.0334`. -/
theorem besselJ0Deriv_fifteen_quarters :
    -334 / 10000 ≤ besselJ0Deriv (15 / 4) ∧ besselJ0Deriv (15 / 4) ≤ 334 / 10000 :=
  ⟨le_besselJ0Deriv_of_partial (N := 9) (by norm_num) (by partial_sum_norm_num),
    besselJ0Deriv_le_of_partial (N := 9) (by norm_num) (by partial_sum_norm_num)⟩

/-- `J₀(9/2) ≥ -0.321`. -/
theorem besselJ0_nine_halves : -321 / 1000 ≤ besselJ0 (9 / 2) :=
  le_besselJ0_of_partial (N := 10) (by partial_sum_norm_num)

/-- `J₁(9/2) ≤ -0.23`. -/
theorem besselJ0Deriv_nine_halves : 23 / 100 ≤ besselJ0Deriv (9 / 2) :=
  le_besselJ0Deriv_of_partial (N := 10) (by norm_num) (by partial_sum_norm_num)

/-- `J₀(24/5) ≥ -0.241`. -/
theorem besselJ0_twenty_four_fifths : -241 / 1000 ≤ besselJ0 (24 / 5) :=
  le_besselJ0_of_partial (N := 11) (by partial_sum_norm_num)

/-- `J₁(11/2) ≤ -0.34`. -/
theorem besselJ0Deriv_eleven_halves : 34 / 100 ≤ besselJ0Deriv (11 / 2) :=
  le_besselJ0Deriv_of_partial (N := 12) (by norm_num) (by partial_sum_norm_num)

/-- `J₀(13/2) ≥ 0.25`. -/
theorem besselJ0_thirteen_halves : 1 / 4 ≤ besselJ0 (13 / 2) :=
  le_besselJ0_of_partial (N := 13) (by partial_sum_norm_num)

/-- `J₀(15/2) ≥ 0.25`. -/
theorem besselJ0_fifteen_halves : 1 / 4 ≤ besselJ0 (15 / 2) :=
  le_besselJ0_of_partial (N := 15) (by partial_sum_norm_num)

/-- `J₁(17/2) ≥ 0.27`. -/
theorem besselJ0Deriv_seventeen_halves : besselJ0Deriv (17 / 2) ≤ -27 / 100 :=
  besselJ0Deriv_le_of_partial (N := 16) (by norm_num) (by partial_sum_norm_num)

/-- `J₁(9) ≥ 0.24`. -/
theorem besselJ0Deriv_nine : besselJ0Deriv 9 ≤ -24 / 100 :=
  besselJ0Deriv_le_of_partial (N := 17) (by norm_num) (by partial_sum_norm_num)

/-- `-0.137 ≤ J₀(46/5) ≤ 0`. -/
theorem besselJ0_forty_six_fifths :
    -137 / 1000 ≤ besselJ0 (46 / 5) ∧ besselJ0 (46 / 5) ≤ 0 :=
  ⟨le_besselJ0_of_partial (N := 17) (by partial_sum_norm_num),
    besselJ0_le_of_partial (N := 17) (by partial_sum_norm_num)⟩

/-- `|J₁(46/5)| ≤ 0.218`. -/
theorem besselJ0Deriv_forty_six_fifths :
    -218 / 1000 ≤ besselJ0Deriv (46 / 5) ∧ besselJ0Deriv (46 / 5) ≤ 218 / 1000 :=
  ⟨le_besselJ0Deriv_of_partial (N := 17) (by norm_num) (by partial_sum_norm_num),
    besselJ0Deriv_le_of_partial (N := 17) (by norm_num) (by partial_sum_norm_num)⟩

end Erdos173

end
