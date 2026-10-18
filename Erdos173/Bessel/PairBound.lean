module

public import Erdos173.Bessel.Shape
public import Erdos173.Bessel.Values
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A lower bound for `J₀(t) + J₀(x t)`

For `x ≥ 3/2` and `t ≥ 0`, `J₀(t) + J₀(x t) ≥ -83/125 > -2/3`. The proof combines the
rational values of `J₀` and `J₁ = -J₀'` at finitely many points
(`Erdos173.Bessel.Values`) with the shape of `J₀` (`Erdos173.Bessel.Shape`):

* `J₁ ≥ 0` on `[0, 15/4]`: on `[0, π]` by the sign of the integrand, and beyond from
  `J₁(3) ≥ 0.33`, `J₁(7/2) ≥ 0.13` and the `1/2`-Lipschitz bound on `J₁`. So `J₀`
  decreases on `[0, 15/4]`; likewise `J₀` increases on `[9/2, 61/10]` (from the values
  of `J₁` at `9/2` and `11/2`) and decreases on `[8, 46/5]` (from `17/2` and `9`).
* Global bound `J₀ ≥ -0.403`: below `15/4` by monotonicity and `J₀(15/4) ≥ -0.4015`;
  beyond by the nonincreasing energy, `J₀(15/4)² + J₁(15/4)² < 0.403²`.
* `J₀ ≥ -0.261` on `[0, 3]` (monotonicity and `J₀(3)`) and on `[24/5, ∞)`: by
  monotonicity on `[24/5, 61/10]` and `[8, 46/5]`, by the `1`-Lipschitz bound from
  `J₀(13/2), J₀(15/2) ≥ 1/4` on `[61/10, 8]`, and by the energy at `46/5` beyond.
* If `t` or `x t` lies outside `(3, 24/5)`, the two bounds give
  `-0.261 - 0.403 = -83/125`. Otherwise `3 < t < 16/5` and `9/2 < x t < 24/5`, where
  monotonicity gives `J₀(t) ≥ J₀(16/5)` and `J₀(x t) ≥ J₀(9/2)`, both `≥ -0.321`.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open Real Set

/-- `J₀' ≤ 0` near a point where `J₀' ≤ -c`. -/
lemma besselJ0Deriv_nonpos_of_near {p c t : ℝ} (hp : besselJ0Deriv p ≤ -c)
    (ht : |t - p| ≤ 2 * c) : besselJ0Deriv t ≤ 0 := by
  linarith [(abs_le.mp (abs_besselJ0Deriv_sub_le p t)).2]

/-- `J₀' ≥ 0` near a point where `J₀' ≥ c`. -/
lemma besselJ0Deriv_nonneg_of_near {p c t : ℝ} (hp : c ≤ besselJ0Deriv p)
    (ht : |t - p| ≤ 2 * c) : 0 ≤ besselJ0Deriv t := by
  linarith [(abs_le.mp (abs_besselJ0Deriv_sub_le p t)).1]

/-- `J₀` decreases on `[0, 15/4]`. -/
theorem antitoneOn_besselJ0_zero_fifteen_quarters :
    AntitoneOn besselJ0 (Icc 0 (15 / 4)) := by
  refine antitoneOn_besselJ0 fun t ht => ?_
  rcases le_or_gt t 3 with h3 | h3
  · exact besselJ0Deriv_nonpos_of_le_pi ht.1 (h3.trans pi_gt_three.le)
  rcases le_or_gt t (18 / 5) with h4 | h4
  · exact besselJ0Deriv_nonpos_of_near (p := 3) (c := 33 / 100)
      (by linarith [besselJ0Deriv_three])
      (abs_le.mpr ⟨by linarith, by linarith⟩)
  · exact besselJ0Deriv_nonpos_of_near (p := 7 / 2) (c := 13 / 100)
      (by linarith [besselJ0Deriv_seven_halves])
      (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)

/-- `J₀` increases on `[9/2, 61/10]`. -/
theorem monotoneOn_besselJ0_nine_halves_sixty_one_tenths :
    MonotoneOn besselJ0 (Icc (9 / 2) (61 / 10)) := by
  refine monotoneOn_besselJ0 fun t ht => ?_
  rcases le_or_gt t (49 / 10) with h | h
  · exact besselJ0Deriv_nonneg_of_near (p := 9 / 2) (c := 23 / 100)
      (by linarith [besselJ0Deriv_nine_halves])
      (abs_le.mpr ⟨by linarith [ht.1], by linarith⟩)
  · exact besselJ0Deriv_nonneg_of_near (p := 11 / 2) (c := 34 / 100)
      (by linarith [besselJ0Deriv_eleven_halves])
      (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)

/-- `J₀` decreases on `[8, 46/5]`. -/
theorem antitoneOn_besselJ0_eight_forty_six_fifths :
    AntitoneOn besselJ0 (Icc 8 (46 / 5)) := by
  refine antitoneOn_besselJ0 fun t ht => ?_
  rcases le_or_gt t 9 with h | h
  · exact besselJ0Deriv_nonpos_of_near (p := 17 / 2) (c := 27 / 100)
      (by linarith [besselJ0Deriv_seventeen_halves])
      (abs_le.mpr ⟨by linarith [ht.1], by linarith⟩)
  · exact besselJ0Deriv_nonpos_of_near (p := 9) (c := 24 / 100)
      (by linarith [besselJ0Deriv_nine])
      (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)

/-- Beyond a point `s > 0` of small energy, `J₀ ≥ -c`. -/
lemma neg_le_besselJ0_of_energy {s t c : ℝ} (hs : 0 < s) (hst : s ≤ t) (hc : 0 ≤ c)
    (hE : besselJ0 s ^ 2 + besselJ0Deriv s ^ 2 ≤ c ^ 2) : -c ≤ besselJ0 t :=
  (abs_le_of_sq_le_sq' ((sq_besselJ0_le_energy hs hst).trans hE) hc).1

/-- The global bound `J₀ ≥ -0.403` on `[0, ∞)`. -/
theorem le_besselJ0_of_nonneg {t : ℝ} (ht : 0 ≤ t) : -403 / 1000 ≤ besselJ0 t := by
  obtain ⟨hJ₁, hJ₂⟩ := besselJ0_fifteen_quarters
  rcases le_or_gt t (15 / 4) with h | h
  · linarith [antitoneOn_besselJ0_zero_fifteen_quarters ⟨ht, h⟩ ⟨by norm_num, le_rfl⟩ h]
  · obtain ⟨hD₁, hD₂⟩ := besselJ0Deriv_fifteen_quarters
    refine le_trans (le_of_eq (by norm_num))
      (neg_le_besselJ0_of_energy (c := 403 / 1000) (by norm_num) h.le (by norm_num) ?_)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0 (15 / 4) + 4015 / 10000)
      (by linarith : (0 : ℝ) ≤ -besselJ0 (15 / 4)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0Deriv (15 / 4) + 334 / 10000)
      (by linarith : (0 : ℝ) ≤ 334 / 10000 - besselJ0Deriv (15 / 4))]

/-- `J₀ ≥ -0.261` on `[0, 3]`. -/
theorem le_besselJ0_of_le_three {t : ℝ} (ht : 0 ≤ t) (h3 : t ≤ 3) :
    -261 / 1000 ≤ besselJ0 t :=
  besselJ0_three.trans
    (antitoneOn_besselJ0_zero_fifteen_quarters ⟨ht, by linarith⟩ ⟨by norm_num, by norm_num⟩ h3)

/-- `J₀ ≥ -0.261` on `[24/5, ∞)`. -/
theorem le_besselJ0_of_twenty_four_fifths_le {t : ℝ} (ht : 24 / 5 ≤ t) :
    -261 / 1000 ≤ besselJ0 t := by
  rcases le_or_gt t (61 / 10) with h | h
  · linarith [besselJ0_twenty_four_fifths, monotoneOn_besselJ0_nine_halves_sixty_one_tenths
      ⟨by norm_num, by norm_num⟩ ⟨by linarith, h⟩ ht]
  rcases le_or_gt t 7 with h7 | h7
  · have := (abs_le.mp (abs_besselJ0_sub_le (13 / 2) t)).1
    have := abs_le.mpr (⟨by linarith, by linarith⟩ : -(1 / 2) ≤ t - 13 / 2 ∧ t - 13 / 2 ≤ 1 / 2)
    linarith [besselJ0_thirteen_halves]
  rcases le_or_gt t 8 with h8 | h8
  · have := (abs_le.mp (abs_besselJ0_sub_le (15 / 2) t)).1
    have := abs_le.mpr (⟨by linarith, by linarith⟩ : -(1 / 2) ≤ t - 15 / 2 ∧ t - 15 / 2 ≤ 1 / 2)
    linarith [besselJ0_fifteen_halves]
  obtain ⟨hJ₁, hJ₂⟩ := besselJ0_forty_six_fifths
  rcases le_or_gt t (46 / 5) with h9 | h9
  · linarith [antitoneOn_besselJ0_eight_forty_six_fifths ⟨h8.le, h9⟩ ⟨by norm_num, le_rfl⟩ h9]
  · obtain ⟨hD₁, hD₂⟩ := besselJ0Deriv_forty_six_fifths
    refine le_trans (le_of_eq (by norm_num))
      (neg_le_besselJ0_of_energy (c := 261 / 1000) (by norm_num) h9.le (by norm_num) ?_)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0 (46 / 5) + 137 / 1000)
      (by linarith : (0 : ℝ) ≤ -besselJ0 (46 / 5)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0Deriv (46 / 5) + 218 / 1000)
      (by linarith : (0 : ℝ) ≤ 218 / 1000 - besselJ0Deriv (46 / 5))]

/-- `J₀(t) + J₀(x t) ≥ -83/125` for `x ≥ 3/2` and `t ≥ 0`. -/
theorem besselJ0_add_lower {x : ℝ} (hx : 3 / 2 ≤ x) {t : ℝ} (ht : 0 ≤ t) :
    -83 / 125 ≤ besselJ0 t + besselJ0 (x * t) := by
  have hxt : 3 / 2 * t ≤ x * t := mul_le_mul_of_nonneg_right hx ht
  have hs : 0 ≤ x * t := by linarith
  have hG₁ := le_besselJ0_of_nonneg ht
  have hG₂ := le_besselJ0_of_nonneg hs
  -- either argument outside `(3, 24/5)`: the bound on `[0, 3] ∪ [24/5, ∞)` and the global one
  rcases le_or_gt t 3 with h | h₁
  · linarith [le_besselJ0_of_le_three ht h]
  rcases le_or_gt (24 / 5) t with h | h₂
  · linarith [le_besselJ0_of_twenty_four_fifths_le h]
  rcases le_or_gt (x * t) 3 with h | h₃
  · linarith [le_besselJ0_of_le_three hs h]
  rcases le_or_gt (24 / 5) (x * t) with h | h₄
  · linarith [le_besselJ0_of_twenty_four_fifths_le h]
  -- both inside: `3 < t < 16/5` and `9/2 < x t < 24/5`
  have hJ₁ := antitoneOn_besselJ0_zero_fifteen_quarters ⟨by linarith, by linarith⟩
    ⟨by norm_num, by norm_num⟩ (by linarith : t ≤ 16 / 5)
  have hJ₂ := monotoneOn_besselJ0_nine_halves_sixty_one_tenths ⟨le_rfl, by norm_num⟩
    ⟨by linarith, by linarith⟩ (by linarith : 9 / 2 ≤ x * t)
  linarith [besselJ0_sixteen_fifths, besselJ0_nine_halves]

end Erdos173

end
