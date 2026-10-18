module

public import Erdos173.Measurable.Circle
public import Erdos173.Template.Transcendental
public import Erdos173.Transfer.Exclusion
public import OAI.Analysis.PlaneSpectrum.Carriers

/-!
# Two equilateral scales

No two-coloring of the plane avoids the equilateral triangles of two different
sides. After rescaling the sides are `1` and `x ≠ 1`. The carrier is the field of
algebraic numbers when `x` is algebraic, and the algebraic closure of `ℚ(x)`
otherwise, whose template property makes the rigidity theorem apply. Outside
`(2/3, 3/2)` the Bessel bound excludes the spectral measure; inside, the binary
transfer gives a measurable weak avoider, which the circle argument excludes.
-/

@[expose] public section

noncomputable section

namespace Erdos173

/-- Rescaling the plane by `r` turns avoidance of side `r * s` into avoidance of
side `s`. -/
lemma avoidsEq_scale {c : ℂ → Fin 2} {r s : ℝ} (h : AvoidsEq c (r * s)) :
    AvoidsEq (fun z => c (r * z)) s := by
  intro p u hu hm
  apply h (r * p) u hu
  simp only [MonoCopy] at hm ⊢
  push_cast at hm ⊢
  constructor
  · convert hm.1 using 2; ring
  · convert hm.2 using 2; ring

open OAI.PlaneFiveColor.Spectral in
/-- Over a carrier containing `x`, no two-coloring avoids the equilateral triangles of
sides `1` and `x ≠ 1`: the Bessel bound excludes `x` outside `(2/3, 3/2)`, and the
circle argument excludes the measurable weak avoider that the binary transfer gives
inside. -/
lemma not_avoidsEq_of_mem [Carrier] {x : ℝ} (hx : 0 < x) (hx₁ : x ≠ 1)
    (hxE : (x : ℂ) ∈ E) (c : ℂ → Fin 2) (h₁ : AvoidsEq c 1) (h₂ : AvoidsEq c x) : False := by
  by_cases hfar : 3 / 2 ≤ x ∨ x ≤ 2 / 3
  · exact far_exclusion hx hxE hfar c h₁ h₂
  · push Not at hfar
    obtain ⟨d, hd, hd₁, hd₂⟩ := binary_transfer hxE c h₁ h₂
    exact circle_exclusion hfar.2 hfar.1 hx₁ d hd hd₁ hd₂

open OAI.PlaneFiveColor.Spectral in
/-- No two-coloring avoids the equilateral triangles of sides `1` and `x ≠ 1`. The
carrier is the field of algebraic numbers when `x` is algebraic, and the algebraic
closure of `ℚ(x)` otherwise. -/
theorem not_avoidsEq_one_and {x : ℝ} (hx : 0 < x) (hx₁ : x ≠ 1) (c : ℂ → Fin 2)
    (h₁ : AvoidsEq c 1) (h₂ : AvoidsEq c x) : False := by
  by_cases ha : IsAlgebraic ℚ x
  · let := algebraicCarrier
    exact not_avoidsEq_of_mem hx hx₁ (ofReal_mem_algebraicCarrier ha) c h₁ h₂
  · let h := templateProperty_fieldOf (x := x) ha
    let := carrierOf x h
    exact not_avoidsEq_of_mem hx hx₁ (ofReal_mem_carrierOf x h) c h₁ h₂

/-- A two-coloring of the plane avoids the equilateral triangles of at most one side. -/
theorem two_scale (c : ℂ → Fin 2) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h₁ : AvoidsEq c r) (h₂ : AvoidsEq c s) : r = s := by
  by_contra hne
  have h₁' : AvoidsEq c (r * 1) := by rwa [mul_one]
  have h₂' : AvoidsEq c (r * (s / r)) := by rwa [mul_div_cancel₀ s hr.ne']
  refine not_avoidsEq_one_and (div_pos hs hr) ?_ _ (avoidsEq_scale h₁') (avoidsEq_scale h₂')
  rw [Ne, div_eq_one_iff_eq hr.ne']
  exact fun h => hne h.symm

end Erdos173

end
