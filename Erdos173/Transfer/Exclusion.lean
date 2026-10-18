module

public import Erdos173.Basic
public import Erdos173.Bessel.PairBound
public import Erdos173.Transfer.Sample
public import Erdos173.Transfer.Spectral
public import OAI.Geometry.PlaneColoring.BorelTransfer

/-!
# From an arbitrary avoiding coloring to the spectral and measurable pictures

Let `c` avoid the equilateral triangles of sides `1` and `x`, with `x` in the
carrier `E`. Its restriction to `E` lies in the compact space of labelings of `E`
with no monochromatic equilateral triangle of side `1` or `x`, which carries a
probability measure invariant under translations by `E` and rotations by `K`.
For the origin's sign `f`, OpenAI's spectral rigidity theorem gives
`⟪f, T_z f⟫ = ⟪P f, T_z P f⟫` for `z ≠ 0`, where `P` projects onto the vectors
continuous under translation.

Avoidance makes the three pair correlations of every equilateral triangle of side
`1` or `x` sum to `-1`, so the radial spectral measure of `P f` has
`∫ J₀(t) dν = ∫ J₀(x t) dν = -1/3` with mass at most one, which the Bessel bound
excludes when `x ≥ 3/2` or `x ≤ 2/3`. For two colors on a triangle the
monochromatic indicator `(1 + ab + ac + bc)/4` is quadratic, so the projected
field, sampled and thresholded, is a measurable coloring that weakly avoids both
sides.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open MeasureTheory
open OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor

variable [Carrier]

namespace Transfer

/-- A real side `r` in the carrier, as an element of `E`. -/
def sideE (r : ℝ) (h : (r : ℂ) ∈ E) : E := ⟨r, h⟩

@[simp] lemma coe_sideE (r : ℝ) (h : (r : ℂ) ∈ E) : (sideE r h : ℂ) = r := rfl

/-- `1` lies in the carrier. -/
lemma one_mem_E : ((1 : ℝ) : ℂ) ∈ E := by simp

/-- The sides `1` and `x`. -/
def sides {x : ℝ} (hxE : (x : ℂ) ∈ E) : Set E := {sideE 1 one_mem_E, sideE x hxE}

/-- A coloring avoiding the equilateral triangles of side `r` restricts to a labeling of
`E` avoiding them. -/
lemma avoidsSide_restrict {r : ℝ} (h : (r : ℂ) ∈ E) {c : ℂ → Fin 2} (hc : AvoidsEq c r) :
    AvoidsSide (sideE r h) (fun z => c z) := by
  intro p u hm
  refine hc p (u.val : ℂ) (Circle.norm_coe _) ⟨?_, ?_⟩
  · simpa [MonoCopy] using hm.1
  · simpa [MonoCopy, mul_assoc] using hm.2

/-- The restriction to `E` of a coloring avoiding the equilateral triangles of sides `1`
and `x`. -/
def restrict {x : ℝ} (hxE : (x : ℂ) ∈ E) (c : ℂ → Fin 2) (h₁ : AvoidsEq c 1)
    (h₂ : AvoidsEq c x) : Space (sides hxE) :=
  ⟨fun z => c z, by
    rintro r (rfl | rfl)
    · exact avoidsSide_restrict one_mem_E (by simpa using h₁)
    · exact avoidsSide_restrict hxE h₂⟩

omit [Carrier] in
/-- The monochromatic copies of a jointly measurable labeling form a measurable set. -/
lemma measurableSet_monoCopy {Ω : Type*} [MeasurableSpace Ω] {col : ℂ × Ω → Fin 2}
    (hcol : Measurable col) (a b : ℂ) :
    MeasurableSet {q : (ℂ × Angles) × Ω |
      MonoCopy (fun y => col (y, q.2)) a b q.1.1 (direction q.1.2)} := by
  have hp : Measurable fun q : (ℂ × Angles) × Ω => q.1.1 := measurable_fst.fst
  have hd : Measurable fun q : (ℂ × Angles) × Ω => direction q.1.2 :=
    direction_continuous.measurable.comp measurable_fst.snd
  have h₀ : Measurable fun q : (ℂ × Angles) × Ω => col (q.1.1, q.2) :=
    hcol.comp (hp.prodMk measurable_snd)
  have h₁ : Measurable fun q : (ℂ × Angles) × Ω => col (q.1.1 + direction q.1.2 * a, q.2) :=
    hcol.comp ((hp.add (hd.mul_const a)).prodMk measurable_snd)
  have h₂ : Measurable fun q : (ℂ × Angles) × Ω => col (q.1.1 + direction q.1.2 * b, q.2) :=
    hcol.comp ((hp.add (hd.mul_const b)).prodMk measurable_snd)
  exact (measurableSet_eq_fun h₁ h₀).inter (measurableSet_eq_fun h₂ h₀)

end Transfer

open Transfer

/-- No coloring avoids the equilateral triangles of sides `1` and `x` when `x` is in
the carrier and `x ≥ 3/2` or `x ≤ 2/3`. -/
theorem far_exclusion {x : ℝ} (hx : 0 < x) (hxE : (x : ℂ) ∈ E)
    (hfar : 3 / 2 ≤ x ∨ x ≤ 2 / 3) (c : ℂ → Fin 2) (h₁ : AvoidsEq c 1)
    (h₂ : AvoidsEq c x) : False := by
  let ω₀ := restrict hxE c h₁ h₂
  obtain ⟨ν, hν, hmass, hcorr⟩ := exists_radial_measure _ ω₀
  -- the correlations at the two sides are `-1/3`
  have hc₁ := corr_side _ ω₀ (r := sideE 1 one_mem_E) (Or.inl rfl)
  have hc₂ := corr_side _ ω₀ (r := sideE x hxE) (Or.inr rfl)
  rw [hcorr _ (fun h => by simpa using congrArg Subtype.val h)] at hc₁
  rw [hcorr _ (fun h => hx.ne' (by simpa using congrArg Subtype.val h))] at hc₂
  simp only [coe_sideE, Complex.norm_real, Real.norm_eq_abs, abs_one, one_mul,
    abs_of_pos hx] at hc₁ hc₂
  have hint (s : ℝ) : Integrable (fun ξ : ℂ => besselJ0 (s * ‖ξ‖)) ν :=
    (integrable_const (1 : ℝ)).mono'
      (continuous_besselJ0.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable
      (ae_of_all _ fun ξ => abs_besselJ0_le_one _)
  have hint₁ : Integrable (fun ξ : ℂ => besselJ0 ‖ξ‖) ν := by simpa using hint 1
  -- the Bessel bound, at `x` or at `1/x`
  have hlow (ξ : ℂ) : -83 / 125 ≤ besselJ0 ‖ξ‖ + besselJ0 (x * ‖ξ‖) := by
    rcases hfar with h | h
    · exact besselJ0_add_lower h (norm_nonneg ξ)
    · have h' : 3 / 2 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
      have hb := besselJ0_add_lower h' (mul_nonneg hx.le (norm_nonneg ξ))
      rw [← mul_assoc, one_div_mul_cancel hx.ne', one_mul] at hb
      linarith
  have hi := integral_mono (integrable_const (-83 / 125 : ℝ)) (hint₁.add (hint x)) hlow
  simp only [Pi.add_apply] at hi
  rw [integral_add hint₁ (hint x), hc₁, hc₂, integral_const, smul_eq_mul] at hi
  have h0 : 0 ≤ ν.real Set.univ := measureReal_nonneg
  nlinarith

/-- A coloring that avoids the equilateral triangles of sides `1` and `x`, with `x` in
the carrier, gives a measurable coloring that weakly avoids both. -/
theorem binary_transfer {x : ℝ} (hxE : (x : ℂ) ∈ E) (c : ℂ → Fin 2)
    (h₁ : AvoidsEq c 1) (h₂ : AvoidsEq c x) :
    ∃ d : ℂ → Fin 2, Measurable d ∧ WeaklyAvoidsEq d 1 ∧ WeaklyAvoidsEq d x := by
  let ω₀ := restrict hxE c h₁ h₂
  obtain ⟨F, hF, hQ⟩ := exists_measurable_qform_field _ ω₀
  -- threshold the measurable field at `0`
  let col : ℂ × Space (sides hxE) → Fin 2 := fun q => threshold (F q).re
  have hcol : Measurable col := measurable_threshold.comp (Complex.measurable_re.comp hF)
  -- for each copy, almost every labeling leaves it non-monochromatic
  have hpt (q : ℂ × Angles) : ∀ᵐ η ∂measure (sides hxE) ω₀,
      ¬ MonoCopy (fun y => col (y, η)) (1 : ℝ) ((1 : ℝ) * ζ) q.1 (direction q.2) ∧
        ¬ MonoCopy (fun y => col (y, η)) x (x * ζ) q.1 (direction q.2) := by
    filter_upwards [hQ _ (Or.inl rfl) q.1 (AddCircle.toCircle q.2),
      hQ _ (Or.inr rfl) q.1 (AddCircle.toCircle q.2)] with η e₁ e₂
    exact ⟨not_mono_of_qform e₁, not_mono_of_qform e₂⟩
  have hm : MeasurableSet {q : (ℂ × Angles) × Space (sides hxE) |
      ¬ MonoCopy (fun y => col (y, q.2)) (1 : ℝ) ((1 : ℝ) * ζ) q.1.1 (direction q.1.2) ∧
        ¬ MonoCopy (fun y => col (y, q.2)) x (x * ζ) q.1.1 (direction q.1.2)} :=
    (measurableSet_monoCopy hcol (1 : ℝ) ((1 : ℝ) * ζ)).compl.inter
      (measurableSet_monoCopy hcol x (x * ζ)).compl
  -- Tonelli: almost every labeling serves almost every copy
  have hh := (Measure.ae_ae_comm (μ := (volume : Measure ℂ).prod angularMeasure)
    (ν := measure (sides hxE) ω₀) hm).mp (.of_forall hpt)
  obtain ⟨η, hη⟩ := hh.exists
  exact ⟨fun y => col (y, η), hcol.comp (measurable_id.prodMk measurable_const),
    hη.mono fun _ h => h.1, hη.mono fun _ h => h.2⟩

end Erdos173

end
