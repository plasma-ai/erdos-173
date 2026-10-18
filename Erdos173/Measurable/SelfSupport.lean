module

public import Erdos173.Measurable.Density
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Group.Prod

/-!
# No null set supports itself on circles

Let `S ⊆ ℂ` be measurable and null and `r > 0`. If every point `p ∈ S` sees `S`
in positive arc length on the circle of radius `r` about it, then `S` is empty.

For `p ∈ S` the pairs of directions `(t, u)` with `p + r e^{it} ∈ S` and
`p + r e^{it} + r e^{iu} ∈ S` have positive measure, by Fubini. But the map
`(t, u) ↦ e^{it} + e^{iu}` pulls null sets back to null sets. After the shear
`u ↦ t + u` it is `(t, u) ↦ e^{it} (1 + e^{iu})`, a point of modulus
`|1 + e^{iu}| = 2 cos (u/2)` turned by `t`. By polar coordinates, almost every
circle about the origin meets a null set in a null set of angles, and the radius
`2 cos (u/2)` lies in a given null set of radii only for a null set of `u`,
since `u = ± 2 arccos (ρ/2)` and `arccos` is differentiable on `(-1, 1)`.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open MeasureTheory Set Real OAI.EuclideanFiveColor

/-- A measurable set of angles is null if its lift to `(-π, π]` is null. -/
lemma angularMeasure_eq_zero_of_volume_preimage {Y : Set Angles} (hY : MeasurableSet Y)
    (h : volume ((QuotientAddGroup.mk : ℝ → Angles) ⁻¹' Y ∩ Ioc (-π) π) = 0) :
    angularMeasure Y = 0 := by
  have hmp := AddCircle.measurePreserving_mk (2 * π) (-π)
  have hvol : (volume : Measure Angles) Y = 0 := by
    rw [← hmp.measure_preimage hY.nullMeasurableSet,
      Measure.restrict_apply (hY.preimage hmp.measurable),
      show -π + 2 * π = π by ring]
    exact h
  simp only [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul,
    mul_eq_zero, ENNReal.ofReal_eq_zero] at hvol
  exact hvol.resolve_left (not_le.2 (by positivity))

/-- Rotating a circle: the directions `t` with `e^{it} w ∈ N` have the measure
of those with `|w| e^{it} ∈ N`. -/
lemma angularMeasure_mul_mem (N : Set ℂ) (w : ℂ) :
    angularMeasure {t | direction t * w ∈ N} =
      angularMeasure {t | (‖w‖ : ℂ) * direction t ∈ N} := by
  have hw : w = (‖w‖ : ℂ) * direction (Complex.arg w : Angles) := by
    rw [direction_real, Circle.coe_exp, Complex.norm_mul_exp_arg_mul_I]
  have : {t | direction t * w ∈ N} =
      (· + (Complex.arg w : Angles)) ⁻¹' {t | (‖w‖ : ℂ) * direction t ∈ N} := by
    ext t
    simp only [mem_ofPred_eq, mem_preimage, direction_add]
    conv_lhs => rw [hw]
    ring_nf
  rw [this, measure_preimage_add_right]

/-- `|1 + e^{iα}| = 2 cos (α/2)` for `|α| ≤ π`. -/
lemma norm_one_add_exp {α : ℝ} (h₁ : -π ≤ α) (h₂ : α ≤ π) :
    ‖1 + Complex.exp (α * Complex.I)‖ = 2 * cos (α / 2) := by
  have hc : 0 ≤ cos (α / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  rw [Complex.norm_def, Complex.normSq_apply]
  have hre : (1 + Complex.exp (α * Complex.I)).re = 1 + cos α := by
    rw [Complex.add_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
  have him : (1 + Complex.exp (α * Complex.I)).im = sin α := by
    rw [Complex.add_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, zero_add]
  have hα : α = 2 * (α / 2) := by ring
  rw [hre, him, hα, cos_two_mul, sin_two_mul, show 2 * (α / 2) / 2 = α / 2 by ring]
  rw [show (1 + (2 * cos (α / 2) ^ 2 - 1)) * (1 + (2 * cos (α / 2) ^ 2 - 1)) +
      2 * sin (α / 2) * cos (α / 2) * (2 * sin (α / 2) * cos (α / 2)) =
        (2 * cos (α / 2)) ^ 2 by nlinarith [sin_sq_add_cos_sq (α / 2)]]
  exact sqrt_sq (by positivity)

/-- The directions `u` for which `|1 + e^{iu}|` lies in a null set of radii form a
null set. -/
lemma angularMeasure_norm_one_add_mem {Z : Set ℝ} (hZ : MeasurableSet Z)
    (h0 : volume Z = 0) : angularMeasure {u | ‖1 + direction u‖ ∈ Z} = 0 := by
  have hmeas : MeasurableSet {u : Angles | ‖1 + direction u‖ ∈ Z} :=
    hZ.preimage (continuous_const.add direction_continuous).norm.measurable
  refine angularMeasure_eq_zero_of_volume_preimage hmeas ?_
  set Z₀ := Z ∩ Ioo (-2) 2 with hZ₀
  set g : ℝ → ℝ := fun ρ => 2 * arccos (ρ / 2) with hg
  have hdiff : DifferentiableOn ℝ g Z₀ := by
    intro ρ hρ
    have hρ' : ρ / 2 ≠ -1 ∧ ρ / 2 ≠ 1 := ⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩
    have h1 : DifferentiableAt ℝ arccos (ρ / 2) := Real.differentiableAt_arccos.2 hρ'
    have h2 : DifferentiableAt ℝ (fun ρ : ℝ => ρ / 2) ρ := differentiableAt_id.div_const 2
    exact ((h1.comp ρ h2).const_mul 2).differentiableWithinAt
  have hZ₀0 : volume Z₀ = 0 := measure_mono_null inter_subset_left h0
  have h₁ : volume (g '' Z₀) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hZ₀0
  have h₂ : volume ((fun ρ => -g ρ) '' Z₀) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff.neg hZ₀0
  refine measure_mono_null (t := g '' Z₀ ∪ (fun ρ => -g ρ) '' Z₀ ∪ {0}) ?_
    (measure_union_null (measure_union_null h₁ h₂) (measure_singleton 0))
  rintro α ⟨hαZ, hα₁, hα₂⟩
  simp only [mem_preimage, mem_ofPred_eq, direction_real, Circle.coe_exp] at hαZ
  rw [norm_one_add_exp hα₁.le hα₂] at hαZ
  rcases lt_trichotomy α 0 with hneg | rfl | hpos
  · have hc : cos (α / 2) = cos (-α / 2) := by rw [← cos_neg]; ring_nf
    have hcos1 : cos (-α / 2) < 1 := by
      rw [← cos_zero]
      exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by linarith)
    have hcos0 : 0 ≤ cos (-α / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    refine Or.inl (Or.inr ⟨2 * cos (α / 2), ⟨hαZ, by rw [hc]; linarith, by rw [hc]; linarith⟩, ?_⟩)
    simp only [hg]
    rw [show 2 * cos (α / 2) / 2 = cos (-α / 2) by rw [hc]; ring,
      arccos_cos (by linarith) (by linarith)]
    ring
  · exact Or.inr rfl
  · have hcos1 : cos (α / 2) < 1 := by
      rw [← cos_zero]
      exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by linarith)
    have hcos0 : 0 ≤ cos (α / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    refine Or.inl (Or.inl ⟨2 * cos (α / 2), ⟨hαZ, by linarith, by linarith⟩, ?_⟩)
    simp only [hg]
    rw [show 2 * cos (α / 2) / 2 = cos (α / 2) by ring, arccos_cos (by linarith) (by linarith)]
    ring

/-- Polar coordinates: almost every circle about the origin meets a null set in a
null set of directions. -/
lemma ae_angularMeasure_mul_mem {N : Set ℂ} (hN : MeasurableSet N) (h0 : volume N = 0) :
    ∀ᵐ ρ : ℝ, 0 < ρ → angularMeasure {t | (ρ : ℂ) * direction t ∈ N} = 0 := by
  set F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) with hF
  have hFm : Measurable F := by fun_prop
  have hint := Complex.lintegral_comp_polarCoord_symm (N.indicator 1)
  rw [lintegral_indicator_one hN, h0] at hint
  simp_rw [Complex.polarCoord_symm_apply] at hint
  have hfm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • N.indicator (1 : ℂ → ENNReal) (F p) := by
    have h1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 :=
      ENNReal.measurable_ofReal.comp measurable_fst
    have h2 : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ENNReal) (F p) :=
      (measurable_one.indicator hN).comp hFm
    exact h1.smul h2
  rw [lintegral_eq_zero_iff' hfm.aemeasurable, Filter.EventuallyEq,
    ae_restrict_iff' (by rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo)]
    at hint
  set W : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.2 ∈ Ioo (-π) π ∧ F p ∈ N} with hW
  have hWm : MeasurableSet W :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_Ioo.preimage measurable_snd).inter (hN.preimage hFm))
  have hW0 : (volume : Measure (ℝ × ℝ)) W = 0 := by
    refine measure_mono_null (fun p hp => ?_) (ae_iff.1 hint)
    obtain ⟨hp1, hp2, hp3⟩ := hp
    simp only [mem_ofPred_eq, polarCoord_target, Pi.zero_apply, not_imp]
    refine ⟨⟨hp1, hp2⟩, ?_⟩
    simp only [Set.indicator_of_mem hp3, Pi.one_apply, smul_eq_mul, mul_one]
    exact (ENNReal.ofReal_pos.2 hp1).ne'
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hWm] at hW0
  filter_upwards [hW0] with ρ hρ hρpos
  have hY : MeasurableSet {t : Angles | (ρ : ℂ) * direction t ∈ N} :=
    hN.preimage (continuous_const.mul direction_continuous).measurable
  refine angularMeasure_eq_zero_of_volume_preimage hY ?_
  refine measure_mono_null (t := Prod.mk ρ ⁻¹' W ∪ {π}) ?_
    (measure_union_null hρ (measure_singleton π))
  rintro α ⟨hα, hα₁, hα₂⟩
  rcases hα₂.lt_or_eq with hlt | rfl
  · refine Or.inl ⟨hρpos, ⟨hα₁, hlt⟩, ?_⟩
    simp only [mem_preimage, mem_ofPred_eq, direction_real, Circle.coe_exp] at hα
    simp only [hF]
    convert hα using 2
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  · exact Or.inr rfl

/-- The map `(t, u) ↦ e^{it} + e^{iu}` pulls null sets back to null sets. -/
lemma angularMeasure_prod_add_mem {N : Set ℂ} (hN : MeasurableSet N) (h0 : volume N = 0) :
    (angularMeasure.prod angularMeasure)
      {q : Angles × Angles | direction q.1 + direction q.2 ∈ N} = 0 := by
  have hX : MeasurableSet {q : Angles × Angles | direction q.1 + direction q.2 ∈ N} :=
    hN.preimage ((direction_continuous.comp continuous_fst).add
      (direction_continuous.comp continuous_snd)).measurable
  rw [← (measurePreserving_prod_add angularMeasure angularMeasure).measure_preimage
    hX.nullMeasurableSet]
  have hY : MeasurableSet ((fun z : Angles × Angles => (z.1, z.1 + z.2)) ⁻¹'
      {q : Angles × Angles | direction q.1 + direction q.2 ∈ N}) :=
    hX.preimage (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  rw [Measure.prod_apply_symm hY]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  -- the radii whose circle meets `N` in positive measure, together with `0`
  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null
    (ae_iff.1 (ae_angularMeasure_mul_mem hN h0))
  have hbad := angularMeasure_norm_one_add_mem (hZm.union (measurableSet_singleton 0))
    (measure_union_null hZ0 (measure_singleton 0))
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun u hu => ?_) hbad
  simp only [mem_ofPred_eq] at hu
  have hsec : (fun t => (t, u)) ⁻¹' ((fun z : Angles × Angles => (z.1, z.1 + z.2)) ⁻¹'
      {q : Angles × Angles | direction q.1 + direction q.2 ∈ N}) =
        {t | direction t * (1 + direction u) ∈ N} := by
    ext t
    simp only [mem_preimage, mem_ofPred_eq, direction_add]
    ring_nf
  rw [hsec, angularMeasure_mul_mem] at hu
  simp only [mem_ofPred_eq, mem_union, mem_singleton_iff]
  by_contra hno
  push Not at hno
  apply hu
  have hpos : 0 < ‖1 + direction u‖ := (norm_nonneg _).lt_of_ne (Ne.symm hno.2)
  by_contra hne
  exact hno.1 (hZsub (by simp only [mem_ofPred_eq, not_imp]; exact ⟨hpos, hne⟩))

/-- A null measurable set which every one of its points sees in positive arc
length on the circle of radius `r` is empty. -/
theorem eq_empty_of_selfSupporting {S : Set ℂ} (hS : MeasurableSet S) (h0 : volume S = 0)
    {r : ℝ} (hr : 0 < r) (h : ∀ p ∈ S, angularMeasure {t | p + r * direction t ∈ S} ≠ 0) :
    S = ∅ := by
  by_contra hne
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 hne
  have hcont : Continuous fun t : Angles => p + r * direction t :=
    continuous_const.add (continuous_const.mul direction_continuous)
  set E : Set (Angles × Angles) :=
    {q | p + r * direction q.1 ∈ S ∧ p + r * direction q.1 + r * direction q.2 ∈ S} with hE
  have hEm : MeasurableSet E :=
    (hS.preimage (hcont.comp continuous_fst).measurable).inter
      (hS.preimage ((hcont.comp continuous_fst).add
        (continuous_const.mul (direction_continuous.comp continuous_snd))).measurable)
  -- the pairs of steps from `p` that stay in `S` have positive measure
  have hpos : (angularMeasure.prod angularMeasure) E ≠ 0 := by
    rw [Measure.prod_apply hEm]
    intro hzero
    rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hEm), Filter.EventuallyEq,
      ae_iff] at hzero
    refine h p hp (measure_mono_null (fun t ht => ?_) hzero)
    simp only [mem_ofPred_eq, Pi.zero_apply]
    have : Prod.mk t ⁻¹' E = {u | (p + r * direction t) + r * direction u ∈ S} := by
      ext u
      simp only [hE, mem_preimage, mem_ofPred_eq, and_iff_right_iff_imp]
      exact fun _ => ht
    rw [this]
    exact h _ ht
  -- their endpoints lie in `S`, which is null
  set N : Set ℂ := (fun w => p + (r : ℂ) * w) ⁻¹' S with hN
  have hNm : MeasurableSet N :=
    hS.preimage (continuous_const.add (continuous_const.mul continuous_id)).measurable
  have hN0 : volume N = 0 := by
    have : N = (fun w : ℂ => r • w) ⁻¹' ((fun w => p + w) ⁻¹' S) := by
      ext w
      simp [hN, Complex.real_smul]
    rw [this, Measure.addHaar_preimage_smul volume hr.ne', measure_preimage_add, h0, mul_zero]
  refine hpos (measure_mono_null (fun q hq => ?_) (angularMeasure_prod_add_mem hNm hN0))
  simp only [hN, mem_ofPred_eq, mem_preimage]
  rw [mul_add, ← add_assoc]
  exact hq.2

end Erdos173

end
