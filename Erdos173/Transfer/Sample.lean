module

public import Erdos173.Transfer.LabelModel
public import OAI.Analysis.PlaneSpectrum.Ergodicity
public import OAI.Geometry.PlaneColoring.BorelTransfer

/-!
# The projected sign field

Let `P` be the orthogonal projection onto the vectors continuous under translation, and
`g = P s` the projected sign. The projection commutes with the contraction
`z ↦ max (-1) (min 1 (Re z))`, so `g` is real with values in `[-1, 1]`. OpenAI's
spectral rigidity theorem (`residual_fourier`) gives `⟪g, T_z g⟫ = ⟪s, T_z s⟫ = ρ(z)` for
`z ≠ 0`. The orbit of `g` extends to a continuous field `G(y)` on `ℂ` with the same
bounds.

For two colors on a triangle the monochromatic indicator is quadratic:
`Q(a, b, c) = 1 + ab + ac + bc` is `4` on equal signs and `0` otherwise, and
`2Q = (1 + a)(1 + b)(1 + c) + (1 - a)(1 - b)(1 - c) ≥ 0` on `[-1, 1]³`. On each triangle
`(y, y + u r, y + u r ζ)` of side `r ∈ R` the mean of `Q(G)` is `1` plus three
correlations, which vanishes for `u ∈ K` by avoidance and so for every unit `u` by
continuity. Hence `Q(G) = 0` almost surely, and a jointly measurable representative of
`G` gives the measurable field that the binary transfer thresholds.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Transfer

open MeasureTheory Filter
open OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor OAI.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace NNReal

variable [Carrier]

/-! ### The quadratic form of a triangle -/

/-- `Q(a, b, c) = 1 + ab + ac + bc`, four times the indicator that three signs agree. -/
def qform (a b c : ℝ) : ℝ := 1 + a * b + a * c + b * c

omit [Carrier] in
/-- `Q ≥ 0` on `[-1, 1]³`. -/
lemma qform_nonneg {a b c : ℝ} (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1)
    (hc : -1 ≤ c ∧ c ≤ 1) : 0 ≤ qform a b c := by
  have h₁ : 0 ≤ (1 + a) * (1 + b) * (1 + c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h₂ : 0 ≤ (1 - a) * (1 - b) * (1 - c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  unfold qform
  nlinarith

/-- The label of a real value: `0` for nonnegative values, `1` for negative ones. -/
def threshold (t : ℝ) : Fin 2 := if 0 ≤ t then 0 else 1

omit [Carrier] in
lemma measurable_threshold : Measurable threshold :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

omit [Carrier] in
/-- Three values with `Q = 0` do not all receive the same label. -/
lemma not_mono_of_qform {a b c : ℝ} (h : qform a b c = 0) :
    ¬ (threshold b = threshold a ∧ threshold c = threshold a) := by
  rintro ⟨hb, hc⟩
  unfold threshold at hb hc
  unfold qform at h
  by_cases ha : 0 ≤ a <;> by_cases hb' : 0 ≤ b <;> by_cases hc' : 0 ≤ c <;>
    simp [ha, hb', hc'] at hb hc
  · nlinarith [mul_nonneg ha hb', mul_nonneg ha hc', mul_nonneg hb' hc']
  · have ha' : a < 0 := by linarith
    have hb'' : b < 0 := by linarith
    have hc'' : c < 0 := by linarith
    nlinarith [mul_pos_of_neg_of_neg ha' hb'', mul_pos_of_neg_of_neg ha' hc'',
      mul_pos_of_neg_of_neg hb'' hc'']

omit [Carrier] in
/-- For real vectors of `L²` of a probability measure, the mean of `Q` is `1` plus the
three inner products. -/
lemma integral_qform {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (A B C : Lp ℂ 2 μ) (hA : ∀ᵐ η ∂μ, (A η).im = 0) (hB : ∀ᵐ η ∂μ, (B η).im = 0) :
    Integrable (fun η => qform (A η).re (B η).re (C η).re) μ ∧
      ∫ η, qform (A η).re (B η).re (C η).re ∂μ =
        (1 + ⟪A, B⟫_ℂ + ⟪A, C⟫_ℂ + ⟪B, C⟫_ℂ).re := by
  have hre (V W : Lp ℂ 2 μ) (hV : ∀ᵐ η ∂μ, (V η).im = 0) :
      (fun η => RCLike.re (⟪V η, W η⟫_ℂ)) =ᵐ[μ] fun η => (V η).re * (W η).re := by
    filter_upwards [hV] with η h
    simp [RCLike.inner_apply, h, mul_comm]
  have hint (V W : Lp ℂ 2 μ) (hV : ∀ᵐ η ∂μ, (V η).im = 0) :
      Integrable (fun η => (V η).re * (W η).re) μ :=
    (L2.integrable_inner (𝕜 := ℂ) V W).re.congr (hre V W hV)
  have hval (V W : Lp ℂ 2 μ) (hV : ∀ᵐ η ∂μ, (V η).im = 0) :
      ∫ η, (V η).re * (W η).re ∂μ = (⟪V, W⟫_ℂ).re := by
    rw [← integral_congr_ae (hre V W hV), integral_re (L2.integrable_inner V W), ← L2.inner_def]
    rfl
  have i₁ : Integrable (fun η => 1 + (A η).re * (B η).re) μ :=
    (integrable_const _).add (hint A B hA)
  have i₂ : Integrable (fun η => 1 + (A η).re * (B η).re + (A η).re * (C η).re) μ :=
    i₁.add (hint A C hA)
  refine ⟨i₂.add (hint B C hB), ?_⟩
  unfold qform
  rw [integral_add i₂ (hint B C hB), integral_add i₁ (hint A C hA),
    integral_add (integrable_const _) (hint A B hA), hval A B hA, hval A C hA, hval B C hB]
  simp

/-! ### The symmetric clamp -/

/-- The contraction of `ℂ` onto the real interval `[-1, 1]`. -/
def clampSign (z : ℂ) : ℂ := (max (-1) (min 1 z.re) : ℝ)

omit [Carrier] in
lemma lipschitzWith_clampSign : LipschitzWith 1 clampSign := by
  have hr : LipschitzWith 1 (fun z : ℂ => z.re) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs,
      ← Complex.sub_re] using Complex.abs_re_le_norm (a - b)
  change LipschitzWith 1 (fun z : ℂ => ((max (-1) (min 1 z.re) : ℝ) : ℂ))
  simpa only [one_mul, Function.comp_def] using
    Complex.isometry_ofReal.lipschitzWith.comp ((hr.const_min 1).const_max (-1))

omit [Carrier] in
@[simp] lemma clampSign_zero : clampSign 0 = 0 := by simp [clampSign]

omit [Carrier] in
/-- The clamp is real with values in `[-1, 1]`. -/
lemma clampSign_range (z : ℂ) :
    (clampSign z).im = 0 ∧ -1 ≤ (clampSign z).re ∧ (clampSign z).re ≤ 1 := by
  change (0 : ℝ) = 0 ∧ -1 ≤ max (-1) (min 1 z.re) ∧ max (-1) (min 1 z.re) ≤ 1
  exact ⟨rfl, le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

omit [Carrier] in
/-- The clamp fixes real numbers in `[-1, 1]`. -/
lemma clampSign_eq {z : ℂ} (hz : z.im = 0 ∧ -1 ≤ z.re ∧ z.re ≤ 1) : clampSign z = z := by
  rw [clampSign, min_eq_right hz.2.2, max_eq_right hz.2.1]
  exact Complex.ext (by simp) (by simpa using hz.1.symm)

/-! ### The projected sign and its field -/

variable (R : Set E) (ω₀ : Space R)

instance continuous_complete : CompleteSpace (space (A := E) (representation R ω₀)) :=
  (isClosed_space (A := E) (representation R ω₀)).completeSpace_coe

/-- The projection of the sign onto the continuous vectors. -/
def projected : Hilbert R ω₀ :=
  (space (A := E) (representation R ω₀)).starProjection (signVector R ω₀)

/-- The projected sign is continuous under translation. -/
lemma projected_mem : projected R ω₀ ∈ space (A := E) (representation R ω₀) :=
  (space (A := E) (representation R ω₀)).starProjection_apply_mem _

/-- The sign vector is real with values in `[-1, 1]`. -/
lemma sign_range : ∀ᵐ η ∂measure R ω₀,
    (signVector R ω₀ η).im = 0 ∧ -1 ≤ (signVector R ω₀ η).re ∧ (signVector R ω₀ η).re ≤ 1 := by
  filter_upwards [sign_ae R ω₀] with η h
  rw [h]
  simp only [Complex.ofReal_im, Complex.ofReal_re, sgnAt]
  split_ifs <;> norm_num

/-- `clampSign` acting on `L²` maps the continuous vectors to themselves. -/
lemma clampSign_mem {v : Hilbert R ω₀} (hv : v ∈ space (A := E) (representation R ω₀)) :
    lipschitzWith_clampSign.compLp clampSign_zero v ∈ space (A := E) (representation R ω₀) :=
  nonlinear_mem (measure R ω₀) (representation R ω₀) (trans R) (trans_preserving R ω₀)
    (op_apply R ω₀) lipschitzWith_clampSign clampSign_zero hv

/-- The projected sign is real with values in `[-1, 1]`, since the projection
commutes with the clamp. -/
lemma projected_range : ∀ᵐ η ∂measure R ω₀,
    (projected R ω₀ η).im = 0 ∧ -1 ≤ (projected R ω₀ η).re ∧ (projected R ω₀ η).re ≤ 1 := by
  have he : lipschitzWith_clampSign.compLp clampSign_zero (signVector R ω₀) = signVector R ω₀ := by
    apply Lp.ext
    filter_upwards [lipschitzWith_clampSign.coeFn_compLp clampSign_zero (signVector R ω₀),
      sign_range R ω₀] with η hη h
    exact hη.trans (clampSign_eq h)
  have hp := projection_fixed_of_contraction (space (A := E) (representation R ω₀))
    (lipschitzWith_clampSign.compLp clampSign_zero)
    (lipschitzWith_clampSign.lipschitzWith_compLp clampSign_zero)
    (fun v hv => clampSign_mem R ω₀ hv) _ he
  have hae := lipschitzWith_clampSign.coeFn_compLp clampSign_zero (projected R ω₀)
  rw [projected, hp] at hae
  filter_upwards [hae] with η hη
  exact hη.symm ▸ clampSign_range _

/-- The projected sign is fixed by the rotations. -/
lemma projected_rotation_fixed (b : K) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) (projected R ω₀) = projected R ω₀ :=
  projection_covariance_fixed (representation R ω₀) (rotation R ω₀ b)
    (Homeomorph.mulLeft₀ (kCoeff b) (kCoeff_ne_zero b)) (mul_zero _)
    (rotation_covariance R ω₀ b) _ (rotation_signVector R ω₀ b)

/-- Spectral rigidity: away from zero, the projected sign has the sign's correlations. -/
lemma projected_corr (z : E) (hz : z ≠ 0) :
    ⟪projected R ω₀, op (representation R ω₀) z (projected R ω₀)⟫_ℂ = (corr R ω₀ z : ℂ) := by
  have hb := residual_fourier (representation R ω₀) (rotation R ω₀) (rotation_covariance R ω₀)
    (signVector R ω₀ - projected R ω₀)
    ((space (A := E) (representation R ω₀)).sub_starProjection_mem_orthogonal (signVector R ω₀))
    (fun b => by rw [map_sub, rotation_signVector, projected_rotation_fixed]) z hz
  exact (projection_coefficient (representation R ω₀) (signVector R ω₀) z hb).trans
    (inner_signVector R ω₀ z)

/-- The continuous extension `G(y)` of the orbit of the projected sign. -/
def field (y : ℂ) : Hilbert R ω₀ := orbitExtension (representation R ω₀) (projected R ω₀) y

/-- The field is continuous. -/
lemma continuous_field : Continuous (field R ω₀) :=
  orbitExtension_continuous _ (projected_mem R ω₀)

/-- On `E` the field is the orbit of the projected sign. -/
lemma field_eq (a : E) : field R ω₀ (a : ℂ) = op (representation R ω₀) a (projected R ω₀) :=
  orbitExtension_eq _ (projected_mem R ω₀) a

/-- The correlations of the field are translation invariant. -/
lemma field_inner (y w : ℂ) :
    ⟪field R ω₀ y, field R ω₀ (y + w)⟫_ℂ = ⟪projected R ω₀, field R ω₀ w⟫_ℂ :=
  orbitExtension_inner _ (projected_mem R ω₀) (projected_mem R ω₀) y w

/-- The field is real with values in `[-1, 1]`. -/
lemma field_range (y : ℂ) : ∀ᵐ η ∂measure R ω₀,
    (field R ω₀ y η).im = 0 ∧ -1 ≤ (field R ω₀ y η).re ∧ (field R ω₀ y η).re ≤ 1 := by
  have he : lipschitzWith_clampSign.compLp clampSign_zero (field R ω₀ y) = field R ω₀ y := by
    refine dense_E.denseRange_val.induction_on y (isClosed_eq
      ((lipschitzWith_clampSign.continuous_compLp clampSign_zero).comp (continuous_field R ω₀))
      (continuous_field R ω₀)) ?_
    intro a
    rw [field_eq, op_apply]
    apply Lp.ext
    filter_upwards [lipschitzWith_clampSign.coeFn_compLp clampSign_zero
        (Lp.compMeasurePreserving (trans R a) (trans_preserving R ω₀ a) (projected R ω₀)),
      Lp.coeFn_compMeasurePreserving (projected R ω₀) (trans_preserving R ω₀ a),
      (trans_preserving R ω₀ a).quasiMeasurePreserving.ae (projected_range R ω₀)]
      with η h1 h2 h3
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2]
    exact clampSign_eq h3
  have ha := lipschitzWith_clampSign.coeFn_compLp clampSign_zero (field R ω₀ y)
  rw [he] at ha
  filter_upwards [ha] with η hη
  exact hη.symm ▸ clampSign_range _

/-! ### Vanishing of `Q` on every triangle -/

/-- The sides avoided by a labeling are nonzero. -/
lemma ne_zero_of_mem (ω : Space R) {r : E} (hr : r ∈ R) : r ≠ 0 := by
  rintro rfl
  exact ω.property 0 hr 0 1 (by simp)

/-- `ζ ≠ 1`. -/
lemma ζE_sub_one_ne_zero : ζE - 1 ≠ 0 := by
  intro h
  have h' := congrArg (fun z : E => (z : ℂ)) h
  push_cast at h'
  have hn := norm_ζ_sub_one
  rw [← coe_ζE, h', norm_zero] at hn
  exact zero_ne_one hn

/-- On every triangle of side `r ∈ R`, `1` plus the three field correlations vanishes. -/
lemma triangle_sum {r : E} (hr : r ∈ R) (u : Circle) :
    1 + ⟪projected R ω₀, field R ω₀ (u * r)⟫_ℂ + ⟪projected R ω₀, field R ω₀ (u * (r * ζ))⟫_ℂ +
      ⟪projected R ω₀, field R ω₀ (u * (r * ζ) - u * r)⟫_ℂ = 0 := by
  have hφ : Continuous fun w => ⟪projected R ω₀, field R ω₀ w⟫_ℂ :=
    continuous_const.inner (continuous_field R ω₀)
  refine circle_closed_induction
    (p := fun v => 1 + ⟪projected R ω₀, field R ω₀ (v * r)⟫_ℂ +
      ⟪projected R ω₀, field R ω₀ (v * (r * ζ))⟫_ℂ +
      ⟪projected R ω₀, field R ω₀ (v * (r * ζ) - v * r)⟫_ℂ = 0)
    (isClosed_eq (((continuous_const.add (hφ.comp (continuous_id.mul continuous_const))).add
      (hφ.comp (continuous_id.mul continuous_const))).add
      (hφ.comp ((continuous_id.mul continuous_const).sub (continuous_id.mul continuous_const))))
      continuous_const) (fun b => ?_) u
  have hr0 := ne_zero_of_mem R ω₀ hr
  have e₁ : (b.val : ℂ) * r = ((kCoeff b * r : E) : ℂ) := rfl
  have e₂ : (b.val : ℂ) * (r * ζ) = ((kCoeff b * (r * ζE) : E) : ℂ) := rfl
  have e₃ : (b.val : ℂ) * (r * ζ) - b.val * r =
      ((kCoeff b * (r * ζE) - kCoeff b * r : E) : ℂ) := rfl
  have n₁ : kCoeff b * r ≠ 0 := mul_ne_zero (kCoeff_ne_zero b) hr0
  have n₂ : kCoeff b * (r * ζE) ≠ 0 :=
    mul_ne_zero (kCoeff_ne_zero b) (mul_ne_zero hr0 (by
      intro h
      have h' := congrArg (fun z : E => ‖(z : ℂ)‖) h
      simp [norm_ζ] at h'))
  have n₃ : kCoeff b * (r * ζE) - kCoeff b * r ≠ 0 := by
    rw [show kCoeff b * (r * ζE) - kCoeff b * r = kCoeff b * r * (ζE - 1) by ring]
    exact mul_ne_zero n₁ ζE_sub_one_ne_zero
  rw [e₃, e₁, e₂, field_eq, field_eq, field_eq, projected_corr R ω₀ _ n₁,
    projected_corr R ω₀ _ n₂, projected_corr R ω₀ _ n₃]
  have h := corr_triangle R ω₀ hr b
  have h' : ((1 + corr R ω₀ (kCoeff b * r) + corr R ω₀ (kCoeff b * (r * ζE)) +
      corr R ω₀ (kCoeff b * (r * ζE) - kCoeff b * r) : ℝ) : ℂ) = 0 := by
    rw [add_assoc, add_assoc, ← add_assoc (corr R ω₀ _), h]
    norm_num
  push_cast at h'
  exact h'

/-- On every triangle of side `r ∈ R`, `Q` of the field vanishes almost surely. -/
theorem qform_field_ae {r : E} (hr : r ∈ R) (p : ℂ) (u : Circle) :
    ∀ᵐ η ∂measure R ω₀, qform (field R ω₀ p η).re (field R ω₀ (p + u * r) η).re
      (field R ω₀ (p + u * (r * ζ)) η).re = 0 := by
  obtain ⟨hi, hval⟩ := integral_qform (measure R ω₀) (field R ω₀ p) (field R ω₀ (p + u * r))
    (field R ω₀ (p + u * (r * ζ))) ((field_range R ω₀ p).mono fun _ h => h.1)
    ((field_range R ω₀ _).mono fun _ h => h.1)
  have h₃ : p + u * (r * ζ) = (p + u * r) + (u * (r * ζ) - u * r) := by ring
  rw [field_inner, field_inner, h₃, field_inner, ← h₃, triangle_sum R ω₀ hr u,
    Complex.zero_re] at hval
  have hnn : 0 ≤ᵐ[measure R ω₀] fun η => qform (field R ω₀ p η).re
      (field R ω₀ (p + u * r) η).re (field R ω₀ (p + u * (r * ζ)) η).re := by
    filter_upwards [field_range R ω₀ p, field_range R ω₀ (p + u * r),
      field_range R ω₀ (p + u * (r * ζ))] with η h1 h2 h3
    exact qform_nonneg h1.2 h2.2 h3.2
  exact (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hval

/-- A jointly measurable field on `ℂ` times the label space whose `Q` vanishes almost
surely on every triangle of side in `R`. -/
theorem exists_measurable_qform_field :
    ∃ F : ℂ × Space R → ℂ, Measurable F ∧ ∀ r ∈ R, ∀ p : ℂ, ∀ u : Circle,
      ∀ᵐ η ∂measure R ω₀, qform (F (p, η)).re (F (p + u * r, η)).re
        (F (p + u * (r * ζ), η)).re = 0 := by
  obtain ⟨F, hF, hae⟩ := exists_measurable_field (measure R ω₀) (field R ω₀)
    (continuous_field R ω₀)
  refine ⟨F, hF, fun r hr p u => ?_⟩
  filter_upwards [hae p, hae (p + u * r), hae (p + u * (r * ζ)), qform_field_ae R ω₀ hr p u]
    with η h1 h2 h3 h4
  rw [h1, h2, h3]
  exact h4

end Erdos173.Transfer

end
