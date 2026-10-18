module

public import Erdos173.Bessel.Basic
public import Erdos173.Transfer.LabelModel
public import OAI.Analysis.PlaneSpectrum.CircleDecay
public import OAI.Analysis.PlaneSpectrum.Ergodicity
public import OAI.Geometry.PlaneColoring.BorelTransfer

/-!
# The radial spectral measure of the sign

The spectral measure of the sign vector lives on the dual `D` of the discrete carrier and
is invariant under the rotations `K`. Its restriction off the ordinary characters `C` is
wild, so by OpenAI's spectral rigidity theorem its Fourier coefficients vanish away from
zero. Its restriction to `C` pulls back along the character map `j` to a finite measure
`ν` on `ℂ` of mass at most `‖s‖² = 1`. Averaging over the circle, which `K` fills
densely, turns its Fourier transform into `J₀`:

`ρ(z) = ∫ J₀(|z| |ξ|) dν(ξ)` for `z ≠ 0`.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Transfer

open MeasureTheory Filter
open OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
open scoped ComplexConjugate

variable [Carrier]

variable (R : Set E) (ω₀ : Space R)

/-- The spectral measure of the sign vector. -/
abbrev spectralMeasure : Measure D :=
  VectorMeasure.measure (CommutingSpectral.calculus (representation R ω₀)) (signVector R ω₀)

/-- Fourier coefficients of the spectral measure are the correlations. -/
lemma integral_eval_spectralMeasure (a : E) :
    ∫ d, (eval a d : ℂ) ∂spectralMeasure R ω₀ = (corr R ω₀ a : ℂ) := by
  have hh := VectorMeasure.integral_complex (CommutingSpectral.calculus (representation R ω₀))
    (signVector R ω₀) (CommutingSpectral.evaluation (G := DiscreteE) (Multiplicative.ofAdd a))
  rw [CommutingSpectral.calculus_evaluation (representation R ω₀) (Multiplicative.ofAdd a)] at hh
  exact hh.trans (inner_signVector R ω₀ a)

/-- Off the ordinary characters, the spectral measure is wild. -/
lemma isWild_restrict_compl : IsWild ((spectralMeasure R ω₀).restrict (C : Set D)ᶜ) := by
  refine ⟨fun u => ?_, ?_⟩
  · have hp := vectorMeasure_invariant (representation R ω₀) (rotation R ω₀)
      (rotation_covariance R ω₀) (signVector R ω₀) (rotation_signVector R ω₀) u
    have hs : (fun d : D => u • d) ⁻¹' (C : Set D)ᶜ = (C : Set D)ᶜ := by
      ext d
      exact not_congr (scalar_mem_C_iff (kCoeff_ne_zero u) d)
    simpa only [hs] using hp.restrict_preimage measurableSet_C.compl
  · rw [Measure.restrict_apply measurableSet_C, Set.inter_compl_self, measure_empty]

omit [Carrier] in
/-- The angular average of `exp (i ⟪ξ, u z⟫)` has real part `J₀(|z| |ξ|)`. -/
lemma re_integral_direction (z ξ : ℂ) :
    (∫ t, (Circle.exp (inner ℝ ξ (direction t * z)) : ℂ) ∂angularMeasure).re =
      besselJ0 (‖z‖ * ‖ξ‖) := by
  let η : ℂ := (2 * Real.pi)⁻¹ • (ξ * conj z)
  have he (t : Angles) : (Circle.exp (inner ℝ ξ (direction t * z)) : ℂ) =
      planePhase (direction t) η := by
    rw [planePhase, Real.fourierChar_apply, Circle.coe_exp]
    congr 3
    simp only [η, Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.smul_re, Complex.smul_im, Complex.mul_im, smul_eq_mul]
    field_simp
    ring
  have hn : 2 * Real.pi * ‖η‖ = ‖z‖ * ‖ξ‖ := by
    simp only [η, norm_smul, norm_mul, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
    field_simp
  rw [integral_congr_ae (Eventually.of_forall he), ← circleSymbol, circleSymbol_integral, hn,
    Complex.smul_re, smul_eq_mul, besselJ0, ← Complex.reCLM_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _
      ((circleOscillation_continuous _).intervalIntegrable _ _)]
  simp only [Complex.reCLM_apply, circleOscillation, Complex.exp_ofReal_mul_I_re]

/-- The sign correlations are the Bessel transforms of a finite measure of mass at most
one: `ρ(z) = ∫ J₀(|z| |ξ|) dν(ξ)` for `z ≠ 0`. -/
theorem exists_radial_measure :
    ∃ ν : Measure ℂ, IsFiniteMeasure ν ∧ ν.real Set.univ ≤ 1 ∧
      ∀ z : E, z ≠ 0 → corr R ω₀ z = ∫ ξ, besselJ0 (‖(z : ℂ)‖ * ‖ξ‖) ∂ν := by
  let μ := spectralMeasure R ω₀
  let ν := μ.comap j
  have hj := j_measurableEmbedding
  -- the wild part has no Fourier coefficients away from zero, so only `ν` remains
  have hfourier (a : E) (ha : a ≠ 0) :
      (corr R ω₀ a : ℂ) = ∫ ξ, (Circle.exp (inner ℝ ξ (a : ℂ)) : ℂ) ∂ν := by
    have hi : Integrable (fun d => (eval a d : ℂ)) μ :=
      Integrable.of_bound (measurable_eval_coe a).aestronglyMeasurable 1
        (Eventually.of_forall fun d => (Circle.norm_coe _).le)
    rw [← integral_eval_spectralMeasure, ← integral_add_compl measurableSet_C hi,
      finite_wild_fourier _ (isWild_restrict_compl R ω₀) a ha, add_zero]
    change ∫ d in Set.range j, (eval a d : ℂ) ∂μ = _
    rw [← hj.map_comap, hj.integral_map]
    rfl
  let φ : ℂ → ℂ := fun w => ∫ ξ, (Circle.exp (inner ℝ ξ w) : ℂ) ∂ν
  have hφ : Continuous φ := by
    refine continuous_of_dominated (bound := fun _ => 1) (fun w => ?_)
      (fun w => Eventually.of_forall fun ξ => (Circle.norm_coe _).le) (integrable_const 1)
      (Eventually.of_forall fun ξ => ?_)
    · exact (by fun_prop : Continuous fun ξ : ℂ => (Circle.exp (inner ℝ ξ w) : ℂ))
        |>.aestronglyMeasurable
    · fun_prop
  -- `K` is dense in the circle, so `φ` is constant on circles about the origin
  have hrot (z : E) (hz : z ≠ 0) (u : Circle) : φ (u * z) = corr R ω₀ z := by
    refine circle_closed_induction (p := fun x => φ (x * z) = corr R ω₀ z)
      (isClosed_eq (hφ.comp (continuous_id.mul continuous_const)) continuous_const)
      (fun b => ?_) u
    have hn : ‖((kCoeff b * z : E) : ℂ)‖ = ‖(z : ℂ)‖ := by
      change ‖(b.val : ℂ) * z‖ = _
      rw [norm_mul, Circle.norm_coe, one_mul]
    change φ ((kCoeff b * z : E) : ℂ) = _
    rw [← corr_radial R ω₀ hn]
    exact (hfourier _ (mul_ne_zero (kCoeff_ne_zero b) hz)).symm
  refine ⟨ν, inferInstance, ?_, fun z hz => ?_⟩
  · have hu : ν.real Set.univ = μ.real (Set.range j) := by
      rw [Measure.real, Measure.real, hj.comap_apply, Set.image_univ]
    rw [hu]
    calc
      _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := (VectorMeasure.measure_univ _ _).trans (norm_signVector_sq R ω₀)
  -- average over the circle and exchange the order of integration
  have hint : Integrable (Function.uncurry fun (t : Angles) (ξ : ℂ) =>
      (Circle.exp (inner ℝ ξ (direction t * z)) : ℂ)) (angularMeasure.prod ν) :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by
      have := direction_continuous
      unfold Function.uncurry
      fun_prop)) 1 (Eventually.of_forall fun p => (Circle.norm_coe _).le)
  have hc : (corr R ω₀ z : ℂ) =
      ∫ ξ, ∫ t, (Circle.exp (inner ℝ ξ (direction t * z)) : ℂ) ∂angularMeasure ∂ν := by
    rw [← integral_integral_swap hint]
    calc
      (corr R ω₀ z : ℂ) = ∫ t : Angles, (corr R ω₀ z : ℂ) ∂angularMeasure := by simp
      _ = _ := integral_congr_ae (Eventually.of_forall fun t =>
        (hrot z hz (AddCircle.toCircle t)).symm)
  -- the correlation is real, so it is the real part `J₀` of the angular average
  have hre := congrArg Complex.re hc
  rw [Complex.ofReal_re] at hre
  rw [hre]
  exact (integral_re hint.integral_prod_right).symm.trans
    (integral_congr_ae (Eventually.of_forall fun ξ => re_integral_direction z ξ))

end Erdos173.Transfer

end
