module

public import Erdos173.Basic
public import OAI.Analysis.PlaneSpectrum.Representations

/-!
# The stationary label model for equilateral avoidance

For a set `R` of sides in the carrier `E`, the labelings `η : E → Fin 2` with no
monochromatic equilateral triangle `(p, p + u r, p + u r ζ)`, `p ∈ E`, `u ∈ K`, `r ∈ R`,
form a compact space. Translations by `E` and rotations by `K` act on it, and OpenAI's
stationary mean gives an invariant probability measure from any one labeling. This
mirrors `OAI.PlaneFiveColor.LabelModel`, with triangle avoidance in place of properness.

The sign `s(η) = ±1` of the origin's label is a unit vector of `L²` fixed by the
rotations, whose translation coefficients are the correlations `ρ(z)`. Two signs out of
three that are not all equal satisfy `ab + ac + bc = -1`, so the three correlations of
every triangle of side `r ∈ R` sum to `-1`; correlations are radial, so `ρ(r) = -1/3`.

The facts about the carrier used here are isolated in the first section: `√3 ∈ E` (so
`ζ ∈ E`), and every unit of `E` is an element of `K`.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Transfer

open MeasureTheory
open OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor OAI.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace

variable [Carrier]

/-! ### Carrier facts -/

/-- `√3` lies in the carrier. -/
lemma sqrt_three_mem : ((√3 : ℝ) : ℂ) ∈ E :=
  Carrier.ofReal_mem (Carrier.sqrt_mem (by simp))

/-- Every unit of the carrier is the coefficient of an element of `K`. -/
lemma exists_kCoeff_eq (z : E) (hz : ‖(z : ℂ)‖ = 1) : ∃ b : K, kCoeff b = z :=
  ⟨⟨⟨z, mem_sphere_zero_iff_norm.mpr hz⟩, z.property⟩, rfl⟩

@[simp] lemma coe_kCoeff (u : K) : ((kCoeff u : E) : ℂ) = (u.val : ℂ) := rfl

/-! ### The sixth root of unity -/

omit [Carrier] in
/-- `ζ = (1 + √3 i)/2`. -/
lemma ζ_eq : ζ = (1 + ((√3 : ℝ) : ℂ) * Complex.I) / 2 := by
  apply Complex.ext <;> simp [ζ]

/-- `ζ` lies in the carrier. -/
lemma ζ_mem : ζ ∈ E := by
  rw [ζ_eq]
  have h₂ : (2 : ℂ) ∈ E := by simp
  exact E.div_mem (E.add_mem E.one_mem (E.mul_mem sqrt_three_mem imagUnit.property)) h₂

/-- `ζ` as an element of the carrier. -/
def ζE : E := ⟨ζ, ζ_mem⟩

@[simp] lemma coe_ζE : (ζE : ℂ) = ζ := rfl

/-! ### The space of admissible labelings -/

/-- `η` has no monochromatic equilateral triangle `(p, p + u r, p + u r ζ)` of side `r`
with `p ∈ E` and `u ∈ K`. -/
def AvoidsSide (r : E) (η : E → Fin 2) : Prop :=
  ∀ p : E, ∀ u : K, ¬ (η (p + kCoeff u * r) = η p ∧ η (p + kCoeff u * (r * ζE)) = η p)

variable (R : Set E)

/-- A labeling of `E` avoiding the equilateral triangles of every side in `R`. -/
def Admissible (η : E → Fin 2) : Prop := ∀ r ∈ R, AvoidsSide r η

/-- The space of admissible labelings. -/
abbrev Space := {η : E → Fin 2 // Admissible R η}

/-- The admissible labelings form a closed set. -/
theorem isClosed_admissible : IsClosed {η : E → Fin 2 | Admissible R η} := by
  unfold Admissible AvoidsSide
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun p =>
    isClosed_iInter fun u => ?_
  have hc : Continuous (fun η : E → Fin 2 =>
      (η p, η (p + kCoeff u * r), η (p + kCoeff u * (r * ζE)))) :=
    (continuous_apply p).prodMk ((continuous_apply _).prodMk (continuous_apply _))
  exact (isClosed_discrete {q : Fin 2 × Fin 2 × Fin 2 | ¬ (q.2.1 = q.1 ∧ q.2.2 = q.1)}).preimage hc

instance : CompactSpace (Space R) := isCompact_iff_compactSpace.mp (isClosed_admissible R).isCompact

/-- Translation by `a`. -/
def trans (a : E) (ω : Space R) : Space R := ⟨fun x => ω.val (x + a), by
  intro r hr p u h
  refine ω.property r hr (p + a) u ?_
  rwa [add_right_comm p a, add_right_comm p a]⟩

/-- Rotation by `b`. -/
def rotate (b : K) (ω : Space R) : Space R := ⟨fun x => ω.val (kCoeff b * x), by
  intro r hr p u h
  refine ω.property r hr (kCoeff b * p) (b * u) ?_
  simpa only [kCoeff_mul, mul_add, mul_assoc] using h⟩

@[simp] lemma trans_apply (a : E) (ω : Space R) (x : E) : (trans R a ω).val x = ω.val (x + a) :=
  rfl

@[simp] lemma rotate_apply (b : K) (ω : Space R) (x : E) :
    (rotate R b ω).val x = ω.val (kCoeff b * x) := rfl

lemma continuous_trans (a : E) : Continuous (trans R a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x + a)).comp continuous_subtype_val

lemma continuous_rotate (b : K) : Continuous (rotate R b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (kCoeff b * x)).comp continuous_subtype_val

@[simp] lemma trans_zero (ω : Space R) : trans R 0 ω = ω := by
  apply Subtype.ext
  funext x
  simp

lemma trans_add (a b : E) (ω : Space R) : trans R a (trans R b ω) = trans R (a + b) ω := by
  apply Subtype.ext
  funext x
  simp [add_assoc]

@[simp] lemma rotate_one (ω : Space R) : rotate R 1 ω = ω := by
  apply Subtype.ext
  funext x
  simp

lemma rotate_mul (a b : K) (ω : Space R) : rotate R a (rotate R b ω) = rotate R (a * b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (kCoeff b * (kCoeff a * x)) = ω.val (kCoeff (a * b) * x)
  rw [kCoeff_mul]
  ring_nf

/-- Translation by `a` after rotation by `b` is rotation after translation by `b a`. -/
lemma covariance (a : E) (b : K) (ω : Space R) :
    trans R a (rotate R b ω) = rotate R b (trans R (kCoeff b * a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply, rotate_apply, mul_add]

/-- Translation as a homeomorphism. -/
def transHomeo (a : E) : Space R ≃ₜ Space R where
  toFun := trans R a
  invFun := trans R (-a)
  left_inv ω := by rw [trans_add, neg_add_cancel, trans_zero]
  right_inv ω := by rw [trans_add, add_neg_cancel, trans_zero]
  continuous_toFun := continuous_trans R a
  continuous_invFun := continuous_trans R (-a)

/-- Rotation as a homeomorphism. -/
def rotateHomeo (b : K) : Space R ≃ₜ Space R where
  toFun := rotate R b
  invFun := rotate R b⁻¹
  left_inv ω := by rw [rotate_mul, inv_mul_cancel, rotate_one]
  right_inv ω := by rw [rotate_mul, mul_inv_cancel, rotate_one]
  continuous_toFun := continuous_rotate R b
  continuous_invFun := continuous_rotate R b⁻¹

/-- Translations, indexed by the discrete additive group. -/
abbrev Trans := Additive DiscreteE

/-- The translation action used by the stationary mean. -/
def tr (a : Trans) : Space R → Space R := trans R (Multiplicative.toAdd (Additive.toMul a))

/-- The rotation action used by the stationary mean. -/
def ro (b : Rot) : Space R → Space R := rotate R (rotMul b)

/-- The invariant probability measure generated by the labeling `ω₀`. -/
def measure (ω₀ : Space R) : Measure (Space R) := StationaryMean.measure (tr R) (ro R) ω₀

instance (ω₀ : Space R) : IsProbabilityMeasure (measure R ω₀) :=
  inferInstanceAs (IsProbabilityMeasure (StationaryMean.measure (tr R) (ro R) ω₀))

/-- Translations preserve the stationary measure. -/
lemma trans_preserving (ω₀ : Space R) (a : E) :
    MeasurePreserving (trans R a) (measure R ω₀) (measure R ω₀) := by
  apply StationaryMean.preserving_of_average (tr R) (ro R) ω₀ (transHomeo R a)
  intro f
  apply StationaryMean.average_translation (tr R) (ro R) ω₀
    (fun a b x => trans_add R _ _ x)
    (fun b a => Additive.ofMul (Multiplicative.ofAdd
      (kCoeff (rotMul b) * Multiplicative.toAdd (Additive.toMul a))))
    (fun a b x => covariance R _ _ x) (Additive.ofMul (Multiplicative.ofAdd a)) f
    (continuous_trans R a)

/-- Rotations preserve the stationary measure. -/
lemma rotate_preserving (ω₀ : Space R) (b : K) :
    MeasurePreserving (rotate R b) (measure R ω₀) (measure R ω₀) := by
  apply StationaryMean.preserving_of_average (tr R) (ro R) ω₀ (rotateHomeo R b)
  intro f
  exact StationaryMean.average_rotation (tr R) (ro R) ω₀
    (fun a b x => rotate_mul R _ _ x) (mulRot b) f (continuous_rotate R b)

variable (ω₀ : Space R)

/-- The `L²` space of the stationary measure. -/
abbrev Hilbert := Lp ℂ 2 (measure R ω₀)

/-- The Koopman operator of a translation. -/
def translation (a : E) : unitary (Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) :=
  Koopman.unitary (measure R ω₀) (transHomeo R a).toMeasurableEquiv (trans_preserving R ω₀ a)

/-- The Koopman operator of a rotation. -/
def rotation (b : K) : unitary (Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) :=
  Koopman.unitary (measure R ω₀) (rotateHomeo R b).toMeasurableEquiv (rotate_preserving R ω₀ b)

/-- The translation representation of the discrete carrier. -/
def representation : DiscreteE →* unitary (Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) where
  toFun a := translation R ω₀ (Multiplicative.toAdd a)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans R 0) (trans_preserving R ω₀ 0) v = v
    have he : trans R 0 = id := funext (trans_zero R)
    simp only [he, Lp.compMeasurePreserving_id_apply]
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving
        (trans R (Multiplicative.toAdd a + Multiplicative.toAdd b)) _ v =
      Lp.compMeasurePreserving (trans R (Multiplicative.toAdd a)) _
        (Lp.compMeasurePreserving (trans R (Multiplicative.toAdd b)) _ v)
    rw [← Lp.compMeasurePreserving_comp_apply]
    congr 2
    funext x
    exact (congrArg (fun c => trans R c x) (add_comm _ _)).trans (trans_add R _ _ x).symm

lemma op_apply (a : E) (v : Hilbert R ω₀) : op (representation R ω₀) a v =
    Lp.compMeasurePreserving (trans R a) (trans_preserving R ω₀ a) v := rfl

lemma rotation_apply (b : K) (v : Hilbert R ω₀) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) v =
      Lp.compMeasurePreserving (rotate R b) (rotate_preserving R ω₀ b) v := rfl

/-- Rotation conjugates translation by `a` to translation by `b a`. -/
lemma rotation_covariance (b : K) (a : E) (v : Hilbert R ω₀) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) (op (representation R ω₀) a v) =
      op (representation R ω₀) (kCoeff b * a)
        ((rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) v) := by
  simp only [rotation_apply, op_apply, ← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance R a b x

/-! ### The sign and its correlations -/

/-- The sign of the label at `z`: `1` for label `0`, `-1` for label `1`. -/
def sgnAt (z : E) (ω : Space R) : ℝ := if ω.val z = 0 then 1 else -1

lemma continuous_sgnAt (z : E) : Continuous (sgnAt R z) :=
  (continuous_of_discreteTopology (f := fun c : Fin 2 => if c = 0 then (1 : ℝ) else -1)).comp
    ((continuous_apply z).comp continuous_subtype_val)

/-- The sign correlation at displacement `z`. -/
def corr (z : E) : ℝ := ∫ ω, sgnAt R 0 ω * sgnAt R z ω ∂measure R ω₀

/-- The sign at the origin is square integrable. -/
lemma memLp_sign : MemLp (fun ω => (sgnAt R 0 ω : ℂ)) 2 (measure R ω₀) := by
  refine MemLp.of_bound ?_ 1 ?_
  · exact (Complex.continuous_ofReal.comp (continuous_sgnAt R 0)).aestronglyMeasurable
  · exact .of_forall fun ω => by dsimp [sgnAt]; split_ifs <;> simp

/-- The sign at the origin, as a vector of `L²`. -/
def signVector : Hilbert R ω₀ := (memLp_sign R ω₀).toLp fun ω => (sgnAt R 0 ω : ℂ)

/-- The sign vector is the sign at the origin. -/
lemma sign_ae : signVector R ω₀ =ᵐ[measure R ω₀] fun ω => (sgnAt R 0 ω : ℂ) :=
  (memLp_sign R ω₀).coeFn_toLp

/-- Translation coefficients of the sign vector are the correlations. -/
lemma inner_signVector (z : E) :
    ⟪signVector R ω₀, op (representation R ω₀) z (signVector R ω₀)⟫_ℂ = (corr R ω₀ z : ℂ) := by
  rw [op_apply, L2.inner_def, corr, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [sign_ae R ω₀,
    Lp.coeFn_compMeasurePreserving (signVector R ω₀) (trans_preserving R ω₀ z),
    (trans_preserving R ω₀ z).quasiMeasurePreserving.ae (sign_ae R ω₀)] with ω h1 h2 h3
  simp only [h1, h2, Function.comp_apply, h3, sgnAt, trans_apply, zero_add]
  split_ifs <;> simp

/-- The sign vector is a unit vector. -/
lemma norm_signVector_sq : ‖signVector R ω₀‖ ^ 2 = 1 := by
  have h : ⟪signVector R ω₀, signVector R ω₀⟫_ℂ = 1 := by
    rw [L2.inner_def]
    have he : (fun ω => ⟪signVector R ω₀ ω, signVector R ω₀ ω⟫_ℂ) =ᵐ[measure R ω₀]
        fun _ => (1 : ℂ) := by
      filter_upwards [sign_ae R ω₀] with ω h1
      simp only [h1, sgnAt]
      split_ifs <;> simp
    rw [integral_congr_ae he]
    simp
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : ((‖signVector R ω₀‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h
  exact Complex.ofReal_injective h'

/-- The sign vector is fixed by the rotations. -/
lemma rotation_signVector (b : K) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) (signVector R ω₀) = signVector R ω₀ := by
  rw [rotation_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (signVector R ω₀) (rotate_preserving R ω₀ b),
    (rotate_preserving R ω₀ b).quasiMeasurePreserving.ae (sign_ae R ω₀), sign_ae R ω₀]
    with ω h1 h2 h3
  simp only [Function.comp_apply, h1, h2, h3, sgnAt, rotate_apply, mul_zero]

lemma integrable_of_continuous {g : Space R → ℝ} (hg : Continuous g) :
    Integrable g (measure R ω₀) :=
  hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

lemma integral_trans (a : E) (g : Space R → ℝ) :
    ∫ ω, g (trans R a ω) ∂measure R ω₀ = ∫ ω, g ω ∂measure R ω₀ :=
  (trans_preserving R ω₀ a).integral_comp (transHomeo R a).measurableEmbedding g

lemma integral_rotate (b : K) (g : Space R → ℝ) :
    ∫ ω, g (rotate R b ω) ∂measure R ω₀ = ∫ ω, g ω ∂measure R ω₀ :=
  (rotate_preserving R ω₀ b).integral_comp (rotateHomeo R b).measurableEmbedding g

/-- The mean product of the signs at `a` and `b` is the correlation at `b - a`. -/
lemma integral_sgnAt_mul (a b : E) :
    ∫ ω, sgnAt R a ω * sgnAt R b ω ∂measure R ω₀ = corr R ω₀ (b - a) := by
  rw [corr, ← integral_trans R ω₀ a (fun ω => sgnAt R 0 ω * sgnAt R (b - a) ω)]
  simp [sgnAt]

/-- Correlations are radial on `E`: equal moduli differ by an element of `K`. -/
theorem corr_radial {z w : E} (h : ‖(z : ℂ)‖ = ‖(w : ℂ)‖) : corr R ω₀ z = corr R ω₀ w := by
  rcases eq_or_ne z 0 with rfl | hz
  · have hw : w = 0 := by
      apply Subtype.ext
      simpa [eq_comm] using h
    rw [hw]
  have hz' : (z : ℂ) ≠ 0 := by simpa using hz
  obtain ⟨b, hb⟩ := exists_kCoeff_eq (w / z) (by
    rw [IntermediateField.coe_div, norm_div, ← h, div_self (norm_ne_zero_iff.mpr hz')])
  have hb' : kCoeff b * z = w := by rw [hb, div_mul_cancel₀ w hz]
  rw [← hb', corr, corr, ← integral_rotate R ω₀ b (fun ω => sgnAt R 0 ω * sgnAt R z ω)]
  simp only [sgnAt, rotate_apply, mul_zero]
  rfl

/-- Three signs that are not all equal have pair products summing to `-1`. -/
lemma sgn_triangle {r : E} (hr : r ∈ R) (ω : Space R) (p : E) (u : K) :
    sgnAt R p ω * sgnAt R (p + kCoeff u * r) ω +
      sgnAt R p ω * sgnAt R (p + kCoeff u * (r * ζE)) ω +
      sgnAt R (p + kCoeff u * r) ω * sgnAt R (p + kCoeff u * (r * ζE)) ω = -1 := by
  have h := ω.property r hr p u
  unfold sgnAt
  generalize ω.val p = A at *
  generalize ω.val (p + kCoeff u * r) = B at *
  generalize ω.val (p + kCoeff u * (r * ζE)) = C at *
  fin_cases A <;> fin_cases B <;> fin_cases C <;> simp_all

/-- The three correlations of an equilateral triangle of side `r ∈ R` sum to `-1`. -/
theorem corr_triangle {r : E} (hr : r ∈ R) (u : K) :
    corr R ω₀ (kCoeff u * r) + corr R ω₀ (kCoeff u * (r * ζE)) +
      corr R ω₀ (kCoeff u * (r * ζE) - kCoeff u * r) = -1 := by
  have hi {g : Space R → ℝ} (hg : Continuous g) := integrable_of_continuous R ω₀ hg
  have hc := continuous_sgnAt R
  have h := integral_congr_ae (μ := measure R ω₀)
    (Filter.Eventually.of_forall (sgn_triangle R hr · 0 u))
  rw [integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    integral_add (hi (by fun_prop)) (hi (by fun_prop)), integral_sgnAt_mul, integral_sgnAt_mul,
    integral_sgnAt_mul] at h
  simpa using h

/-- The correlation at every side `r ∈ R` is `-1/3`. -/
theorem corr_side {r : E} (hr : r ∈ R) : corr R ω₀ r = -1 / 3 := by
  have h := corr_triangle R ω₀ hr 1
  have h₁ : corr R ω₀ (kCoeff 1 * (r * ζE)) = corr R ω₀ r := by
    apply corr_radial
    simp [norm_ζ]
  have h₂ : corr R ω₀ (kCoeff 1 * (r * ζE) - kCoeff 1 * r) = corr R ω₀ r := by
    apply corr_radial
    have he : ((kCoeff 1 * (r * ζE) - kCoeff 1 * r : E) : ℂ) = (r : ℂ) * (ζ - 1) := by
      simp only [kCoeff_one, one_mul]
      push_cast
      rw [coe_ζE]
      ring
    rw [he, norm_mul, norm_ζ_sub_one, mul_one]
  rw [h₁, h₂, kCoeff_one, one_mul] at h
  linarith

end Erdos173.Transfer

end
