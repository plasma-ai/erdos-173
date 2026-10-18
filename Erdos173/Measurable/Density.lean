module

public import Erdos173.Basic
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Density points of a measurable two-coloring

A set `K ⊆ ℂ` has *density zero* at `p` when `|K ∩ B(p, ρ)| = o(ρ²)` as `ρ → 0`.
For a two-coloring `c`, the point `p` is a density point of the class `i` when the
other class has density zero there. The *boundary* of `c` is the set of points at
which neither class has density zero; at such a point both classes have positive
upper density.

The density-zero condition can be tested along the radii `1/(k+1)`, because the
measure of `K ∩ B(p, ρ)` is monotone in `ρ`, so the set of points where `K` has
density zero is measurable. Lebesgue's density theorem makes the boundary null.
A coloring that weakly avoids some triangle has two classes of positive area:
if one class were null, almost every copy of the triangle would lie in the
other.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open MeasureTheory Metric Set Filter Topology OAI.EuclideanFiveColor

/-- The set `K` has density zero at `p`: `|K ∩ B(p, ρ)| = o(ρ²)` as `ρ → 0`. -/
def DensityZero (K : Set ℂ) (p : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ ρ, 0 < ρ → ρ < δ →
    volume (K ∩ closedBall p ρ) ≤ ENNReal.ofReal (ε * ρ ^ 2)

/-- The boundary of a two-coloring: the points at which neither class has density
zero. -/
def boundary (c : ℂ → Fin 2) : Set ℂ :=
  {p | ∀ i, ¬ DensityZero {z | c z = i} p}

/-- The measure of `K ∩ B(p, ρ)` is measurable in `p`. -/
lemma measurable_measure_inter_closedBall {K : Set ℂ} (hK : MeasurableSet K) (ρ : ℝ) :
    Measurable fun p => volume (K ∩ closedBall p ρ) := by
  have hs : MeasurableSet {q : ℂ × ℂ | q.2 ∈ K ∧ dist q.2 q.1 ≤ ρ} :=
    (hK.preimage measurable_snd).inter
      (measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const)
  exact measurable_measure_prodMk_left hs

/-- Density zero along the radii `1/(k+1)` implies density zero. -/
lemma densityZero_of_seq {K : Set ℂ} {p : ℂ}
    (h : ∀ n : ℕ, ∃ m : ℕ, ∀ k, m ≤ k →
      volume (K ∩ closedBall p (1 / (k + 1))) ≤
        ENNReal.ofReal (1 / (n + 1) * (1 / (k + 1)) ^ 2)) :
    DensityZero K p := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by positivity : 0 < ε / 4)
  obtain ⟨m, hm⟩ := h n
  refine ⟨1 / (m + 1), by positivity, fun ρ hρ hρδ => ?_⟩
  have hinv : (m + 1 : ℝ) < ρ⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hρ]; simpa using hρδ
  set j := ⌊ρ⁻¹⌋₊ with hj
  have hj1 : (m + 1 : ℝ) ≤ j := by
    have : m + 1 ≤ j := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hjle : (j : ℝ) ≤ ρ⁻¹ := Nat.floor_le (by positivity)
  have hjlt : ρ⁻¹ < j + 1 := Nat.lt_floor_add_one _
  have hjpos : (1 : ℝ) ≤ j := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hjnat : 1 ≤ j := by exact_mod_cast hjpos
  have hk : m ≤ j - 1 := by
    have : m + 1 ≤ j := by exact_mod_cast hj1
    omega
  have hcast : ((j - 1 : ℕ) : ℝ) + 1 = j := by
    rw [Nat.cast_sub hjnat]; push_cast; ring
  have key := hm (j - 1) hk
  rw [hcast] at key
  have hρj : ρ ≤ 1 / j := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hjle hρ.le
    rw [mul_inv_cancel₀ hρ.ne'] at this
    linarith [mul_comm ρ (j : ℝ)]
  have hj2 : 1 / (j : ℝ) < 2 * ρ := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 < ρ * (j + 1) := by
      have := mul_lt_mul_of_pos_left hjlt hρ
      rwa [mul_inv_cancel₀ hρ.ne'] at this
    nlinarith
  calc volume (K ∩ closedBall p ρ)
      ≤ volume (K ∩ closedBall p (1 / j)) := by
        gcongr
    _ ≤ ENNReal.ofReal (1 / (n + 1) * (1 / j) ^ 2) := key
    _ ≤ ENNReal.ofReal (ε * ρ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have h0 : 0 ≤ 1 / (j : ℝ) := by positivity
        have hsq : (1 / (j : ℝ)) ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
        have hn' : (1 : ℝ) / (n + 1) ≤ ε / 4 := hn.le
        calc 1 / ((n : ℝ) + 1) * (1 / j) ^ 2 ≤ ε / 4 * (4 * ρ ^ 2) := by
              gcongr
          _ = ε * ρ ^ 2 := by ring

/-- The points at which a measurable set has density zero form a measurable set. -/
theorem measurableSet_densityZero {K : Set ℂ} (hK : MeasurableSet K) :
    MeasurableSet {p | DensityZero K p} := by
  have heq : {p | DensityZero K p} = ⋂ n : ℕ, ⋃ m : ℕ, ⋂ k : ℕ, ⋂ (_ : m ≤ k),
      {p | volume (K ∩ closedBall p (1 / (k + 1))) ≤
        ENNReal.ofReal (1 / (n + 1) * (1 / (k + 1)) ^ 2)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro h n
      obtain ⟨δ, hδ, hp⟩ := h (1 / (n + 1)) (by positivity)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine ⟨m, fun k hk => hp _ (by positivity) (lt_of_le_of_lt ?_ hm)⟩
      gcongr
    · exact densityZero_of_seq
  rw [heq]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
    MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (measurable_measure_inter_closedBall hK _) measurable_const

/-- Lebesgue's density theorem: a measurable set has density zero at almost every
point outside it. -/
theorem ae_densityZero {K : Set ℂ} (hK : MeasurableSet K) :
    ∀ᵐ p, p ∉ K → DensityZero K p := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hK]
    with p hp hpK
  rw [indicator_of_notMem hpK] at hp
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.1 hp) (ENNReal.ofReal (ε / 4)) (by positivity)
  obtain ⟨δ, hδ, hP⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hball : volume (closedBall p ρ) = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow hρ.le, mul_comm]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  have h1 := hP ⟨hρ, hρδ⟩
  rw [ENNReal.div_le_iff (by rw [hball]; simp; positivity) (by rw [hball]; simp)] at h1
  refine h1.trans ?_
  rw [hball, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := Real.pi_le_four
  have : 0 ≤ ε * ρ ^ 2 := by positivity
  nlinarith

/-- The boundary of a measurable two-coloring is measurable. -/
theorem measurableSet_boundary {c : ℂ → Fin 2} (hc : Measurable c) :
    MeasurableSet (boundary c) := by
  have : boundary c = ⋂ i, {p | DensityZero {z | c z = i} p}ᶜ := by
    ext p; simp [boundary]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_densityZero (measurableSet_eq_fun hc measurable_const)).compl

/-- The boundary of a measurable two-coloring is null. -/
theorem volume_boundary {c : ℂ → Fin 2} (hc : Measurable c) : volume (boundary c) = 0 := by
  have h : ∀ᵐ p, ∀ i, p ∉ {z | c z = i} → DensityZero {z | c z = i} p :=
    ae_all_iff.2 fun i => ae_densityZero (measurableSet_eq_fun hc measurable_const)
  refine measure_mono_null (fun p hp => ?_) (ae_iff.1 h)
  intro hall
  refine hp (c p + 1) (hall _ ?_)
  change c p ≠ c p + 1
  generalize c p = a
  fin_cases a <;> decide

/-- Translating a null set along a continuous family of directions gives a null set
of copies. -/
lemma ae_prod_add_notMem {N : Set ℂ} (hN : MeasurableSet N) (hN0 : volume N = 0)
    {w : Angles → ℂ} (hw : Continuous w) :
    ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure, q.1 + w q.2 ∉ N := by
  rw [ae_iff]
  simp only [not_not]
  have hm : MeasurableSet {q : ℂ × Angles | q.1 + w q.2 ∈ N} :=
    hN.preimage (by fun_prop)
  rw [Measure.prod_apply_symm hm]
  refine (lintegral_congr fun t => ?_).trans lintegral_zero
  change volume ((· + w t) ⁻¹' N) = 0
  rw [measure_preimage_add_right]
  exact hN0

/-- If a measurable two-coloring weakly avoids a triangle, both classes have
positive area. -/
theorem volume_ne_zero_of_weaklyAvoids {c : ℂ → Fin 2} (hc : Measurable c) {a b : ℂ}
    (h : WeaklyAvoids c a b) (i : Fin 2) : volume {z | c z = i} ≠ 0 := by
  intro h0
  have hN : MeasurableSet {z | c z = i} := measurableSet_eq_fun hc measurable_const
  have h1 := ae_prod_add_notMem hN h0 (w := fun _ => 0) continuous_const
  have h2 := ae_prod_add_notMem hN h0 (w := fun t => direction t * a)
    (direction_continuous.mul continuous_const)
  have h3 := ae_prod_add_notMem hN h0 (w := fun t => direction t * b)
    (direction_continuous.mul continuous_const)
  have hfalse : ∀ᵐ _q ∂(volume : Measure ℂ).prod angularMeasure, False := by
    filter_upwards [h, h1, h2, h3] with q hq hq1 hq2 hq3
    apply hq
    simp only [add_zero] at hq1 hq2 hq3
    constructor
    · generalize c (q.1 + direction q.2 * a) = x at hq2
      generalize c q.1 = y at hq1
      fin_cases i <;> fin_cases x <;> fin_cases y <;> simp_all
    · generalize c (q.1 + direction q.2 * b) = x at hq3
      generalize c q.1 = y at hq1
      fin_cases i <;> fin_cases x <;> fin_cases y <;> simp_all
  rw [ae_iff] at hfalse
  simp only [not_false_eq_true] at hfalse
  have huniv : (volume.prod angularMeasure) (univ : Set (ℂ × Angles)) = 0 := hfalse
  rw [← univ_prod_univ, Measure.prod_prod] at huniv
  simp at huniv

end Erdos173

end
