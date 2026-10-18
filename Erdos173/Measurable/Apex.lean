module

public import Erdos173.Measurable.Density

/-!
# The apex lemma

Let a measurable two-coloring `c` weakly avoid the triangle `(0, a, b)`, let the
class `i` have positive upper density at `p`, and let `u₀` be a direction. Then
`p + u₀ a` and `p + u₀ b` are not both density points of the class `i`.

Otherwise take a radius `h` at which `|K ∩ B(p, h)| > ε h²`, where `K` is the
class `i`, and the arc `T` of directions within `h / L` of `u₀`, with
`L = |a| + |b| + 1`. For `q ∈ B(p, h)` and `u ∈ T` the vertex `q + u a` lies in
`B(p + u₀ a, 2h)`, where the other class has measure `o(h²)`; so the copies
`(q, u)` with `q ∈ K ∩ B(p, h)` and `u ∈ T` whose vertex `q + u a` or `q + u b`
leaves `K` have measure `o(h²) |T|`, while all of them have measure at least
`ε h² |T|`. The remaining copies are monochromatic and have positive measure,
contrary to weak avoidance.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open MeasureTheory Metric Set Filter OAI.EuclideanFiveColor

/-- The apex lemma: if `c` weakly avoids `(0, a, b)` and the class `i` has
positive upper density at `p`, then for no direction `u₀` are both `p + u₀ a` and
`p + u₀ b` density points of the class `i`. -/
theorem apex_density {c : ℂ → Fin 2} (hc : Measurable c) {a b : ℂ} (h : WeaklyAvoids c a b)
    {i : Fin 2} {p : ℂ} (hp : ¬ DensityZero {z | c z = i} p) (t₀ : Angles)
    (ha : DensityZero {z | c z ≠ i} (p + direction t₀ * a))
    (hb : DensityZero {z | c z ≠ i} (p + direction t₀ * b)) : False := by
  set K : Set ℂ := {z | c z = i} with hK
  set L : ℝ := ‖a‖ + ‖b‖ + 1 with hL
  have hL0 : 0 < L := by rw [hL]; positivity
  unfold DensityZero at hp
  push Not at hp
  obtain ⟨ε, hε, hp⟩ := hp
  obtain ⟨δa, hδa, ha⟩ := ha (ε / 16) (by positivity)
  obtain ⟨δb, hδb, hb⟩ := hb (ε / 16) (by positivity)
  obtain ⟨r, hr, hrδ, hgood⟩ := hp (min δa δb / 2) (by positivity)
  have h2a : 2 * r < δa := by have := min_le_left δa δb; linarith
  have h2b : 2 * r < δb := by have := min_le_right δa δb; linarith
  set T : Set Angles := {t | dist (direction t) (direction t₀) < r / L} with hT
  have hTo : IsOpen T :=
    isOpen_lt (direction_continuous.dist continuous_const) continuous_const
  have hTpos : angularMeasure T ≠ 0 :=
    (hTo.measure_pos _ ⟨t₀, by simp only [hT, mem_ofPred_eq, dist_self]; positivity⟩).ne'
  have hTfin : angularMeasure T ≠ ⊤ := measure_ne_top _ _
  -- the copies whose vertex `q + u w` leaves the class `i`
  have hbad : ∀ w : ℂ, ‖w‖ ≤ L → ∀ C,
      volume ({z | c z ≠ i} ∩ closedBall (p + direction t₀ * w) (2 * r)) ≤ C →
      (volume.prod angularMeasure)
        {q : ℂ × Angles | q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * w) ≠ i}
        ≤ C * angularMeasure T := by
    intro w hw C hC
    have hm : MeasurableSet {q : ℂ × Angles |
        q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * w) ≠ i} := by
      refine (measurableSet_closedBall.preimage measurable_fst).inter
        ((hTo.measurableSet.preimage measurable_snd).inter ?_)
      refine (measurableSet_eq_fun (hc.comp ?_) measurable_const).compl
      exact (continuous_fst.add
        ((direction_continuous.comp continuous_snd).mul continuous_const)).measurable
    rw [Measure.prod_apply_symm hm, ← lintegral_indicator_const hTo.measurableSet]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ T
    · rw [indicator_of_mem ht]
      refine le_trans (measure_mono (t := (· + direction t * w) ⁻¹'
        ({z | c z ≠ i} ∩ closedBall (p + direction t₀ * w) (2 * r))) ?_) ?_
      · rintro x ⟨hx, -, hcx⟩
        refine ⟨hcx, ?_⟩
        rw [mem_closedBall] at hx ⊢
        have htd : dist (direction t) (direction t₀) < r / L := ht
        calc dist (x + direction t * w) (p + direction t₀ * w)
            ≤ dist x p + dist (direction t * w) (direction t₀ * w) := dist_add_add_le _ _ _ _
          _ ≤ r + r := by
            gcongr
            rw [dist_eq_norm, ← sub_mul, norm_mul, ← dist_eq_norm]
            calc dist (direction t) (direction t₀) * ‖w‖ ≤ r / L * L := by
                  gcongr
              _ = r := by field_simp
          _ = 2 * r := by ring
      · rw [measure_preimage_add_right]
        exact hC
    · rw [indicator_of_notMem ht]
      exact le_of_eq (measure_mono_null (fun x hx => (ht hx.2.1).elim) measure_empty)
  have hmono : (volume.prod angularMeasure)
      {q : ℂ × Angles | MonoCopy c a b q.1 (direction q.2)} = 0 := by
    simpa using ae_iff.1 h
  set C := ENNReal.ofReal (ε / 16 * (2 * r) ^ 2) with hC
  have hA := hbad a (by rw [hL]; linarith [norm_nonneg b]) C (ha (2 * r) (by positivity) h2a)
  have hB := hbad b (by rw [hL]; linarith [norm_nonneg a]) C (hb (2 * r) (by positivity) h2b)
  have hsub : (K ∩ closedBall p r) ×ˢ T ⊆
      {q : ℂ × Angles | MonoCopy c a b q.1 (direction q.2)} ∪
        {q : ℂ × Angles | q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * a) ≠ i} ∪
        {q : ℂ × Angles | q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * b) ≠ i} := by
    rintro ⟨x, t⟩ ⟨⟨hxK, hxr⟩, ht⟩
    by_contra hq
    simp only [mem_union, mem_ofPred_eq, not_or, not_and, not_not] at hq
    obtain ⟨⟨hm, hqa⟩, hqb⟩ := hq
    have hxK' : c x = i := hxK
    exact hm ⟨(hqa hxr ht).trans hxK'.symm, (hqb hxr ht).trans hxK'.symm⟩
  have hle : volume (K ∩ closedBall p r) * angularMeasure T ≤ (C + C) * angularMeasure T := by
    rw [← Measure.prod_prod, add_mul]
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add_left (measure_union_le _ _) _
      _ ≤ 0 + C * angularMeasure T + C * angularMeasure T := by
        rw [hmono]
        gcongr
      _ = _ := by rw [zero_add]
  rw [ENNReal.mul_le_mul_iff_left hTpos hTfin] at hle
  have hCC : C + C < ENNReal.ofReal (ε * r ^ 2) := by
    rw [hC, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith [sq_nonneg r, mul_pos hε (pow_pos hr 2)]
  exact absurd (hle.trans_lt (hCC.trans hgood)) (lt_irrefl _)

end Erdos173

end
