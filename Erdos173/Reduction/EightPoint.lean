module

public import Erdos173.Basic

/-!
# The eight-point configuration

Lemma 1.3 of Jelínek, Kynčl, Stolař and Valla, which they take from Erdős,
Graham, Montgomery, Rothschild, Spencer and Straus, in coordinates. Put
`A = 0`, `B = a`, `C = a ζ`, `D = z`, `B' = ζ z`, `A' = a + ζ z`,
`C' = a ζ̄ + ζ z` and `D' = a - ζ̄ z`. The triples `ABC`, `A'B'C'` are
equilateral of side `a`, `ADB'`, `A'D'B` of side `|z|` and `BDC'`, `B'D'C` of
side `|z - a|`, and `BAD`, `CAB'`, `CBD'`, `B'A'D'`, `C'A'B`, `C'B'D` are
orientation-preserving copies of the triangle `(a, 0, z)`.

(i) If `A, B, C` have one color, one of the six copies is monochromatic.
(ii) If `B, A, D` have one color, one of the six equilateral triples is
monochromatic. The positive-measure form of (ii) composes the configuration
with a variable motion, which preserves area times arc length.

In the proofs `ζ̄` is written `1 - ζ`, so that every incidence of the
configuration is a ring identity. The copy of `(0, a, b)` with multiplier `m`
and translation `t`, placed by the motion `(p, u)`, is the copy placed by
`(p + u t, u m)`; each listed triple is such a copy of the template or of a
standard equilateral triangle.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open MeasureTheory OAI.EuclideanFiveColor

namespace EightPoint

/-- Composing a placement with a fixed rotation and a translation along the placed frame
preserves area times normalized arc length. -/
lemma ae_motion {P : ℂ → ℂ → Prop} (X w : ℂ) (hw : ‖w‖ = 1)
    (h : ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure, P q.1 (direction q.2)) :
    ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure,
      P (q.1 + direction q.2 * X) (direction q.2 * w) := by
  obtain ⟨t, ht⟩ := Circle.exp_surjective (⟨w, mem_sphere_zero_iff_norm.2 hw⟩ : Circle)
  set φ : Angles := (t : Angles)
  have hφ : direction φ = w := by simp [φ, ht]
  have hS : MeasurePreserving (fun q : Angles × ℂ => (q.1 + φ, q.2 + direction q.1 * X))
      (angularMeasure.prod (volume : Measure ℂ)) (angularMeasure.prod volume) :=
    (measurePreserving_add_right angularMeasure φ).skew_product
      (g := fun θ p => p + direction θ * X)
      (by
        have := direction_continuous
        exact Continuous.measurable (by fun_prop))
      (Filter.Eventually.of_forall fun θ => map_add_right_eq_self volume _)
  have hT : MeasurePreserving
      (fun q : ℂ × Angles => (q.1 + direction q.2 * X, q.2 + φ))
      ((volume : Measure ℂ).prod angularMeasure) ((volume : Measure ℂ).prod angularMeasure) :=
    Measure.measurePreserving_swap.comp (hS.comp Measure.measurePreserving_swap)
  filter_upwards [hT.quasiMeasurePreserving.tendsto_ae.eventually h] with q hq
  simpa [direction, AddCircle.toCircle_add, ← hφ] using hq

/-- The copy of `(0, a, b)` with multiplier `m` and translation `t`, placed by `(p, u)`. -/
lemma monoCopy_iff (c : ℂ → Fin 2) (a b p u t m x y : ℂ) (hx : t + m * a = x)
    (hy : t + m * b = y) :
    MonoCopy c a b (p + u * t) (u * m) ↔
      c (p + u * x) = c (p + u * t) ∧ c (p + u * y) = c (p + u * t) := by
  subst hx hy
  have e₁ : p + u * t + u * m * a = p + u * (t + m * a) := by ring
  have e₂ : p + u * t + u * m * b = p + u * (t + m * b) := by ring
  simp only [MonoCopy, e₁, e₂]

/-- The color bookkeeping of part (i). -/
lemma forcing_i : ∀ A B C D B' A' C' D' : Fin 2, B = A → C = A →
    ¬ (B = A ∧ D = A) → ¬ (C = A ∧ B' = A) → ¬ (C = B ∧ D' = B) →
    ¬ (B' = A' ∧ D' = A') → ¬ (C' = A' ∧ B = A') → ¬ (C' = B' ∧ D = B') → False := by
  intro A B C D B' A' C' D'
  omega

/-- The color bookkeeping of part (ii). -/
lemma forcing_ii : ∀ A B C D B' A' C' D' : Fin 2, B = A → D = A →
    ¬ (D = A ∧ B' = A) → ¬ (B = A ∧ C = A) → ¬ (D = B ∧ C' = B) →
    ¬ (B' = A' ∧ C' = A') → ¬ (D' = A' ∧ B = A') → ¬ (D' = B' ∧ C = B') → False := by
  intro A B C D B' A' C' D'
  omega

end EightPoint

open EightPoint

/-- Part (i): a monochromatic equilateral triangle of side `a` forces a
monochromatic copy of every triangle with a side `a`. -/
theorem not_avoids_of_not_avoidsEq (c : ℂ → Fin 2) {a : ℝ} {z : ℂ}
    (h : ¬ AvoidsEq c a) : ¬ Avoids c a z := by
  intro hav
  simp only [AvoidsEq, Avoids, not_forall, not_not] at h
  obtain ⟨p, u, hu, hABC⟩ := h
  have key : ∀ t m x y : ℂ, ‖m‖ = 1 → t + m * a = x → t + m * z = y →
      ¬ (c (p + u * x) = c (p + u * t) ∧ c (p + u * y) = c (p + u * t)) := by
    intro t m x y hm hx hy
    rw [← monoCopy_iff c a z p u t m x y hx hy]
    exact hav _ _ (by rw [norm_mul, hu, hm, one_mul])
  -- `BAD`, `CAB'`, `CBD'`, `B'A'D'`, `C'A'B`, `C'B'D`
  have h₁ := key 0 1 a z (by simp) (by ring) (by ring)
  have h₂ := key 0 ζ (a * ζ) (ζ * z) norm_ζ (by ring) (by ring)
  have h₃ := key a (ζ - 1) (a * ζ) (a - (1 - ζ) * z) norm_ζ_sub_one (by ring) (by ring)
  have h₄ := key (a + ζ * z) (-1) (ζ * z) (a - (1 - ζ) * z) (by simp) (by ring) (by ring)
  have h₅ := key (a + ζ * z) (-ζ) (a * (1 - ζ) + ζ * z) a (by simp [norm_ζ]) (by ring)
    (by ring)
  have h₆ := key (ζ * z) (1 - ζ) (a * (1 - ζ) + ζ * z) z norm_one_sub_ζ (by ring) (by ring)
  simp only [mul_zero, add_zero] at h₁ h₂
  exact forcing_i _ _ _ _ _ _ _ _ hABC.1 hABC.2 h₁ h₂ h₃ h₄ h₅ h₆

/-- Part (ii), in measure form: if almost no equilateral triangle of side `a`,
`|z|` or `|z - a|` is monochromatic, then almost no copy of `(0, a, z)` is. -/
theorem weaklyAvoids_of_weaklyAvoidsEq (c : ℂ → Fin 2) {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz0 : z ≠ 0) (hza : z ≠ a) (h₁ : WeaklyAvoidsEq c a) (h₂ : WeaklyAvoidsEq c ‖z‖)
    (h₃ : WeaklyAvoidsEq c ‖z - a‖) : WeaklyAvoids c a z := by
  have key : ∀ {s : ℝ}, 0 < s → WeaklyAvoidsEq c s → ∀ X Y Z : ℂ, ‖Y - X‖ = s →
      Z = X + ζ * (Y - X) → ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure,
        ¬ (c (q.1 + direction q.2 * Y) = c (q.1 + direction q.2 * X) ∧
          c (q.1 + direction q.2 * Z) = c (q.1 + direction q.2 * X)) := by
    intro s hs h X Y Z hY hZ
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hw : ‖(Y - X) / s‖ = 1 := by
      rw [norm_div, hY, Complex.norm_real, Real.norm_of_nonneg hs.le, div_self hs.ne']
    filter_upwards [ae_motion (P := fun p u => ¬ MonoCopy c s (s * ζ) p u) X _ hw h]
      with q hq
    rwa [monoCopy_iff c s (s * ζ) q.1 (direction q.2) X ((Y - X) / s) Y Z
      (by field_simp; ring) (by rw [hZ]; field_simp)] at hq
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hza' : 0 < ‖z - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hza)
  -- `ADB'`, `ABC`, `BDC'`, `A'B'C'`, `A'D'B`, `B'D'C`
  have e₁ := key hz h₂ 0 z (ζ * z) (by simp) (by ring)
  have e₂ := key ha h₁ 0 a (a * ζ) (by simp [ha.le]) (by ring)
  have e₃ := key hza' h₃ a z (a * (1 - ζ) + ζ * z) rfl (by ring)
  have e₄ := key ha h₁ (a + ζ * z) (ζ * z) (a * (1 - ζ) + ζ * z)
    (by rw [show ζ * z - (a + ζ * z) = -(a : ℂ) by ring, norm_neg]; simp [ha.le]) (by ring)
  have e₅ := key hz h₂ (a + ζ * z) (a - (1 - ζ) * z) a
    (by rw [show a - (1 - ζ) * z - (a + ζ * z) = -z by ring, norm_neg]) (by ring)
  have e₆ := key hza' h₃ (ζ * z) (a - (1 - ζ) * z) (a * ζ)
    (by rw [show a - (1 - ζ) * z - ζ * z = a - z by ring, norm_sub_rev]) (by ring)
  filter_upwards [e₁, e₂, e₃, e₄, e₅, e₆] with q h₁ h₂ h₃ h₄ h₅ h₆ hBAD
  simp only [mul_zero, add_zero] at h₁ h₂
  exact forcing_ii _ _ _ _ _ _ _ _ hBAD.1 hBAD.2 h₁ h₂ h₃ h₄ h₅ h₆

end Erdos173

end
