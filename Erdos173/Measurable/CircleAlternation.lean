module

public import Erdos173.Basic
public import Mathlib.Dynamics.Ergodic.Action.OfMinimal
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Alternation on a circle

Let `R` be a measurable subset of the circle `𝕋 = ℝ / 2πℤ` with normalized arc
length `|·|`, and write `R - s = {t | t + s ∈ R}`. Suppose that
`R ∩ (R - π/3)`, `Rᶜ ∩ (Rᶜ - π/3)` and `R ∩ (R - γ)` are null. Then `γ / π` is
rational.

The first condition gives `R - π/3 ⊆ Rᶜ` up to a null set, so `|R| ≤ |Rᶜ|`, and
the second gives the reverse inequality. Inclusions between sets of equal
finite measure are equalities up to null sets, so `R - π/3 = Rᶜ` and, by the
third condition, `R - γ = Rᶜ`, again up to null sets. Hence `R` is invariant
up to a null set under the rotation by `γ - π/3`. If `γ / π` is irrational this
rotation is ergodic, so `R` is null or conull, contradicting `|R| = |Rᶜ|`.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open MeasureTheory Set Real OAI.EuclideanFiveColor

/-- If `R ∩ (R - s)` is null, then `R - s ⊆ Rᶜ` up to a null set. -/
lemma preimage_add_ae_le_compl {R : Set Angles} {s : Angles}
    (h : angularMeasure (R ∩ (· + s) ⁻¹' R) = 0) :
    (· + s) ⁻¹' R ≤ᵐ[angularMeasure] Rᶜ := by
  rw [ae_le_set, sdiff_compl, inter_comm]
  exact h

/-- Alternation on a circle: the three null intersections force `γ / π` to be
rational. -/
theorem circle_alternation {R : Set Angles} (hR : MeasurableSet R) {γ : ℝ}
    (hγ : Irrational (γ / π))
    (h₁ : angularMeasure (R ∩ (· + ((π / 3 : ℝ) : Angles)) ⁻¹' R) = 0)
    (h₂ : angularMeasure (Rᶜ ∩ (· + ((π / 3 : ℝ) : Angles)) ⁻¹' Rᶜ) = 0)
    (h₃ : angularMeasure (R ∩ (· + (γ : Angles)) ⁻¹' R) = 0) : False := by
  set s : Angles := ((π / 3 : ℝ) : Angles) with hs
  set g : Angles := (γ : Angles) with hg
  have hmp : ∀ x : Angles, MeasurePreserving (· + x) angularMeasure angularMeasure :=
    fun x => measurePreserving_add_right angularMeasure x
  have hmeas : ∀ x : Angles, angularMeasure ((· + x) ⁻¹' R) = angularMeasure R :=
    fun x => (hmp x).measure_preimage hR.nullMeasurableSet
  have hmeas' : ∀ x : Angles, angularMeasure ((· + x) ⁻¹' Rᶜ) = angularMeasure Rᶜ :=
    fun x => (hmp x).measure_preimage hR.compl.nullMeasurableSet
  have hle₁ := preimage_add_ae_le_compl h₁
  have hle₂ := preimage_add_ae_le_compl h₂
  rw [compl_compl] at hle₂
  have hRc : angularMeasure R ≤ angularMeasure Rᶜ := (hmeas s).symm.le.trans (measure_mono_ae hle₁)
  have hcR : angularMeasure Rᶜ ≤ angularMeasure R := (hmeas' s).symm.le.trans (measure_mono_ae hle₂)
  have hnull : ∀ x : Angles, NullMeasurableSet ((· + x) ⁻¹' R) angularMeasure :=
    fun x => (hR.preimage (measurable_add_const x)).nullMeasurableSet
  have heq_s : (· + s) ⁻¹' R =ᵐ[angularMeasure] Rᶜ :=
    ae_eq_of_ae_subset_of_measure_ge hle₁ ((hmeas s).symm ▸ hcR) (hnull s) (measure_ne_top _ _)
  have heq_g : (· + g) ⁻¹' R =ᵐ[angularMeasure] Rᶜ :=
    ae_eq_of_ae_subset_of_measure_ge (preimage_add_ae_le_compl h₃) ((hmeas g).symm ▸ hcR)
      (hnull g) (measure_ne_top _ _)
  -- `R` is invariant up to a null set under the rotation by `γ - π/3`
  have hinv : (fun x => (g - s) + x) ⁻¹' R =ᵐ[angularMeasure] R := by
    have h := (hmp (-s)).quasiMeasurePreserving.preimage_ae_eq (heq_g.trans heq_s.symm)
    have e1 : (· + -s) ⁻¹' ((· + g) ⁻¹' R) = (fun x => (g - s) + x) ⁻¹' R := by
      ext t; simp only [mem_preimage]; congr! 1; abel
    have e2 : (· + -s) ⁻¹' ((· + s) ⁻¹' R) = R := by
      ext t; simp
    rwa [e1, e2] at h
  have hdense : DenseRange (fun n : ℤ => n • (g - s)) := by
    rw [hg, hs, ← AddCircle.coe_sub, AddCircle.denseRange_zsmul_coe_iff]
    have h' : Irrational (γ / π * ((1 / 2 : ℚ) : ℝ) - ((1 / 6 : ℚ) : ℝ)) :=
      (hγ.mul_ratCast (by norm_num)).sub_ratCast _
    convert h' using 1
    field_simp
    ring
  have herg := ergodic_add_left_of_denseRange_zsmul hdense angularMeasure
  have hsum : angularMeasure R + angularMeasure Rᶜ = 1 := by
    rw [measure_add_measure_compl hR, measure_univ]
  have hRR : angularMeasure Rᶜ = angularMeasure R := le_antisymm hcR hRc
  rw [hRR] at hsum
  rcases herg.ae_empty_or_univ_of_preimage_ae_le hR.nullMeasurableSet hinv.le with h0 | h1
  · rw [measure_congr h0, measure_empty] at hsum
    simp at hsum
  · rw [measure_congr h1, measure_univ] at hsum
    norm_num at hsum

end Erdos173

end
