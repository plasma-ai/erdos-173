module

public import Erdos173.Reduction.EightPoint
public import Erdos173.Reduction.Plane
public import Erdos173.Reduction.Strips
public import Erdos173.Statement
public import Erdos173.TwoScale
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# Assembly of Erdős Problem 173

Identify `ℝ²` with `ℂ`. A triangle without a monochromatic copy has none
oriented as it is, so by part (i) of the eight-point configuration the coloring
avoids the equilateral triangles of each of its side lengths that differs from
another. By `two_scale` that is impossible for two different sides, so the
triangle is equilateral, of the unique avoided side. Two such triangles are
equilateral of the same side, hence congruent. A right triangle is not
equilateral. Alternating half-open strips of width `√3/2` contain no
monochromatic equilateral triangle of side one.
-/

@[expose] public section

open Affine
open scoped Congruent EuclideanGeometry

namespace Erdos173

open Plane Strips

/-- The Euclidean plane, as in `formal-conjectures`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- A triangle without a monochromatic copy has every side avoided, as an
equilateral side of the transported coloring. -/
lemma avoidsEq_side (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²) (h : ¬ HasMonochromaticCopy c T)
    (σ : Equiv.Perm (Fin 3)) : AvoidsEq (c ∘ toC.symm) (side T σ) := by
  by_contra hne
  have := not_avoids_of_not_avoidsEq (z := apex T σ) _ hne
  simp only [Avoids, not_forall, not_not] at this
  obtain ⟨p, u, hu, hm⟩ := this
  exact h (hasMonochromaticCopy_of_monoCopy c T σ hu hm)

/-- A triangle without a monochromatic copy is equilateral, and its side is avoided. -/
theorem equilateral_of_not_hasMonochromaticCopy (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²)
    (h : ¬ HasMonochromaticCopy c T) :
    AvoidsEq (c ∘ toC.symm) (dist (T.points 0) (T.points 1)) ∧
      ∀ i j, i ≠ j → dist (T.points i) (T.points j) = dist (T.points 0) (T.points 1) := by
  have h₀ := avoidsEq_side c T h 1
  have h₁ := avoidsEq_side c T h (finRotate 3)
  have h₂ := avoidsEq_side c T h (finRotate 3).symm
  have e₁ := two_scale _ (side_pos T 1) (side_pos T _) h₀ h₁
  have e₂ := two_scale _ (side_pos T 1) (side_pos T _) h₀ h₂
  have s₀ : side T 1 = dist (T.points 0) (T.points 1) := rfl
  have s₁ : side T (finRotate 3) = dist (T.points 1) (T.points 2) := rfl
  have s₂ : side T (finRotate 3).symm = dist (T.points 2) (T.points 0) := rfl
  rw [s₀, s₁] at e₁
  rw [s₀, s₂] at e₂
  refine ⟨s₀ ▸ h₀, fun i j hij => ?_⟩
  have c₀ := dist_comm (T.points 0) (T.points 1)
  have c₁ := dist_comm (T.points 1) (T.points 2)
  have c₂ := dist_comm (T.points 2) (T.points 0)
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith

/-- Two triangles without a monochromatic copy are equilateral of the one avoided
side, hence congruent. -/
theorem erdos_173_proved : ∀ (c : ℝ² → Fin 2) (T₁ T₂ : Triangle ℝ ℝ²),
    ¬ HasMonochromaticCopy c T₁ → ¬ HasMonochromaticCopy c T₂ →
      ∃ σ : Equiv.Perm (Fin 3), T₁.points ∘ σ ≅ T₂.points := by
  intro c T₁ T₂ h₁ h₂
  obtain ⟨a₁, e₁⟩ := equilateral_of_not_hasMonochromaticCopy c T₁ h₁
  obtain ⟨a₂, e₂⟩ := equilateral_of_not_hasMonochromaticCopy c T₂ h₂
  have e := two_scale _ (dist_pos.2 (T₁.independent.injective.ne (by decide)))
    (dist_pos.2 (T₂.independent.injective.ne (by decide))) a₁ a₂
  refine ⟨1, congruent_iff_dist_eq.2 fun i j => ?_⟩
  by_cases hij : i = j
  · simp [hij]
  · simp only [Equiv.Perm.coe_one, Function.comp_apply, id]
    rw [e₁ i j hij, e₂ i j hij, e]

/-- A right triangle is not equilateral, so it has a monochromatic copy. -/
theorem right_triangle_proved (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²)
    (hT : ∠ (T.points 0) (T.points 1) (T.points 2) = Real.pi / 2) :
    HasMonochromaticCopy c T := by
  by_contra h
  obtain ⟨-, e⟩ := equilateral_of_not_hasMonochromaticCopy c T h
  have hp := (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ _ _).2 hT
  have hs := dist_pos.2 (T.independent.injective.ne (show (0 : Fin 3) ≠ 1 by decide))
  rw [e 0 2 (by decide), e 2 1 (by decide)] at hp
  nlinarith

/-- The strip coloring has no monochromatic equilateral triangle of side one. -/
theorem equilateral_exception_proved : ∃ (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²),
    dist (T.points 0) (T.points 1) = dist (T.points 1) (T.points 2) ∧
    dist (T.points 1) (T.points 2) = dist (T.points 2) (T.points 0) ∧
    ¬ HasMonochromaticCopy c T :=
  ⟨stripColor, unitTriangle, by rw [dist_unitTriangle (by decide), dist_unitTriangle (by decide)],
    by rw [dist_unitTriangle (by decide), dist_unitTriangle (by decide)],
    not_hasMonochromaticCopy_strip⟩

end Erdos173
