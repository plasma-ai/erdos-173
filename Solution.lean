module

public import Erdos173.FinalAssembly

/-!
# Proof of Erdős Problem 173

Comparator checks the four theorems in this module against the Mathlib-only
statements in `Challenge.lean`.
-/

@[expose] public section

open Affine
open scoped Congruent EuclideanGeometry

namespace Erdos173

/-- The Euclidean plane, as in `formal-conjectures`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/--
In any $2$-colouring of $\mathbb{R}^2$, for all but at most one triangle $T$ (up to
congruence), there is a monochromatic congruent copy of $T$.
-/
theorem erdos_173 : ∀ (c : ℝ² → Fin 2) (T₁ T₂ : Triangle ℝ ℝ²),
    ¬ HasMonochromaticCopy c T₁ → ¬ HasMonochromaticCopy c T₂ →
      ∃ σ : Equiv.Perm (Fin 3), T₁.points ∘ σ ≅ T₂.points :=
  erdos_173_proved

/--
In any $2$-colouring of $\mathbb{R}^2$, every right-angled triangle has a monochromatic
congruent copy.
-/
theorem erdos_173.variants.right_triangle (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²)
    (hT : ∠ (T.points 0) (T.points 1) (T.points 2) = Real.pi / 2) :
    HasMonochromaticCopy c T :=
  right_triangle_proved c T hT

/--
The exceptional triangle can exist: colouring the plane in alternating half-open strips of
suitable width gives no monochromatic copy of some equilateral triangle.
-/
theorem erdos_173.variants.equilateral_exception : ∃ (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²),
    dist (T.points 0) (T.points 1) = dist (T.points 1) (T.points 2) ∧
    dist (T.points 1) (T.points 2) = dist (T.points 2) (T.points 0) ∧
    ¬ HasMonochromaticCopy c T :=
  equilateral_exception_proved

/--
Every non-equilateral triangle has a monochromatic congruent copy in every $2$-colouring of
$\mathbb{R}^2$.
-/
theorem erdos_173.variants.non_equilateral (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²)
    (hT : ¬ (dist (T.points 0) (T.points 1) = dist (T.points 1) (T.points 2) ∧
      dist (T.points 1) (T.points 2) = dist (T.points 2) (T.points 0))) :
    HasMonochromaticCopy c T :=
  non_equilateral_proved c T hT

end Erdos173
