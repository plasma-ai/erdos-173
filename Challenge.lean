module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.Topology.MetricSpace.Congruence

/-!
# Erdős Problem 173: monochromatic triangles in two-colorings of the plane

Erdős, Graham, Montgomery, Rothschild, Spencer and Straus conjectured that, in
every two-coloring of the plane, every triangle except possibly one equilateral
triangle has a monochromatic congruent copy. Thomas F. Bloom catalogs the
question as [Erdős Problem 173](https://www.erdosproblems.com/173).

**Claim.** In every two-coloring of the plane, any two triangles without a
monochromatic congruent copy are congruent. Any three distinct points that are
not the vertices of an equilateral triangle, collinear points included, have a
monochromatic congruent copy, and so the exceptional triangle, if there is one,
is equilateral. Some coloring has such an exception: alternating half-open strips
of suitable width contain no monochromatic copy of some equilateral triangle.

`HasMonochromaticCopy`, `erdos_173`, `erdos_173.variants.right_triangle` and
`erdos_173.variants.equilateral_exception` are copied verbatim, apart from their
category attributes, from `formal-conjectures`
(`FormalConjectures/ErdosProblems/173.lean`, commit `7db2ea3b91`, Copyright 2026
The Formal Conjectures Authors, under the Apache License 2.0), with its `ℝ²`
notation for `EuclideanSpace ℝ (Fin 2)` declared locally.
`erdos_173.variants.non_equilateral` and
`erdos_173.variants.three_distinct_points` are not from `formal-conjectures`:
they state the claim that every non-equilateral triangle has a monochromatic
copy, Conjecture 3 of *Euclidean Ramsey theorems, III*. A triangle in the first
four theorems is Mathlib's `Affine.Triangle`, whose vertices are affinely
independent, so collinear triples are not covered there.
`erdos_173.variants.three_distinct_points` covers them: it is stated for any
three distinct points, which Conjecture 3 counts as a triangle even when they
are collinear. In every statement a copy may be reflected and relabelled.

[Sh76] L. E. Shader, *All right triangles are Ramsey in $E^2$!*, J. Combin.
Theory Ser. A 20 (1976), 385–389.

The five theorems below have deliberate proof holes. `Solution.lean` supplies
their proofs, and Comparator checks them against these statements.
-/

@[expose] public section

open Affine
open scoped Congruent EuclideanGeometry

namespace Erdos173

/-- The Euclidean plane, as in `formal-conjectures`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/--
The colouring `c` contains a monochromatic triangle congruent to `T`.

Since `T'` is arbitrary, relabellings and reflections of `T` are allowed. Rescaling is not.
-/
def HasMonochromaticCopy (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²) : Prop :=
  ∃ T' : Triangle ℝ ℝ², (T'.points ≅ T.points) ∧ ∃ i, ∀ j, c (T'.points j) = i

/--
In any $2$-colouring of $\mathbb{R}^2$, for all but at most one triangle $T$ (up to
congruence), there is a monochromatic congruent copy of $T$.

The colouring is arbitrary. No measurability is assumed. `≅` compares vertices with the same
label, so the conclusion allows a relabelling `σ`.
-/
theorem erdos_173 : ∀ (c : ℝ² → Fin 2) (T₁ T₂ : Triangle ℝ ℝ²),
    ¬ HasMonochromaticCopy c T₁ → ¬ HasMonochromaticCopy c T₂ →
      ∃ σ : Equiv.Perm (Fin 3), T₁.points ∘ σ ≅ T₂.points := by
  sorry

/--
Shader [Sh76] proved that in any $2$-colouring of $\mathbb{R}^2$, every right-angled triangle
has a monochromatic congruent copy.
-/
theorem erdos_173.variants.right_triangle (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²)
    (hT : ∠ (T.points 0) (T.points 1) (T.points 2) = Real.pi / 2) :
    HasMonochromaticCopy c T := by
  sorry

/--
The exceptional triangle can exist: colouring the plane in alternating half-open strips of
suitable width gives no monochromatic copy of some equilateral triangle.
-/
theorem erdos_173.variants.equilateral_exception : ∃ (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²),
    dist (T.points 0) (T.points 1) = dist (T.points 1) (T.points 2) ∧
    dist (T.points 1) (T.points 2) = dist (T.points 2) (T.points 0) ∧
    ¬ HasMonochromaticCopy c T := by
  sorry

/--
Every non-equilateral triangle has a monochromatic congruent copy in every $2$-colouring of
$\mathbb{R}^2$. This is Conjecture 3 of Erdős, Graham, Montgomery, Rothschild, Spencer and
Straus, for nondegenerate triangles.
-/
theorem erdos_173.variants.non_equilateral (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²)
    (hT : ¬ (dist (T.points 0) (T.points 1) = dist (T.points 1) (T.points 2) ∧
      dist (T.points 1) (T.points 2) = dist (T.points 2) (T.points 0))) :
    HasMonochromaticCopy c T := by
  sorry

/--
Any three distinct points of $\mathbb{R}^2$ that are not the vertices of an equilateral triangle
have a monochromatic congruent copy in every $2$-colouring of $\mathbb{R}^2$. This is Conjecture 3
of Erdős, Graham, Montgomery, Rothschild, Spencer and Straus, including its degenerate triangles:
the points may be collinear, and three distinct collinear points never have equal pairwise
distances, so every collinear triple is covered.

Since `q` is arbitrary, relabellings and reflections of `p` are allowed. Rescaling is not.
-/
theorem erdos_173.variants.three_distinct_points (c : ℝ² → Fin 2) (p : Fin 3 → ℝ²)
    (hp : Function.Injective p)
    (he : ¬ (dist (p 0) (p 1) = dist (p 1) (p 2) ∧ dist (p 1) (p 2) = dist (p 2) (p 0))) :
    ∃ q : Fin 3 → ℝ², (q ≅ p) ∧ ∃ i, ∀ j, c (q j) = i := by
  sorry

end Erdos173
