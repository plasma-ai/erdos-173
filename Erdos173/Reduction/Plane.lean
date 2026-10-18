module

public import Erdos173.Basic
public import Erdos173.Statement

/-!
# The Euclidean plane as `ℂ`

`toC` identifies `ℝ²` with `ℂ` by the standard orthonormal basis `1, i`. A
motion `w ↦ k w + t` of `ℂ` with `‖k‖ = 1` is an orientation-preserving
isometry, and conjugated by `toC` it is an injective affine isometry of `ℝ²`.

A triangle `T` of `ℝ²`, with its vertices relabelled by `σ`, is the copy of
the template `(0, a, z)` placed by `(w₀, u₀)`, where `w_j` is the image of
vertex `σ j` in `ℂ`, `a = |w₁ - w₀|`, `u₀ = (w₁ - w₀)/a` and
`z = (w₂ - w₀)/u₀`. Placing the template by any other motion `(p, u)` is the
image of `T` under the motion `w ↦ (u/u₀)(w - w₀) + p`, which is a congruent
copy of `T`. A monochromatic copy of the template in the transported coloring
is therefore a monochromatic congruent copy of `T`.
-/

@[expose] public section

noncomputable section

open Affine
open scoped Congruent

namespace Erdos173.Plane

/-- The Euclidean plane, as in `formal-conjectures`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The identification of the Euclidean plane with `ℂ`. -/
def toC : ℝ² ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- The motion `w ↦ k w + t` of `ℂ`, as a real affine map. -/
def cMotion (k t : ℂ) : ℂ →ᵃ[ℝ] ℂ where
  toFun w := k * w + t
  linear := LinearMap.mulLeft ℝ k
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.mulLeft_apply]
    ring

/-- The motion `w ↦ k w + t` of `ℂ`, transported to `ℝ²`. -/
def pMotion (k t : ℂ) : ℝ² →ᵃ[ℝ] ℝ² :=
  toC.symm.toLinearEquiv.toLinearMap.toAffineMap.comp
    ((cMotion k t).comp toC.toLinearEquiv.toLinearMap.toAffineMap)

lemma pMotion_apply (k t : ℂ) (x : ℝ²) : pMotion k t x = toC.symm (k * toC x + t) :=
  rfl

/-- A motion with `‖k‖ = 1` is an isometry. -/
lemma isometry_pMotion {k : ℂ} (hk : ‖k‖ = 1) (t : ℂ) : Isometry (pMotion k t) :=
  Isometry.of_dist_eq fun x y => by
    rw [pMotion_apply, pMotion_apply, LinearIsometryEquiv.dist_map, dist_eq_norm,
      add_sub_add_right_eq_sub, ← mul_sub, norm_mul, hk, one_mul, ← dist_eq_norm,
      LinearIsometryEquiv.dist_map]

/-- The vertex `σ j` of `T`, in `ℂ`. -/
def vertex (T : Triangle ℝ ℝ²) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) : ℂ :=
  toC (T.points (σ j))

/-- The side `a = |w₁ - w₀|` of the template of `T` relabelled by `σ`. -/
def side (T : Triangle ℝ ℝ²) (σ : Equiv.Perm (Fin 3)) : ℝ :=
  dist (T.points (σ 0)) (T.points (σ 1))

/-- The direction `u₀ = (w₁ - w₀)/a` of the first side. -/
def frame (T : Triangle ℝ ℝ²) (σ : Equiv.Perm (Fin 3)) : ℂ :=
  (vertex T σ 1 - vertex T σ 0) / side T σ

/-- The apex `z = (w₂ - w₀)/u₀` of the template of `T` relabelled by `σ`. -/
def apex (T : Triangle ℝ ℝ²) (σ : Equiv.Perm (Fin 3)) : ℂ :=
  (vertex T σ 2 - vertex T σ 0) / frame T σ

/-- The vertices of a triangle are distinct. -/
lemma vertex_ne (T : Triangle ℝ ℝ²) (σ : Equiv.Perm (Fin 3)) {i j : Fin 3} (h : i ≠ j) :
    vertex T σ i ≠ vertex T σ j := fun e =>
  h (σ.injective (T.independent.injective (toC.injective e)))

/-- The identification with `ℂ` preserves the distances between vertices. -/
lemma norm_vertex_sub (T : Triangle ℝ ℝ²) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    ‖vertex T σ i - vertex T σ j‖ = dist (T.points (σ i)) (T.points (σ j)) := by
  rw [vertex, vertex, ← dist_eq_norm, LinearIsometryEquiv.dist_map]

/-- The first side of a triangle is positive. -/
lemma side_pos (T : Triangle ℝ ℝ²) (σ : Equiv.Perm (Fin 3)) : 0 < side T σ :=
  dist_pos.2 fun e => absurd (σ.injective (T.independent.injective e)) (by decide)

/-- The direction of the first side is a unit. -/
lemma norm_frame (T : Triangle ℝ ℝ²) (σ : Equiv.Perm (Fin 3)) : ‖frame T σ‖ = 1 := by
  rw [frame, norm_div, norm_vertex_sub, Complex.norm_real, Real.norm_of_nonneg
    (side_pos T σ).le, dist_comm]
  exact div_self (side_pos T σ).ne'

/-- Turning the first side back by its direction gives its length. -/
lemma side_eq (T : Triangle ℝ ℝ²) (σ : Equiv.Perm (Fin 3)) :
    (vertex T σ 1 - vertex T σ 0) / frame T σ = side T σ :=
  div_div_cancel₀ (sub_ne_zero.2 (vertex_ne T σ (by decide)))

/-- A monochromatic copy of the template of `T`, for the coloring transported to `ℂ`,
gives a monochromatic congruent copy of `T`. -/
theorem hasMonochromaticCopy_of_monoCopy (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²)
    (σ : Equiv.Perm (Fin 3)) {p u : ℂ} (hu : ‖u‖ = 1)
    (h : MonoCopy (c ∘ toC.symm) (side T σ) (apex T σ) p u) :
    HasMonochromaticCopy c T := by
  set k := u / frame T σ
  have hk : ‖k‖ = 1 := by rw [norm_div, hu, norm_frame, div_one]
  set t := p - k * vertex T σ 0
  have hF := isometry_pMotion hk t
  refine ⟨T.map (pMotion k t) hF.injective,
    show pMotion k t ∘ T.points ≅ T.points from (Congruent.refl _).comp_left hF,
    c (toC.symm p), fun j => ?_⟩
  obtain ⟨m, rfl⟩ := σ.surjective j
  change c (pMotion k t (T.points (σ m))) = c (toC.symm p)
  rw [pMotion_apply, ← vertex]
  fin_cases m
  · simp [t]
  · have e : k * vertex T σ 1 + t = p + u * side T σ := by
      rw [← side_eq]
      simp only [k, t]
      ring
    simpa [e] using h.1
  · have e : k * vertex T σ 2 + t = p + u * apex T σ := by
      simp only [k, t, apex]
      ring
    simpa [e] using h.2

end Erdos173.Plane

end
