module

public import Erdos173.Basic
public import Erdos173.Statement

/-!
# The Euclidean plane as `ℂ`

`toC` identifies `ℝ²` with `ℂ` by the standard orthonormal basis `1, i`. A
motion `w ↦ k w + t` of `ℂ` with `‖k‖ = 1` is an orientation-preserving
isometry, and conjugated by `toC` it is an injective affine isometry of `ℝ²`.

Three distinct points `v` of `ℝ²`, collinear or not, relabelled by `σ`, are
the copy of the template `(0, a, z)` placed by `(w₀, u₀)`, where `w_j` is the
image of `v (σ j)` in `ℂ`, `a = |w₁ - w₀|`, `u₀ = (w₁ - w₀)/a` and
`z = (w₂ - w₀)/u₀`; `z` is real when the points are collinear. Placing the
template by any other motion `(p, u)` is the image of `v` under the motion
`w ↦ (u/u₀)(w - w₀) + p`. A monochromatic copy of the template in the
transported coloring is therefore a monochromatic image of `v` under a motion,
which is congruent to `v`.
-/

@[expose] public section

noncomputable section

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

/-- `pMotion k t` acts as `w ↦ k w + t` in the coordinate `toC`. -/
lemma pMotion_apply (k t : ℂ) (x : ℝ²) : pMotion k t x = toC.symm (k * toC x + t) :=
  rfl

/-- A motion with `‖k‖ = 1` is an isometry. -/
lemma isometry_pMotion {k : ℂ} (hk : ‖k‖ = 1) (t : ℂ) : Isometry (pMotion k t) :=
  Isometry.of_dist_eq fun x y => by
    rw [pMotion_apply, pMotion_apply, LinearIsometryEquiv.dist_map, dist_eq_norm,
      add_sub_add_right_eq_sub, ← mul_sub, norm_mul, hk, one_mul, ← dist_eq_norm,
      LinearIsometryEquiv.dist_map]

/-- The point `v (σ j)`, in `ℂ`. -/
def vertex (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) : ℂ :=
  toC (v (σ j))

/-- The side `a = |w₁ - w₀|` of the template of `v` relabelled by `σ`. -/
def side (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) : ℝ :=
  dist (v (σ 0)) (v (σ 1))

/-- The direction `u₀ = (w₁ - w₀)/a` of the first side. -/
def frame (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) : ℂ :=
  (vertex v σ 1 - vertex v σ 0) / side v σ

/-- The apex `z = (w₂ - w₀)/u₀` of the template of `v` relabelled by `σ`. -/
def apex (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) : ℂ :=
  (vertex v σ 2 - vertex v σ 0) / frame v σ

/-- Distinct points stay distinct in `ℂ`. -/
lemma vertex_ne {v : Fin 3 → ℝ²} (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3))
    {i j : Fin 3} (h : i ≠ j) : vertex v σ i ≠ vertex v σ j := fun e =>
  h (σ.injective (hv (toC.injective e)))

/-- The identification with `ℂ` preserves the distances between the points. -/
lemma norm_vertex_sub (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    ‖vertex v σ i - vertex v σ j‖ = dist (v (σ i)) (v (σ j)) := by
  rw [vertex, vertex, ← dist_eq_norm, LinearIsometryEquiv.dist_map]

/-- The first side of three distinct points is positive. -/
lemma side_pos {v : Fin 3 → ℝ²} (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3)) :
    0 < side v σ :=
  dist_pos.2 fun e => absurd (σ.injective (hv e)) (by decide)

/-- The direction of the first side is a unit. -/
lemma norm_frame {v : Fin 3 → ℝ²} (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3)) :
    ‖frame v σ‖ = 1 := by
  rw [frame, norm_div, norm_vertex_sub, Complex.norm_real, Real.norm_of_nonneg
    (side_pos hv σ).le, dist_comm]
  exact div_self (side_pos hv σ).ne'

/-- Turning the first side back by its direction gives its length. -/
lemma side_eq {v : Fin 3 → ℝ²} (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3)) :
    (vertex v σ 1 - vertex v σ 0) / frame v σ = side v σ :=
  div_div_cancel₀ (sub_ne_zero.2 (vertex_ne hv σ (by decide)))

/-- A monochromatic copy of the template of `v`, for the coloring transported to `ℂ`,
gives a monochromatic image of `v` under a motion. -/
theorem exists_motion_of_monoCopy (c : ℝ² → Fin 2) {v : Fin 3 → ℝ²}
    (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3)) {p u : ℂ} (hu : ‖u‖ = 1)
    (h : MonoCopy (c ∘ toC.symm) (side v σ) (apex v σ) p u) :
    ∃ k t : ℂ, ‖k‖ = 1 ∧ ∃ i, ∀ j, c (pMotion k t (v j)) = i := by
  set k := u / frame v σ
  have hk : ‖k‖ = 1 := by rw [norm_div, hu, norm_frame hv, div_one]
  set t := p - k * vertex v σ 0
  refine ⟨k, t, hk, c (toC.symm p), fun j => ?_⟩
  obtain ⟨m, rfl⟩ := σ.surjective j
  rw [pMotion_apply, ← vertex]
  fin_cases m
  · simp [t]
  · have e : k * vertex v σ 1 + t = p + u * side v σ := by
      rw [← side_eq hv]
      simp only [k, t]
      ring
    simpa [e] using h.1
  · have e : k * vertex v σ 2 + t = p + u * apex v σ := by
      simp only [k, t, apex]
      ring
    simpa [e] using h.2

end Erdos173.Plane

end
