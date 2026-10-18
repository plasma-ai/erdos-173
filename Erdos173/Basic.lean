module

public import OAI.Geometry.PlaneColoring.Coloring

/-!
# Colorings of the complex plane and copies of triangles

The proof works in `ℂ`. A triangle is given by a template `(0, a, b)` with
`a b : ℂ`, and its orientation-preserving copies are `(p, p + u a, p + u b)` for
`p : ℂ` and `‖u‖ = 1`. A two-coloring `c : ℂ → Fin 2` *avoids* the template when
no copy is monochromatic, and *weakly avoids* it when the monochromatic copies
form a null set for area times normalized arc length, the angular measure of
`OAI.EuclideanFiveColor.WeakColoring`.

The equilateral triangle of side `r` is the template `(0, r, r ζ)`, with
`ζ = e^{iπ/3}`. The numbers `ζ`, `1 - ζ = ζ̄` and `ζ - 1` lie on the unit circle, and
directions add angles: `e^{i(s+t)} = e^{is} e^{it}`.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open MeasureTheory OAI.EuclideanFiveColor

/-- The sixth root of unity `ζ = e^{iπ/3} = 1/2 + (√3/2) i`. -/
def ζ : ℂ := ⟨1 / 2, √3 / 2⟩

/-- `ζ` lies on the unit circle. -/
lemma norm_ζ : ‖ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

/-- `ζ̄ = 1 - ζ` lies on the unit circle. -/
lemma norm_one_sub_ζ : ‖1 - ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

/-- `-ζ̄ = ζ - 1` lies on the unit circle. -/
lemma norm_ζ_sub_one : ‖ζ - 1‖ = 1 := by
  rw [norm_sub_rev, norm_one_sub_ζ]

/-- Directions add angles: `e^{i(s+t)} = e^{is} e^{it}`. -/
lemma direction_add (s t : Angles) : direction (s + t) = direction s * direction t := by
  simp [direction, AddCircle.toCircle_add]

/-- The copy `(p, p + u a, p + u b)` of the template `(0, a, b)` is monochromatic. -/
def MonoCopy (c : ℂ → Fin 2) (a b p u : ℂ) : Prop :=
  c (p + u * a) = c p ∧ c (p + u * b) = c p

/-- No orientation-preserving copy of the template `(0, a, b)` is monochromatic. -/
def Avoids (c : ℂ → Fin 2) (a b : ℂ) : Prop :=
  ∀ p u : ℂ, ‖u‖ = 1 → ¬ MonoCopy c a b p u

/-- Almost no orientation-preserving copy of the template `(0, a, b)` is
monochromatic, for area times normalized arc length. -/
def WeaklyAvoids (c : ℂ → Fin 2) (a b : ℂ) : Prop :=
  ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure, ¬ MonoCopy c a b q.1 (direction q.2)

/-- No equilateral triangle of side `r` is monochromatic. -/
def AvoidsEq (c : ℂ → Fin 2) (r : ℝ) : Prop :=
  Avoids c r (r * ζ)

/-- Almost no equilateral triangle of side `r` is monochromatic. -/
def WeaklyAvoidsEq (c : ℂ → Fin 2) (r : ℝ) : Prop :=
  WeaklyAvoids c r (r * ζ)

end Erdos173

end
