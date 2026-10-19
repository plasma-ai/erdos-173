module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Analysis.Real.Sqrt

/-!
# Plane carriers

New in this repository; not part of openai/math.

The source fixes its carrier, the field of algebraic numbers. This module states the
properties of a carrier field `E ⊆ ℂ` that its rigidity theorem for wild character laws
uses, so that the theorem applies to the algebraic closure of `ℚ(x)` for every real `x`.

A carrier is a countable subfield `E` of `ℂ` that is relatively algebraically closed and
is the complexification of its real slice `F`. Its unit circle has the *template
property*: for every finite set `Q` of units there is a finite set `S` of units such
that, whichever `q ∈ Q` is chosen for each `s ∈ S`, the products `q s` span `1` and `i`
over `ℚ`. For number fields this is the general-position selection of the source's
Lemma 3.4.
-/

@[expose] public section

noncomputable section

namespace OAI.PlaneFiveColor.Spectral

/-- For every finite set `Q` of units of `E` there is a finite set `S` of units of `E`
such that, for every choice of `j s ∈ Q` at each `s ∈ S`, both `1` and `i` lie in the
rational span of the products `j s * s`. -/
def TemplateProperty (E : Set ℂ) : Prop :=
  ∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
    ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s * s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s * s) '' (S : Set ℂ))

/-- A carrier for the rigidity theorem for wild character laws. -/
class Carrier where
  /-- The complex carrier field. -/
  E : IntermediateField ℚ ℂ
  /-- Its real slice. -/
  F : IntermediateField ℚ ℝ
  /-- `E` is countable. -/
  countable : Countable E
  /-- A complex number lies in `E` exactly when its real and imaginary parts lie in `F`. -/
  mem_iff : ∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F
  /-- Every root in `ℂ` of a nonzero polynomial with coefficients in `E` lies in `E`. -/
  algClosed : ∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) →
    ∀ z : ℂ, p.eval z = 0 → z ∈ E
  /-- The unit circle of `E` has the template property. -/
  template : TemplateProperty (E : Set ℂ)

namespace Carrier

variable [Carrier]

/-! ### Closure properties

The source's uses of algebraicity over `ℚ` are replaced by the following consequences
of the carrier fields. -/

/-- The real part of an element of `E` lies in `F`. -/
theorem re_mem {z : ℂ} (hz : z ∈ E) : z.re ∈ F := ((mem_iff z).mp hz).1

/-- The imaginary part of an element of `E` lies in `F`. -/
theorem im_mem {z : ℂ} (hz : z ∈ E) : z.im ∈ F := ((mem_iff z).mp hz).2

/-- An element of `F` lies in `E`. -/
theorem ofReal_mem {t : ℝ} (ht : t ∈ F) : (t : ℂ) ∈ E :=
  (mem_iff _).mpr ⟨by simpa using ht, by simp⟩

/-- `i` lies in `E`. -/
theorem I_mem : Complex.I ∈ E :=
  (mem_iff _).mpr ⟨by simp, by simp⟩

/-- Rationals lie in `F`. -/
theorem ratCast_mem (q : ℚ) : (q : ℝ) ∈ F := SubfieldClass.ratCast_mem F q

/-- A root of an element of the carrier lies in the carrier. -/
theorem mem_of_pow_mem {w : ℂ} {n : ℕ} (hn : n ≠ 0) (hw : w ^ n ∈ E) : w ∈ E := by
  classical
  have hdeg : (Polynomial.X ^ n - Polynomial.C (w ^ n)).natDegree = n :=
    Polynomial.natDegree_X_pow_sub_C
  apply algClosed (Polynomial.X ^ n - Polynomial.C (w ^ n))
  · intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    exact hn hdeg.symm
  · intro k
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs
    · exact E.sub_mem E.one_mem hw
    · simp
    · simpa using E.neg_mem hw
    · simp
  · simp

/-- `F` is closed under square roots, with `√t = 0` for `t < 0`. -/
theorem sqrt_mem {t : ℝ} (ht : t ∈ F) : Real.sqrt t ∈ F := by
  by_cases h : 0 ≤ t
  · have hc : ((Real.sqrt t : ℝ) : ℂ) ∈ E := by
      apply mem_of_pow_mem (n := 2) (by norm_num)
      rw [← Complex.ofReal_pow, Real.sq_sqrt h]
      exact ofReal_mem ht
    simpa using re_mem hc
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
    exact F.zero_mem

/-- The modulus of an element of `E` lies in `F`. -/
theorem norm_mem {z : ℂ} (hz : z ∈ E) : ‖z‖ ∈ F := by
  have h : ‖z‖ = Real.sqrt (z.re * z.re + z.im * z.im) := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
  rw [h]
  exact sqrt_mem (F.add_mem (F.mul_mem (re_mem hz) (re_mem hz))
    (F.mul_mem (im_mem hz) (im_mem hz)))

/-- The real slice is countable. -/
theorem countable_F : Countable F := by
  have := countable
  let f : F → E := fun t => ⟨((t : ℝ) : ℂ), ofReal_mem t.property⟩
  apply Function.Injective.countable (f := f)
  intro s t h
  exact Subtype.ext (Complex.ofReal_injective (congrArg Subtype.val h))

end Carrier

/-- The algebraic closure of `ℚ(x)` in `ℂ`. -/
def fieldOf (x : ℝ) : IntermediateField ℚ ℂ :=
  (algebraicClosure (IntermediateField.adjoin ℚ {(x : ℂ)}) ℂ).restrictScalars ℚ

/-- The algebraic closure of `ℚ(x)` in `ℝ`. -/
def realFieldOf (x : ℝ) : IntermediateField ℚ ℝ :=
  (algebraicClosure (IntermediateField.adjoin ℚ {x}) ℝ).restrictScalars ℚ

end OAI.PlaneFiveColor.Spectral
