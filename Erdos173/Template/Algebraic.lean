module

public import Erdos173.Template.Density
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.AlgebraicClosure

/-!
# The algebraic numbers and the Cauchy parameter plane

`𝔸` is the field of complex algebraic numbers, an algebraically closed subfield of `ℂ`
stable under conjugation. The Cauchy parameter plane is the set `Ω` of pairs
`(a, h)` of algebraic numbers with `a ≠ 0`, `|a| ≠ 1` and `h = a - 1/ā`. For a unit
`T` the element `a (1 + h/(T - a)) = a (T - 1/ā)/(T - a)` is again a unit. The set
`Ω` is Zariski dense in `𝔸²`: it contains, for every rational `r > 1`, the points
`(a, (1 - r⁻²) a)` with `|a| = r`, infinitely many on each line through the origin.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Template

open Polynomial ComplexConjugate

/-- The complex algebraic numbers. -/
abbrev 𝔸 : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

instance : IsAlgClosed 𝔸 := IsAlgClosure.isAlgClosed ℚ

instance : Infinite 𝔸 := Infinite.of_injective (algebraMap ℚ 𝔸) (algebraMap ℚ 𝔸).injective

/-- `i` is algebraic. -/
lemma I_mem_𝔸 : Complex.I ∈ 𝔸 :=
  mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow (n := 2) (by norm_num) (by
    rw [Complex.I_sq]; exact isAlgebraic_one.neg))

/-- The conjugate of an algebraic number is algebraic. -/
lemma conj_mem_𝔸 {z : ℂ} (hz : z ∈ 𝔸) : conj z ∈ 𝔸 :=
  mem_algebraicClosure_iff.mpr ((mem_algebraicClosure_iff.mp hz).algHom
    (Complex.conjAe.restrictScalars ℚ).toAlgHom)

/-- The imaginary unit as an algebraic number. -/
def iA : 𝔸 := ⟨Complex.I, I_mem_𝔸⟩

@[simp] lemma coe_iA : ((iA : 𝔸) : ℂ) = Complex.I := rfl

/-- Complex conjugation on the algebraic numbers. -/
def conjA (a : 𝔸) : 𝔸 := ⟨conj (a : ℂ), conj_mem_𝔸 a.property⟩

@[simp] lemma coe_conjA (a : 𝔸) : ((conjA a : 𝔸) : ℂ) = conj (a : ℂ) := rfl

/-- The action of `𝔸` on `ℂ` is multiplication. -/
lemma smul_eq (a : 𝔸) (z : ℂ) : a • z = (a : ℂ) * z := rfl

/-- The Cauchy parameter plane: `a ≠ 0`, `|a| ≠ 1`, `h = a - 1/ā`. -/
def Ω : Set (Fin 2 → 𝔸) :=
  {z | z 0 ≠ 0 ∧ ‖((z 0 : 𝔸) : ℂ)‖ ≠ 1 ∧ z 1 = z 0 - (conjA (z 0))⁻¹}

/-- On the parameter plane `h ≠ 0`, since `|a| ≠ 1`. -/
lemma Ω_h_ne_zero {z : Fin 2 → 𝔸} (hz : z ∈ Ω) : z 1 ≠ 0 := by
  obtain ⟨h0, h1, hh⟩ := hz
  intro he
  rw [he, eq_comm, sub_eq_zero] at hh
  apply h1
  have hc := congrArg (fun w : 𝔸 => (w : ℂ)) hh
  simp only [IntermediateField.coe_inv, coe_conjA] at hc
  have hn : (z 0 : ℂ) * conj (z 0 : ℂ) = 1 := by
    nth_rewrite 1 [hc]
    exact inv_mul_cancel₀ (by simpa using h0)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hn
  have : ‖(z 0 : ℂ)‖ ^ 2 = 1 := by exact_mod_cast hn
  nlinarith [norm_nonneg (z 0 : ℂ)]

/-- `a (1 + h/(T - a))` is a unit when `T` is a unit and `(a, h) ∈ Ω`. -/
lemma Ω_unit {z : Fin 2 → 𝔸} (hz : z ∈ Ω) {T : ℂ} (hT : ‖T‖ = 1) :
    T - (z 0 : ℂ) ≠ 0 ∧ ‖(z 0 : ℂ) * (1 + (z 1 : ℂ) / (T - z 0))‖ = 1 := by
  obtain ⟨h0, h1, hh⟩ := hz
  set a : ℂ := (z 0 : ℂ)
  have ha : a ≠ 0 := by simpa [a] using h0
  have hTa : T - a ≠ 0 := by
    intro he
    apply h1
    rw [← sub_eq_zero.mp he, hT]
  refine ⟨hTa, ?_⟩
  have hh' : (z 1 : ℂ) = a - (conj a)⁻¹ := by
    have hc := congrArg (fun w : 𝔸 => (w : ℂ)) hh
    simpa [a] using hc
  have hca : conj a ≠ 0 := by simpa using ha
  have he : a * (1 + (z 1 : ℂ) / (T - a)) = (conj a * T - 1) * (a / conj a) / (T - a) := by
    rw [hh']
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr ha),
    mul_one, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hTa)]
  have hTT : T * conj T = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hT]
    simp
  have h2 : conj (conj a * T - 1) = conj T * (a - T) := by
    simp only [map_sub, map_mul, Complex.conj_conj, map_one]
    linear_combination hTT
  rw [← Complex.norm_conj, h2, norm_mul, Complex.norm_conj, hT, one_mul, norm_sub_rev]

/-- The Cayley parametrization of the rational points of the unit circle. -/
def cayA (s : ℚ) : 𝔸 := (1 + (s : 𝔸) * iA) / (1 - (s : 𝔸) * iA)

lemma coe_cayA (s : ℚ) : ((cayA s : 𝔸) : ℂ) = (1 + s * Complex.I) / (1 - s * Complex.I) := by
  simp [cayA]

/-- The denominator `1 - s i` of a rational Cayley transform is nonzero. -/
lemma one_sub_mul_I_ne (s : ℚ) : (1 : ℂ) - s * Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- The conjugate of a rational Cayley transform is its inverse. -/
lemma conj_cayA (s : ℚ) : conj ((cayA s : 𝔸) : ℂ) = ((cayA s : 𝔸) : ℂ)⁻¹ := by
  rw [coe_cayA, map_div₀, inv_div]
  simp [sub_eq_add_neg]

/-- Rational Cayley transforms are units. -/
lemma norm_cayA (s : ℚ) : ‖((cayA s : 𝔸) : ℂ)‖ = 1 := by
  rw [coe_cayA, norm_div]
  have he : conj (1 + (s : ℂ) * Complex.I) = 1 - s * Complex.I := by simp [sub_eq_add_neg]
  rw [← he, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr ?_)]
  intro h
  have := congrArg Complex.re h
  simp at this

/-- The rational Cayley transform is injective. -/
lemma cayA_injective : Function.Injective cayA := by
  intro s t hst
  have hc := congrArg (fun w : 𝔸 => (w : ℂ)) hst
  simp only [coe_cayA] at hc
  rw [div_eq_div_iff (one_sub_mul_I_ne s) (one_sub_mul_I_ne t)] at hc
  have h2 := congrArg Complex.im hc
  simp at h2
  exact_mod_cast (by linarith : (s : ℝ) = t)

/-- The parameter plane is Zariski dense. -/
lemma zariskiDense_Ω : ZariskiDense Ω := by
  intro f hf hzero
  -- the slope attached to the radius `r`
  let κ : ℚ → 𝔸 := fun r => 1 - ((r : 𝔸) ^ 2)⁻¹
  have hκ : ∀ r s : ℚ, 1 < r → 1 < s → κ r = κ s → r = s := by
    intro r s hr hs he
    have he' : ((r : 𝔸) ^ 2)⁻¹ = ((s : 𝔸) ^ 2)⁻¹ := by simpa [κ] using he
    rw [inv_inj] at he'
    have : ((r ^ 2 : ℚ) : 𝔸) = ((s ^ 2 : ℚ) : 𝔸) := by push_cast; exact he'
    have h2 : r ^ 2 = s ^ 2 := Rat.cast_injective this
    nlinarith
  -- the points of `Ω` on the line of slope `κ r`
  have hline (r : ℚ) (hr : 1 < r) (t : ℚ) : ![(r : 𝔸) * cayA t, κ r * ((r : 𝔸) * cayA t)] ∈ Ω := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by linarith : r ≠ 0)
    have hc0 : ((cayA t : 𝔸) : ℂ) ≠ 0 := by
      intro h
      have := norm_cayA t
      rw [h, norm_zero] at this
      exact zero_ne_one this
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hc := congrArg (fun w : 𝔸 => (w : ℂ)) h
      simp only [Matrix.cons_val_zero] at hc
      push_cast at hc
      exact mul_ne_zero hr0 hc0 hc
    · simp only [Matrix.cons_val_zero]
      push_cast
      rw [norm_mul, norm_cayA, mul_one, Complex.norm_ratCast]
      have : (1 : ℝ) < |(r : ℝ)| := by
        rw [abs_of_pos (by exact_mod_cast (by linarith : (0 : ℚ) < r))]
        exact_mod_cast hr
      exact ne_of_gt this
    · apply Subtype.ext
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, κ]
      push_cast
      rw [coe_conjA]
      push_cast
      rw [map_mul, conj_cayA]
      simp only [map_ratCast]
      field_simp
  -- step 1: `f` vanishes on each line of slope `κ r`
  have h1 (r : ℚ) (hr : 1 < r) (a : 𝔸) : f ![a, κ r * a] = 0 := by
    obtain ⟨p, hp⟩ := exists_poly_comp (φ := fun t => ![t, κ r * t]) (fun i => by
      fin_cases i
      · exact ⟨X, fun t => by simp⟩
      · exact ⟨C (κ r) * X, fun t => by simp⟩) hf
    have hp0 : p = 0 := by
      apply poly_eq_zero_of_infinite (s := Set.range (fun t : ℚ => (r : 𝔸) * cayA t))
      · apply Set.infinite_range_of_injective
        intro s t hst
        apply cayA_injective
        have hr0 : (r : 𝔸) ≠ 0 := by exact_mod_cast (by linarith : r ≠ 0)
        exact mul_left_cancel₀ hr0 hst
      · rintro _ ⟨t, rfl⟩
        rw [← hp]
        exact hzero _ (hline r hr t)
    rw [hp, hp0, eval_zero]
  -- step 2: off `a = 0`, `f` vanishes on vertical lines
  have h2 (a : 𝔸) (ha : a ≠ 0) (h : 𝔸) : f ![a, h] = 0 := by
    obtain ⟨p, hp⟩ := exists_poly_comp (φ := fun t => ![a, t]) (fun i => by
      fin_cases i
      · exact ⟨C a, fun t => by simp⟩
      · exact ⟨X, fun t => by simp⟩) hf
    have hp0 : p = 0 := by
      apply poly_eq_zero_of_infinite (s := (fun r : {r : ℚ // 1 < r} => κ r * a) '' Set.univ)
      · refine Set.Infinite.image (fun r _ s _ hrs => Subtype.ext (hκ r s r.property s.property
          (mul_right_cancel₀ ha hrs))) ?_
        have : Infinite {r : ℚ // 1 < r} :=
          Infinite.of_injective (fun n : ℕ => (⟨n + 2, by linarith [n.cast_nonneg (α := ℚ)]⟩ :
            {r : ℚ // 1 < r})) (fun m n h => by
              have := congrArg Subtype.val h
              simpa using this)
        exact Set.infinite_univ
      · rintro _ ⟨r, -, rfl⟩
        rw [← hp]
        exact h1 r r.property a
    rw [hp, hp0, eval_zero]
  -- step 3: the remaining line `a = 0`
  have h3 (a h : 𝔸) : f ![a, h] = 0 := by
    by_cases ha : a = 0
    · obtain ⟨p, hp⟩ := exists_poly_comp (φ := fun t => ![t, h]) (fun i => by
        fin_cases i
        · exact ⟨X, fun t => by simp⟩
        · exact ⟨C h, fun t => by simp⟩) hf
      have hp0 : p = 0 := by
        apply poly_eq_zero_of_infinite (s := {t : 𝔸 | t ≠ 0})
        · exact (Set.infinite_univ.sdiff (Set.finite_singleton (0 : 𝔸))).mono fun t ht => ht.2
        · intro t ht
          rw [← hp]
          exact h2 t ht h
      rw [hp, hp0, eval_zero]
    · exact h2 a ha h
  funext z
  have hz : z = ![z 0, z 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hz]
  exact h3 (z 0) (z 1)

end Erdos173.Template

end
