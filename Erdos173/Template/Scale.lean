module

public import Erdos173.Template.Cover
public import OAI.Analysis.PlaneSpectrum.Carrier

/-!
# The carrier of a transcendental scale

Let `x` be a real transcendental number and `L` the algebraic closure of `ℚ(x)` in
`ℂ`. The Cayley transform `T = (x + i)/(x - i)` is a unit of `L`, transcendental over
the algebraic numbers `𝔸`, and `𝔸(T) = 𝔸(x)`. For a finite set `Q` of units of `L`,
the field `N = 𝔸(T)(Q)` is a finite extension of `𝔸(T)` inside `L`, spanned over
`𝔸(T)` by its units since it is spanned by the monomials in `Q`. The theorem on
finite covers therefore applies: no `𝔸`-linear `ℓ` with `ℓ 1 = 1` has every unit of
`L` in some translate `q⁻¹ ker ℓ`, `q ∈ Q`.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Template

open Polynomial IntermediateField ComplexConjugate OAI.PlaneFiveColor.Spectral

/-- The Cayley transform `(x + i)/(x - i)` of a real number. -/
def cayX (x : ℝ) : ℂ := ((x : ℂ) + Complex.I) / ((x : ℂ) - Complex.I)

/-- The denominator `x - i` of the Cayley transform is nonzero. -/
lemma sub_I_ne (x : ℝ) : (x : ℂ) - Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

/-- The Cayley transform of a real number is a unit. -/
lemma norm_cayX (x : ℝ) : ‖cayX x‖ = 1 := by
  have he : conj ((x : ℂ) + Complex.I) = (x : ℂ) - Complex.I := by
    simp [sub_eq_add_neg]
  rw [cayX, norm_div, ← he, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr ?_)]
  rw [← (RingHom.injective (starRingEnd ℂ)).ne_iff, he, map_zero]
  exact sub_I_ne x

/-- `x = i (T + 1)/(T - 1)`. -/
lemma x_eq_cayX (x : ℝ) : (x : ℂ) = Complex.I * (cayX x + 1) / (cayX x - 1) := by
  have h1 : cayX x - 1 = 2 * Complex.I / ((x : ℂ) - Complex.I) := by
    rw [cayX]
    field_simp [sub_I_ne x]
    ring
  have h2 : (2 : ℂ) * Complex.I ≠ 0 := by simp
  rw [h1, cayX]
  field_simp [sub_I_ne x]
  ring_nf

/-- The Cayley transform of a transcendental real is transcendental over `𝔸`. -/
lemma transcendental_cayX {x : ℝ} (hx : Transcendental ℚ x) : Transcendental 𝔸 (cayX x) := by
  intro hT
  have hxC : Transcendental ℚ (x : ℂ) :=
    (transcendental_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ) Complex.ofReal_injective).mpr hx
  have hI : IsAlgebraic 𝔸 Complex.I := by
    simpa using isAlgebraic_algebraMap (R := 𝔸) (A := ℂ) iA
  have hA : IsAlgebraic 𝔸 (x : ℂ) := by
    rw [x_eq_cayX]
    rw [div_eq_mul_inv]
    exact (hI.mul (hT.add isAlgebraic_one)).mul (hT.sub isAlgebraic_one).inv
  exact hxC (hA.restrictScalars ℚ)

/-- The carrier consists of the numbers algebraic over `ℚ(x)`. -/
lemma mem_fieldOf_iff {x : ℝ} {z : ℂ} : z ∈ fieldOf x ↔ IsAlgebraic ℚ⟮(x : ℂ)⟯ z := by
  rw [fieldOf, IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]

/-- The algebraic numbers lie in the carrier. -/
lemma mem_fieldOf_of_𝔸 {x : ℝ} {z : ℂ} (hz : z ∈ 𝔸) : z ∈ fieldOf x :=
  mem_fieldOf_iff.mpr ((mem_algebraicClosure_iff.mp hz).tower_top _)

/-- `x` lies in the carrier. -/
lemma x_mem_fieldOf (x : ℝ) : (x : ℂ) ∈ fieldOf x :=
  mem_fieldOf_iff.mpr (by
    simpa using isAlgebraic_algebraMap (R := ℚ⟮(x : ℂ)⟯) (A := ℂ) (AdjoinSimple.gen ℚ (x : ℂ)))

/-- `T` lies in the carrier. -/
lemma cayX_mem_fieldOf (x : ℝ) : cayX x ∈ fieldOf x := by
  have hI : Complex.I ∈ fieldOf x := mem_fieldOf_of_𝔸 I_mem_𝔸
  exact (fieldOf x).div_mem ((fieldOf x).add_mem (x_mem_fieldOf x) hI)
    ((fieldOf x).sub_mem (x_mem_fieldOf x) hI)

/-- `𝔸(T)` lies in the carrier. -/
lemma mem_fieldOf_of_mem_base {x : ℝ} {z : ℂ} (hz : z ∈ 𝔸⟮cayX x⟯) : z ∈ fieldOf x := by
  induction hz using IntermediateField.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff.mp hz]
    exact cayX_mem_fieldOf x
  | algebraMap a => exact mem_fieldOf_of_𝔸 a.property
  | add z w _ _ hz hw => exact (fieldOf x).add_mem hz hw
  | inv z _ hz => exact (fieldOf x).inv_mem hz
  | mul z w _ _ hz hw => exact (fieldOf x).mul_mem hz hw

/-- `x ∈ 𝔸(T)`. -/
lemma x_mem_base (x : ℝ) : (x : ℂ) ∈ 𝔸⟮cayX x⟯ := by
  rw [x_eq_cayX]
  have hT := mem_adjoin_simple_self 𝔸 (cayX x)
  have hI : Complex.I ∈ 𝔸⟮cayX x⟯ := (𝔸⟮cayX x⟯).algebraMap_mem iA
  exact (𝔸⟮cayX x⟯).div_mem ((𝔸⟮cayX x⟯).mul_mem hI ((𝔸⟮cayX x⟯).add_mem hT
    (𝔸⟮cayX x⟯).one_mem)) ((𝔸⟮cayX x⟯).sub_mem hT (𝔸⟮cayX x⟯).one_mem)

/-- Elements of the carrier are algebraic over `𝔸(T)`. -/
lemma isIntegral_base {x : ℝ} {z : ℂ} (hz : z ∈ fieldOf x) : IsIntegral 𝔸⟮cayX x⟯ z := by
  obtain ⟨p, hp, hpz⟩ := mem_fieldOf_iff.mp hz
  have hle : ∀ c ∈ ℚ⟮(x : ℂ)⟯, c ∈ 𝔸⟮cayX x⟯ := fun c hc =>
    (adjoin_simple_le_iff (K := (𝔸⟮cayX x⟯).restrictScalars ℚ)).mpr (x_mem_base x) hc
  let φ : ℚ⟮(x : ℂ)⟯ →+* 𝔸⟮cayX x⟯ :=
    { toFun := fun c => ⟨c, hle c c.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  refine IsAlgebraic.isIntegral ⟨p.map φ, (Polynomial.map_ne_zero_iff hφ).mpr hp, ?_⟩
  rw [aeval_def, eval₂_map]
  exact hpz

/-- The field `𝔸(T)(Q)`. -/
def fieldN (x : ℝ) (Q : Finset ℂ) : IntermediateField 𝔸⟮cayX x⟯ ℂ :=
  IntermediateField.adjoin 𝔸⟮cayX x⟯ (Q : Set ℂ)

variable {x : ℝ} {Q : Finset ℂ}

/-- `N` lies in the carrier. -/
lemma mem_fieldOf_of_mem_fieldN (hQ : ∀ q ∈ Q, q ∈ fieldOf x) {z : ℂ} (hz : z ∈ fieldN x Q) :
    z ∈ fieldOf x := by
  induction hz using IntermediateField.adjoin_induction with
  | mem z hz => exact hQ z hz
  | algebraMap a => exact mem_fieldOf_of_mem_base a.property
  | add z w _ _ hz hw => exact (fieldOf x).add_mem hz hw
  | inv z _ hz => exact (fieldOf x).inv_mem hz
  | mul z w _ _ hz hw => exact (fieldOf x).mul_mem hz hw

/-- `N` is a finite extension of `𝔸(T)`. -/
lemma finiteDimensional_fieldN (hQ : ∀ q ∈ Q, q ∈ fieldOf x) :
    FiniteDimensional 𝔸⟮cayX x⟯ (fieldN x Q) :=
  IntermediateField.finiteDimensional_adjoin fun q hq => isIntegral_base (hQ q hq)

/-- `N` is spanned over `𝔸(T)` by its units, since it is spanned by the monomials in `Q`. -/
lemma span_units_fieldN (hQ : ∀ q ∈ Q, q ∈ fieldOf x ∧ ‖q‖ = 1) (y : fieldN x Q) :
    y ∈ Submodule.span 𝔸⟮cayX x⟯ {u : fieldN x Q | ‖(u : ℂ)‖ = 1} := by
  have hy : (y : ℂ) ∈ Subalgebra.toSubmodule (Algebra.adjoin 𝔸⟮cayX x⟯ (Q : Set ℂ)) := by
    rw [← adjoin_toSubalgebra_of_isAlgebraic fun q hq =>
      (isIntegral_base (hQ q hq).1).isAlgebraic]
    exact y.property
  rw [Algebra.adjoin_eq_span] at hy
  have hcl (z : ℂ) (hz : z ∈ Submonoid.closure (Q : Set ℂ)) : z ∈ fieldN x Q ∧ ‖z‖ = 1 := by
    induction hz using Submonoid.closure_induction with
    | mem z hz => exact ⟨subset_adjoin _ _ hz, (hQ z hz).2⟩
    | one => exact ⟨(fieldN x Q).one_mem, norm_one⟩
    | mul z w _ _ hz hw =>
      exact ⟨(fieldN x Q).mul_mem hz.1 hw.1, by rw [norm_mul, hz.2, hw.2, one_mul]⟩
  have key : ∀ z ∈ Submodule.span 𝔸⟮cayX x⟯ (Submonoid.closure (Q : Set ℂ) : Set ℂ),
      ∃ hz : z ∈ fieldN x Q, (⟨z, hz⟩ : fieldN x Q) ∈
        Submodule.span 𝔸⟮cayX x⟯ {u : fieldN x Q | ‖(u : ℂ)‖ = 1} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact ⟨(hcl z hz).1, Submodule.subset_span (hcl z hz).2⟩
    | zero => exact ⟨(fieldN x Q).zero_mem, Submodule.zero_mem _⟩
    | add z w _ _ hz hw =>
      obtain ⟨hz, hz'⟩ := hz
      obtain ⟨hw, hw'⟩ := hw
      exact ⟨(fieldN x Q).add_mem hz hw, Submodule.add_mem _ hz' hw'⟩
    | smul c z _ hz =>
      obtain ⟨hz, hz'⟩ := hz
      exact ⟨SMulMemClass.smul_mem c hz, Submodule.smul_mem _ c hz'⟩
  obtain ⟨_, h⟩ := key _ hy
  exact h

/-- No finite cover of the unit circle of the carrier by translated kernels. -/
theorem cover_impossible_fieldOf (hx : Transcendental ℚ x)
    (hQ : ∀ q ∈ Q, q ∈ fieldOf x ∧ ‖q‖ = 1) (ℓ : ℂ →ₗ[𝔸] 𝔸) (hℓ : ℓ 1 = 1) :
    ∃ u ∈ fieldOf x, ‖u‖ = 1 ∧ ∀ q ∈ Q, ℓ (q * u) ≠ 0 := by
  have := finiteDimensional_fieldN fun q hq => (hQ q hq).1
  obtain ⟨u, hu, h⟩ := cover_impossible (N := fieldN x Q) (norm_cayX x) (transcendental_cayX hx)
    (span_units_fieldN hQ) Q (fun q hq => ⟨subset_adjoin _ _ hq, (hQ q hq).2⟩) hℓ
  exact ⟨u, mem_fieldOf_of_mem_fieldN (fun q hq => (hQ q hq).1) hu.1, hu.2, h⟩

end Erdos173.Template

end
