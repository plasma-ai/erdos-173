module

public import Erdos173.Template.Annihilator
public import Erdos173.Template.CayleyEscape
public import Erdos173.Template.GeneralPosition
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Cauchy frames in a finite extension of `𝔸(T)`

Let `T` be a complex unit transcendental over the algebraic numbers `𝔸`, let
`B = 𝔸(T)`, and let `N ⊆ ℂ` be a finite extension of `B` spanned over `B` by its
units `K_N`. Units in general position over `B` exist: the real elements of `N`
together with `i` span `N` over `B`, so Cayley transforms of real elements escape
every finite union of proper `B`-subspaces. Taking `d = [N : B]` of them as a basis
and clearing denominators in the coordinates of `q s_k` gives a Cauchy frame on the
units of `N` for any finite set `Q` of units.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Template

open Polynomial IntermediateField ComplexConjugate Module

variable {T : ℂ}

/-- A nonzero polynomial does not vanish at a transcendental `T`. -/
lemma aeval_ne_zero (hT : Transcendental 𝔸 T) {p : 𝔸[X]} (hp : p ≠ 0) : aeval T p ≠ 0 :=
  fun h => hp (transcendental_iff.mp hT p h)

/-- Elements of `𝔸(T)` have a common polynomial denominator. -/
lemma exists_common_denom (hT : Transcendental 𝔸 T) {ι : Type*} [Fintype ι] (g : ι → 𝔸⟮T⟯) :
    ∃ κ : 𝔸[X], κ ≠ 0 ∧ ∃ P : ι → 𝔸[X], ∀ i, aeval T κ * (g i : ℂ) = aeval T (P i) := by
  classical
  have hrep (i : ι) : ∃ r s : 𝔸[X], s ≠ 0 ∧ (g i : ℂ) = aeval T r / aeval T s := by
    obtain ⟨r, s, h⟩ := (mem_adjoin_simple_iff 𝔸 (g i : ℂ)).mp (g i).property
    by_cases hs : s = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      rw [h, hs]
      simp
    · exact ⟨r, s, hs, h⟩
  choose r s hs hrs using hrep
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.mpr fun i _ => hs i,
    fun i => r i * ∏ j ∈ Finset.univ.erase i, s j, fun i => ?_⟩
  rw [hrs i, map_mul, map_prod, map_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  field_simp [aeval_ne_zero hT (hs i)]

variable (N : IntermediateField 𝔸⟮T⟯ ℂ)

/-- `T ∈ N`. -/
lemma T_mem : T ∈ N := N.algebraMap_mem (AdjoinSimple.gen 𝔸 T)

/-- The algebraic numbers lie in `N`. -/
lemma coe_𝔸_mem (a : 𝔸) : (a : ℂ) ∈ N := N.algebraMap_mem (algebraMap 𝔸 𝔸⟮T⟯ a)

/-- `i ∈ N`. -/
lemma I_mem : Complex.I ∈ N := coe_𝔸_mem N iA

/-- The units of `N`. -/
def units : Set ℂ := {u | u ∈ N ∧ ‖u‖ = 1}

variable {N}

/-- The units of `N` are closed under multiplication. -/
lemma mul_mem_units {u v : ℂ} (hu : u ∈ units N) (hv : v ∈ units N) : u * v ∈ units N :=
  ⟨N.mul_mem hu.1 hv.1, by rw [norm_mul, hu.2, hv.2, one_mul]⟩

/-- The conjugate of a unit is its inverse. -/
lemma conj_eq_inv {u : ℂ} (hu : ‖u‖ = 1) : conj u = u⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu]
  simp

/-- The units of `N` are closed under inversion. -/
lemma inv_mem_units {u : ℂ} (hu : u ∈ units N) : u⁻¹ ∈ units N :=
  ⟨N.inv_mem hu.1, by rw [norm_inv, hu.2, inv_one]⟩

/-- The units of `N` are closed under conjugation. -/
lemma conj_mem_units {u : ℂ} (hu : u ∈ units N) : conj u ∈ units N := by
  rw [conj_eq_inv hu.2]
  exact inv_mem_units hu

/-- The Cayley denominator `1 - i r` of a real `r` is nonzero. -/
lemma one_sub_I_mul_ne {r : ℂ} (hr : r.im = 0) : 1 - Complex.I * r ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [hr] at this

/-- The Cayley transform of a real number is a unit. -/
lemma norm_cayley {r : ℂ} (hr : r.im = 0) :
    ‖(1 + Complex.I * r) / (1 - Complex.I * r)‖ = 1 := by
  have he : conj (1 + Complex.I * r) = 1 - Complex.I * r := by
    rw [← Complex.re_add_im r, hr]
    simp [sub_eq_add_neg]
  rw [norm_div, ← he, Complex.norm_conj, div_self]
  rw [norm_ne_zero_iff, ← (RingHom.injective (starRingEnd ℂ)).ne_iff, he, map_zero]
  exact one_sub_I_mul_ne hr

variable (N)

/-- The real structure of `N`: real elements and `i`. -/
def realStructure : RealStructure 𝔸⟮T⟯ N where
  ι := ⟨Complex.I, I_mem N⟩
  Re := {z | (z : ℂ).im = 0}
  ι_sq := Subtype.ext (by simp)
  one_mem := by simp
  add_mem r hr s hs := by simp_all
  smul_mem t r hr := by
    change ((algebraMap 𝔸⟮T⟯ ℂ (t : 𝔸⟮T⟯)) * (r : ℂ)).im = 0
    have : algebraMap 𝔸⟮T⟯ ℂ (t : 𝔸⟮T⟯) = (t : ℂ) := by simp
    rw [this, Complex.mul_im]
    simp [show (r : ℂ).im = 0 from hr]
  isUnit r hr := by
    refine isUnit_iff_ne_zero.mpr fun h => one_sub_I_mul_ne (r := (r : ℂ)) hr ?_
    simpa using congrArg (fun z : N => (z : ℂ)) h

/-- The Cayley transform of the real structure is `(1 + i r)/(1 - i r)`. -/
lemma coe_realStructure_cay (r : (realStructure N).Re) :
    (((realStructure N).cay r : N) : ℂ) =
      (1 + Complex.I * (r : ℂ)) / (1 - Complex.I * (r : ℂ)) := by
  have h := (realStructure N).cay_spec r
  have hc := congrArg (fun z : N => (z : ℂ)) h
  simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one,
    AddMemClass.coe_add] at hc
  rw [eq_div_iff (one_sub_I_mul_ne r.property), mul_comm]
  exact hc

/-- A functional killing every real element `r` of `N` and every `i r` is zero, since
the units span `N`. -/
lemma realStructure_span
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1})
    (ℓ : N →ₗ[𝔸⟮T⟯] 𝔸⟮T⟯)
    (h : ∀ r ∈ (realStructure N).Re, ℓ r = 0 ∧ ℓ ((realStructure N).ι * r) = 0) : ℓ = 0 := by
  have hu (y : N) (hy : ‖(y : ℂ)‖ = 1) : ℓ y = 0 := by
    have hy0 : (y : ℂ) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hy
      exact zero_ne_one hy
    have hc : conj (y : ℂ) = (y : ℂ)⁻¹ := conj_eq_inv hy
    let ι : N := (realStructure N).ι
    have hι : (ι : ℂ) = Complex.I := rfl
    have h2 : ((2 : N) : ℂ) = 2 := rfl
    let r₁ : N := (y + y⁻¹) / 2
    let r₂ : N := (y - y⁻¹) / (2 * ι)
    have hr₁ : r₁ ∈ (realStructure N).Re := by
      change ((((y + y⁻¹) / 2 : N)) : ℂ).im = 0
      push_cast
      rw [h2, ← hc, Complex.add_conj]
      simp
    have hr₂ : r₂ ∈ (realStructure N).Re := by
      change ((((y - y⁻¹) / (2 * ι) : N)) : ℂ).im = 0
      push_cast
      rw [h2, hι, ← hc, Complex.sub_conj]
      field_simp
      simp
    have he : y = r₁ + ι * r₂ := by
      apply Subtype.ext
      simp only [r₁, r₂]
      push_cast
      rw [h2, hι]
      field_simp
      ring
    rw [he, map_add, (h r₁ hr₁).1, (h r₂ hr₂).2, add_zero]
  ext x
  induction hspan x using Submodule.span_induction with
  | mem y hy => simp [hu y hy]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

variable [FiniteDimensional 𝔸⟮T⟯ N]

/-- Units of `N` in general position over `𝔸(T)`. -/
lemma exists_general_units
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1}) (n : ℕ) :
    ∃ s : Fin n → N, (∀ i, ‖(s i : ℂ)‖ = 1) ∧ GeneralFamily 𝔸⟮T⟯ s := by
  have : Algebra.IsIntegral 𝔸⟮T⟯ N := Algebra.IsIntegral.of_finite _ _
  refine exists_generalFamily {y : N | ‖(y : ℂ)‖ = 1} (fun P hP => ?_) n
  obtain ⟨r, hr⟩ := (realStructure N).cay_subspaces_avoid (realStructure_span N hspan) P hP
  refine ⟨_, ?_, hr⟩
  change ‖(((realStructure N).cay r : N) : ℂ)‖ = 1
  rw [coe_realStructure_cay]
  exact norm_cayley r.property

omit [FiniteDimensional 𝔸⟮T⟯ N] in
/-- The multipliers of the parameter plane preserve the units of `N`. -/
lemma mul_multiplier_mem_units (hT1 : ‖T‖ = 1) {z : Fin 2 → 𝔸} (hz : z ∈ Ω) {u : ℂ}
    (hu : u ∈ units N) :
    u * ((z 0 : ℂ) * (1 + (z 1 : ℂ) / (T - z 0))) ∈ units N := by
  refine mul_mem_units hu ⟨?_, (Ω_unit hz hT1).2⟩
  exact N.mul_mem (coe_𝔸_mem N _) (N.add_mem N.one_mem (N.div_mem (coe_𝔸_mem N _)
    (N.sub_mem (T_mem N) (coe_𝔸_mem N _))))

/-- Evaluating at the generator of `𝔸(T)` is evaluating at `T`. -/
lemma coe_aeval_gen (p : 𝔸[X]) : ((aeval (AdjoinSimple.gen 𝔸 T) p : 𝔸⟮T⟯) : ℂ) = aeval T p := by
  rw [← AdjoinSimple.coe_gen 𝔸 T]
  exact (aeval_algHom_apply (𝔸⟮T⟯).val (AdjoinSimple.gen 𝔸 T) p).symm

/-- A Cauchy frame on the units of `N`. -/
theorem exists_frame (hT1 : ‖T‖ = 1) (hT : Transcendental 𝔸 T)
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1})
    (Q : Finset ℂ) (hQ : ∀ q ∈ Q, q ∈ units N) :
    ∃ 𝔣 : CauchyFrame, 𝔣.T = T ∧ 𝔣.Q = Q ∧ 𝔣.U = units N ∧ 0 < 𝔣.d ∧
      ∀ l, 𝔣.b l ∈ units N := by
  classical
  set d := finrank 𝔸⟮T⟯ N with hd_def
  have hd : 0 < d := finrank_pos
  set n := Fintype.card Q * (d - 1) + d with hn
  obtain ⟨s, hsn, hsg⟩ := exists_general_units N hspan n
  let e₀ : Fin d ↪ Fin n := Fin.castLEEmb (by omega)
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hli : LinearIndependent 𝔸⟮T⟯ (s ∘ e₀) := hsg.linearIndependent e₀
  let bas : Basis (Fin d) 𝔸⟮T⟯ N := basisOfLinearIndependentOfCardEqFinrank hli (by simp [d])
  have hbas (l : Fin d) : bas l = s (e₀ l) := by
    simp [bas, coe_basisOfLinearIndependentOfCardEqFinrank]
  let qN : Q → N := fun j => ⟨j, (hQ j j.2).1⟩
  let g : Q × Fin n × Fin d → 𝔸⟮T⟯ := fun x => bas.repr (qN x.1 * s x.2.1) x.2.2
  obtain ⟨κ, hκ, P, hP⟩ := exists_common_denom hT g
  let TB := AdjoinSimple.gen 𝔸 T
  have hPB (x : Q × Fin n × Fin d) : aeval TB κ * g x = aeval TB (P x) := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, coe_aeval_gen, coe_aeval_gen, hP]
  have hsmul (c : 𝔸⟮T⟯) (x : N) : ((c • x : N) : ℂ) = (c : ℂ) * x := rfl
  refine ⟨{
    T := T
    d := d
    n := n
    Q := Q
    b := fun l => (s (e₀ l) : ℂ)
    s := fun k => (s k : ℂ)
    κ := κ
    p := fun j k l => P (j, k, l)
    U := units N
    norm_T := hT1
    κ_ne := hκ
    coord := fun j k => ?_
    det_ne := fun j e => ?_
    card_lt := by omega
    s_mem := fun k => ⟨(s k).property, hsn k⟩
    mul_mem := fun z hz u hu => mul_multiplier_mem_units N hT1 hz hu }, rfl, rfl, rfl, hd,
    fun l => ⟨(s (e₀ l)).property, hsn (e₀ l)⟩⟩
  · have h := congrArg (fun x : N => (x : ℂ)) (bas.sum_repr (qN j * s k))
    simp only [AddSubmonoidClass.coe_finsetSum, hsmul, hbas, MulMemClass.coe_mul] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc]
    congr 1
    exact hP (j, k, l)
  · intro hdet
    have hq0 : (j : ℂ) ≠ 0 := by
      intro h0
      have := (hQ j j.2).2
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    let c : N := algebraMap 𝔸⟮T⟯ N (aeval TB κ) * qN j
    have hc : c ≠ 0 := by
      intro h0
      have := congrArg (fun x : N => (x : ℂ)) h0
      simp only [c, MulMemClass.coe_mul, ZeroMemClass.coe_zero] at this
      rcases mul_eq_zero.mp this with h | h
      · exact aeval_ne_zero hT hκ (by rw [← coe_aeval_gen]; exact h)
      · exact hq0 h
    let v : Fin d → N := fun i => c * s (e i)
    have hv : LinearIndependent 𝔸⟮T⟯ v :=
      (hsg.linearIndependent e).map' (LinearMap.mulLeft 𝔸⟮T⟯ c)
        (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hc))
    have hspanv : Submodule.span 𝔸⟮T⟯ (Set.range v) = ⊤ := by
      have := (basisOfLinearIndependentOfCardEqFinrank hv (by simp [d])).span_eq
      rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at this
    have hunit := (Module.Basis.is_basis_iff_det bas).mp ⟨hv, hspanv⟩
    have hmat : bas.toMatrix v = ((aeval TB).toRingHom.mapMatrix
        (Matrix.of fun i l => P (j, e i, l))).transpose := by
      ext l i
      rw [Basis.toMatrix_apply]
      simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← hPB (j, e i, l)]
      have he : v i = aeval TB κ • (qN j * s (e i)) := by
        simp only [v, c, Algebra.smul_def, mul_assoc]
      rw [he, map_smul]
      rfl
    rw [Basis.det_apply, hmat, Matrix.det_transpose, ← RingHom.map_det] at hunit
    erw [hdet, map_zero] at hunit
    exact not_isUnit_zero hunit

end Erdos173.Template

end
