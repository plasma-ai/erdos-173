module

public import Erdos173.Template.FunctionField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# No finite cover of the units by translated kernels

Let `T` be a complex unit transcendental over `𝔸`, and let `N ⊆ ℂ` be a finite
extension of `𝔸(T)` spanned over `𝔸(T)` by its units `K_N`. There is no finite set
`Q ⊆ K_N` and `𝔸`-linear `ℓ : ℂ → 𝔸` with `ℓ 1 = 1` such that every unit `u` of `N`
has some `q ∈ Q` with `ℓ(q u) = 0`.

Suppose there were. The Cauchy-transform argument gives a nonzero `p ∈ 𝔸[X]` with
`ℓ(p(T) w) = 0` for every `w` in the `𝔸`-span `A` of `K_N`. The algebra
`A / (T - a)A` has dimension at most `[N : 𝔸(T)]`: a relation over `𝔸(T)`, cleared of
denominators and of the largest common power of `X - a`, reduces to a nontrivial
relation over `𝔸`. Since `𝔸` is algebraically closed, `p` splits and `A / p(T)A` is
finite-dimensional, hence so is the quotient `R = A/I` by the ideal `I` of elements
`v` with `ℓ(v A) = 0`, through which `ℓ` factors. The real elements of `A` and `i`
span `A`, the Cayley transforms of real elements are units, and in the
finite-dimensional algebra `R` some Cayley transform escapes all the nonzero
functionals `x ↦ ℓ(q x)`, `q ∈ Q`, contradicting the cover.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Template

open Polynomial IntermediateField ComplexConjugate Module

variable {T : ℂ} (N : IntermediateField 𝔸⟮T⟯ ℂ)

/-- The `𝔸`-span of the units of `N`. -/
def spanA : Submodule 𝔸 ℂ := Submodule.span 𝔸 (units N)

variable {N}

/-- `A` lies in `N`. -/
lemma mem_of_mem_spanA {v : ℂ} (hv : v ∈ spanA N) : v ∈ N := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact hv.1
  | zero => exact N.zero_mem
  | add v w _ _ hv hw => exact N.add_mem hv hw
  | smul c v _ hv => rw [smul_eq]; exact N.mul_mem (coe_𝔸_mem N c) hv

/-- The units of `N` lie in `A`. -/
lemma mem_spanA_of_mem_units {u : ℂ} (hu : u ∈ units N) : u ∈ spanA N := Submodule.subset_span hu

/-- `A` is closed under multiplication. -/
lemma mul_mem_spanA {v w : ℂ} (hv : v ∈ spanA N) (hw : w ∈ spanA N) : v * w ∈ spanA N := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    induction hw using Submodule.span_induction with
    | mem w hw => exact mem_spanA_of_mem_units (mul_mem_units hv hw)
    | zero => simp
    | add w w' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul c w _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => simp
  | add v v' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
  | smul c v _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

/-- `1 ∈ A`. -/
lemma one_mem_spanA : (1 : ℂ) ∈ spanA N :=
  mem_spanA_of_mem_units ⟨N.one_mem, norm_one⟩

/-- The algebraic numbers lie in `A`. -/
lemma coe_mem_spanA (a : 𝔸) : (a : ℂ) ∈ spanA N := by
  have h := Submodule.smul_mem (spanA N) a (one_mem_spanA (N := N))
  rwa [smul_eq, mul_one] at h

/-- Polynomials in `T` lie in `A`. -/
lemma aeval_mem_spanA (hT1 : ‖T‖ = 1) (p : 𝔸[X]) : aeval T p ∈ spanA N := by
  have hT : T ∈ units N := ⟨T_mem N, hT1⟩
  have hpow (n : ℕ) : T ^ n ∈ spanA N := by
    induction n with
    | zero => simpa using one_mem_spanA (N := N)
    | succ n ih => rw [pow_succ]; exact mul_mem_spanA ih (mem_spanA_of_mem_units hT)
  rw [aeval_eq_sum_range]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpow i)

/-- `A` is closed under conjugation. -/
lemma conj_mem_spanA {v : ℂ} (hv : v ∈ spanA N) : conj v ∈ spanA N := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact mem_spanA_of_mem_units (conj_mem_units hv)
  | zero => simp
  | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
  | smul c v _ hv =>
    rw [smul_eq, map_mul]
    have h := Submodule.smul_mem _ (conjA c) hv
    rwa [smul_eq, coe_conjA] at h

/-- Every element of `A` is `r₁ + i r₂` with `r₁, r₂` real elements of `A`. -/
lemma spanA_re_im {v : ℂ} (hv : v ∈ spanA N) :
    ∃ r₁ r₂ : ℂ, r₁ ∈ spanA N ∧ r₂ ∈ spanA N ∧ r₁.im = 0 ∧ r₂.im = 0 ∧
      v = r₁ + Complex.I * r₂ := by
  have h2 : ((2 : 𝔸) : ℂ) = 2 := rfl
  refine ⟨((2 : 𝔸)⁻¹ : 𝔸) • (v + conj v), ((2 * iA : 𝔸)⁻¹ : 𝔸) • (v - conj v),
    Submodule.smul_mem _ _ (Submodule.add_mem _ hv (conj_mem_spanA hv)),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hv (conj_mem_spanA hv)), ?_, ?_, ?_⟩
  · rw [smul_eq, Complex.add_conj]
    push_cast
    rw [h2]
    simp
  · rw [smul_eq, Complex.sub_conj]
    push_cast
    rw [h2, coe_iA]
    field_simp
    simp
  · simp only [smul_eq]
    push_cast
    rw [h2, coe_iA]
    field_simp
    ring

/-- The Cayley transform of a real element of `A` is a unit, and its denominator is
invertible in `A`. -/
lemma cayley_mem {z : ℂ} (hz : z ∈ spanA N) (hre : z.im = 0) :
    (1 + Complex.I * z) / (1 - Complex.I * z) ∈ units N ∧
      (1 - Complex.I * z)⁻¹ ∈ spanA N := by
  have hd := one_sub_I_mul_ne hre
  have hzN := mem_of_mem_spanA hz
  have hu : (1 + Complex.I * z) / (1 - Complex.I * z) ∈ units N :=
    ⟨N.div_mem (N.add_mem N.one_mem (N.mul_mem (I_mem N) hzN))
      (N.sub_mem N.one_mem (N.mul_mem (I_mem N) hzN)), norm_cayley hre⟩
  refine ⟨hu, ?_⟩
  have he : (1 - Complex.I * z)⁻¹ = ((2 : 𝔸)⁻¹ : 𝔸) •
      (1 + (1 + Complex.I * z) / (1 - Complex.I * z)) := by
    rw [smul_eq]
    push_cast
    rw [show ((2 : 𝔸) : ℂ) = 2 from rfl]
    field_simp
    ring
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ one_mem_spanA (mem_spanA_of_mem_units hu))

/-- `p(T) A` is spanned modulo by a finite set. -/
def Good (p : 𝔸[X]) : Prop :=
  ∃ F : Finset ℂ, (↑F ⊆ (spanA N : Set ℂ)) ∧
    ∀ v ∈ spanA N, ∃ w ∈ spanA N, v - aeval T p * w ∈ Submodule.span 𝔸 (F : Set ℂ)

section Reduction

variable (hT1 : ‖T‖ = 1) (hT : Transcendental 𝔸 T)
include hT1 hT

/-- A polynomial relation among elements of `A`, divided by the largest common power
of `X - a`, reduces to a nontrivial relation over `𝔸` modulo `(T - a) A`. -/
lemma reduce_relation {ι : Type*} [Fintype ι] (a : 𝔸) (P : ι → 𝔸[X]) (hP : ∃ i, P i ≠ 0)
    (vs : ι → ℂ) (hvs : ∀ i, vs i ∈ spanA N) (hrel : ∑ i, aeval T (P i) * vs i = 0) :
    ∃ c : ι → 𝔸, (∃ i, c i ≠ 0) ∧ ∃ w ∈ spanA N, ∑ i, c i • vs i = (T - a) * w := by
  classical
  obtain ⟨i₀, hi₀, hmin⟩ := (Finset.univ.filter fun i => P i ≠ 0).exists_min_image
    (fun i => rootMultiplicity a (P i)) (by
      obtain ⟨i, hi⟩ := hP
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
  have hP₀ : P i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  set m := rootMultiplicity a (P i₀)
  have hdvd (i : ι) : (X - C a) ^ m ∣ P i := by
    by_cases hi : P i = 0
    · rw [hi]
      exact dvd_zero _
    · exact (pow_dvd_pow _ (hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))).trans
        (pow_rootMultiplicity_dvd _ _)
  choose P' hP' using hdvd
  have hXa : (X - C a) ^ m ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero a)
  have hev : (P' i₀).eval a ≠ 0 := by
    obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (P i₀) hP₀ a
    have : P' i₀ = q := mul_left_cancel₀ hXa ((hP' i₀).symm.trans hq)
    rw [this]
    intro h
    exact hnd (dvd_iff_isRoot.mpr h)
  have hTa : T - (a : ℂ) ≠ 0 := by
    intro h
    have := transcendental_iff.mp hT (X - C a) (by simpa [sub_eq_zero] using h)
    exact X_sub_C_ne_zero a this
  have hrel' : ∑ i, aeval T (P' i) * vs i = 0 := by
    have h : (T - a) ^ m * ∑ i, aeval T (P' i) * vs i = 0 := by
      rw [Finset.mul_sum, ← hrel]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hP' i, map_mul, map_pow, map_sub, aeval_X, aeval_C]
      simp only [IntermediateField.algebraMap_apply]
      ring
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hTa)
  have hR (i : ι) : X - C a ∣ P' i - C ((P' i).eval a) := X_sub_C_dvd_sub_C_eval
  choose R hR using hR
  refine ⟨fun i => (P' i).eval a, ⟨i₀, hev⟩, -∑ i, aeval T (R i) * vs i,
    Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
      mul_mem_spanA (aeval_mem_spanA hT1 _) (hvs i)), ?_⟩
  have hpt (i : ι) : (((P' i).eval a : 𝔸) : ℂ) = aeval T (P' i) - (T - a) * aeval T (R i) := by
    have h := congrArg (aeval T) (hR i)
    rw [map_sub, aeval_C, map_mul, map_sub, aeval_X, aeval_C] at h
    simp only [IntermediateField.algebraMap_apply] at h
    rw [← h]
    ring
  simp only [smul_eq, hpt, sub_mul, Finset.sum_sub_distrib, hrel', mul_assoc, ← Finset.mul_sum]
  ring

omit hT1 hT in
/-- Nonzero constants are good. -/
lemma good_C {c : 𝔸} (hc : c ≠ 0) : Good (N := N) (C c) := by
  refine ⟨∅, by simp, fun v hv => ⟨((c⁻¹ : 𝔸) : ℂ) * v, ?_, ?_⟩⟩
  · rw [← smul_eq]
    exact Submodule.smul_mem _ _ hv
  · rw [aeval_C, IntermediateField.algebraMap_apply, ← mul_assoc, ← IntermediateField.coe_mul,
      mul_inv_cancel₀ hc]
    simp

/-- `A / (T - a) A` has dimension at most `[N : 𝔸(T)]`. -/
lemma good_linear [FiniteDimensional 𝔸⟮T⟯ N] (a : 𝔸) : Good (N := N) (X - C a) := by
  classical
  let A' : Subalgebra 𝔸 ℂ := (spanA N).toSubalgebra one_mem_spanA fun _ _ => mul_mem_spanA
  have hTa : (T - a : ℂ) ∈ A' := Submodule.sub_mem _ (by
    simpa using aeval_mem_spanA (N := N) hT1 X) (coe_mem_spanA a)
  let S : Submodule 𝔸 A' := LinearMap.range (LinearMap.mulLeft 𝔸 (⟨T - a, hTa⟩ : A'))
  have hrank : Module.rank 𝔸 (A' ⧸ S) ≤ finrank 𝔸⟮T⟯ N := by
    apply rank_le
    intro s hs
    by_contra! hlt
    let f : Fin (finrank 𝔸⟮T⟯ N + 1) → s := fun i => s.equivFin.symm ⟨i, by omega⟩
    have hf : Function.Injective f := fun i j h => by
      have := Fin.ext_iff.mp (s.equivFin.symm.injective h)
      exact Fin.ext this
    have hli := hs.comp f hf
    choose vs hvs using fun i => Submodule.Quotient.mk_surjective S (f i : A' ⧸ S)
    let wN : Fin (finrank 𝔸⟮T⟯ N + 1) → N := fun i => ⟨(vs i : ℂ), mem_of_mem_spanA (vs i).property⟩
    have hnli : ¬ LinearIndependent 𝔸⟮T⟯ wN := fun h => by
      have := h.fintype_card_le_finrank
      simp at this
    obtain ⟨g, hg, i, hgi⟩ := Fintype.not_linearIndependent_iff.mp hnli
    obtain ⟨κ, hκ, P, hP⟩ := exists_common_denom hT g
    have hrel : ∑ i, aeval T (P i) * (vs i : ℂ) = 0 := by
      have h := congrArg (fun x : N => aeval T κ * (x : ℂ)) hg
      simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, mul_zero,
        Finset.mul_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hP j]
      change _ = aeval T κ * ((g j : ℂ) * (vs j : ℂ))
      ring
    have hPi : P i ≠ 0 := by
      intro h0
      have := hP i
      rw [h0, map_zero] at this
      exact hgi (Subtype.ext ((mul_eq_zero.mp this).resolve_left (aeval_ne_zero hT hκ)))
    obtain ⟨c, ⟨j, hcj⟩, w, hw, hcw⟩ := reduce_relation hT1 hT a P ⟨i, hPi⟩
      (fun i => (vs i : ℂ)) (fun i => (vs i).property) hrel
    have hS : ∑ i, c i • vs i ∈ S := ⟨⟨w, hw⟩, by
      apply Subtype.ext
      simp only [LinearMap.mulLeft_apply, MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum,
        SetLike.val_smul]
      rw [hcw]⟩
    have hzero : ∑ i, c i • (f i : A' ⧸ S) = 0 := by
      have h : S.mkQ (∑ i, c i • vs i) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hS
      simpa only [map_sum, map_smul, Submodule.mkQ_apply, hvs] using h
    exact hcj (Fintype.linearIndependent_iff.mp hli c hzero j)
  have : Module.Finite 𝔸 (A' ⧸ S) :=
    Module.rank_lt_aleph0_iff.mp (hrank.trans_lt (Cardinal.natCast_lt_aleph0))
  obtain ⟨k, fs, hfs⟩ := Module.Finite.exists_fin (R := 𝔸) (M := A' ⧸ S)
  choose ls hls using fun i => Submodule.Quotient.mk_surjective S (fs i)
  refine ⟨Finset.univ.image fun i => (ls i : ℂ), ?_, fun v hv => ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact (ls i).property
  have hmem : Submodule.Quotient.mk (⟨v, hv⟩ : A') ∈ Submodule.span 𝔸 (Set.range fs) := by
    rw [hfs]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝔸).mp hmem
  have hd : (⟨v, hv⟩ : A') - ∑ i, c i • ls i ∈ S := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← hc, sub_eq_zero]
    have h := map_sum S.mkQ (fun i => c i • ls i) Finset.univ
    simp only [map_smul, Submodule.mkQ_apply, hls] at h
    exact h.symm
  obtain ⟨w, hw⟩ := hd
  refine ⟨w, w.property, ?_⟩
  have hw' := congrArg (fun x : A' => (x : ℂ)) hw
  simp only [LinearMap.mulLeft_apply, MulMemClass.coe_mul, AddSubgroupClass.coe_sub,
    AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at hw'
  have he : v - aeval T (X - C a) * (w : ℂ) = ∑ i, c i • (ls i : ℂ) := by
    rw [map_sub, aeval_X, aeval_C, IntermediateField.algebraMap_apply, hw']
    ring
  rw [he]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

omit hT in
/-- A good polynomial times a good linear factor is good. -/
lemma good_mul {p : 𝔸[X]} (a : 𝔸) (hp : Good (N := N) p) (ha : Good (N := N) (X - C a)) :
    Good (N := N) (p * (X - C a)) := by
  classical
  obtain ⟨F, hF, hFp⟩ := hp
  obtain ⟨G, hG, hGa⟩ := ha
  refine ⟨F ∪ G.image (fun g => aeval T p * g), ?_, fun v hv => ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hF hx
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
      exact mul_mem_spanA (aeval_mem_spanA hT1 p) (hG hg)
  obtain ⟨w₁, hw₁, h₁⟩ := hFp v hv
  obtain ⟨w₂, hw₂, h₂⟩ := hGa w₁ hw₁
  refine ⟨w₂, hw₂, ?_⟩
  have he : v - aeval T (p * (X - C a)) * w₂ =
      (v - aeval T p * w₁) + aeval T p * (w₁ - aeval T (X - C a) * w₂) := by
    rw [map_mul]
    ring
  rw [he]
  refine Submodule.add_mem _ (Submodule.span_mono Finset.subset_union_left h₁) ?_
  have hmap : aeval T p * (w₁ - aeval T (X - C a) * w₂) ∈
      (Submodule.span 𝔸 (G : Set ℂ)).map (LinearMap.mulLeft 𝔸 (aeval T p)) :=
    ⟨_, h₂, rfl⟩
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨g, hg, rfl⟩
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg)

/-- `A / p(T) A` is spanned by a finite set for every nonzero `p`. -/
lemma good_of_ne_zero [FiniteDimensional 𝔸⟮T⟯ N] {p : 𝔸[X]} (hp : p ≠ 0) : Good (N := N) p := by
  induction h : p.natDegree generalizing p with
  | zero =>
    rw [eq_C_of_natDegree_eq_zero h]
    exact good_C (fun hc => hp (by rw [eq_C_of_natDegree_eq_zero h, hc, map_zero]))
  | succ n ih =>
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
      rw [degree_eq_natDegree hp, h]
      exact_mod_cast Nat.succ_ne_zero n)
    have hdiv := mul_divByMonic_eq_iff_isRoot.mpr ha
    set q := p /ₘ (X - C a)
    have hq : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdiv
      exact hp hdiv.symm
    have hqd : q.natDegree = n := by
      have := congrArg natDegree hdiv
      rw [natDegree_mul (X_sub_C_ne_zero a) hq, natDegree_X_sub_C, h] at this
      omega
    rw [← hdiv, mul_comm]
    exact good_mul hT1 a (ih hq hqd) (good_linear hT1 hT a)

end Reduction

variable (N)

/-- The span of the units as a subalgebra. -/
def algA : Subalgebra 𝔸 ℂ := (spanA N).toSubalgebra one_mem_spanA fun _ _ => mul_mem_spanA

variable {N}

/-- Membership in the subalgebra `A` is membership in the span. -/
lemma mem_algA {x : ℂ} : x ∈ algA N ↔ x ∈ spanA N := Submodule.mem_toSubalgebra

variable (N) (ℓ : ℂ →ₗ[𝔸] 𝔸)

/-- The annihilator ideal `{v | ℓ(v A) = 0}`. -/
def annIdeal : Ideal (algA N) where
  carrier := {v | ∀ w : algA N, ℓ ((v : ℂ) * w) = 0}
  add_mem' {v v'} hv hv' w := by
    simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, add_mul, map_add] at hv hv' ⊢
    rw [hv w, hv' w, add_zero]
  zero_mem' w := by simp
  smul_mem' c v hv w := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul] at hv ⊢
    have := hv (c * w)
    rw [Subalgebra.coe_mul] at this
    rw [← this]
    ring_nf

/-- The quotient algebra `A / I`. -/
abbrev quotA := algA N ⧸ annIdeal N ℓ

/-- The quotient map. -/
abbrev πA : algA N →ₐ[𝔸] quotA N ℓ := Ideal.Quotient.mkₐ 𝔸 (annIdeal N ℓ)

/-- The annihilator ideal lies in the kernel of `ℓ`. -/
lemma annIdeal_le_ker :
    (annIdeal N ℓ).restrictScalars 𝔸 ≤ LinearMap.ker (ℓ ∘ₗ (algA N).val.toLinearMap) :=
  fun v hv => by simpa using hv 1

/-- The functional `ℓ` on the quotient. -/
def ℓbar : quotA N ℓ →ₗ[𝔸] 𝔸 :=
  ((annIdeal N ℓ).restrictScalars 𝔸).liftQ _ (annIdeal_le_ker N ℓ) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv 𝔸 (annIdeal N ℓ)).symm.toLinearMap

/-- `ℓ` factors through the quotient. -/
lemma ℓbar_π (v : algA N) : ℓbar N ℓ (πA N ℓ v) = ℓ v := by
  have h : (Submodule.Quotient.restrictScalarsEquiv 𝔸 (annIdeal N ℓ)).symm (πA N ℓ v) =
      Submodule.Quotient.mk v :=
    (Submodule.Quotient.restrictScalarsEquiv 𝔸 (annIdeal N ℓ)).symm_apply_eq.mpr
      (Submodule.Quotient.restrictScalarsEquiv_mk 𝔸 (annIdeal N ℓ) v).symm
  simp only [ℓbar, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h]
  rfl

variable {N ℓ}

/-- The quotient is finite-dimensional when `ℓ(p(T) A) = 0` for some nonzero `p`. -/
lemma finiteDimensional_quotA [FiniteDimensional 𝔸⟮T⟯ N] (hT1 : ‖T‖ = 1)
    (hT : Transcendental 𝔸 T) {p : 𝔸[X]} (hp : p ≠ 0)
    (hann : ∀ w ∈ spanA N, ℓ (aeval T p * w) = 0) : FiniteDimensional 𝔸 (quotA N ℓ) := by
  classical
  obtain ⟨F, hF, hFp⟩ := good_of_ne_zero hT1 hT (N := N) hp
  let F' : Finset (algA N) := F.attach.image fun x : F => (⟨x.1, mem_algA.mpr (hF x.2)⟩ : algA N)
  refine ⟨⟨F'.image (πA N ℓ), eq_top_iff.mpr fun x _ => ?_⟩⟩
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mkₐ_surjective 𝔸 (annIdeal N ℓ) x
  obtain ⟨w, hw, hvw⟩ := hFp v (mem_algA.mp v.property)
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hvw
  let pw : algA N := ⟨aeval T p * w, mem_algA.mpr (mul_mem_spanA (aeval_mem_spanA hT1 p) hw)⟩
  have hpw : pw ∈ annIdeal N ℓ := fun w' => by
    change ℓ (aeval T p * w * w') = 0
    rw [mul_assoc]
    exact hann _ (mul_mem_spanA hw (mem_algA.mp w'.property))
  have hv : v = pw + ∑ x ∈ F.attach, c x • (⟨x.1, mem_algA.mpr (hF x.2)⟩ : algA N) := by
    apply Subtype.ext
    simp only [pw, Subalgebra.coe_add, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    rw [Finset.sum_attach F (fun x => c x • x), hc]
    ring
  have hπ0 : πA N ℓ pw = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpw
  rw [hv, map_add, hπ0, zero_add, map_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr
    (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_attach _ x)))))

variable (N ℓ)

/-- `i` in `A`. -/
def iAlg : algA N := ⟨Complex.I, mem_algA.mpr (coe_mem_spanA iA)⟩

/-- The Cayley denominator `1 - i z` of a real `z ∈ A` is a unit of `A`. -/
lemma isUnit_one_sub (z : algA N) (hz : (z : ℂ).im = 0) : IsUnit (1 - iAlg N * z) := by
  refine isUnit_iff_exists_inv.mpr
    ⟨⟨(1 - Complex.I * z)⁻¹, mem_algA.mpr (cayley_mem (mem_algA.mp z.property) hz).2⟩, ?_⟩
  apply Subtype.ext
  change (1 - Complex.I * z) * (1 - Complex.I * z)⁻¹ = 1
  exact mul_inv_cancel₀ (one_sub_I_mul_ne hz)

/-- The real structure on the quotient: images of real elements and of `i`. -/
def quotReal : RealStructure 𝔸 (quotA N ℓ) where
  ι := πA N ℓ (iAlg N)
  Re := {x | ∃ z : algA N, (z : ℂ).im = 0 ∧ πA N ℓ z = x}
  ι_sq := by
    have h : iAlg N * iAlg N = -1 := Subtype.ext Complex.I_mul_I
    rw [← map_mul, h, map_neg, map_one]
  one_mem := ⟨1, by simp, map_one _⟩
  add_mem r := fun ⟨z, hz, hzr⟩ r' ⟨z', hz', hzr'⟩ =>
    ⟨z + z', by simp [hz, hz'], by rw [← hzr, ← hzr']; exact (πA N ℓ).toRingHom.map_add z z'⟩
  smul_mem t r := fun ⟨z, hz, hzr⟩ => ⟨algebraMap 𝔸 (algA N) t * z, by
      change ((t : ℂ) * (z : ℂ)).im = 0
      rw [Complex.mul_im, hz]
      simp, by rw [map_mul, AlgHom.commutes, hzr]⟩
  isUnit r := fun ⟨z, hz, hzr⟩ => by
    rw [← hzr, ← map_mul, ← map_one (πA N ℓ), ← map_sub]
    exact (isUnit_one_sub N z hz).map _

/-- A functional on the quotient killing every real element `r` and every `i r` is
zero. -/
lemma quotReal_span (ℓ' : quotA N ℓ →ₗ[𝔸] 𝔸)
    (h : ∀ r ∈ (quotReal N ℓ).Re, ℓ' r = 0 ∧ ℓ' ((quotReal N ℓ).ι * r) = 0) : ℓ' = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mkₐ_surjective 𝔸 (annIdeal N ℓ) x
  obtain ⟨r₁, r₂, h₁, h₂, hr₁, hr₂, hv⟩ := spanA_re_im (mem_algA.mp v.property)
  have hv' : v = ⟨r₁, mem_algA.mpr h₁⟩ + iAlg N * ⟨r₂, mem_algA.mpr h₂⟩ := Subtype.ext hv
  rw [LinearMap.zero_apply, hv', map_add, map_mul, map_add,
    (h _ ⟨⟨r₁, mem_algA.mpr h₁⟩, hr₁, rfl⟩).1, zero_add]
  exact (h _ ⟨⟨r₂, mem_algA.mpr h₂⟩, hr₂, rfl⟩).2

variable {N ℓ}

-- instance synthesis on the quotient algebra `A / I` needs more than the default budget
set_option synthInstance.maxHeartbeats 200000 in
/-- In the finite-dimensional quotient some Cayley transform escapes every
functional `x ↦ ℓ(q x)`. -/
lemma escape_of_finiteDimensional [FiniteDimensional 𝔸 (quotA N ℓ)] (hℓ : ℓ 1 = 1)
    (Q : Finset ℂ) (hQ : ∀ q ∈ Q, q ∈ units N) : ∃ u ∈ units N, ∀ q ∈ Q, ℓ (q * u) ≠ 0 := by
  classical
  have : Algebra.IsIntegral 𝔸 (quotA N ℓ) := Algebra.IsIntegral.of_finite _ _
  let S := quotReal N ℓ
  let qA : Q → algA N := fun q => ⟨q, mem_algA.mpr (mem_spanA_of_mem_units (hQ q q.2))⟩
  let μ : Q → quotA N ℓ →ₗ[𝔸] 𝔸 := fun q => ℓbar N ℓ ∘ₗ LinearMap.mulLeft 𝔸 (πA N ℓ (qA q))
  have hμ (q : Q) (v : algA N) : μ q (πA N ℓ v) = ℓ (q * v) := by
    simp only [μ, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, ← map_mul,
      ℓbar_π]
    rfl
  have hμ0 (q : Q) : μ q ≠ 0 := by
    intro h0
    have hq := hQ q q.2
    have h := LinearMap.congr_fun h0
      (πA N ℓ ⟨conj (q : ℂ), mem_algA.mpr (mem_spanA_of_mem_units (conj_mem_units hq))⟩)
    rw [hμ, LinearMap.zero_apply] at h
    have hqq : (q : ℂ) * conj (q : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hq.2]
      simp
    rw [show (q : ℂ) * ((⟨conj (q : ℂ), _⟩ : algA N) : ℂ) = 1 from hqq, hℓ] at h
    exact one_ne_zero h
  obtain ⟨r, hr⟩ := S.cay_finite_avoid (quotReal_span N ℓ) (Finset.univ.image μ) (by
    intro ψ hψ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hψ
    exact hμ0 q)
  obtain ⟨z, hz, hzr⟩ := r.property
  obtain ⟨hu, -⟩ := cayley_mem (mem_algA.mp z.property) hz
  let uA : algA N :=
    ⟨(1 + Complex.I * z) / (1 - Complex.I * z), mem_algA.mpr (mem_spanA_of_mem_units hu)⟩
  have hcay : S.cay r = πA N ℓ uA := by
    symm
    apply S.cay_unique
    change (1 - πA N ℓ (iAlg N) * (r : quotA N ℓ)) * πA N ℓ uA =
      1 + πA N ℓ (iAlg N) * (r : quotA N ℓ)
    rw [← hzr, ← map_mul, ← map_one (πA N ℓ), ← map_sub, ← map_mul, ← map_add]
    congr 1
    apply Subtype.ext
    change (1 - Complex.I * z) * ((1 + Complex.I * z) / (1 - Complex.I * z)) = 1 + Complex.I * z
    field_simp [one_sub_I_mul_ne hz]
  refine ⟨_, hu, fun q hq hqu => hr (μ ⟨q, hq⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_⟩
  rw [hcay, hμ]
  exact hqu

/-- A cover gives a nonzero polynomial `p` with `ℓ(p(T) A) = 0`. -/
lemma annihilator_of_cover [FiniteDimensional 𝔸⟮T⟯ N] (hT1 : ‖T‖ = 1) (hT : Transcendental 𝔸 T)
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1})
    (Q : Finset ℂ) (hQ : ∀ q ∈ Q, q ∈ units N)
    (hcov0 : ∀ u ∈ units N, ∃ q ∈ Q, ℓ (q * u) = 0) :
    ∃ p : 𝔸[X], p ≠ 0 ∧ ∀ w ∈ spanA N, ℓ (aeval T p * w) = 0 := by
  obtain ⟨𝔣, hfT, hfQ, hfU, hd, hb⟩ := exists_frame N hT1 hT hspan Q hQ
  have hcov : 𝔣.Covered ℓ := by
    intro u hu
    rw [hfU] at hu
    rw [hfQ]
    exact hcov0 u hu
  have hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U := by
    rw [hfU]
    exact fun u hu v hv => mul_mem_units hu hv
  have hTU : 𝔣.T ∈ 𝔣.U := by
    rw [hfU, hfT]
    exact ⟨T_mem N, hT1⟩
  obtain ⟨p, hp, hann⟩ := CauchyFrame.exists_annihilator hmul hcov hTU
  have hA : 𝔣.A = spanA N := by rw [CauchyFrame.A, hfU]; rfl
  refine ⟨p, hp, fun w hw => ?_⟩
  let l : Fin 𝔣.d := ⟨0, hd⟩
  have hb0 : 𝔣.b l ≠ 0 := by
    intro h0
    have := (hb l).2
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h := hann (w * (𝔣.b l)⁻¹) (by
    rw [hA]
    exact mul_mem_spanA hw (mem_spanA_of_mem_units (inv_mem_units (hb l)))) l
  rwa [hfT, mul_assoc, inv_mul_cancel_right₀ hb0] at h

/-- There is no finite cover of the units of `N` by translated kernels of an
`𝔸`-linear functional `ℓ` with `ℓ 1 = 1`. -/
theorem cover_impossible [FiniteDimensional 𝔸⟮T⟯ N] (hT1 : ‖T‖ = 1) (hT : Transcendental 𝔸 T)
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1})
    (Q : Finset ℂ) (hQ : ∀ q ∈ Q, q ∈ units N) (hℓ : ℓ 1 = 1) :
    ∃ u ∈ units N, ∀ q ∈ Q, ℓ (q * u) ≠ 0 := by
  by_contra! hcov0
  obtain ⟨p, hp, hann⟩ := annihilator_of_cover hT1 hT hspan Q hQ hcov0
  have := finiteDimensional_quotA hT1 hT hp hann
  obtain ⟨u, hu, hq⟩ := escape_of_finiteDimensional hℓ Q hQ
  obtain ⟨q, hqQ, hqu⟩ := hcov0 u hu
  exact hq q hqQ hqu

end Erdos173.Template

end
