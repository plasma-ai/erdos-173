module

public import Erdos173.Template.Branches
public import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# A polynomial in `T` annihilating a covered functional

Let `ℓ` be covered on a set `U` of units closed under multiplication and containing
`T`, and let `A` be the `𝔸`-span of `U`. For `v ∈ U` the twisted functional
`z ↦ ℓ(v z)` is again covered, so its Cauchy transform is generically
`P_v(a)/Δ(a)` with `deg P_v ≤ degBound`. Uniqueness of generic agreement makes
`v ↦ P_v` a linear map `Φ` from `A` to a finite-dimensional space. The exact
identity `F_{Tv}(a) = a F_v(a) + (ℓ(v b_l))_l` gives
`P_{Tv} = X P_v + Δ (ℓ(v b_l))_l`. If `P_v = 0` but some `ℓ(v b_l) ≠ 0`, then
`P_{T^m v}` would have degree at least `m - 1` for every `m`; so the kernel of `Φ`
lies in the kernel of `v ↦ (ℓ(v b_l))_l` and is stable under multiplication by `T`.
The characteristic polynomial `p` of the induced operator on the finite-dimensional
quotient then satisfies `ℓ(p(T) v b_l) = 0` for all `v ∈ A`.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Template

open Polynomial

namespace CauchyFrame

variable (𝔣 : CauchyFrame) (ℓ : ℂ →ₗ[𝔸] 𝔸)

/-- The twisted functional `z ↦ ℓ(v z)`. -/
def twist (v : ℂ) : ℂ →ₗ[𝔸] 𝔸 := ℓ.comp (LinearMap.mulLeft 𝔸 v)

/-- `twist ℓ v` is `z ↦ ℓ(v z)`. -/
@[simp] lemma twist_apply (v z : ℂ) : twist ℓ v z = ℓ (v * z) := rfl

/-- Twisting by a member of `U` keeps a functional covered. -/
lemma covered_twist (hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U) (hcov : 𝔣.Covered ℓ)
    {v : ℂ} (hv : v ∈ 𝔣.U) : 𝔣.Covered (twist ℓ v) := by
  intro u hu
  obtain ⟨q, hq, h⟩ := hcov _ (hmul v hv u hu)
  refine ⟨q, hq, ?_⟩
  rw [twist_apply, ← h]
  ring_nf

/-- A generic numerator vector is unique. -/
lemma Tame.unique {μ : ℂ →ₗ[𝔸] 𝔸} {P P' : Fin 𝔣.d → 𝔸[X]} (h : 𝔣.Tame μ P)
    (h' : 𝔣.Tame μ P') : P = P' := by
  funext l
  rw [← sub_eq_zero]
  refine Gen.poly_eq_zero ((h.and h').mono fun z _ hz => ?_)
  rw [eval_sub, ← hz.1 l, ← hz.2 l, sub_self]

/-- Generic numerator vectors are linear in the twist. -/
lemma Tame.linear {v w : ℂ} {P P' : Fin 𝔣.d → 𝔸[X]} (c : 𝔸) (h : 𝔣.Tame (twist ℓ v) P)
    (h' : 𝔣.Tame (twist ℓ w) P') : 𝔣.Tame (twist ℓ (c • v + w)) (c • P + P') := by
  refine (h.and h').mono fun z _ hz l => ?_
  simp only [cauchy, twist_apply, Pi.add_apply, Pi.smul_apply, eval_add, eval_smul,
    smul_eq_mul] at hz ⊢
  rw [add_mul, smul_mul_assoc, map_add, map_smul, smul_eq_mul, mul_add, ← hz.1 l, ← hz.2 l]
  ring

/-- The twist by `0` has numerator vector `0`. -/
lemma Tame.zero : 𝔣.Tame (twist ℓ 0) 0 := by
  refine ⟨1, const_mem_polyFuns 1, fun h => one_ne_zero (congrFun h 0), fun z _ _ l => ?_⟩
  simp [cauchy]

/-- Multiplying the twist by `T` gives the numerator vector `X P_v + Δ (ℓ(v b_l))_l`. -/
lemma Tame.shift {v : ℂ} {P : Fin 𝔣.d → 𝔸[X]} (h : 𝔣.Tame (twist ℓ v) P) :
    𝔣.Tame (twist ℓ (𝔣.T * v)) (fun l => X * P l + C (ℓ (v * 𝔣.b l)) * 𝔣.Δ) := by
  refine h.mono fun z hz hP l => ?_
  have hTa := (Ω_unit hz 𝔣.norm_T).1
  have he : 𝔣.T * v * (𝔣.b l / (𝔣.T - z 0)) = v * 𝔣.b l + z 0 • (v * (𝔣.b l / (𝔣.T - z 0))) := by
    rw [smul_eq]
    field_simp
    ring
  simp only [cauchy, twist_apply] at hP ⊢
  rw [he, map_add, map_smul, smul_eq_mul, eval_add, eval_mul, eval_X, eval_mul, eval_C, ← hP l]
  ring

/-- The `𝔸`-span of the units. -/
def A : Submodule 𝔸 ℂ := Submodule.span 𝔸 𝔣.U

variable {𝔣 ℓ}

/-- Every twist by an element of `A` has a numerator vector of degree at most
`degBound`. -/
lemma exists_tame (hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U) (hcov : 𝔣.Covered ℓ)
    {v : ℂ} (hv : v ∈ 𝔣.A) :
    ∃ P : Fin 𝔣.d → 𝔸[X], (∀ l, (P l).natDegree ≤ 𝔣.degBound) ∧ 𝔣.Tame (twist ℓ v) P := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact 𝔣.tame_of_covered (𝔣.covered_twist ℓ hmul hcov hv)
  | zero => exact ⟨0, fun l => by simp, Tame.zero 𝔣 ℓ⟩
  | add v w _ _ hv hw =>
    obtain ⟨P, hPd, hP⟩ := hv
    obtain ⟨P', hPd', hP'⟩ := hw
    refine ⟨1 • P + P', fun l => ?_, by simpa using Tame.linear 𝔣 ℓ 1 hP hP'⟩
    simp only [one_smul, Pi.add_apply]
    exact (natDegree_add_le _ _).trans (max_le (hPd l) (hPd' l))
  | smul c v _ hv =>
    obtain ⟨P, hPd, hP⟩ := hv
    refine ⟨c • P + 0, fun l => ?_, by simpa using Tame.linear 𝔣 ℓ c hP (Tame.zero 𝔣 ℓ)⟩
    simp only [add_zero, Pi.smul_apply]
    exact (natDegree_smul_le _ _).trans (hPd l)

variable (hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U) (hcov : 𝔣.Covered ℓ)
include hmul hcov

/-- The numerator vector of the twisted Cauchy transform. -/
def tameVec (v : 𝔣.A) : Fin 𝔣.d → 𝔸[X] := Classical.choose (exists_tame hmul hcov v.property)

/-- The chosen numerator vector has degree at most `degBound` and is generic. -/
lemma tameVec_spec (v : 𝔣.A) :
    (∀ l, (tameVec hmul hcov v l).natDegree ≤ 𝔣.degBound) ∧
      𝔣.Tame (twist ℓ v) (tameVec hmul hcov v) :=
  Classical.choose_spec (exists_tame hmul hcov v.property)

/-- The chosen numerator vector is the generic one. -/
lemma tameVec_eq {v : 𝔣.A} {P : Fin 𝔣.d → 𝔸[X]} (h : 𝔣.Tame (twist ℓ v) P) :
    tameVec hmul hcov v = P :=
  Tame.unique 𝔣 (tameVec_spec hmul hcov v).2 h

/-- The coefficients of the numerator vector, a linear map to a finite-dimensional
space. -/
def Φ : 𝔣.A →ₗ[𝔸] (Fin 𝔣.d → Fin (𝔣.degBound + 1) → 𝔸) where
  toFun v l m := (tameVec hmul hcov v l).coeff m
  map_add' v w := by
    have hl := Tame.linear 𝔣 ℓ 1 (tameVec_spec hmul hcov v).2 (tameVec_spec hmul hcov w).2
    rw [one_smul, one_smul] at hl
    have h' := tameVec_eq hmul hcov (v := v + w) hl
    funext l m
    change (tameVec hmul hcov (v + w) l).coeff m =
      (tameVec hmul hcov v l).coeff m + (tameVec hmul hcov w l).coeff m
    rw [h', Pi.add_apply, coeff_add]
  map_smul' c v := by
    have hl := Tame.linear 𝔣 ℓ c (tameVec_spec hmul hcov v).2 (Tame.zero 𝔣 ℓ)
    rw [add_zero, add_zero] at hl
    have h' := tameVec_eq hmul hcov (v := c • v) hl
    funext l m
    change (tameVec hmul hcov (c • v) l).coeff m = c • (tameVec hmul hcov v l).coeff m
    rw [h', Pi.smul_apply, coeff_smul]

/-- `Φ v` lists the coefficients of the numerator vector of `v`. -/
lemma Φ_apply (v : 𝔣.A) (l : Fin 𝔣.d) (m : Fin (𝔣.degBound + 1)) :
    Φ hmul hcov v l m = (tameVec hmul hcov v l).coeff m := rfl

/-- On the kernel of `Φ` the numerator vector vanishes. -/
lemma tameVec_eq_zero {v : 𝔣.A} (hv : v ∈ LinearMap.ker (Φ hmul hcov)) :
    tameVec hmul hcov v = 0 := by
  funext l
  refine Polynomial.ext fun m => ?_
  rw [Pi.zero_apply, coeff_zero]
  by_cases hm : m ≤ 𝔣.degBound
  · have h := congrFun (congrFun (LinearMap.mem_ker.mp hv) l) ⟨m, Nat.lt_succ_of_le hm⟩
    rwa [Φ_apply] at h
  · exact coeff_eq_zero_of_natDegree_lt ((tameVec_spec hmul hcov v).1 l |>.trans_lt
      (not_le.mp hm))

variable (hTU : 𝔣.T ∈ 𝔣.U)
include hTU

omit hmul hcov hTU in
/-- `A` is stable under multiplication by `T`. -/
lemma T_mul_mem (hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U) (hTU : 𝔣.T ∈ 𝔣.U) {v : ℂ}
    (hv : v ∈ 𝔣.A) : 𝔣.T * v ∈ 𝔣.A := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span (hmul _ hTU _ hv)
  | zero => simp
  | add v w _ _ hv hw => rw [mul_add]; exact Submodule.add_mem _ hv hw
  | smul c v _ hv => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hv

/-- Multiplication by `T` on `A`. -/
def τ : 𝔣.A →ₗ[𝔸] 𝔣.A := (LinearMap.mulLeft 𝔸 𝔣.T).restrict fun _ hv => T_mul_mem hmul hTU hv

omit hcov in
/-- `τ` is multiplication by `T`. -/
@[simp] lemma coe_τ (v : 𝔣.A) : ((τ hmul hTU v : 𝔣.A) : ℂ) = 𝔣.T * v := rfl

/-- The numerator vector of `T v` is `X P_v + Δ (ℓ(v b_l))_l`. -/
lemma tameVec_τ (v : 𝔣.A) : tameVec hmul hcov (τ hmul hTU v) =
    fun l => X * tameVec hmul hcov v l + C (ℓ (v * 𝔣.b l)) * 𝔣.Δ :=
  tameVec_eq hmul hcov (Tame.shift 𝔣 ℓ (tameVec_spec hmul hcov v).2)

/-- The kernel of `Φ` lies in the kernel of `v ↦ (ℓ(v b_l))_l`. -/
lemma Λ_eq_zero {v : 𝔣.A} (hv : v ∈ LinearMap.ker (Φ hmul hcov)) (l : Fin 𝔣.d) :
    ℓ (v * 𝔣.b l) = 0 := by
  by_contra hne
  have hv0 := tameVec_eq_zero hmul hcov hv
  have key : ∀ m : ℕ, ∃ Q : 𝔸[X], Q ≠ 0 ∧ Q.natDegree = m ∧
      tameVec hmul hcov (((τ hmul hTU) ^ (m + 1)) v) l = 𝔣.Δ * Q := by
    intro m
    induction m with
    | zero =>
      refine ⟨C (ℓ (v * 𝔣.b l)), C_ne_zero.mpr hne, natDegree_C _, ?_⟩
      rw [zero_add, pow_one, tameVec_τ, hv0]
      simp only [Pi.zero_apply, mul_zero, zero_add]
      ring
    | succ m ih =>
      obtain ⟨Q, hQ, hQd, hQe⟩ := ih
      set c := ℓ ((((τ hmul hTU) ^ (m + 1)) v : 𝔣.A) * 𝔣.b l)
      refine ⟨X * Q + C c, ?_, ?_, ?_⟩
      · intro h
        have := congrArg natDegree h
        rw [natDegree_add_C, natDegree_X_mul hQ, natDegree_zero] at this
        omega
      · rw [natDegree_add_C, natDegree_X_mul hQ, hQd]
      · rw [pow_succ', Module.End.mul_apply, tameVec_τ]
        dsimp only
        rw [hQe]
        ring
  obtain ⟨Q, hQ, hQd, hQe⟩ := key (𝔣.degBound + 1)
  have hb := (tameVec_spec hmul hcov (((τ hmul hTU) ^ (𝔣.degBound + 2)) v)).1 l
  rw [hQe, natDegree_mul 𝔣.Δ_ne hQ, hQd] at hb
  omega

/-- The kernel of `Φ` is stable under `τ`. -/
lemma ker_Φ_stable :
    LinearMap.ker (Φ hmul hcov) ≤ (LinearMap.ker (Φ hmul hcov)).comap (τ hmul hTU) := by
  intro v hv
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  have h : tameVec hmul hcov (τ hmul hTU v) = 0 := by
    rw [tameVec_τ, tameVec_eq_zero hmul hcov hv]
    funext l
    simp [Λ_eq_zero hmul hcov hTU hv l]
  funext l m
  rw [Φ_apply, h]
  rfl

omit hcov in
/-- `τⁿ` is multiplication by `Tⁿ`. -/
lemma pow_τ (n : ℕ) (v : 𝔣.A) : ((((τ hmul hTU) ^ n) v : 𝔣.A) : ℂ) = 𝔣.T ^ n * v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, coe_τ, ih]
    ring

omit hcov in
/-- `p(τ)` is multiplication by `p(T)`. -/
lemma aeval_τ (p : 𝔸[X]) (v : 𝔣.A) : ((aeval (τ hmul hTU) p v : 𝔣.A) : ℂ) = aeval 𝔣.T p * v := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply,
    Submodule.coe_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Submodule.coe_smul, pow_τ, smul_eq, smul_eq]
  ring

/-- A nonzero polynomial in `T` annihilates the covered functional on `A`, in the
sense that `ℓ(p(T) v b_l) = 0` for every `v ∈ A` and every `l`. -/
theorem exists_annihilator :
    ∃ p : 𝔸[X], p ≠ 0 ∧ ∀ v ∈ 𝔣.A, ∀ l, ℓ (aeval 𝔣.T p * v * 𝔣.b l) = 0 := by
  classical
  set K := LinearMap.ker (Φ hmul hcov)
  have hstab := ker_Φ_stable hmul hcov hTU
  let τq := K.mapQ K (τ hmul hTU) hstab
  have : FiniteDimensional 𝔸 (𝔣.A ⧸ K) :=
    LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange (Φ hmul hcov)).symm
  have hpow (n : ℕ) (v : 𝔣.A) : (τq ^ n) (K.mkQ v) = K.mkQ (((τ hmul hTU) ^ n) v) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      rfl
  have hcomm (p : 𝔸[X]) (v : 𝔣.A) :
      aeval τq p (K.mkQ v) = K.mkQ (aeval (τ hmul hTU) p v) := by
    rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply,
      LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hpow, map_smul]
  refine ⟨τq.charpoly, τq.charpoly_monic.ne_zero, fun v hv l => ?_⟩
  have hmem : aeval (τ hmul hTU) τq.charpoly ⟨v, hv⟩ ∈ K := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← hcomm,
      LinearMap.aeval_self_charpoly]
    rfl
  have h := Λ_eq_zero hmul hcov hTU hmem l
  rwa [aeval_τ] at h

end CauchyFrame

end Erdos173.Template

end
