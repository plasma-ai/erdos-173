module

-- Adapts code from openai/math at adc7f124; see OAI/README.md.

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Cayley transforms escape finitely many hyperplanes

Let `R` be a commutative algebra, integral over a field `K` of characteristic zero,
with an element `ι` of square `-1` and a set `Re` of "real" elements, closed under
sums and rational multiples and containing `1`, such that each `1 - ι r` is a unit.
The Cayley transform of a real `r` is `(1 + ι r)(1 - ι r)⁻¹`. If a `K`-linear
functional killing every `r` and every `ι r` is zero, then for finitely many nonzero
functionals some Cayley transform is killed by none of them.

This is the argument of the source's algebraic Cayley lemmas over `ℚ`, run over an
arbitrary base field `K` with rational parameters: integrality makes the reciprocal
`(1 - b t)⁻¹` a rational function of `t` with no rational pole, the first three
formal coefficients of a Cayley curve annihilate `1`, `b` and `b²`, and rational
lines join escapes from single hyperplanes to an escape from their union.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Template

open Polynomial

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- A scalar common denominator for the reciprocal of `1 - b t` with `b` integral. -/
lemma reciprocal_denominator (b : R) (hb : IsIntegral K b) :
    ∃ (P : K[X]) (Rp : R[X]), P.coeff 0 = 1 ∧
      (1 - C b * X) * Rp = P.map (algebraMap K R) ∧
      ∀ t : K, IsUnit (1 - b * algebraMap K R t) → P.eval t ≠ 0 := by
  set m := minpoly K b with hm_def
  have hm : m.Monic := minpoly.monic hb
  set n := m.natDegree
  let P : K[X] := ∑ k ∈ Finset.range (n + 1), C (m.coeff k) * X ^ (n - k)
  let Rp : R[X] := ∑ k ∈ Finset.range (n + 1),
    C (algebraMap K R (m.coeff k)) * X ^ (n - k) * ∑ i ∈ Finset.range k, (C b * X) ^ i
  have hP0 : P.coeff 0 = 1 := by
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single n]
    · rw [ite_eq_left (by omega)]
      exact hm.coeff_natDegree
    · intro k hk hkn
      have : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [ite_eq_right (by omega)]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  refine ⟨P, Rp, hP0, ?_, ?_⟩
  · have hz : ∑ k ∈ Finset.range (n + 1), algebraMap K R (m.coeff k) * b ^ k = 0 := by
      have h := minpoly.aeval K b
      rw [← hm_def, aeval_eq_sum_range] at h
      simpa only [Algebra.smul_def] using h
    calc (1 - C b * X) * Rp
        = ∑ k ∈ Finset.range (n + 1), (C (algebraMap K R (m.coeff k)) * X ^ (n - k) -
            C (algebraMap K R (m.coeff k) * b ^ k) * X ^ n) := by
          simp only [Rp]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have he : (1 - C b * X) * (C (algebraMap K R (m.coeff k)) * X ^ (n - k) *
              ∑ i ∈ Finset.range k, (C b * X) ^ i) =
              C (algebraMap K R (m.coeff k)) * X ^ (n - k) *
                ((1 - C b * X) * ∑ i ∈ Finset.range k, (C b * X) ^ i) := by ring
          rw [he, mul_neg_geom_sum, map_mul, map_pow]
          have hX : (X : R[X]) ^ n = X ^ (n - k) * X ^ k := by
            rw [← pow_add, Nat.sub_add_cancel hk]
          rw [hX]
          ring
      _ = P.map (algebraMap K R) - C (∑ k ∈ Finset.range (n + 1),
            algebraMap K R (m.coeff k) * b ^ k) * X ^ n := by
          rw [Finset.sum_sub_distrib, map_sum, Finset.sum_mul]
          simp [P, Polynomial.map_sum]
      _ = P.map (algebraMap K R) := by rw [hz, map_zero, zero_mul, sub_zero]
  · intro t ht hP
    by_cases ht0 : t = 0
    · subst t
      rw [← coeff_zero_eq_eval_zero, hP0] at hP
      exact one_ne_zero hP
    have hroot : m.IsRoot t⁻¹ := by
      have he : P.eval t = t ^ n * m.eval t⁻¹ := by
        simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
        rw [eval_eq_sum_range, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [inv_pow, pow_sub₀ _ ht0 hk]
        ring
      rw [he] at hP
      exact (mul_eq_zero.mp hP).resolve_left (pow_ne_zero _ ht0)
    have hdiv := mul_divByMonic_eq_iff_isRoot.mpr hroot
    set g := m /ₘ (X - C t⁻¹)
    have hg : aeval b g = 0 := by
      have h := minpoly.aeval K b
      rw [← hm_def, ← hdiv, map_mul] at h
      have hu : IsUnit (aeval b (X - C t⁻¹)) := by
        have hti : algebraMap K R t⁻¹ * algebraMap K R t = 1 := by
          rw [← map_mul, inv_mul_cancel₀ ht0, map_one]
        have he : aeval b (X - C t⁻¹) = algebraMap K R (-t⁻¹) * (1 - b * algebraMap K R t) := by
          simp only [map_sub, aeval_X, aeval_C, map_neg]
          linear_combination (-b) * hti
        rw [he]
        exact ((isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (inv_ne_zero ht0))).map
          (algebraMap K R)).mul ht
      exact (hu.mul_right_eq_zero).mp h
    have hm0 : m ≠ 0 := hm.ne_zero
    have hg0 : g ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdiv
      exact hm0 hdiv.symm
    have hle := minpoly.degree_le_of_ne_zero K b hg0 hg
    have hlt := degree_divByMonic_lt m (X - C t⁻¹) hm0 (by rw [degree_X_sub_C]; exact one_pos)
    exact absurd (hle.trans_lt hlt) (lt_irrefl _)

/-- Coefficientwise transport by a linear functional. -/
def polyLinear (ℓ : R →ₗ[K] K) (p : R[X]) : K[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange ℓ (map_zero ℓ)))

/-- `polyLinear ℓ` applies `ℓ` to each coefficient. -/
@[simp] lemma coeff_polyLinear (ℓ : R →ₗ[K] K) (p : R[X]) (n : ℕ) :
    (polyLinear ℓ p).coeff n = ℓ (p.coeff n) := rfl

/-- `polyLinear ℓ` is additive. -/
lemma polyLinear_add (ℓ : R →ₗ[K] K) (p q : R[X]) :
    polyLinear ℓ (p + q) = polyLinear ℓ p + polyLinear ℓ q := by
  ext n
  simp only [coeff_polyLinear, coeff_add, map_add]

/-- `polyLinear ℓ` maps monomials to monomials. -/
lemma polyLinear_monomial (ℓ : R →ₗ[K] K) (n : ℕ) (a : R) :
    polyLinear ℓ (monomial n a) = monomial n (ℓ a) := by
  ext k
  simp only [coeff_polyLinear, coeff_monomial]
  split_ifs <;> simp

/-- Evaluating the transported polynomial is applying `ℓ` to the evaluation. -/
lemma eval_polyLinear (ℓ : R →ₗ[K] K) (p : R[X]) (t : K) :
    (polyLinear ℓ p).eval t = ℓ (p.eval (algebraMap K R t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [polyLinear_add, eval_add, hp, hq, map_add]
  | monomial n a =>
    rw [polyLinear_monomial, eval_monomial, eval_monomial]
    have he : a * (algebraMap K R t) ^ n = (t ^ n) • a := by
      rw [Algebra.smul_def, map_pow, mul_comm]
    rw [he, map_smul]
    exact mul_comm _ _

variable [CharZero K]

/-- A polynomial over `K` vanishing at every rational point is zero. -/
lemma eq_zero_of_forall_rat {p : K[X]} (hp : ∀ t : ℚ, p.eval (t : K) = 0) : p = 0 :=
  p.eq_zero_of_infinite_isRoot ((Set.infinite_range_of_injective
    (Rat.cast_injective (α := K))).mono fun x hx => by
      obtain ⟨t, rfl⟩ := hx
      exact hp t)

/-- The first three formal coefficients of a Cayley curve annihilate `1`, `b` and `b²`. -/
lemma cayley_annihilation (b : R) (hb : IsIntegral K b) (ℓ : R →ₗ[K] K)
    (hd : ∀ t : ℚ, IsUnit (1 - b * algebraMap K R t))
    (h : ∀ t : ℚ, ∀ u, (1 - b * algebraMap K R t) * u = 1 + b * algebraMap K R t → ℓ u = 0) :
    ℓ 1 = 0 ∧ ℓ b = 0 ∧ ℓ (b ^ 2) = 0 := by
  obtain ⟨P, Rp, hP, hR, hPreg⟩ := reciprocal_denominator (K := K) b hb
  have hR' : Rp - (C b * Rp) * X = P.map (algebraMap K R) := by
    rw [← hR]
    ring
  let T := Rp + (C b * Rp) * X
  have hT : polyLinear ℓ T = 0 := by
    apply eq_zero_of_forall_rat
    intro t
    rw [eval_polyLinear]
    have hRt := congrArg (Polynomial.eval (algebraMap K R t)) hR
    simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
    have hPt := hPreg t (hd t)
    have hu : (1 - b * algebraMap K R t) * ((P.eval (t : K))⁻¹ • T.eval (algebraMap K R t)) =
        1 + b * algebraMap K R t := by
      rw [mul_smul_comm]
      have he : (1 - b * algebraMap K R t) * T.eval (algebraMap K R t) =
          (1 + b * algebraMap K R t) * algebraMap K R (P.eval (t : K)) := by
        simp only [T, eval_add, eval_mul, eval_C, eval_X]
        rw [← hRt]
        ring
      rw [he, Algebra.smul_def, ← mul_assoc, mul_comm (algebraMap K R _), mul_assoc, ← map_mul,
        inv_mul_cancel₀ hPt, map_one, mul_one]
    have h0 := h t _ hu
    rw [map_smul, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (inv_ne_zero hPt)
  have h0 : Rp.coeff 0 = 1 := by
    have he := congrArg (fun p : R[X] => p.coeff 0) hR'
    simpa only [coeff_sub, coeff_mul_X_zero, sub_zero, coeff_map, hP, map_one] using he
  have h1 : Rp.coeff 1 - b = algebraMap K R (P.coeff 1) := by
    have he := congrArg (fun p : R[X] => p.coeff 1) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, h0, mul_one, coeff_map] using he
  have h2 : Rp.coeff 2 - b * Rp.coeff 1 = algebraMap K R (P.coeff 2) := by
    have he := congrArg (fun p : R[X] => p.coeff 2) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, coeff_map] using he
  have ht0 : ℓ 1 = 0 := by
    have he := congrArg (fun p : K[X] => p.coeff 0) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X_zero, add_zero, h0, coeff_zero] using he
  have ht1 : ℓ (Rp.coeff 1) + ℓ b = 0 := by
    have he := congrArg (fun p : K[X] => p.coeff 1) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul, h0, mul_one,
      map_add, coeff_zero] using he
  have ht2 : ℓ (Rp.coeff 2) + ℓ (b * Rp.coeff 1) = 0 := by
    have he := congrArg (fun p : K[X] => p.coeff 2) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul,
      map_add, coeff_zero] using he
  have hlK (c : K) : ℓ (algebraMap K R c) = 0 := by
    have he : algebraMap K R c = c • (1 : R) := by rw [Algebra.smul_def, mul_one]
    rw [he, map_smul, ht0, smul_zero]
  have hh1 := congrArg ℓ h1
  rw [map_sub, hlK] at hh1
  have hb0 : ℓ b = 0 := by
    have h2b : (2 : K) * ℓ b = 0 := by linear_combination ht1 - hh1
    exact (mul_eq_zero.mp h2b).resolve_left two_ne_zero
  have hh2 := congrArg ℓ h2
  rw [map_sub, hlK] at hh2
  have hbR : ℓ (b * Rp.coeff 1) = 0 := by
    have h2b : (2 : K) * ℓ (b * Rp.coeff 1) = 0 := by linear_combination ht2 - hh2
    exact (mul_eq_zero.mp h2b).resolve_left two_ne_zero
  have hR1 : Rp.coeff 1 = algebraMap K R (P.coeff 1) + b := sub_eq_iff_eq_add.mp h1
  rw [hR1, mul_add, map_add] at hbR
  have he : b * algebraMap K R (P.coeff 1) = (P.coeff 1) • b := by
    rw [Algebra.smul_def, mul_comm]
  rw [he, map_smul, hb0, smul_zero, zero_add, ← sq] at hbR
  exact ⟨ht0, hb0, hbR⟩

omit [CharZero K] in
/-- A linear-fractional curve with integral coefficients has rational functional values. -/
lemma linearFraction_polynomials [Algebra.IsIntegral K R] (A B C' D : R) (ℓ : R →ₗ[K] K)
    (hd : ∀ t : ℚ, IsUnit (C' + D * algebraMap K R t)) :
    ∃ P Q : K[X], ∀ t : ℚ, Q.eval (t : K) ≠ 0 ∧ ∀ u : R,
      (C' + D * algebraMap K R t) * u = A + B * algebraMap K R t →
        P.eval (t : K) = Q.eval (t : K) * ℓ u := by
  have hC : IsUnit C' := by simpa using hd 0
  obtain ⟨c, hc⟩ := hC
  let ci : R := ↑c⁻¹
  have hcc : C' * ci = 1 := by rw [← hc]; exact c.mul_inv
  let b := -(D * ci)
  have hfac (t : ℚ) : C' + D * algebraMap K R t = C' * (1 - b * algebraMap K R t) := by
    have : C' + D * algebraMap K R t = C' + (C' * ci) * D * algebraMap K R t := by
      rw [hcc, one_mul]
    rw [this]
    ring
  obtain ⟨Q, Rp, -, hR, hQreg⟩ := reciprocal_denominator (K := K) b
    (Algebra.IsIntegral.isIntegral b)
  have hdn (t : ℚ) : IsUnit (1 - b * algebraMap K R t) := by
    have h := hd t
    rw [hfac] at h
    exact isUnit_of_mul_isUnit_right h
  let U : R[X] := (Polynomial.C (ci * A) + Polynomial.C (ci * B) * X) * Rp
  refine ⟨polyLinear ℓ U, Q, fun t => ⟨hQreg t (hdn t), fun u hu => ?_⟩⟩
  rw [eval_polyLinear]
  have hRt := congrArg (Polynomial.eval (algebraMap K R t)) hR
  simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
  have he : U.eval (algebraMap K R t) = (Q.eval (t : K)) • u := by
    simp only [U, eval_mul, eval_add, eval_C, eval_X, Algebra.smul_def]
    rw [← hRt]
    have hu' : ci * (A + B * algebraMap K R t) = (1 - b * algebraMap K R t) * u := by
      rw [← hu, hfac, ← mul_assoc, ← mul_assoc, mul_comm ci C', hcc, one_mul]
    calc (ci * A + ci * B * algebraMap K R t) * Rp.eval (algebraMap K R t)
        = (ci * (A + B * algebraMap K R t)) * Rp.eval (algebraMap K R t) := by ring
      _ = _ := by rw [hu']; ring
  rw [he, map_smul, smul_eq_mul]

/-- Finite simultaneous avoidance for rational functions with no rational poles. -/
lemma rational_functions_avoid {α : Type*} (s : Finset α) (f : α → ℚ → K)
    (hpoly : ∀ i ∈ s, ∃ P Q : K[X], ∀ t : ℚ, Q.eval (t : K) ≠ 0 ∧
      P.eval (t : K) = Q.eval (t : K) * f i t)
    (hn : ∀ i ∈ s, ∃ t, f i t ≠ 0) :
    ∃ t, ∀ i ∈ s, f i t ≠ 0 := by
  classical
  choose P Q hQ using fun i : s => hpoly i i.property
  have hP (i : s) : P i ≠ 0 := by
    obtain ⟨t, ht⟩ := hn i i.property
    intro he
    have hh := (hQ i t).2
    rw [he, eval_zero] at hh
    exact mul_ne_zero (hQ i t).1 ht hh.symm
  have hz : (∏ i : s, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => hP _)
  obtain ⟨t, ht⟩ : ∃ t : ℚ, (∏ i : s, P i).eval (t : K) ≠ 0 := by
    by_contra! hn
    exact hz (eq_zero_of_forall_rat hn)
  refine ⟨t, fun i hi hh => ?_⟩
  have hpt : (P ⟨i, hi⟩).eval (t : K) ≠ 0 := by
    rw [eval_prod] at ht
    exact Finset.prod_ne_zero_iff.mp ht _ (Finset.mem_univ _)
  apply hpt
  rw [(hQ ⟨i, hi⟩ t).2, hh, mul_zero]

/-- A rational curve escaping each hyperplane also escapes their finite union. -/
lemma finite_hyperplanes_avoid {T : Type*} [Nonempty T]
    (f : T → R) (line : T → T → ℚ → T)
    (hzero : ∀ a b, line a b 0 = a) (hone : ∀ a b, line a b 1 = b)
    (hline : ∀ a b (ℓ : R →ₗ[K] K), ∃ P Q : K[X], ∀ t : ℚ,
      Q.eval (t : K) ≠ 0 ∧ P.eval (t : K) = Q.eval (t : K) * ℓ (f (line a b t)))
    (s : Finset (R →ₗ[K] K)) (hs : ∀ ℓ ∈ s, ∃ t, ℓ (f t) ≠ 0) :
    ∃ t, ∀ ℓ ∈ s, ℓ (f t) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary T, by simp⟩
  | @insert ℓ s hℓ ih =>
    obtain ⟨a, ha⟩ := ih (fun ψ hψ => hs ψ (Finset.mem_insert_of_mem hψ))
    obtain ⟨b, hb⟩ := hs ℓ (Finset.mem_insert_self _ _)
    obtain ⟨t, ht⟩ := rational_functions_avoid (insert ℓ s)
      (fun ψ t => ψ (f (line a b t))) (fun ψ _ => hline a b ψ) (by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · exact ⟨1, by simpa only [hone] using hb⟩
        · exact ⟨0, by simpa only [hzero] using ha ψ hψ⟩)
    exact ⟨line a b t, ht⟩

/-- The data of a real structure on `R`: an element `ι` of square `-1` and a set of
real elements, closed under sums and rational multiples and containing `1`, whose
Cayley denominators `1 - ι r` are units. -/
structure RealStructure (K R : Type*) [Field K] [CommRing R] [Algebra K R] where
  /-- The imaginary unit. -/
  ι : R
  /-- The real elements. -/
  Re : Set R
  /-- `ι` has square `-1`. -/
  ι_sq : ι * ι = -1
  /-- `1` is real. -/
  one_mem : (1 : R) ∈ Re
  /-- The real elements are closed under sums. -/
  add_mem : ∀ r ∈ Re, ∀ s ∈ Re, r + s ∈ Re
  /-- The real elements are closed under rational multiples. -/
  smul_mem : ∀ t : ℚ, ∀ r ∈ Re, algebraMap K R t * r ∈ Re
  /-- The Cayley denominator `1 - ι r` of a real element is a unit. -/
  isUnit : ∀ r ∈ Re, IsUnit (1 - ι * r)

namespace RealStructure

variable (S : RealStructure K R)

/-- The Cayley transform `(1 + ι r)(1 - ι r)⁻¹` of a real element. -/
def cay (r : S.Re) : R := (1 + S.ι * r) * ↑(S.isUnit r r.property).unit⁻¹

omit [CharZero K] in
/-- The defining equation of the Cayley transform. -/
lemma cay_spec (r : S.Re) : (1 - S.ι * r) * S.cay r = 1 + S.ι * r := by
  rw [cay, mul_left_comm, IsUnit.mul_val_inv, mul_one]

omit [CharZero K] in
/-- The Cayley transform is the unique solution of its defining equation. -/
lemma cay_unique (r : S.Re) {u : R} (hu : (1 - S.ι * r) * u = 1 + S.ι * r) : u = S.cay r := by
  have h := (S.isUnit r r.property)
  calc u = ↑h.unit⁻¹ * ((1 - S.ι * r) * u) := by
        rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
    _ = S.cay r := by rw [hu, cay, mul_comm]

/-- The real line through `a` and `b`. -/
def line (a b : S.Re) (t : ℚ) : S.Re :=
  ⟨(a : R) + algebraMap K R t * ((b : R) + algebraMap K R (-1 : ℚ) * a),
    S.add_mem _ a.property _
      (S.smul_mem t _ (S.add_mem _ b.property _ (S.smul_mem _ _ a.property)))⟩

omit [CharZero K] in
/-- The real line through `a` and `b` starts at `a`. -/
lemma line_zero (a b : S.Re) : S.line a b 0 = a := by
  ext
  simp [line]

omit [CharZero K] in
/-- The real line through `a` and `b` reaches `b` at `1`. -/
lemma line_one (a b : S.Re) : S.line a b 1 = b := by
  ext
  simp [line]

variable [Algebra.IsIntegral K R]

omit [CharZero K] in
/-- Functional values along the Cayley transform of a real line are rational functions
with no rational pole. -/
lemma cay_line_polynomials (a b : S.Re) (ℓ : R →ₗ[K] K) :
    ∃ P Q : K[X], ∀ t : ℚ, Q.eval (t : K) ≠ 0 ∧
      P.eval (t : K) = Q.eval (t : K) * ℓ (S.cay (S.line a b t)) := by
  set w : R := (b : R) + algebraMap K R (-1 : ℚ) * a
  have hl (t : ℚ) : (S.line a b t : R) = a + algebraMap K R t * w := rfl
  obtain ⟨P, Q, hPQ⟩ := linearFraction_polynomials (1 + S.ι * a) (S.ι * w) (1 - S.ι * a)
    (-(S.ι * w)) ℓ (fun t => by
      have h := S.isUnit _ (S.line a b t).property
      rw [hl] at h
      convert h using 1
      ring)
  refine ⟨P, Q, fun t => ⟨(hPQ t).1, (hPQ t).2 _ ?_⟩⟩
  have h := S.cay_spec (S.line a b t)
  rw [hl] at h
  rw [← sub_eq_zero] at h ⊢
  rw [← h]
  ring

/-- A nonzero functional killed by no Cayley transform would kill every real `r`
and every `ι r`. -/
lemma cay_functional_escape (hspan : ∀ ℓ : R →ₗ[K] K,
      (∀ r ∈ S.Re, ℓ r = 0 ∧ ℓ (S.ι * r) = 0) → ℓ = 0)
    (ℓ : R →ₗ[K] K) (hℓ : ℓ ≠ 0) : ∃ r : S.Re, ℓ (S.cay r) ≠ 0 := by
  by_contra! hh
  have hx (r : R) (hr : r ∈ S.Re) : ℓ 1 = 0 ∧ ℓ (S.ι * r) = 0 ∧ ℓ (r ^ 2) = 0 := by
    have hrt (t : ℚ) : algebraMap K R t * r ∈ S.Re := S.smul_mem t r hr
    have he (t : ℚ) : S.ι * (algebraMap K R t * r) = (S.ι * r) * algebraMap K R t := by ring
    obtain ⟨h1, hb, hb2⟩ := cayley_annihilation (K := K) (S.ι * r)
      (Algebra.IsIntegral.isIntegral _) ℓ
      (fun t => by rw [← he]; exact S.isUnit _ (hrt t))
      (fun t u hu => by
        have hu' : (1 - S.ι * ((⟨_, hrt t⟩ : S.Re) : R)) * u =
            1 + S.ι * ((⟨_, hrt t⟩ : S.Re) : R) := by simpa only [he] using hu
        rw [S.cay_unique ⟨_, hrt t⟩ hu']
        exact hh _)
    refine ⟨h1, hb, ?_⟩
    have hsq : (S.ι * r) ^ 2 = -(r ^ 2) := by
      rw [mul_pow, sq S.ι, S.ι_sq]
      ring
    rw [hsq, map_neg, neg_eq_zero] at hb2
    exact hb2
  have hreal (r : R) (hr : r ∈ S.Re) : ℓ r = 0 := by
    have hm : algebraMap K R (-1 : ℚ) * 1 ∈ S.Re := S.smul_mem _ _ S.one_mem
    have h1 := (hx _ (S.add_mem r hr 1 S.one_mem)).2.2
    have h2 := (hx _ (S.add_mem r hr _ hm)).2.2
    have he : (r + 1) ^ 2 - (r + algebraMap K R (-1 : ℚ) * 1) ^ 2 = (4 : K) • r := by
      simp only [Algebra.smul_def, Rat.cast_neg, Rat.cast_one, map_neg, map_one, map_ofNat]
      ring
    have hh := congrArg ℓ he
    rw [map_sub, h1, h2, sub_self, map_smul, smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (by norm_num)
  exact hℓ (hspan ℓ fun r hr => ⟨hreal r hr, (hx r hr).2.1⟩)

/-- Some Cayley transform of a real element escapes finitely many nonzero functionals. -/
lemma cay_finite_avoid (hspan : ∀ ℓ : R →ₗ[K] K,
      (∀ r ∈ S.Re, ℓ r = 0 ∧ ℓ (S.ι * r) = 0) → ℓ = 0)
    (s : Finset (R →ₗ[K] K)) (hs : ∀ ℓ ∈ s, ℓ ≠ 0) :
    ∃ r : S.Re, ∀ ℓ ∈ s, ℓ (S.cay r) ≠ 0 := by
  have : Nonempty S.Re := ⟨⟨1, S.one_mem⟩⟩
  exact finite_hyperplanes_avoid S.cay S.line S.line_zero S.line_one S.cay_line_polynomials s
    (fun ℓ hℓ => S.cay_functional_escape hspan ℓ (hs ℓ hℓ))

/-- Some Cayley transform of a real element avoids finitely many proper subspaces. -/
lemma cay_subspaces_avoid (hspan : ∀ ℓ : R →ₗ[K] K,
      (∀ r ∈ S.Re, ℓ r = 0 ∧ ℓ (S.ι * r) = 0) → ℓ = 0)
    (P : Finset (Submodule K R)) (hP : ∀ p ∈ P, p < ⊤) :
    ∃ r : S.Re, ∀ p ∈ P, S.cay r ∉ p := by
  classical
  choose ℓ hn hker using fun p : P => Submodule.exists_le_ker_of_lt_top p.val (hP p p.property)
  obtain ⟨r, hr⟩ := S.cay_finite_avoid hspan (Finset.univ.image ℓ) (by
    intro ψ hψ
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hψ
    exact hn p)
  exact ⟨r, fun p hp hx => hr (ℓ ⟨p, hp⟩)
    (Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩) (hker ⟨p, hp⟩ hx)⟩

end RealStructure

end Erdos173.Template

end
