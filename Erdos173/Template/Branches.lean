module

public import Erdos173.Template.Algebraic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Rational Cauchy transforms forced by a cover

Fix a complex unit `T`, a finite set `Q` of units, units `b₁, …, b_d` and
`s₁, …, s_n`, and polynomial coordinates
`κ(T) q s_k = ∑_l p_{qkl}(T) b_l` over the algebraic numbers `𝔸`, such that for each
`q` every `d` of the coordinate rows `p_{qk}` form a matrix of nonzero determinant,
and `n > |Q|(d - 1)`. This is a *Cauchy frame*. An `𝔸`-linear functional `μ` on `ℂ`
is *covered* when each unit of a set `U`, stable under the multipliers
`a (1 + h/(T - a))` with `(a, h)` in the parameter plane `Ω`, has some `q ∈ Q` with
`μ(q u) = 0`.

The Cauchy transform of `μ` is the vector `F(a) = (μ(b_l/(T - a)))_l`. Applying the
cover to `s_k a (1 + h/(T - a))` gives, for each `k`, some `q` with
`μ(q s_k) + h μ(q s_k/(T - a)) = 0`, and divided differences of the coordinates turn
`μ(q s_k/(T - a))` into `p_{qk}(a) · F(a)` plus a polynomial in `a`. By pigeonhole
some `d` rows share their `q`; inverting them expresses `F(a)` on one of finitely
many *branches* as `R_β(a) + S_β(a)/h`. Applying the cover to products of two
multipliers and comparing coefficients in the independent variables `h` and `k'`
shows that each Zariski-dense branch has `S_β = 0`, and that all dense branches
have the same rational vector. Hence, with a fixed denominator `Δ`, the transform
`Δ(a) F(a)` agrees off a proper algebraic subset of `Ω` with a polynomial vector of
uniformly bounded degree.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Template

open Polynomial

/-- A property holds generically on the parameter plane: off the zero set of a
nonzero polynomial function. -/
def Gen (P : (Fin 2 → 𝔸) → Prop) : Prop :=
  ∃ g ∈ polyFuns 𝔸 (Fin 2), g ≠ 0 ∧ ∀ z ∈ Ω, g z ≠ 0 → P z

/-- A generic property implies its consequences on `Ω` generically. -/
lemma Gen.mono {P P' : (Fin 2 → 𝔸) → Prop} (h : Gen P) (hP : ∀ z ∈ Ω, P z → P' z) : Gen P' := by
  obtain ⟨g, hg, hg0, hP0⟩ := h
  exact ⟨g, hg, hg0, fun z hz hgz => hP z hz (hP0 z hz hgz)⟩

/-- Two generic properties hold generically together. -/
lemma Gen.and {P P' : (Fin 2 → 𝔸) → Prop} (h : Gen P) (h' : Gen P') : Gen fun z => P z ∧ P' z := by
  obtain ⟨g, hg, hg0, hP⟩ := h
  obtain ⟨g', hg', hg0', hP'⟩ := h'
  refine ⟨fun z => g z * g' z, mul_mem_polyFuns hg hg', fun he => ?_, fun z hz hgz => ?_⟩
  · rcases eq_zero_or_eq_zero_of_mul_eq_zero hg hg' he with h | h
    · exact hg0 h
    · exact hg0' h
  · exact ⟨hP z hz (left_ne_zero_of_mul hgz), hP' z hz (right_ne_zero_of_mul hgz)⟩

/-- A generic property holds on a Zariski-dense set. -/
lemma Gen.zariskiDense {P : (Fin 2 → 𝔸) → Prop} (h : Gen P) : ZariskiDense {z | P z} := by
  obtain ⟨g, hg, hg0, hP⟩ := h
  exact (zariskiDense_Ω.inter hg hg0).mono fun z hz => hP z hz.1 hz.2

/-- A polynomial vanishing generically at the first coordinate is zero. -/
lemma Gen.poly_eq_zero {p : 𝔸[X]} (h : Gen fun z => p.eval (z 0) = 0) : p = 0 := by
  have hz := h.zariskiDense _ (eval_coord_mem_polyFuns p 0) fun z hz => hz
  exact poly_eq_zero_of_forall fun a => by simpa using congrFun hz (fun _ => a)

/-- The fixed data of the Cauchy-transform argument. -/
structure CauchyFrame where
  /-- The transcendental unit. -/
  T : ℂ
  /-- The rank of the function field over `𝔸(T)`. -/
  d : ℕ
  /-- The number of units in general position. -/
  n : ℕ
  /-- The cover. -/
  Q : Finset ℂ
  /-- A basis of units. -/
  b : Fin d → ℂ
  /-- Units in general position. -/
  s : Fin n → ℂ
  /-- The common denominator of the coordinates. -/
  κ : 𝔸[X]
  /-- The coordinates. -/
  p : Q → Fin n → Fin d → 𝔸[X]
  /-- The units on which the cover acts. -/
  U : Set ℂ
  norm_T : ‖T‖ = 1
  κ_ne : κ ≠ 0
  coord : ∀ (j : Q) k, aeval T κ * ((j : ℂ) * s k) = ∑ l, aeval T (p j k l) * b l
  det_ne : ∀ (j : Q) (e : Fin d ↪ Fin n), (Matrix.of fun i l => p j (e i) l).det ≠ 0
  card_lt : Fintype.card Q * (d - 1) < n
  s_mem : ∀ k, s k ∈ U
  mul_mem : ∀ z ∈ Ω, ∀ u ∈ U, u * ((z 0 : ℂ) * (1 + (z 1 : ℂ) / (T - z 0))) ∈ U

namespace CauchyFrame

variable (𝔣 : CauchyFrame) (μ : ℂ →ₗ[𝔸] 𝔸)

/-- The functional `μ` is covered by `Q` on `U`. -/
def Covered : Prop := ∀ u ∈ 𝔣.U, ∃ q ∈ 𝔣.Q, μ (q * u) = 0

/-- The Cauchy transform `a ↦ (μ(b_l/(T - a)))_l`. -/
def cauchy (a : 𝔸) (l : Fin 𝔣.d) : 𝔸 := μ (𝔣.b l / (𝔣.T - a))

/-- The scalar transform `μ(q s_k/(T - a))`. -/
def H (j : 𝔣.Q) (k : Fin 𝔣.n) (a : 𝔸) : 𝔸 := μ ((j : ℂ) * 𝔣.s k / (𝔣.T - a))

/-- The value `μ(q s_k)`. -/
def L (j : 𝔣.Q) (k : Fin 𝔣.n) : 𝔸 := μ ((j : ℂ) * 𝔣.s k)

/-- The divided difference `a ↦ μ(z (p(T) - p(a))/(T - a))`, a polynomial in `a`. -/
def divDiff (p : 𝔸[X]) (z : ℂ) : 𝔸[X] :=
  ∑ m ∈ Finset.range (p.natDegree + 1), ∑ i ∈ Finset.range m,
    C (p.coeff m * μ (z * 𝔣.T ^ i)) * X ^ (m - 1 - i)

/-- The divided difference evaluates to `μ(z (p(T) - p(a))/(T - a))`. -/
lemma eval_divDiff (p : 𝔸[X]) (z : ℂ) (a : 𝔸) (hTa : 𝔣.T - a ≠ 0) :
    (𝔣.divDiff μ p z).eval a = μ (z * (aeval 𝔣.T p - ((p.eval a : 𝔸) : ℂ)) / (𝔣.T - a)) := by
  have key : z * (aeval 𝔣.T p - ((p.eval a : 𝔸) : ℂ)) / (𝔣.T - a) =
      ∑ m ∈ Finset.range (p.natDegree + 1), ∑ i ∈ Finset.range m,
        (p.coeff m * a ^ (m - 1 - i)) • (z * 𝔣.T ^ i) := by
    rw [aeval_eq_sum_range, eval_eq_sum_range]
    push_cast
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [div_eq_iff hTa, Finset.sum_mul]
    have hg := geom_sum₂_mul 𝔣.T (a : ℂ) m
    simp only [Algebra.smul_def, IntermediateField.algebraMap_apply] at *
    push_cast
    rw [show z * ((p.coeff m : ℂ) * 𝔣.T ^ m - (p.coeff m : ℂ) * (a : ℂ) ^ m) =
      z * (p.coeff m : ℂ) * (𝔣.T ^ m - (a : ℂ) ^ m) by ring, ← hg, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [key, map_sum]
  simp only [divDiff, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_smul,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The divided difference has degree at most `deg p`. -/
lemma natDegree_divDiff_le (p : 𝔸[X]) (z : ℂ) : (𝔣.divDiff μ p z).natDegree ≤ p.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro m hm
  apply natDegree_sum_le_of_forall_le
  intro i _
  have hm : m ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- The polynomial part `D_{qk}` in `κ(a) H_{qk}(a) = p_{qk}(a) · F(a) + D_{qk}(a)`. -/
def D (j : 𝔣.Q) (k : Fin 𝔣.n) : 𝔸[X] :=
  ∑ l, 𝔣.divDiff μ (𝔣.p j k l) (𝔣.b l) - 𝔣.divDiff μ 𝔣.κ ((j : ℂ) * 𝔣.s k)

/-- `κ(a) H_{qk}(a) = p_{qk}(a) · F(a) + D_{qk}(a)`. -/
lemma κ_mul_H (j : 𝔣.Q) (k : Fin 𝔣.n) (a : 𝔸) (hTa : 𝔣.T - a ≠ 0) :
    𝔣.κ.eval a * 𝔣.H μ j k a =
      ∑ l, (𝔣.p j k l).eval a * 𝔣.cauchy μ a l + (𝔣.D μ j k).eval a := by
  have hc := congrArg (fun w : ℂ => w / (𝔣.T - a)) (𝔣.coord j k)
  have h1 : aeval 𝔣.T 𝔣.κ * ((j : ℂ) * 𝔣.s k) / (𝔣.T - a) =
      𝔣.κ.eval a • ((j : ℂ) * 𝔣.s k / (𝔣.T - a)) +
        (j : ℂ) * 𝔣.s k * (aeval 𝔣.T 𝔣.κ - ((𝔣.κ.eval a : 𝔸) : ℂ)) / (𝔣.T - a) := by
    rw [smul_eq]
    ring
  have h2 : (∑ l, aeval 𝔣.T (𝔣.p j k l) * 𝔣.b l) / (𝔣.T - a) =
      ∑ l, ((𝔣.p j k l).eval a • (𝔣.b l / (𝔣.T - a)) +
        𝔣.b l * (aeval 𝔣.T (𝔣.p j k l) - (((𝔣.p j k l).eval a : 𝔸) : ℂ)) / (𝔣.T - a)) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_eq]
    ring
  rw [h1, h2] at hc
  have hμ := congrArg μ hc
  simp only [map_add, map_sum, map_smul, smul_eq_mul, Finset.sum_add_distrib] at hμ
  rw [D, eval_sub, eval_finsetSum, 𝔣.eval_divDiff μ _ _ a hTa]
  simp only [𝔣.eval_divDiff μ _ _ a hTa, H, cauchy]
  linear_combination hμ

/-- The cover on `s_k` times one multiplier. -/
lemma cover_single {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) {z : Fin 2 → 𝔸} (hz : z ∈ Ω)
    (k : Fin 𝔣.n) : ∃ j : 𝔣.Q, 𝔣.L μ j k + z 1 * 𝔣.H μ j k (z 0) = 0 := by
  obtain ⟨q, hq, hμ⟩ := hcov _ (𝔣.mul_mem z hz _ (𝔣.s_mem k))
  refine ⟨⟨q, hq⟩, ?_⟩
  have hTa := (Ω_unit hz 𝔣.norm_T).1
  have he : q * (𝔣.s k * ((z 0 : ℂ) * (1 + (z 1 : ℂ) / (𝔣.T - z 0)))) =
      z 0 • (q * 𝔣.s k) + (z 0 * z 1) • (q * 𝔣.s k / (𝔣.T - z 0)) := by
    simp only [smul_eq]
    push_cast
    ring
  rw [he, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hμ
  have h0 : z 0 ≠ 0 := hz.1
  have : z 0 * (𝔣.L μ ⟨q, hq⟩ k + z 1 * 𝔣.H μ ⟨q, hq⟩ k (z 0)) = 0 := by
    rw [← hμ, L, H]
    ring
  exact (mul_eq_zero.mp this).resolve_left h0

/-- A branch: a member of the cover and `d` indices. -/
abbrev Branch := 𝔣.Q × (Fin 𝔣.d ↪ Fin 𝔣.n)

/-- The coordinate matrix of a branch. -/
def M (β : 𝔣.Branch) : Matrix (Fin 𝔣.d) (Fin 𝔣.d) 𝔸[X] := Matrix.of fun i l => 𝔣.p β.1 (β.2 i) l

/-- The determinant of a branch. -/
def δ (β : 𝔣.Branch) : 𝔸[X] := (𝔣.M β).det

/-- The determinant of a branch is nonzero. -/
lemma δ_ne (β : 𝔣.Branch) : 𝔣.δ β ≠ 0 := 𝔣.det_ne β.1 β.2

/-- The constant part of the branch formula. -/
def R (β : 𝔣.Branch) (l : Fin 𝔣.d) : 𝔸[X] :=
  -∑ i, (𝔣.M β).adjugate l i * 𝔣.D μ β.1 (β.2 i)

/-- The polar part of the branch formula. -/
def S (β : 𝔣.Branch) (l : Fin 𝔣.d) : 𝔸[X] :=
  -∑ i, (𝔣.M β).adjugate l i * C (𝔣.L μ β.1 (β.2 i)) * 𝔣.κ

/-- The parameters at which the branch `β` holds. -/
def Z (β : 𝔣.Branch) : Set (Fin 2 → 𝔸) :=
  {z | z ∈ Ω ∧ ∀ i, 𝔣.L μ β.1 (β.2 i) + z 1 * 𝔣.H μ β.1 (β.2 i) (z 0) = 0}

/-- Pigeonhole: `n > |Q|(d - 1)` indices labelled by `Q` contain `d` with one label. -/
lemma exists_branch (f : Fin 𝔣.n → 𝔣.Q) : ∃ β : 𝔣.Branch, ∀ i, f (β.2 i) = β.1 := by
  classical
  obtain ⟨j, hj⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (by simpa using 𝔣.card_lt)
  have hd : 𝔣.d ≤ (Finset.univ.filter fun x => f x = j).card := by omega
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hd
  let e : Fin 𝔣.d ↪ Fin 𝔣.n := (t.orderEmbOfFin htc).toEmbedding
  refine ⟨(j, e), fun i => ?_⟩
  have hm : e i ∈ t := Finset.orderEmbOfFin_mem t htc i
  exact (Finset.mem_filter.mp (ht hm)).2

/-- Every parameter lies on some branch. -/
lemma cover_branches {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) {z : Fin 2 → 𝔸} (hz : z ∈ Ω) :
    ∃ β, z ∈ 𝔣.Z μ β := by
  choose f hf using 𝔣.cover_single hcov hz
  obtain ⟨β, hβ⟩ := 𝔣.exists_branch f
  refine ⟨β, hz, fun i => ?_⟩
  have h := hf (β.2 i)
  rwa [hβ i] at h

/-- On its branch the Cauchy transform is `R_β(a) + S_β(a)/h`, after clearing `δ_β`. -/
lemma branch_formula (β : 𝔣.Branch) {z : Fin 2 → 𝔸} (hz : z ∈ 𝔣.Z μ β) (l : Fin 𝔣.d) :
    (𝔣.δ β).eval (z 0) * z 1 * 𝔣.cauchy μ (z 0) l =
      z 1 * (𝔣.R μ β l).eval (z 0) + (𝔣.S μ β l).eval (z 0) := by
  classical
  set a := z 0
  set h := z 1
  have hTa := (Ω_unit hz.1 𝔣.norm_T).1
  let Ma : Matrix (Fin 𝔣.d) (Fin 𝔣.d) 𝔸 := (evalRingHom a).mapMatrix (𝔣.M β)
  let x : Fin 𝔣.d → 𝔸 := fun l => h * 𝔣.cauchy μ a l
  have hMx : Ma.mulVec x = fun i =>
      -(𝔣.κ.eval a * 𝔣.L μ β.1 (β.2 i) + h * (𝔣.D μ β.1 (β.2 i)).eval a) := by
    funext i
    have h1 := 𝔣.κ_mul_H μ β.1 (β.2 i) a hTa
    have h2 := hz.2 i
    simp only [Ma, x, Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, M,
      Matrix.of_apply, coe_evalRingHom]
    have : ∑ l, eval a (𝔣.p β.1 (β.2 i) l) * (h * 𝔣.cauchy μ a l) =
        h * ∑ l, eval a (𝔣.p β.1 (β.2 i) l) * 𝔣.cauchy μ a l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]
    linear_combination (-h) * h1 + 𝔣.κ.eval a * h2
  have hadj := congrArg (fun v => Ma.adjugate.mulVec v) hMx
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hadj
  have hl := congrFun hadj l
  have hdet : Ma.det = (𝔣.δ β).eval a := by
    rw [δ, ← coe_evalRingHom, RingHom.map_det]
  have hadjM : Ma.adjugate = (evalRingHom a).mapMatrix (𝔣.M β).adjugate := by
    rw [RingHom.map_adjugate]
  simp only [Pi.smul_apply, smul_eq_mul, hdet, x] at hl
  rw [← mul_assoc] at hl
  rw [hl, hadjM]
  simp only [R, S, eval_neg, eval_finsetSum, eval_mul, eval_C, Matrix.mulVec, dotProduct,
    RingHom.mapMatrix_apply, Matrix.map_apply, coe_evalRingHom]
  rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The cleared denominator of a branch. -/
def ε (β : 𝔣.Branch) : 𝔸[X] := 𝔣.δ β * 𝔣.κ

/-- The cleared denominator of a branch is nonzero. -/
lemma ε_ne (β : 𝔣.Branch) : 𝔣.ε β ≠ 0 := mul_ne_zero (𝔣.δ_ne β) 𝔣.κ_ne

/-- The constant part of `q s_k`'s scalar transform on a branch. -/
def V (β : 𝔣.Branch) (j : 𝔣.Q) (k : Fin 𝔣.n) : 𝔸[X] :=
  ∑ l, 𝔣.p j k l * 𝔣.R μ β l + 𝔣.δ β * 𝔣.D μ j k

/-- The polar part of `q s_k`'s scalar transform on a branch. -/
def W (β : 𝔣.Branch) (j : 𝔣.Q) (k : Fin 𝔣.n) : 𝔸[X] := ∑ l, 𝔣.p j k l * 𝔣.S μ β l

/-- On a branch the scalar transform of every `q s_k` is `V_β + W_β/h`, after clearing
`ε_β`. -/
lemma branch_H (β : 𝔣.Branch) {z : Fin 2 → 𝔸} (hz : z ∈ 𝔣.Z μ β) (j : 𝔣.Q) (k : Fin 𝔣.n) :
    (𝔣.ε β).eval (z 0) * z 1 * 𝔣.H μ j k (z 0) =
      z 1 * (𝔣.V μ β j k).eval (z 0) + (𝔣.W μ β j k).eval (z 0) := by
  have hTa := (Ω_unit hz.1 𝔣.norm_T).1
  have h1 := 𝔣.κ_mul_H μ j k (z 0) hTa
  have h2 (l : Fin 𝔣.d) := 𝔣.branch_formula μ β hz l
  simp only [ε, V, W, eval_mul, eval_add, eval_finsetSum]
  calc (𝔣.δ β).eval (z 0) * 𝔣.κ.eval (z 0) * z 1 * 𝔣.H μ j k (z 0)
      = (𝔣.δ β).eval (z 0) * z 1 * (𝔣.κ.eval (z 0) * 𝔣.H μ j k (z 0)) := by ring
    _ = ∑ l, (𝔣.p j k l).eval (z 0) * ((𝔣.δ β).eval (z 0) * z 1 * 𝔣.cauchy μ (z 0) l) +
          z 1 * ((𝔣.δ β).eval (z 0) * (𝔣.D μ j k).eval (z 0)) := by
        rw [h1, mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun l _ => by ring
        · ring
    _ = _ := by
        simp only [h2]
        have : ∑ l, (𝔣.p j k l).eval (z 0) * (z 1 * (𝔣.R μ β l).eval (z 0) +
            (𝔣.S μ β l).eval (z 0)) = z 1 * ∑ l, (𝔣.p j k l).eval (z 0) * (𝔣.R μ β l).eval (z 0) +
            ∑ l, (𝔣.p j k l).eval (z 0) * (𝔣.S μ β l).eval (z 0) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [this]
        ring

omit 𝔣 μ in
/-- Comparing coefficients in the independent variables `h` and `k` of the
double-product identity. -/
lemma double_coefficients {εβ εγ Vβ Wβ Vγ Wγ : 𝔸[X]} {L₀ : 𝔸} (hεβ : εβ ≠ 0) (hεγ : εγ ≠ 0)
    (hE : ∀ a h c k : 𝔸, (a - c) * εβ.eval a * εγ.eval c * L₀
      + (a - c) * εγ.eval c * (h * Vβ.eval a + Wβ.eval a)
      + (a - c) * εβ.eval a * (k * Vγ.eval c + Wγ.eval c)
      + k * εγ.eval c * (h * Vβ.eval a + Wβ.eval a)
      - h * εβ.eval a * (k * Vγ.eval c + Wγ.eval c) = 0) :
    Wβ = 0 ∧ Vβ = 0 ∧ Wγ = 0 ∧ Vγ = 0 ∧ L₀ = 0 := by
  have hWγ : Wγ = 0 := by
    have h0 : εβ * Wγ = 0 := poly_eq_zero_of_forall fun a => by
      have := hE a 1 a 0
      rw [eval_mul]
      linear_combination -this
    exact (mul_eq_zero.mp h0).resolve_left hεβ
  have hWβ : Wβ = 0 := by
    have h0 : εγ * Wβ = 0 := poly_eq_zero_of_forall fun a => by
      have := hE a 0 a 1
      rw [eval_mul]
      linear_combination this
    exact (mul_eq_zero.mp h0).resolve_left hεγ
  subst hWβ hWγ
  obtain ⟨c₀, -, hc₀⟩ := exists_eval_ne_zero hεγ ∅
  obtain ⟨a₀, -, ha₀⟩ := exists_eval_ne_zero hεβ ∅
  have hVβ : Vβ = 0 := by
    have h0 : (X - C c₀) * C (εγ.eval c₀) * Vβ = 0 := poly_eq_zero_of_forall fun a => by
      have h1 := hE a 1 c₀ 0
      have h2 := hE a 0 c₀ 0
      simp only [eval_mul, eval_sub, eval_X, eval_C, eval_zero] at h1 h2 ⊢
      linear_combination h1 - h2
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (mul_ne_zero (X_sub_C_ne_zero c₀) (C_ne_zero.mpr hc₀))
    · exact h
  have hVγ : Vγ = 0 := by
    have h0 : (C a₀ - X) * C (εβ.eval a₀) * Vγ = 0 := poly_eq_zero_of_forall fun c => by
      have h1 := hE a₀ 0 c 1
      have h2 := hE a₀ 0 c 0
      simp only [eval_mul, eval_sub, eval_X, eval_C, eval_zero] at h1 h2 ⊢
      linear_combination h1 - h2
    rcases mul_eq_zero.mp h0 with h | h
    · refine absurd h (mul_ne_zero ?_ (C_ne_zero.mpr ha₀))
      rw [← neg_sub]
      exact neg_ne_zero.mpr (X_sub_C_ne_zero a₀)
    · exact h
  refine ⟨rfl, hVβ, rfl, hVγ, ?_⟩
  have h0 : (X - C c₀) * εβ * C (εγ.eval c₀ * L₀) = 0 := poly_eq_zero_of_forall fun a => by
    have h1 := hE a 0 c₀ 0
    simp only [eval_mul, eval_sub, eval_X, eval_C, eval_zero] at h1 ⊢
    linear_combination h1
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h (mul_ne_zero (X_sub_C_ne_zero c₀) hεβ)
  · exact (mul_eq_zero.mp (C_eq_zero.mp h)).resolve_left hc₀

/-- The polynomial form of the cover on `s_k` times two multipliers, cleared of
denominators on two branches. -/
def doubleForm (β γ : 𝔣.Branch) (j : 𝔣.Q) (k : Fin 𝔣.n) (w : Fin 2 ⊕ Fin 2 → 𝔸) : 𝔸 :=
  (w (.inl 0) - w (.inr 0)) * (𝔣.ε β).eval (w (.inl 0)) * (𝔣.ε γ).eval (w (.inr 0)) * 𝔣.L μ j k
  + (w (.inl 0) - w (.inr 0)) * (𝔣.ε γ).eval (w (.inr 0)) *
      (w (.inl 1) * (𝔣.V μ β j k).eval (w (.inl 0)) + (𝔣.W μ β j k).eval (w (.inl 0)))
  + (w (.inl 0) - w (.inr 0)) * (𝔣.ε β).eval (w (.inl 0)) *
      (w (.inr 1) * (𝔣.V μ γ j k).eval (w (.inr 0)) + (𝔣.W μ γ j k).eval (w (.inr 0)))
  + w (.inr 1) * (𝔣.ε γ).eval (w (.inr 0)) *
      (w (.inl 1) * (𝔣.V μ β j k).eval (w (.inl 0)) + (𝔣.W μ β j k).eval (w (.inl 0)))
  - w (.inl 1) * (𝔣.ε β).eval (w (.inl 0)) *
      (w (.inr 1) * (𝔣.V μ γ j k).eval (w (.inr 0)) + (𝔣.W μ γ j k).eval (w (.inr 0)))

/-- The cover on `s_k` times two multipliers from dense branches kills the polar and
constant parts of some `q s_k`. -/
lemma double_branch {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) {β γ : 𝔣.Branch}
    (hβ : ZariskiDense (𝔣.Z μ β)) (hγ : ZariskiDense (𝔣.Z μ γ)) (k : Fin 𝔣.n) :
    ∃ j, 𝔣.W μ β j k = 0 ∧ 𝔣.V μ β j k = 0 ∧ 𝔣.W μ γ j k = 0 ∧ 𝔣.V μ γ j k = 0 ∧
      𝔣.L μ j k = 0 := by
  classical
  have hg : (fun w : Fin 2 ⊕ Fin 2 → 𝔸 => w (.inl 0) - w (.inr 0)) ∈
      polyFuns 𝔸 (Fin 2 ⊕ Fin 2) := by
    polyfun
  have hg0 : (fun w : Fin 2 ⊕ Fin 2 → 𝔸 => w (.inl 0) - w (.inr 0)) ≠ 0 := by
    intro h
    have := congrFun h (Sum.elim (fun _ => 1) (fun _ => 0))
    simp at this
  have hD := (hβ.prod hγ).inter hg hg0
  -- the expression of the cover at `w`
  let Ex : 𝔣.Q → (Fin 2 ⊕ Fin 2 → 𝔸) → 𝔸 := fun j w =>
    𝔣.L μ j k + w (.inl 1) * 𝔣.H μ j k (w (.inl 0)) + w (.inr 1) * 𝔣.H μ j k (w (.inr 0)) +
      w (.inl 1) * w (.inr 1) * (w (.inl 0) - w (.inr 0))⁻¹ *
        (𝔣.H μ j k (w (.inl 0)) - 𝔣.H μ j k (w (.inr 0)))
  obtain ⟨j, -, hj⟩ := hD.exists_of_cover Finset.univ
      (fun j => {w | (w ∘ Sum.inl ∈ 𝔣.Z μ β ∧ w ∘ Sum.inr ∈ 𝔣.Z μ γ) ∧
        w (.inl 0) - w (.inr 0) ≠ 0 ∧ Ex j w = 0}) (by
    rintro w ⟨⟨hw1, hw2⟩, hac⟩
    have hu := 𝔣.mul_mem _ hw2.1 _ (𝔣.mul_mem _ hw1.1 _ (𝔣.s_mem k))
    obtain ⟨q, hq, hμ⟩ := hcov _ hu
    refine ⟨⟨q, hq⟩, Finset.mem_univ _, ⟨hw1, hw2⟩, hac, ?_⟩
    have hTa : 𝔣.T - (w (.inl 0) : ℂ) ≠ 0 := (Ω_unit hw1.1 𝔣.norm_T).1
    have hTc : 𝔣.T - (w (.inr 0) : ℂ) ≠ 0 := (Ω_unit hw2.1 𝔣.norm_T).1
    have hac' : (w (.inl 0) : ℂ) - w (.inr 0) ≠ 0 := by
      intro h
      apply hac
      have : w (.inl 0) = w (.inr 0) := Subtype.ext (sub_eq_zero.mp h)
      simp [this]
    have he : q * (𝔣.s k * ((w (.inl 0) : ℂ) * (1 + (w (.inl 1) : ℂ) / (𝔣.T - w (.inl 0)))) *
        ((w (.inr 0) : ℂ) * (1 + (w (.inr 1) : ℂ) / (𝔣.T - w (.inr 0))))) =
        (w (.inl 0) * w (.inr 0)) • (q * 𝔣.s k) +
        (w (.inl 0) * w (.inr 0) * w (.inl 1)) • (q * 𝔣.s k / (𝔣.T - w (.inl 0))) +
        (w (.inl 0) * w (.inr 0) * w (.inr 1)) • (q * 𝔣.s k / (𝔣.T - w (.inr 0))) +
        (w (.inl 0) * w (.inr 0) * w (.inl 1) * w (.inr 1) * (w (.inl 0) - w (.inr 0))⁻¹) •
          (q * 𝔣.s k / (𝔣.T - w (.inl 0)) - q * 𝔣.s k / (𝔣.T - w (.inr 0))) := by
      simp only [smul_eq]
      push_cast
      field_simp
      ring
    simp only [Function.comp] at hμ
    rw [he] at hμ
    simp only [map_add, map_sub, map_smul, smul_eq_mul] at hμ
    have h0 : w (.inl 0) * w (.inr 0) ≠ 0 := mul_ne_zero hw1.1.1 hw2.1.1
    show Ex ⟨q, hq⟩ w = 0
    apply (mul_eq_zero.mp _).resolve_left h0
    rw [← hμ]
    simp only [Ex, L, H]
    ring)
  have hΦ : (fun w => 𝔣.doubleForm μ β γ j k w) ∈ polyFuns 𝔸 (Fin 2 ⊕ Fin 2) := by
    unfold doubleForm
    polyfun
  have hzero := hj _ hΦ (by
    rintro w ⟨⟨hw1, hw2⟩, hac, hEx⟩
    have hb := 𝔣.branch_H μ β hw1 j k
    have hc := 𝔣.branch_H μ γ hw2 j k
    simp only [Function.comp] at hb hc
    have hac' : w (.inl 0) - w (.inr 0) ≠ 0 := hac
    simp only [doubleForm]
    have hE : (w (.inl 0) - w (.inr 0)) * (𝔣.ε β).eval (w (.inl 0)) *
        (𝔣.ε γ).eval (w (.inr 0)) * Ex j w = 0 := by rw [hEx, mul_zero]
    simp only [Ex] at hE
    rw [← hb, ← hc]
    rw [← hE]
    field_simp
    ring)
  have hc := double_coefficients (𝔣.ε_ne β) (𝔣.ε_ne γ) (L₀ := 𝔣.L μ j k)
    (Vβ := 𝔣.V μ β j k) (Wβ := 𝔣.W μ β j k) (Vγ := 𝔣.V μ γ j k) (Wγ := 𝔣.W μ γ j k)
    fun a h c k' => by
      have := congrFun hzero (Sum.elim ![a, h] ![c, k'])
      simpa [doubleForm] using this
  exact ⟨j, hc⟩

/-- A nonzero determinant kills no nonzero polynomial vector. -/
lemma eq_zero_of_rows (β : 𝔣.Branch) (v : Fin 𝔣.d → 𝔸[X])
    (hv : ∀ i, ∑ l, 𝔣.p β.1 (β.2 i) l * v l = 0) : v = 0 := by
  classical
  have hM : (𝔣.M β).mulVec v = 0 := by
    funext i
    simpa [Matrix.mulVec, dotProduct, M] using hv i
  have h := congrArg (fun w => (𝔣.M β).adjugate.mulVec w) hM
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  funext l
  have hl := congrFun h l
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hl
  exact (mul_eq_zero.mp hl).resolve_left (𝔣.δ_ne β)

/-- Zariski-dense branches have no polar part and a common rational vector. -/
lemma dense_branches {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) {β γ : 𝔣.Branch}
    (hβ : ZariskiDense (𝔣.Z μ β)) (hγ : ZariskiDense (𝔣.Z μ γ)) :
    𝔣.S μ β = 0 ∧ 𝔣.δ γ • 𝔣.R μ β = 𝔣.δ β • 𝔣.R μ γ := by
  choose j hj using 𝔣.double_branch hcov hβ hγ
  obtain ⟨β', hβ'⟩ := 𝔣.exists_branch j
  have hk (i : Fin 𝔣.d) := hj (β'.2 i)
  simp only [hβ'] at hk
  refine ⟨𝔣.eq_zero_of_rows β' _ fun i => (hk i).1, ?_⟩
  rw [← sub_eq_zero]
  refine 𝔣.eq_zero_of_rows β' _ fun i => ?_
  have h1 := (hk i).2.1
  have h2 := (hk i).2.2.2.1
  simp only [V] at h1 h2
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have e1 : ∑ l, 𝔣.p β'.1 (β'.2 i) l * (𝔣.δ γ * 𝔣.R μ β l) =
      𝔣.δ γ * ∑ l, 𝔣.p β'.1 (β'.2 i) l * 𝔣.R μ β l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e2 : ∑ l, 𝔣.p β'.1 (β'.2 i) l * (𝔣.δ β * 𝔣.R μ γ l) =
      𝔣.δ β * ∑ l, 𝔣.p β'.1 (β'.2 i) l * 𝔣.R μ γ l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e1, e2]
  linear_combination 𝔣.δ γ * h1 - 𝔣.δ β * h2

/-- The common denominator `Δ = ∏_β δ_β`. -/
def Δ : 𝔸[X] := ∏ β, 𝔣.δ β

/-- The common denominator is nonzero. -/
lemma Δ_ne : 𝔣.Δ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun β _ => 𝔣.δ_ne β

/-- The bound on the adjugate degrees. -/
def adjBound : ℕ := Finset.univ.sup fun x : 𝔣.Branch × Fin 𝔣.d × Fin 𝔣.d =>
  ((𝔣.M x.1).adjugate x.2.1 x.2.2).natDegree

/-- The bound on the coordinate degrees. -/
def coordBound : ℕ :=
  (Finset.univ.sup fun x : 𝔣.Q × Fin 𝔣.n × Fin 𝔣.d => (𝔣.p x.1 x.2.1 x.2.2).natDegree) ⊔
    𝔣.κ.natDegree

/-- A bound for the degrees of the rational vectors. -/
def degBound : ℕ := ∑ β, (𝔣.δ β).natDegree + (𝔣.adjBound + 𝔣.coordBound)

/-- `Δ(a) F(a)` agrees generically with the polynomial vector `P`. -/
def Tame (P : Fin 𝔣.d → 𝔸[X]) : Prop :=
  Gen fun z => ∀ l, 𝔣.Δ.eval (z 0) * 𝔣.cauchy μ (z 0) l = (P l).eval (z 0)

/-- The polynomial part `D_{qk}` has degree at most `coordBound`. -/
lemma natDegree_D_le (j : 𝔣.Q) (k : Fin 𝔣.n) : (𝔣.D μ j k).natDegree ≤ 𝔣.coordBound := by
  refine (natDegree_sub_le _ _).trans (max_le_max ?_ (𝔣.natDegree_divDiff_le μ _ _))
  refine natDegree_sum_le_of_forall_le _ _ fun l _ => (𝔣.natDegree_divDiff_le μ _ _).trans ?_
  exact Finset.le_sup (f := fun x : 𝔣.Q × Fin 𝔣.n × Fin 𝔣.d => (𝔣.p x.1 x.2.1 x.2.2).natDegree)
    (Finset.mem_univ (j, k, l))

/-- The adjugate entries have degree at most `adjBound`. -/
lemma natDegree_adj_le (β : 𝔣.Branch) (l i : Fin 𝔣.d) :
    ((𝔣.M β).adjugate l i).natDegree ≤ 𝔣.adjBound := by
  unfold adjBound
  have h := Finset.le_sup (f := fun x : 𝔣.Branch × Fin 𝔣.d × Fin 𝔣.d =>
    ((𝔣.M x.1).adjugate x.2.1 x.2.2).natDegree) (Finset.mem_univ (β, l, i))
  exact h

/-- The constant part of a branch formula has degree at most `adjBound + coordBound`. -/
lemma natDegree_R_le (β : 𝔣.Branch) (l : Fin 𝔣.d) :
    (𝔣.R μ β l).natDegree ≤ 𝔣.adjBound + 𝔣.coordBound := by
  rw [R, natDegree_neg]
  exact natDegree_sum_le_of_forall_le _ _ fun i _ => natDegree_mul_le.trans
    (add_le_add (𝔣.natDegree_adj_le β l i) (𝔣.natDegree_D_le μ _ _))

/-- The Cauchy transform of a covered functional is generically rational, with
the fixed denominator `Δ` and numerators of degree at most `degBound`. -/
theorem tame_of_covered {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) :
    ∃ P : Fin 𝔣.d → 𝔸[X], (∀ l, (P l).natDegree ≤ 𝔣.degBound) ∧ 𝔣.Tame μ P := by
  classical
  obtain ⟨β₀, -, hβ₀⟩ := zariskiDense_Ω.exists_of_cover Finset.univ (𝔣.Z μ)
    fun z hz => (𝔣.cover_branches hcov hz).imp fun β h => ⟨Finset.mem_univ _, h⟩
  have hg (β : 𝔣.Branch) : ∃ g ∈ polyFuns 𝔸 (Fin 2), g ≠ 0 ∧
      (¬ ZariskiDense (𝔣.Z μ β) → ∀ z ∈ 𝔣.Z μ β, g z = 0) ∧
      (ZariskiDense (𝔣.Z μ β) → ∀ z, g z ≠ 0 → (𝔣.δ β).eval (z 0) ≠ 0) := by
    by_cases hd : ZariskiDense (𝔣.Z μ β)
    · refine ⟨fun z => (𝔣.δ β).eval (z 0), eval_coord_mem_polyFuns _ 0, fun h => 𝔣.δ_ne β ?_,
        fun h => absurd hd h, fun _ z hz => hz⟩
      exact poly_eq_zero_of_forall fun a => by simpa using congrFun h (fun _ => a)
    · simp only [ZariskiDense, not_forall] at hd
      obtain ⟨g, hg, hgZ, hg0⟩ := hd
      exact ⟨g, hg, hg0, fun _ => hgZ,
        fun h => absurd h (by simpa [ZariskiDense] using ⟨g, hg, hgZ, hg0⟩)⟩
  choose g hgm hg0 hgnd hgd using hg
  obtain ⟨hG, hG0⟩ := prod_mem_ne_zero Finset.univ (fun β _ => hgm β) (fun β _ => hg0 β)
  refine ⟨fun l => (∏ β ∈ Finset.univ.erase β₀, 𝔣.δ β) * 𝔣.R μ β₀ l, fun l => ?_,
    _, hG, hG0, fun z hz hGz l => ?_⟩
  · have h1 : (∏ β ∈ Finset.univ.erase β₀, 𝔣.δ β).natDegree ≤ ∑ β, (𝔣.δ β).natDegree :=
      (natDegree_prod_le _ _).trans (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
    have h2 := 𝔣.natDegree_R_le μ β₀ l
    calc _ ≤ _ := natDegree_mul_le
      _ ≤ _ := add_le_add h1 h2
      _ = 𝔣.degBound := rfl
  have hgz (β : 𝔣.Branch) : g β z ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hGz β (Finset.mem_univ _)
  obtain ⟨β, hzβ⟩ := 𝔣.cover_branches hcov hz
  have hβ : ZariskiDense (𝔣.Z μ β) := by
    by_contra hnd
    exact hgz β (hgnd β hnd z hzβ)
  have hδ : (𝔣.δ β).eval (z 0) ≠ 0 := hgd β hβ z (hgz β)
  have hS := (𝔣.dense_branches hcov hβ hβ).1
  have hRR := congrFun (𝔣.dense_branches hcov hβ hβ₀).2 l
  have hF := 𝔣.branch_formula μ β hzβ l
  rw [hS, Pi.zero_apply, eval_zero, add_zero, mul_comm _ (z 1), mul_assoc] at hF
  have hF' := mul_left_cancel₀ (Ω_h_ne_zero hz) hF
  have hRR' := congrArg (eval (z 0)) hRR
  simp only [Pi.smul_apply, smul_eq_mul, eval_mul] at hRR'
  have hkey : (𝔣.δ β₀).eval (z 0) * 𝔣.cauchy μ (z 0) l = (𝔣.R μ β₀ l).eval (z 0) := by
    apply mul_left_cancel₀ hδ
    rw [← hRR', ← hF']
    ring
  rw [Δ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ β₀), eval_mul, eval_mul, mul_comm
    ((𝔣.δ β₀).eval _), mul_assoc, hkey]

end CauchyFrame

end Erdos173.Template

end
