module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Two rational chord angles

Let `2/3 < x < 3/2` with `x ≠ 1`, and put `A = arcsin (x / 2)` and
`B = arcsin (1 / (2x))`, the half apex angles of the isosceles triangles with
sides `1, 1, x` and `x, x, 1`. Then `A / π` and `B / π` are not both rational.

Since `sin A sin B = 1/4`, the angles `u = A - B` and `v = A + B` satisfy
`2 cos u - 2 cos v = 1`. If both are rational multiples of `π`, write
`u = 2πa/m` and `v = 2πb/m` modulo `2π`. Then `ω = e^{2πi/m}` is a root of
`X^a + X^{(m-1)a} - X^b - X^{(m-1)b} - 1`, so every primitive `m`-th root of
unity `ω^k` is one too, since the minimal polynomial of `ω` over `ℚ` is the
cyclotomic polynomial: `2 cos (ku) - 2 cos (kv) = 1` for every `k` coprime to
`m`. In the window `cos u > cos (π/5)`, and `cos u ≠ 1` as `x ≠ 1`, so the
reduced denominator `m₁` of `u / 2π` is at least `11`. Every such `m₁` has a
unit `j` with `m₁ < 3j < 2m₁`, and a `k` coprime to `m` carries `u` to
`2πj/m₁`, where `cos < -1/2`, so `2 cos (ku) - 2 cos (kv) < 1`.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open Real Polynomial

/-- For `ω = e^{2πi/m}`, `ω^{jn} + ω^{j(m-1)n} = 2 cos (2π jn / m)`. -/
lemma pow_add_pow_eq_two_cos {m : ℕ} (hm : 0 < m) (j n : ℕ) :
    (Complex.exp (2 * π * Complex.I / m) ^ j) ^ n +
        (Complex.exp (2 * π * Complex.I / m) ^ j) ^ ((m - 1) * n) =
      ((2 * cos (2 * π * (j * n) / m) : ℝ) : ℂ) := by
  set ω := Complex.exp (2 * π * Complex.I / m) with hω
  have hprim : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hz : (ω ^ j) ^ n = Complex.exp (↑(2 * π * (j * n) / m) * Complex.I) := by
    rw [← pow_mul, hω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv : (ω ^ j) ^ ((m - 1) * n) = ((ω ^ j) ^ n)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add, ← add_one_mul, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm.ne'), ← pow_mul,
      show j * (m * n) = m * (j * n) by ring, pow_mul, hprim.pow_eq_one, one_pow]
  rw [hinv, hz, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-- The Galois step: if `2 cos (2πa/m) - 2 cos (2πb/m) = 1`, the same holds after
multiplying both angles by any `k` coprime to `m`. -/
lemma two_cos_sub_two_cos_of_coprime {m a b : ℕ} (hm : 0 < m)
    (h : 2 * cos (2 * π * a / m) - 2 * cos (2 * π * b / m) = 1) {k : ℕ} (hk : k.Coprime m) :
    2 * cos (2 * π * (k * a) / m) - 2 * cos (2 * π * (k * b) / m) = 1 := by
  set ω := Complex.exp (2 * π * Complex.I / m) with hω
  have hprim : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hprimk : IsPrimitiveRoot (ω ^ k) m := hprim.pow_of_coprime k hk
  have hmin : minpoly ℚ (ω ^ k) = minpoly ℚ ω := by
    rw [← cyclotomic_eq_minpoly_rat hprim hm, ← cyclotomic_eq_minpoly_rat hprimk hm]
  set P : ℚ[X] := X ^ a + X ^ ((m - 1) * a) - X ^ b - X ^ ((m - 1) * b) - 1 with hP
  have hev : ∀ j : ℕ, aeval (ω ^ j) P =
      ((2 * cos (2 * π * (j * a) / m) - 2 * cos (2 * π * (j * b) / m) - 1 : ℝ) : ℂ) := by
    intro j
    have ha := pow_add_pow_eq_two_cos hm j a
    have hb := pow_add_pow_eq_two_cos hm j b
    simp only [hP, map_sub, map_add, map_pow, aeval_X, map_one]
    push_cast at ha hb ⊢
    rw [← ha, ← hb]
    ring
  have h1 : aeval ω P = 0 := by
    have := hev 1
    rw [pow_one] at this
    rw [this]
    simp only [Nat.cast_one, one_mul, h, sub_self, Complex.ofReal_zero]
  obtain ⟨Q, hQ⟩ := minpoly.dvd ℚ ω h1
  have hk0 : aeval (ω ^ k) P = 0 := by
    rw [hQ, map_mul, ← hmin, minpoly.aeval, zero_mul]
  rw [hev k] at hk0
  have := Complex.ofReal_eq_zero.1 hk0
  linarith

/-- Every `m ≥ 11` has a unit `j` modulo `m` with `m < 3j < 2m`. -/
lemma exists_coprime_middle_third {m : ℕ} (hm : 11 ≤ m) :
    ∃ j : ℕ, j.Coprime m ∧ m < 3 * j ∧ 3 * j < 2 * m := by
  obtain ⟨l, rfl | rfl | rfl | rfl⟩ : ∃ l, m = 4 * l ∨ m = 4 * l + 1 ∨ m = 4 * l + 2 ∨
      m = 4 * l + 3 := ⟨m / 4, by omega⟩
  · refine ⟨2 * l + 1, ?_, by omega, by omega⟩
    rw [show 4 * l = 2 * (2 * l) by ring]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    · exact Nat.coprime_self_add_left.2 (Nat.coprime_one_left _)
  · refine ⟨2 * l, ?_, by omega, by omega⟩
    rw [show 4 * l + 1 = 2 * (2 * l) + 1 by ring, Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right _
  · refine ⟨2 * l + 3, ?_, by omega, by omega⟩
    rw [show 4 * l + 2 = 2 * (2 * l + 1) by ring]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    · rw [show 2 * l + 3 = (2 * l + 1) + 2 by ring, Nat.coprime_self_add_left,
        Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
  · refine ⟨2 * l + 1, ?_, by omega, by omega⟩
    rw [show 4 * l + 3 = 2 * (2 * l + 1) + 1 by ring, Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right _

/-- `cos θ < -1/2` for `2π/3 < θ < 4π/3`. -/
lemma cos_lt_neg_half {θ : ℝ} (h₁ : 2 * π / 3 < θ) (h₂ : θ < 4 * π / 3) :
    cos θ < -1 / 2 := by
  have hc : cos θ = -cos (θ - π) := by rw [cos_sub_pi]; ring
  rw [hc]
  have : 1 / 2 < cos (θ - π) := by
    rw [← cos_pi_div_three]
    rcases le_total 0 (θ - π) with h | h
    · exact cos_lt_cos_of_nonneg_of_le_pi h (by linarith [pi_pos]) (by linarith)
    · rw [← cos_neg (θ - π)]
      exact cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos]) (by linarith)
  linarith

/-- Angles `2πx/m` and `2πy/m` with `x ≡ y` modulo `m` have the same cosine. -/
lemma cos_eq_of_dvd_sub {m : ℕ} (hm : 0 < m) {x y : ℤ} (h : (m : ℤ) ∣ y - x) :
    cos (2 * π * x / m) = cos (2 * π * y / m) := by
  obtain ⟨t, ht⟩ := h
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hy : (y : ℝ) = x + m * t := by
    have : ((y - x : ℤ) : ℝ) = ((m * t : ℤ) : ℝ) := by rw [ht]
    push_cast at this
    linarith
  rw [hy, show 2 * π * (x + m * t) / m = 2 * π * x / m + t * (2 * π) by field_simp,
    cos_add_int_mul_two_pi]

/-- `cos (2π a / m) ≤ cos (2π / m)` unless `m ∣ a`. -/
lemma cos_two_pi_div_le {m a : ℕ} (hm : 0 < m) (ha : ¬ m ∣ a) :
    cos (2 * π * a / m) ≤ cos (2 * π / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set r := a % m with hr
  set q := a / m with hq
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero fun h => ha (Nat.dvd_of_mod_eq_zero h)
  have hr2 : r + 1 ≤ m := Nat.mod_lt _ hm
  have hadd : (a : ℝ) = r + m * q := by exact_mod_cast (Nat.mod_add_div a m).symm
  rw [hadd, show 2 * π * (r + m * q) / m = 2 * π * r / m + q * (2 * π) by field_simp,
    cos_add_nat_mul_two_pi]
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr2' : (r : ℝ) + 1 ≤ m := by exact_mod_cast hr2
  have h1 : 2 * π / m ≤ 2 * π * r / m := by
    apply div_le_div_of_nonneg_right _ hmR.le
    nlinarith [pi_pos]
  have h2 : 2 * π * r / m ≤ 2 * π - 2 * π / m := by
    rw [div_le_iff₀ hmR, sub_mul, div_mul_cancel₀ _ hmR.ne']
    nlinarith [pi_pos]
  rcases le_total (2 * π * r / m) π with h | h
  · exact cos_le_cos_of_nonneg_of_le_pi (by positivity) h h1
  · rw [← cos_two_pi_sub (2 * π * r / m)]
    exact cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)

/-- The arithmetic step: if `cos (2πa/m) > cos (π/5)` and `cos (2πa/m) ≠ 1`, some
`k` coprime to `m` gives `cos (2πka/m) < -1/2`. -/
lemma exists_coprime_cos_lt {m a : ℕ} (hm : 0 < m)
    (h₁ : (1 + √5) / 4 < cos (2 * π * a / m)) (h₂ : cos (2 * π * a / m) ≠ 1) :
    ∃ k : ℕ, k.Coprime m ∧ cos (2 * π * (k * a) / m) < -1 / 2 := by
  obtain ⟨a₁, m₁, hcop, ha, hmm⟩ := Nat.exists_coprime a m
  set g := a.gcd m with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right a hm
  have hm₁ : 0 < m₁ := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · rw [h, zero_mul] at hmm; omega
    · exact h
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hm₁R : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
  -- the angle in lowest terms
  have hangle : ∀ k : ℕ, 2 * π * (k * a) / m = 2 * π * (k * a₁) / m₁ := by
    intro k
    rw [ha, hmm]
    push_cast
    field_simp
  have h1' := hangle 1
  simp only [Nat.cast_one, one_mul] at h1'
  rw [h1'] at h₁ h₂
  -- the reduced denominator is at least `11`
  have h11 : 11 ≤ m₁ := by
    by_contra hlt
    push Not at hlt
    by_cases hdvd : m₁ ∣ a₁
    · have h1 : m₁ = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd
      apply h₂
      rw [h1, Nat.cast_one, div_one]
      obtain ⟨t, rfl⟩ := hdvd
      rw [h1, one_mul, mul_comm]
      exact_mod_cast cos_nat_mul_two_pi t
    · have hm₁2 : 2 ≤ m₁ := by
        rcases Nat.lt_or_ge m₁ 2 with h | h
        · exact absurd (by interval_cases m₁; exact one_dvd a₁) hdvd
        · exact h
      have hle := cos_two_pi_div_le hm₁ hdvd
      have hm₁le : (m₁ : ℝ) ≤ 10 := by exact_mod_cast (Nat.lt_succ_iff.1 hlt)
      have hm₁2' : (2 : ℝ) ≤ m₁ := by exact_mod_cast hm₁2
      have : cos (2 * π / m₁) ≤ cos (π / 5) := by
        apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
        · rw [div_le_iff₀ hm₁R]; nlinarith [pi_pos]
        · rw [div_le_div_iff₀ (by norm_num) hm₁R]; nlinarith [pi_pos]
      rw [cos_pi_div_five] at this
      linarith
  obtain ⟨j, hj, hj₁, hj₂⟩ := exists_coprime_middle_third h11
  -- lift the unit `j / a₁` modulo `m₁` to a unit modulo `m`
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero m₁ := ⟨hm₁.ne'⟩
  have hdvd : m₁ ∣ m := ⟨g, by rw [hmm]⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hdvd
    (ZMod.unitOfCoprime j hj * (ZMod.unitOfCoprime a₁ hcop)⁻¹)
  refine ⟨(v : ZMod m).val, ZMod.val_coe_unit_coprime v, ?_⟩
  have hcong : ((((v : ZMod m).val * a₁ : ℕ)) : ZMod m₁) = (j : ZMod m₁) := by
    have hv' : ((ZMod.unitsMap hdvd v : (ZMod m₁)ˣ) : ZMod m₁) = ZMod.cast (v : ZMod m) := rfl
    rw [Nat.cast_mul, ZMod.natCast_val, ← hv', hv, ← ZMod.coe_unitOfCoprime a₁ hcop,
      ← Units.val_mul, inv_mul_cancel_right, ZMod.coe_unitOfCoprime]
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).1 hcong
  rw [hangle]
  have hcos := cos_eq_of_dvd_sub hm₁ (x := ((v : ZMod m).val * a₁ : ℕ)) (y := (j : ℕ))
    ((Nat.modEq_iff_dvd).1 hmod)
  push_cast at hcos
  rw [hcos]
  have hj₁' : (m₁ : ℝ) < 3 * j := by exact_mod_cast hj₁
  have hj₂' : 3 * (j : ℝ) < 2 * m₁ := by exact_mod_cast hj₂
  apply cos_lt_neg_half
  · rw [lt_div_iff₀ hm₁R]; nlinarith [pi_pos]
  · rw [div_lt_div_iff₀ hm₁R (by norm_num)]; nlinarith [pi_pos]

/-- An integer multiple of `2π / m` is, modulo `2π`, a natural multiple. -/
lemma exists_nat_cos_eq_int {m : ℕ} (hm : 0 < m) (N : ℤ) :
    ∃ a : ℕ, cos (2 * π * N / m) = cos (2 * π * a / m) := by
  have hm' : (0 : ℤ) ≤ N % m := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  refine ⟨(N % m).toNat, ?_⟩
  have hcast : (((N % m).toNat : ℕ) : ℝ) = ((N % m : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm']
  rw [hcast]
  exact cos_eq_of_dvd_sub hm (Int.mod_modEq N m).dvd |>.symm

/-- Two rational multiples of `2π` are, modulo `2π`, `2πa/m` and `2πb/m` for a
common denominator `m`. -/
lemma exists_nat_cos_eq (s t : ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ a b : ℕ, cos (2 * π * s) = cos (2 * π * a / m) ∧
      cos (2 * π * t) = cos (2 * π * b / m) := by
  have hm : 0 < s.den * t.den := Nat.mul_pos s.den_pos t.den_pos
  refine ⟨s.den * t.den, hm, ?_⟩
  have hsd : (s.den : ℝ) ≠ 0 := by exact_mod_cast s.den_pos.ne'
  have htd : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_pos.ne'
  obtain ⟨a, ha⟩ := exists_nat_cos_eq_int hm (s.num * t.den)
  obtain ⟨b, hb⟩ := exists_nat_cos_eq_int hm (t.num * s.den)
  refine ⟨a, b, ?_, ?_⟩
  · rw [← ha, Rat.cast_def]
    congr 1
    push_cast
    field_simp
  · rw [← hb, Rat.cast_def]
    congr 1
    push_cast
    field_simp

/-- For `2/3 < x < 3/2` with `x ≠ 1`, one of the apex angles of the isosceles
triangles with sides `1, 1, x` and `x, x, 1` is an irrational multiple of `π`. -/
theorem irrational_apex_angle {x : ℝ} (hx₁ : 2 / 3 < x) (hx₂ : x < 3 / 2) (hx : x ≠ 1) :
    Irrational (2 * arcsin (x / 2) / π) ∨ Irrational (2 * arcsin (1 / (2 * x)) / π) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold Irrational at h1 h2
  rw [not_not] at h1 h2
  obtain ⟨q₁, hq₁⟩ := h1
  obtain ⟨q₂, hq₂⟩ := h2
  have hx0 : 0 < x := by linarith
  set A := arcsin (x / 2) with hA
  set B := arcsin (1 / (2 * x)) with hB
  set y := 1 / (2 * x) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by positivity)]; linarith
  have hsA : sin A = x / 2 := sin_arcsin (by linarith) (by linarith)
  have hsB : sin B = y := sin_arcsin (by linarith) hy1.le
  have hcA : cos A = √(1 - (x / 2) ^ 2) := cos_arcsin _
  have hcB : cos B = √(1 - y ^ 2) := cos_arcsin _
  have hA' : A = 2 * π * ((q₁ / 4 : ℚ) : ℝ) := by
    push_cast; rw [hq₁]; field_simp; ring
  have hB' : B = 2 * π * ((q₂ / 4 : ℚ) : ℝ) := by
    push_cast; rw [hq₂]; field_simp; ring
  have hu : A - B = 2 * π * (((q₁ - q₂) / 4 : ℚ) : ℝ) := by
    rw [hA', hB']; push_cast; ring
  have hv : A + B = 2 * π * (((q₁ + q₂) / 4 : ℚ) : ℝ) := by
    rw [hA', hB']; push_cast; ring
  obtain ⟨m, hm, a, b, ha, hb⟩ := exists_nat_cos_eq ((q₁ - q₂) / 4) ((q₁ + q₂) / 4)
  have hxy : x * y = 1 / 2 := by rw [hy]; field_simp
  have hkey : 2 * cos (2 * π * a / m) - 2 * cos (2 * π * b / m) = 1 := by
    rw [← ha, ← hb, ← hu, ← hv, cos_sub, cos_add, hsA, hsB]
    linear_combination 2 * hxy
  have hbig : (1 + √5) / 4 < cos (2 * π * a / m) := by
    rw [← ha, ← hu, cos_sub, hsA, hsB, hcA, hcB]
    have hP : 0 ≤ √(1 - (x / 2) ^ 2) * √(1 - y ^ 2) := by positivity
    have hsq : (√(1 - (x / 2) ^ 2) * √(1 - y ^ 2)) ^ 2 = (1 - (x / 2) ^ 2) * (1 - y ^ 2) := by
      rw [mul_pow, sq_sqrt (by nlinarith), sq_sqrt (by nlinarith)]
    have h5 : (√5 / 4) ^ 2 < (√(1 - (x / 2) ^ 2) * √(1 - y ^ 2)) ^ 2 := by
      rw [hsq, div_pow, sq_sqrt (by norm_num)]
      have hy₁ : 1 / 3 < y := by rw [hy, lt_div_iff₀ (by positivity)]; linarith
      have hy₂ : y < 3 / 4 := by rw [hy, div_lt_iff₀ (by positivity)]; linarith
      nlinarith [mul_pos (sub_pos.2 hx₁) (sub_pos.2 hx₂), mul_pos (sub_pos.2 hy₁) (sub_pos.2 hy₂)]
    have := lt_of_pow_lt_pow_left₀ 2 hP h5
    have hxy' : x / 2 * y = 1 / 4 := by linear_combination hxy / 2
    linarith
  have hne : cos (2 * π * a / m) ≠ 1 := by
    rw [← ha, ← hu]
    intro h1
    have hAb := neg_pi_div_two_le_arcsin (x / 2)
    have hAt := arcsin_le_pi_div_two (x / 2)
    have hBb := neg_pi_div_two_le_arcsin y
    have hBt := arcsin_le_pi_div_two y
    have h0 := (cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) (by linarith [pi_pos])).1 h1
    have hAB : A = B := by linarith
    have : x / 2 = y := by rw [← hsA, ← hsB, hAB]
    have hx2 : x * x = 1 := by
      have h' : x / 2 * (2 * x) = y * (2 * x) := by rw [this]
      rw [hy, div_mul_cancel₀ _ (by positivity)] at h'
      linarith
    have hfac : (x - 1) * (x + 1) = 0 := by linear_combination hx2
    rcases mul_eq_zero.1 hfac with h | h
    · exact hx (by linarith)
    · linarith
  obtain ⟨k, hk, hlt⟩ := exists_coprime_cos_lt hm hbig hne
  have := two_cos_sub_two_cos_of_coprime hm hkey hk
  have := neg_one_le_cos (2 * π * (k * b) / m)
  linarith

end Erdos173

end
