module

public import Erdos173.Measurable.Density
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.Order.IntermediateValue

/-!
# A set with density points of both kinds has a boundary point

Let `A ⊆ ℂ` be measurable, with a point `a` at which `Aᶜ` has density zero and a
point `b` at which `A` has density zero. Then at some point `z` neither `A` nor
`Aᶜ` has density zero.

For a small side `s`, the axis-parallel square of side `s` at `a` is mostly in
`A` and the one at `b` mostly in `Aᶜ`. The measure of `A` in a square of fixed
side is continuous in its position, so some square between them is balanced:
half of it lies in `A`. The four half-side quadrants of a balanced square
average one half, so one of them is at least half in `A` and one at least half
in `Aᶜ`; sliding a half-side square between them inside the parent gives a
balanced half-side subsquare. The nested balanced squares shrink to a point
`z`, and each lies in the disk of radius twice its side about `z`, so both `A`
and `Aᶜ` have measure at least `ρ² / 8` in disks `B(z, ρ)` of arbitrarily small
radius.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open MeasureTheory Metric Set Filter Topology
open scoped symmDiff

/-- The closed axis-parallel square with lower-left corner `p` and side `s`. -/
def square (p : ℂ) (s : ℝ) : Set ℂ :=
  {z | p.re ≤ z.re ∧ z.re ≤ p.re + s ∧ p.im ≤ z.im ∧ z.im ≤ p.im + s}

/-- A square of nonnegative side contains its corner. -/
lemma mem_square_self (p : ℂ) {s : ℝ} (hs : 0 ≤ s) : p ∈ square p s :=
  ⟨le_rfl, by linarith, le_rfl, by linarith⟩

/-- The square is a product of intervals in the coordinates `(re, im)`. -/
lemma square_eq_preimage (p : ℂ) (s : ℝ) :
    square p s = Complex.measurableEquivRealProd ⁻¹'
      (Icc p.re (p.re + s) ×ˢ Icc p.im (p.im + s)) := by
  ext z
  simp [square, Complex.measurableEquivRealProd]
  tauto

/-- A square of side `s` has area `s²`. -/
lemma volume_square (p : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    volume (square p s) = ENNReal.ofReal (s ^ 2) := by
  rw [square_eq_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

/-- Squares are closed. -/
lemma isClosed_square (p : ℂ) (s : ℝ) : IsClosed (square p s) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

/-- Squares are convex. -/
lemma convex_square (p : ℂ) (s : ℝ) : Convex ℝ (square p s) := by
  have : square p s = Complex.reLm ⁻¹' Icc p.re (p.re + s) ∩
      Complex.imLm ⁻¹' Icc p.im (p.im + s) := by
    ext z
    simp [square]
    tauto
  rw [this]
  exact ((convex_Icc _ _).linear_preimage _).inter ((convex_Icc _ _).linear_preimage _)

/-- A square containing `z` lies in the closed disk about `z` of radius twice its
side. -/
lemma square_subset_closedBall {p z : ℂ} {s : ℝ} (hz : z ∈ square p s) :
    square p s ⊆ closedBall z (2 * s) := by
  rintro w ⟨h1, h2, h3, h4⟩
  obtain ⟨g1, g2, g3, g4⟩ := hz
  rw [mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  have hre : |w.re - z.re| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  have him : |w.im - z.im| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- Squares are compact. -/
lemma isCompact_square (p : ℂ) (s : ℝ) : IsCompact (square p s) := by
  rcases (square p s).eq_empty_or_nonempty with he | ⟨z, hz⟩
  · rw [he]
    exact isCompact_empty
  · exact Metric.isCompact_of_isClosed_isBounded (isClosed_square p s)
      (isBounded_closedBall.subset (square_subset_closedBall hz))

/-- Squares have finite area. -/
lemma volume_square_ne_top (p : ℂ) (s : ℝ) : volume (square p s) ≠ ⊤ :=
  (isCompact_square p s).measure_lt_top.ne

/-- The part of any set inside a square has finite area. -/
lemma volume_inter_square_ne_top (K : Set ℂ) (p : ℂ) (s : ℝ) :
    volume (K ∩ square p s) ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_square_ne_top p s) (measure_mono inter_subset_right)

/-- The square at `p` is the translate by `p` of the square at `0`. -/
lemma square_eq_preimage_sub (p : ℂ) (s : ℝ) :
    square p s = (fun z => z - p) ⁻¹' square 0 s := by
  ext z
  simp only [square, mem_ofPred_eq, mem_preimage, Complex.sub_re, Complex.sub_im,
    Complex.zero_re, Complex.zero_im, zero_add]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Translating a square moves it continuously in measure. -/
lemma tendsto_volume_square_symmDiff (s : ℝ) (p₀ : ℂ) :
    Tendsto (fun p => volume (square p s ∆ square p₀ s)) (𝓝 p₀) (𝓝 0) := by
  let f : ℂ → C(ℂ, ℂ) := fun p => ⟨fun z => z - p, by fun_prop⟩
  have hf : Continuous f :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.sub continuous_fst)
  have h := tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume)
    (s := square 0 s) (hf.tendsto p₀)
    (Eventually.of_forall fun p => measurePreserving_sub_right volume p)
    (measurePreserving_sub_right volume p₀) (isClosed_square 0 s).measurableSet.nullMeasurableSet
    (volume_square_ne_top 0 s)
  convert h using 3 with p
  rw [square_eq_preimage_sub p, square_eq_preimage_sub p₀]
  rfl

/-- The measure of `A ∩ X` moves by at most the measure of `X ∆ Y` when `X` is
replaced by `Y`. -/
lemma abs_sub_toReal_le {A X Y : Set ℂ} (hX : volume X ≠ ⊤) (hY : volume Y ≠ ⊤) :
    |(volume (A ∩ X)).toReal - (volume (A ∩ Y)).toReal| ≤ (volume (X ∆ Y)).toReal := by
  have hXY : volume (X ∆ Y) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hX, hY⟩)
    ((measure_mono symmDiff_subset_union).trans (measure_union_le _ _))
  have hAX : volume (A ∩ X) ≠ ⊤ := ne_top_of_le_ne_top hX (measure_mono inter_subset_right)
  have hAY : volume (A ∩ Y) ≠ ⊤ := ne_top_of_le_ne_top hY (measure_mono inter_subset_right)
  have key : ∀ X Y : Set ℂ, volume (A ∩ X) ≤ volume (A ∩ Y) + volume (X ∆ Y) := by
    intro X Y
    calc volume (A ∩ X) ≤ volume ((A ∩ Y) ∪ (X ∆ Y)) := by
          refine measure_mono fun z ⟨hzA, hzX⟩ => ?_
          by_cases hzY : z ∈ Y
          · exact Or.inl ⟨hzA, hzY⟩
          · exact Or.inr (mem_symmDiff.2 (Or.inl ⟨hzX, hzY⟩))
      _ ≤ _ := measure_union_le _ _
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAY, hXY⟩) (key X Y)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAX, hXY⟩)
    ((key Y X).trans_eq (by rw [symmDiff_comm]))
  rw [ENNReal.toReal_add hAY hXY] at h1
  rw [ENNReal.toReal_add hAX hXY] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The measure of a set inside a square of fixed side is continuous in the
square's position. -/
lemma continuous_volume_inter_square (A : Set ℂ) (s : ℝ) :
    Continuous fun p => (volume (A ∩ square p s)).toReal := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun p => (volume (square p s ∆ square p₀ s)).toReal)
    (fun _ => dist_nonneg) (fun p => ?_) ?_
  · rw [Real.dist_eq]
    exact abs_sub_toReal_le (volume_square_ne_top p s) (volume_square_ne_top p₀ s)
  · have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_volume_square_symmDiff s p₀)
    exact this

/-- A square of side `s` splits into its parts in `A` and in `Aᶜ`, of total
area `s²`. -/
lemma toReal_inter_add_compl {A : Set ℂ} (hA : MeasurableSet A) (p : ℂ) {s : ℝ}
    (hs : 0 ≤ s) :
    (volume (A ∩ square p s)).toReal + (volume (Aᶜ ∩ square p s)).toReal = s ^ 2 := by
  rw [← ENNReal.toReal_add (volume_inter_square_ne_top _ _ _) (volume_inter_square_ne_top _ _ _),
    inter_comm A, inter_comm Aᶜ, ← sdiff_eq, measure_inter_add_sdiff _ hA, volume_square p hs,
    ENNReal.toReal_ofReal (by positivity)]

/-- Between a square at least half in `A` and one at most half in `A`, some square
on the segment joining their corners is exactly half in `A`. -/
lemma exists_balanced_mem_segment (A : Set ℂ) (s : ℝ) {q₁ q₂ : ℂ}
    (h₁ : (volume (Aᶜ ∩ square q₁ s)).toReal ≤ (volume (A ∩ square q₁ s)).toReal)
    (h₂ : (volume (A ∩ square q₂ s)).toReal ≤ (volume (Aᶜ ∩ square q₂ s)).toReal) :
    ∃ q ∈ segment ℝ q₁ q₂,
      (volume (A ∩ square q s)).toReal = (volume (Aᶜ ∩ square q s)).toReal := by
  set g : ℂ → ℝ := fun q => (volume (A ∩ square q s)).toReal - (volume (Aᶜ ∩ square q s)).toReal
    with hg
  have hgc : Continuous g :=
    (continuous_volume_inter_square A s).sub (continuous_volume_inter_square Aᶜ s)
  obtain ⟨q, hq, hq0⟩ := (convex_segment q₁ q₂).isPreconnected.intermediate_value
    (right_mem_segment ℝ q₁ q₂) (left_mem_segment ℝ q₁ q₂) hgc.continuousOn
    (show (0 : ℝ) ∈ Icc (g q₂) (g q₁) from
      ⟨by simp only [hg]; linarith, by simp only [hg]; linarith⟩)
  exact ⟨q, hq, by simp only [hg] at hq0; linarith⟩

/-- A balanced square has a balanced half-side subsquare. -/
lemma exists_balanced_subsquare {A : Set ℂ} (hA : MeasurableSet A) {p : ℂ} {s : ℝ}
    (hs : 0 ≤ s)
    (h : (volume (A ∩ square p s)).toReal = (volume (Aᶜ ∩ square p s)).toReal) :
    ∃ q, square q (s / 2) ⊆ square p s ∧
      (volume (A ∩ square q (s / 2))).toReal = (volume (Aᶜ ∩ square q (s / 2))).toReal := by
  set t := s / 2 with ht
  have ht0 : 0 ≤ t := by positivity
  set c₁ := p
  set c₂ := p + (t : ℂ)
  set c₃ := p + (t : ℂ) * Complex.I
  set c₄ := p + (t : ℂ) + (t : ℂ) * Complex.I
  have hcorner : ∀ c ∈ ({c₁, c₂, c₃, c₄} : Set ℂ), c ∈ square p t := by
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro c (rfl | rfl | rfl | rfl) <;>
      simp [c₂, c₃, c₄, square, ht0]
  have hcov : square p s ⊆ square c₁ t ∪ square c₂ t ∪ square c₃ t ∪ square c₄ t := by
    rintro z ⟨h1, h2, h3, h4⟩
    simp only [mem_union, square, mem_ofPred_eq, c₁, c₂, c₃, c₄, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    rcases le_total z.re (p.re + t) with hr | hr <;>
      rcases le_total z.im (p.im + t) with hi | hi
    · exact Or.inl (Or.inl (Or.inl ⟨h1, hr, h3, hi⟩))
    · exact Or.inl (Or.inr ⟨h1, hr, by linarith, by linarith⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨hr, by linarith, h3, hi⟩))
    · exact Or.inr ⟨hr, by linarith, hi, by linarith⟩
  have hsub : ∀ K : Set ℂ, (volume (K ∩ square p s)).toReal ≤
      (volume (K ∩ square c₁ t)).toReal + (volume (K ∩ square c₂ t)).toReal +
        (volume (K ∩ square c₃ t)).toReal + (volume (K ∩ square c₄ t)).toReal := by
    intro K
    have hf := fun c => volume_inter_square_ne_top K c t
    have h12 := ENNReal.add_ne_top.2 ⟨hf c₁, hf c₂⟩
    have h123 := ENNReal.add_ne_top.2 ⟨h12, hf c₃⟩
    rw [← ENNReal.toReal_add (hf _) (hf _), ← ENNReal.toReal_add h12 (hf _),
      ← ENNReal.toReal_add h123 (hf _)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h123, hf c₄⟩) ?_
    calc volume (K ∩ square p s)
        ≤ volume ((K ∩ square c₁ t) ∪ (K ∩ square c₂ t) ∪ (K ∩ square c₃ t) ∪
            (K ∩ square c₄ t)) := by
          refine measure_mono fun z ⟨hzK, hz⟩ => ?_
          rcases hcov hz with ((h | h) | h) | h
          · exact Or.inl (Or.inl (Or.inl ⟨hzK, h⟩))
          · exact Or.inl (Or.inl (Or.inr ⟨hzK, h⟩))
          · exact Or.inl (Or.inr ⟨hzK, h⟩)
          · exact Or.inr ⟨hzK, h⟩
      _ ≤ _ := by
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          exact measure_union_le _ _
  have hsumA := hsub A
  have hsumB := hsub Aᶜ
  have hbig := toReal_inter_add_compl hA p hs
  have hq := fun c => toReal_inter_add_compl hA c ht0
  have hts : s ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
  -- one quadrant is at least half in `A`, one at least half in `Aᶜ`
  have hex₁ : ∃ c ∈ ({c₁, c₂, c₃, c₄} : Set ℂ),
      (volume (Aᶜ ∩ square c t)).toReal ≤ (volume (A ∩ square c t)).toReal := by
    by_contra hno
    push Not at hno
    have e1 := hno c₁ (by simp)
    have e2 := hno c₂ (by simp)
    have e3 := hno c₃ (by simp)
    have e4 := hno c₄ (by simp)
    linarith [hq c₁, hq c₂, hq c₃, hq c₄]
  have hex₂ : ∃ c ∈ ({c₁, c₂, c₃, c₄} : Set ℂ),
      (volume (A ∩ square c t)).toReal ≤ (volume (Aᶜ ∩ square c t)).toReal := by
    by_contra hno
    push Not at hno
    have e1 := hno c₁ (by simp)
    have e2 := hno c₂ (by simp)
    have e3 := hno c₃ (by simp)
    have e4 := hno c₄ (by simp)
    linarith [hq c₁, hq c₂, hq c₃, hq c₄]
  obtain ⟨d₁, hd₁, hle₁⟩ := hex₁
  obtain ⟨d₂, hd₂, hle₂⟩ := hex₂
  obtain ⟨q, hqseg, hqbal⟩ := exists_balanced_mem_segment A t hle₁ hle₂
  have hqmem : q ∈ square p t :=
    (convex_square p t).segment_subset (hcorner d₁ hd₁) (hcorner d₂ hd₂) hqseg
  refine ⟨q, ?_, hqbal⟩
  obtain ⟨g1, g2, g3, g4⟩ := hqmem
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- If the complement of a measurable set `A` has density zero at some point and
`A` has density zero at another, then at some point neither has density zero. -/
theorem exists_not_densityZero {A : Set ℂ} (hA : MeasurableSet A) {a b : ℂ}
    (ha : DensityZero Aᶜ a) (hb : DensityZero A b) :
    ∃ z, ¬ DensityZero A z ∧ ¬ DensityZero Aᶜ z := by
  -- a square containing a point where `K` has density zero has little of `K`
  have hsmall : ∀ (K : Set ℂ) (x : ℂ) (δ : ℝ),
      (∀ ρ, 0 < ρ → ρ < δ → volume (K ∩ closedBall x ρ) ≤ ENNReal.ofReal (1 / 16 * ρ ^ 2)) →
      ∀ (q : ℂ) (t : ℝ), 0 < t → 2 * t < δ → x ∈ square q t →
        (volume (K ∩ square q t)).toReal ≤ t ^ 2 / 4 := by
    intro K x δ hK q t ht htδ hx
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc volume (K ∩ square q t) ≤ volume (K ∩ closedBall x (2 * t)) :=
          measure_mono (inter_subset_inter_right _ (square_subset_closedBall hx))
      _ ≤ ENNReal.ofReal (1 / 16 * (2 * t) ^ 2) := hK _ (by positivity) htδ
      _ = ENNReal.ofReal (t ^ 2 / 4) := by congr 1; ring
  -- a first balanced square
  obtain ⟨δa, hδa, ha'⟩ := ha (1 / 16) (by norm_num)
  obtain ⟨δb, hδb, hb'⟩ := hb (1 / 16) (by norm_num)
  set s := min δa δb / 4 with hsdef
  have hs : 0 < s := by positivity
  have h2sa : 2 * s < δa := by have := min_le_left δa δb; linarith
  have h2sb : 2 * s < δb := by have := min_le_right δa δb; linarith
  have hla := hsmall Aᶜ a δa ha' a s hs h2sa (mem_square_self a hs.le)
  have hlb := hsmall A b δb hb' b s hs h2sb (mem_square_self b hs.le)
  have hsa := toReal_inter_add_compl hA a hs.le
  have hsb := toReal_inter_add_compl hA b hs.le
  obtain ⟨p₀, -, hp₀⟩ := exists_balanced_mem_segment A s (q₁ := a) (q₂ := b)
    (by nlinarith) (by nlinarith)
  -- nested balanced squares
  have step : ∀ (n : ℕ) (p : ℂ),
      (volume (A ∩ square p (s / 2 ^ n))).toReal = (volume (Aᶜ ∩ square p (s / 2 ^ n))).toReal →
      ∃ q, square q (s / 2 ^ (n + 1)) ⊆ square p (s / 2 ^ n) ∧
        (volume (A ∩ square q (s / 2 ^ (n + 1)))).toReal =
          (volume (Aᶜ ∩ square q (s / 2 ^ (n + 1)))).toReal := by
    intro n p hp
    have := exists_balanced_subsquare hA (by positivity) hp
    rwa [show s / 2 ^ n / 2 = s / 2 ^ (n + 1) by rw [pow_succ]; ring] at this
  choose! next hnext_sub hnext_bal using step
  let seq : ℕ → ℂ := fun n => Nat.rec p₀ (fun n q => next n q) n
  have hseq : ∀ n, (volume (A ∩ square (seq n) (s / 2 ^ n))).toReal =
      (volume (Aᶜ ∩ square (seq n) (s / 2 ^ n))).toReal := by
    intro n
    induction n with
    | zero => simpa [seq] using hp₀
    | succ n ih => exact hnext_bal n _ ih
  have hnest : ∀ n, square (seq (n + 1)) (s / 2 ^ (n + 1)) ⊆ square (seq n) (s / 2 ^ n) :=
    fun n => hnext_sub n _ (hseq n)
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => square (seq n) (s / 2 ^ n)) hnest
    (fun n => ⟨seq n, mem_square_self _ (by positivity)⟩) (isCompact_square _ _)
    (fun n => isClosed_square _ _)
  rw [mem_iInter] at hz
  -- both `A` and `Aᶜ` fill half of every square, so neither has density zero at `z`
  have hnot : ∀ K : Set ℂ, (∀ n, (volume (K ∩ square (seq n) (s / 2 ^ n))).toReal =
      (s / 2 ^ n) ^ 2 / 2) → ¬ DensityZero K z := by
    intro K hK hz0
    obtain ⟨δ, hδ, hzδ⟩ := hz0 (1 / 16) (by norm_num)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (2 * s) by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have hsn : s / 2 ^ n = s * (1 / 2) ^ n := by rw [one_div_pow]; ring
    have hn' : 2 * (s / 2 ^ n) < δ := by
      rw [hsn]
      rw [lt_div_iff₀ (by positivity)] at hn
      linarith
    have hpos : 0 < s / 2 ^ n := by positivity
    have := hsmall K z δ hzδ (seq n) (s / 2 ^ n) hpos hn' (hz n)
    rw [hK n] at this
    nlinarith
  refine ⟨z, hnot A fun n => ?_, hnot Aᶜ fun n => ?_⟩
  · have := toReal_inter_add_compl hA (seq n) (show 0 ≤ s / 2 ^ n by positivity)
    linarith [hseq n]
  · have := toReal_inter_add_compl hA (seq n) (show 0 ≤ s / 2 ^ n by positivity)
    linarith [hseq n]

end Erdos173

end
