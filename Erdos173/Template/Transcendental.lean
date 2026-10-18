module

public import Erdos173.Template.Scale
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import OAI.Analysis.PlaneSpectrum.Selections

/-!
# The template property of a transcendental carrier

Let `x` be a real transcendental number and `L` the algebraic closure of `ℚ(x)`
in `ℂ`. There is no finite set `Q` of units of `L` and `𝔸`-linear `ℓ : ℂ → 𝔸` with
`ℓ 1 = 1` such that every unit `u` of `L` has some `q ∈ Q` with `ℓ (q u) = 0`. The
proof reduces such a cover to a finite extension `N` of `𝔸(T)`, `T = (x + i)/(x - i)`,
forces the Cauchy transforms `a ↦ ℓ(b / (T - a))` to be rational, factors `ℓ` through
the finite-dimensional algebra `A / p(T) A`, and there contradicts the cover with
Cayley transforms.

By compactness of the space of choices (König's lemma) a failure of the template
property with algebraic coefficients gives such a cover, and number-field general
position turns algebraic coefficients into rational ones.
-/

@[expose] public section

noncomputable section

namespace Erdos173

open OAI.PlaneFiveColor.Spectral Erdos173.Template Module

/-- Templates with algebraic coefficients: for every finite set `Q` of units of
the carrier there is a finite set `P` of units such that every choice `p ↦ j p ∈ Q`
has `1` in the `𝔸`-span of the products `j p * p`. Otherwise a compactness argument
on the space of choices gives a global choice whose span misses `1`, and a
functional vanishing on that span is covered by `Q`. -/
lemma algebraic_template {x : ℝ} (hx : Transcendental ℚ x) (Q : Finset ℂ)
    (hQ : ∀ q ∈ Q, q ∈ fieldOf x ∧ ‖q‖ = 1) :
    ∃ P : Finset ℂ, (∀ p ∈ P, p ∈ fieldOf x ∧ ‖p‖ = 1) ∧ ∀ j : ℂ → ℂ, (∀ p ∈ P, j p ∈ Q) →
      (1 : ℂ) ∈ Submodule.span 𝔸 ((fun p => j p * p) '' (P : Set ℂ)) := by
  classical
  by_contra! h
  let K := {z : ℂ // z ∈ fieldOf x ∧ ‖z‖ = 1}
  obtain ⟨j₁, hj₁, -⟩ := h {1} (by simp [(fieldOf x).one_mem])
  let q₀ : Q := ⟨j₁ 1, hj₁ 1 (Finset.mem_singleton_self 1)⟩
  let _ : TopologicalSpace Q := ⊥
  have : DiscreteTopology Q := ⟨rfl⟩
  -- the choices on `P` whose span misses `1`
  let C : Finset K → Set (K → Q) := fun P =>
    {f | (1 : ℂ) ∉ Submodule.span 𝔸 ((fun p : K => ((f p : ℂ)) * p) '' (P : Set K))}
  have hC : ∀ P, (C P).Nonempty := by
    intro P
    obtain ⟨j, hjQ, hj⟩ := h (P.image Subtype.val) (by
      intro p hp
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hp
      exact p.property)
    refine ⟨fun p => if hp : (p : ℂ) ∈ P.image Subtype.val then ⟨j p, hjQ p hp⟩ else q₀, ?_⟩
    have he : (fun p : K => (((fun p : K => if hp : (p : ℂ) ∈ P.image Subtype.val then
        (⟨j p, hjQ p hp⟩ : Q) else q₀) p : Q) : ℂ) * p) '' (P : Set K) =
        (fun p => j p * p) '' ((P.image Subtype.val : Finset ℂ) : Set ℂ) := by
      ext y
      simp only [Set.mem_image, Finset.mem_coe, Finset.coe_image]
      constructor
      · rintro ⟨p, hp, rfl⟩
        refine ⟨p, ⟨p, hp, rfl⟩, ?_⟩
        rw [dite_eq_left (Finset.mem_image_of_mem _ hp)]
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        refine ⟨p, hp, ?_⟩
        rw [dite_eq_left (Finset.mem_image_of_mem _ hp)]
    change (1 : ℂ) ∉ _
    rw [he]
    exact hj
  have hCc : ∀ P, IsClosed (C P) := by
    intro P
    let r : (K → Q) → (P → Q) := fun f p => f p
    have hr : Continuous r := continuous_pi fun p => continuous_apply _
    have he : C P = r ⁻¹' {g | (1 : ℂ) ∉ Submodule.span 𝔸
        (Set.range fun p : P => ((g p : ℂ)) * (p : ℂ))} := by
      ext f
      simp only [C, r, Set.mem_ofPred_eq, Set.mem_preimage]
      have : (fun p : K => ((f p : ℂ)) * p) '' (P : Set K) =
          Set.range (fun p : P => ((f p : ℂ)) * (p : ℂ)) := by
        ext y
        simp
      rw [this]
    rw [he]
    exact (isClosed_discrete _).preimage hr
  have hdir : Directed (· ⊇ ·) C := by
    intro P₁ P₂
    refine ⟨P₁ ∪ P₂, fun f hf h1 => hf (Submodule.span_mono (Set.image_mono ?_) h1),
      fun f hf h1 => hf (Submodule.span_mono (Set.image_mono ?_) h1)⟩
    · simp
    · simp
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hC
    (fun P => (hCc P).isCompact) hCc
  rw [Set.mem_iInter] at hf
  -- the span of the global choice misses `1`
  let W := Submodule.span 𝔸 (Set.range fun p : K => ((f p : ℂ)) * p)
  have h1 : (1 : ℂ) ∉ W := by
    intro hW
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hW
    apply hf c.support
    rw [← hc]
    exact Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨p, hp, rfl⟩)
  obtain ⟨g, hg1, hgW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h1 inferInstance
  let ℓ : ℂ →ₗ[𝔸] 𝔸 := (g 1)⁻¹ • g
  have hℓ : ℓ 1 = 1 := by simp [ℓ, inv_mul_cancel₀ hg1]
  obtain ⟨u, hu, hu1, hℓu⟩ := cover_impossible_fieldOf hx hQ ℓ hℓ
  apply hℓu (f ⟨u, hu, hu1⟩) (f ⟨u, hu, hu1⟩).property
  have hgu : g ((f ⟨u, hu, hu1⟩ : ℂ) * u) = 0 := by
    have : g ((f ⟨u, hu, hu1⟩ : ℂ) * u) ∈ W.map g :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨u, hu, hu1⟩, rfl⟩)
    rwa [hgW, Submodule.mem_bot] at this
  simp [ℓ, hgu]

open OAI.EuclideanFiveColor.AlgebraicCayley OAI.EuclideanFiveColor.GeneralPosition in
/-- The unit circle of the algebraic closure of `ℚ(x)` has the template property
when `x` is transcendental. -/
theorem templateProperty_fieldOf {x : ℝ} (hx : Transcendental ℚ x) :
    TemplateProperty (fieldOf x : Set ℂ) := by
  classical
  intro Q hQ
  obtain ⟨P, hP, hPspan⟩ := algebraic_template hx Q hQ
  -- the choice on `P` determined by `L`
  let ext : (P → Q) → ℂ → ℂ := fun L p => if h : p ∈ P then (L ⟨p, h⟩ : ℂ) else 0
  let img : (P → Q) → Finset ℂ := fun L => P.image fun p => ext L p * p
  have hcoef (L : P → Q) : ∃ c : ℂ → 𝔸, ∑ y ∈ img L, (c y : ℂ) * y = 1 := by
    have h := hPspan (ext L) fun p hp => by simp [ext, hp]
    rw [← Finset.coe_image] at h
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp h
    exact ⟨c, hc⟩
  choose c hc using hcoef
  -- a number field containing all coefficients
  let Cset : Finset ℂ := Finset.univ.biUnion fun L => (img L).image fun y => (c L y : ℂ)
  have hCalg : ∀ z ∈ Cset, IsAlgebraic ℚ z := by
    intro z hz
    obtain ⟨L, -, hL⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hL
    exact mem_algebraicClosure_iff.mp (c L y).property
  let Ng := generatedField Cset
  have : FiniteDimensional ℚ Ng := generatedField_finite Cset hCalg
  have hcN (L : P → Q) (y : ℂ) (hy : y ∈ img L) : (c L y : ℂ) ∈ Ng :=
    generatedField_contains Cset _
      (Finset.mem_biUnion.mpr ⟨L, Finset.mem_univ _, Finset.mem_image_of_mem _ hy⟩)
  have hIN : Complex.I ∈ Ng := generatedField_I Cset
  obtain ⟨S₀, hS₀c, hS₀n, hS₀g⟩ := numberField_general_position Ng hIN
    (generatedField_re_closed Cset) (generatedField_im_closed Cset)
    (Q.card * (finrank ℚ Ng - 1) + 1)
  have hNalg (s : Ng) : (s : ℂ) ∈ fieldOf x :=
    mem_fieldOf_of_𝔸 (mem_algebraicClosure_iff.mpr
      (IsAlgebraic.algHom Ng.val (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s)))
  -- the template
  refine ⟨(P ×ˢ S₀).image fun ps => ps.1 * (ps.2 : ℂ), ?_, fun j hj => ?_⟩
  · intro σ hσ
    obtain ⟨⟨p, s⟩, hps, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨hp, hs⟩ := Finset.mem_product.mp hps
    exact ⟨(fieldOf x).mul_mem (hP p hp).1 (hNalg s),
      by rw [norm_mul, (hP p hp).2, hS₀n s hs, one_mul]⟩
  set W := Submodule.span ℚ ((fun s => j s * s) '' ↑((P ×ˢ S₀).image fun ps => ps.1 * (ps.2 : ℂ)))
  have hmemS (p : ℂ) (hp : p ∈ P) (s : Ng) (hs : s ∈ S₀) :
      p * (s : ℂ) ∈ (P ×ˢ S₀).image fun ps => ps.1 * (ps.2 : ℂ) :=
    Finset.mem_image.mpr ⟨(p, s), Finset.mem_product.mpr ⟨hp, hs⟩, rfl⟩
  -- in each block `p S₀` some member of `Q` is chosen on a rational basis
  have hsel (p : P) : ∃ q ∈ Q, ∃ T ⊆ S₀, T.card = finrank ℚ Ng ∧
      Submodule.span ℚ (T : Set Ng) = ⊤ ∧ ∀ s ∈ T, j (p * (s : ℂ)) = q :=
    spanning_selection Q S₀ hS₀g (by omega)
      (fun q s => j (p * (s : ℂ)) = q) fun s hs => ⟨_, hj _ (hmemS p p.2 s hs), rfl⟩
  choose q hq T hTS _hTc hTspan hTj using hsel
  have key (p : P) (a : Ng) : (a : ℂ) * (q p * p) ∈ W := by
    have ha : a ∈ Submodule.span ℚ (T p : Set Ng) := by rw [hTspan p]; trivial
    induction ha using Submodule.span_induction with
    | mem s hs =>
      have he : (s : ℂ) * (q p * p) = j (p * s) * (p * s) := by
        rw [hTj p s hs]
        ring
      rw [he]
      exact Submodule.subset_span ⟨_, Finset.mem_coe.mpr (hmemS p p.2 s (hTS p hs)), rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [show ((a + b : Ng) : ℂ) = a + b from rfl, add_mul]
      exact W.add_mem ha hb
    | smul r a _ ha =>
      rw [show ((r • a : Ng) : ℂ) = r • (a : ℂ) from rfl, smul_mul_assoc]
      exact W.smul_mem r ha
  let L : P → Q := fun p => ⟨q p, hq p⟩
  have hterm (z : ℂ) (hz : z ∈ Ng) (y : ℂ) (hy : y ∈ img L) : z * y ∈ W := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have he : ext L p = q ⟨p, hp⟩ := by simp [ext, hp, L]
    rw [he]
    exact key ⟨p, hp⟩ ⟨z, hz⟩
  have hsum (z : ℂ → ℂ) (hz : ∀ y ∈ img L, z y ∈ Ng) : ∑ y ∈ img L, z y * y ∈ W :=
    W.sum_mem fun y hy => hterm _ (hz y hy) y hy
  refine ⟨?_, ?_⟩
  · rw [← hc L]
    exact hsum _ fun y hy => hcN L y hy
  · have he : ∑ y ∈ img L, (Complex.I * (c L y : ℂ)) * y = Complex.I := by
      conv_rhs => rw [← mul_one Complex.I, ← hc L, Finset.mul_sum]
      simp only [mul_assoc]
    rw [← he]
    exact hsum _ fun y hy => Ng.mul_mem hIN (hcN L y hy)

end Erdos173

end
