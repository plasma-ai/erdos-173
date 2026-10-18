# Blueprint: monochromatic triangles in two-colorings of the plane

This document proves, in prose, the four theorems that Comparator checks.
Section 1 states them and derives them from the reduction and from §2; the
later sections follow the Lean development. Each section names the module and
the Lean declarations it describes. The argument is Plasma AI's, apart from
the inputs credited below. GPT-6 Astra in Codex and Claude Opus 5.5 in Claude
Code found it. This document, written by Claude Opus 5.5 in Claude Code from
Plasma AI's unpublished write-up of the proof, is its first public
presentation.

**Conventions.** The plane is `ℂ`. A coloring is `c : ℂ → Fin 2`, with no
regularity unless measurability is stated. A *template* `(0, a, b)` has the
orientation-preserving copies `(p, p + u a, p + u b)`, `|u| = 1`; a copy is
monochromatic (`MonoCopy`) when its vertices have one color. Directions are
`direction t = e^{it}`, `t ∈ Angles = ℝ/2πℤ`, with normalized arc length
`angularMeasure`. A coloring *avoids* a template (`Avoids`) when no copy is
monochromatic, and *weakly avoids* it (`WeaklyAvoids`) when the monochromatic
copies `(p, t)` are null for area times `angularMeasure`. With
`ζ = e^{iπ/3}`, `AvoidsEq c r` and `WeaklyAvoidsEq c r` refer to the
equilateral template `(0, r, r ζ)`. `𝔸` is the field of complex algebraic
numbers. For a carrier `E` (§3), `F` is its real slice, `K` its unit circle,
`D` the compact dual group of `E`, with `E` taken discrete, and `C ⊆ D` the
ordinary characters `j ξ : z ↦ e^{i⟨ξ, z⟩}`, `ξ ∈ ℂ`.

---

## 1. The challenge, the plane and the reduction

`Challenge.lean`, `Solution.lean`, `Erdos173/Statement.lean`,
`Erdos173/Basic.lean`.

- **The statements.** `HasMonochromaticCopy c T` says that some triangle
  congruent to `T` has one color; triangles are Mathlib's `Affine.Triangle`,
  with affinely independent vertices. `erdos_173`,
  `erdos_173.variants.right_triangle` and
  `erdos_173.variants.equilateral_exception` are copied verbatim, apart
  from their category attributes, from `formal-conjectures`;
  `erdos_173.variants.non_equilateral` is not from `formal-conjectures` and
  states that every non-equilateral triangle has a monochromatic copy.
  `Solution.lean` proves them by `erdos_173_proved`, `right_triangle_proved`,
  `equilateral_exception_proved` and `non_equilateral_proved`.
  `Basic.lean` defines the templates of the conventions.

`Erdos173/Reduction/Plane.lean`.

- **Triangles as templates** (`toC`, `side`, `frame`, `apex`,
  `hasMonochromaticCopy_of_monoCopy`). Identify `ℝ²` with `ℂ`. For a
  triangle `T` relabelled by `σ`, with vertices `w_j`, put
  `a = |w₁ - w₀|`, `u₀ = (w₁ - w₀)/a` and `z = (w₂ - w₀)/u₀`. Placing
  `(0, a, z)` by `(p, u)` is the image of `T` under the isometry
  `w ↦ (u/u₀)(w - w₀) + p` (`isometry_pMotion`), so a monochromatic copy of
  the template is a monochromatic congruent copy of `T`.

`Erdos173/Reduction/EightPoint.lean`.

- **The configuration** (`monoCopy_iff`). Lemma 1.3 of Jelínek, Kynčl,
  Stolař and Valla, taken from Erdős, Graham, Montgomery, Rothschild,
  Spencer and Straus. Put `A = 0`, `B = a`, `C = a ζ`, `D = z`, `B' = ζ z`,
  `A' = a + ζ z`, `C' = a ζ̄ + ζ z`, `D' = a - ζ̄ z`. The triples `ABC`,
  `A'B'C'` are equilateral of side `a`, `ADB'`, `A'D'B` of side `|z|`, and
  `BDC'`, `B'D'C` of side `|z - a|`; `BAD`, `CAB'`, `CBD'`, `B'A'D'`,
  `C'A'B`, `C'B'D` are orientation-preserving copies of `(a, 0, z)`. With
  `ζ̄ = 1 - ζ` every incidence is a ring identity.
- **Part (i)** (`not_avoids_of_not_avoidsEq`, `forcing_i`). If an
  equilateral triangle of side `a` is monochromatic, so is a copy of
  `(0, a, z)`: with `ABC` of one color, the first three copies force `D`,
  `B'`, `D'` to the other color, the fourth forces `A'` back, the fifth
  forces `C'` across, and the sixth fails.
- **Part (ii), measure form** (`weaklyAvoids_of_weaklyAvoidsEq`,
  `ae_motion`, `forcing_ii`). If almost no equilateral triangle of side `a`,
  `|z|` or `|z - a|` is monochromatic, almost no copy of `(0, a, z)` is.
  Each equilateral triple of the configuration placed by `(p, u)` is a
  standard copy placed by `(p + u X, u w)` for fixed `X` and unit `w`, a
  change of placement preserving area times arc length. Part (ii) is used
  only in §7.

`Erdos173/FinalAssembly.lean`.

- **Avoided triangles are equilateral** (`avoidsEq_side`,
  `equilateral_of_not_hasMonochromaticCopy`). If `T` has no monochromatic
  copy, part (i) with `z = apex T σ` shows that the side `side T σ` is
  avoided as an equilateral side. Relabelling cyclically, all three sides
  are avoided, and they are equal by `two_scale` (§2).
- **The theorems** (`erdos_173_proved`, `right_triangle_proved`,
  `non_equilateral_proved`). Two triangles without a monochromatic copy are
  equilateral with avoided sides, equal by `two_scale`, so congruent. A
  triangle that is not equilateral therefore has a monochromatic copy; a
  right triangle is not equilateral, since `a² = 2a²` is impossible.

`Erdos173/Reduction/Strips.lean`.

- **The exception** (`stripColor`, `vertical_identity`, `strip_pair`,
  `strip_parity`, `not_hasMonochromaticCopy_strip`). Color by the parity of
  `⌊y/h⌋`, `h = √3/2`. A unit equilateral triangle with consecutive vertical
  gaps `t₁`, `t₂` has `t₁² + t₂² + t₁ t₂ = h²`. Two heights of equal parity
  lie in one strip, closer than `h`, or in strips at least two apart,
  farther than `h`, and both alternatives for three vertices contradict the
  identity.

---

## 2. Two scales and the choice of carrier

`Erdos173/TwoScale.lean`.

- **Rescaling** (`avoidsEq_scale`, `two_scale`). If `c` avoids the
  equilateral sides `r ≠ s`, then `z ↦ c(r z)` avoids `1` and `x = s/r ≠ 1`.
- **The carrier** (`not_avoidsEq_one_and`). For algebraic `x` the carrier is
  `algebraicCarrier`, the algebraic numbers. For transcendental `x` it is
  `carrierOf x h`, the algebraic closure of `ℚ(x)` in `ℂ`, with `h` its
  template property (`templateProperty_fieldOf`, §8). Either contains `x`
  (`ofReal_mem_algebraicCarrier`, `ofReal_mem_carrierOf`).
- **The case split** (`not_avoidsEq_of_mem`). For `x ≥ 3/2` or `x ≤ 2/3`
  the Bessel bound excludes avoidance (`far_exclusion`, §5). For
  `2/3 < x < 3/2` the binary transfer gives a measurable coloring weakly
  avoiding both sides (`binary_transfer`, §6), which the circle argument
  excludes (`circle_exclusion`, §7).

---

## 3. Carriers and the template property

`OAI/Analysis/PlaneSpectrum/Carrier.lean`.

- **Carriers** (`Carrier`, `TemplateProperty`). A carrier is a countable
  subfield `E ⊆ ℂ` with a real slice `F ⊆ ℝ` such that
  `z ∈ E ↔ Re z, Im z ∈ F` (`mem_iff`), every root of a nonzero polynomial
  over `E` lies in `E` (`algClosed`), and the unit circle has the *template
  property* (`template`): for every finite set `Q` of units of `E` there is
  a finite set `S` of units such that, for every choice of `q_s ∈ Q` at each
  `s ∈ S`, both `1` and `i` lie in the `ℚ`-span of the products `q_s s`.
- **Closure properties** (`Carrier.I_mem`, `re_mem`, `im_mem`,
  `ofReal_mem`, `mem_of_pow_mem`, `sqrt_mem`, `norm_mem`, `countable_F`).
  `i ∈ E`; `E` is closed under roots, `F` under square roots of nonnegative
  elements; `|z| ∈ F` for `z ∈ E`; and `F` is countable. With
  `K_pow_surjective` in `OAI/Analysis/PlaneSpectrum/Basic.lean` (`K` is
  divisible) and `dense_E` in `OAI/Geometry/PlaneColoring/BorelTransfer.lean`
  (`E ⊇ ℚ(i)` is dense), these replace the source's uses of algebraicity
  over `ℚ`.
- **The fields of `ℚ(x)`** (`fieldOf`, `realFieldOf`). The algebraic
  closures of `ℚ(x)` in `ℂ` and `ℝ`.

`OAI/Analysis/PlaneSpectrum/Ergodicity.lean`.

**The rigidity theorem.** The input from OpenAI's *The Euclidean plane is
not five-colorable* (23 September 2026) is its rigidity theorem for wild
character laws (Theorem 2.3), in the Lean form below. A finite measure `ν` on
`D` is *wild* (`IsWild`) when it is invariant under the rotations
`d ↦ d(u ·)`, `u ∈ K`, and `ν(C) = 0`.

- **Wild laws are Haar** (`finite_wild_fourier`). A finite wild measure `ν`
  has `∫ d(z) dν(d) = 0` for every nonzero `z ∈ E`.
- **Residual coefficients** (`residual_fourier`). Let `z ↦ T_z` be a unitary
  representation of the discrete group `E` on a complex Hilbert space, and
  `W_k`, `k ∈ K`, unitaries with `W_k T_z = T_{kz} W_k`. If `v` is fixed by
  every `W_k` and orthogonal to the vectors `w` with `T_z w → w` as `z → 0`
  in `ℂ`, then `⟨v, T_z v⟩ = 0` for every nonzero `z ∈ E`.

The source proves both for `E = 𝔸`. The vendored modules take a `[Carrier]`
argument and are otherwise the source's proofs, rechecked over a general
carrier; this blueprint does not reprove them. Every use of algebraicity
becomes a closure property above, except one.

`OAI/Analysis/PlaneSpectrum/Selections.lean`,
`OAI/Analysis/PlaneSpectrum/RadialEnergy.lean`.

- **Where the template property enters** (`cover_mass_positive`,
  `uniform_selection_of_template`). In the source's completion a radial mass
  function `m` on `F`, with `m(0) = 1` and `m(a) m(b) ≤ m(|a - b|)`, is
  shown bounded below near `0` from a finite cover `Q`: every unit `v` has
  some `q ∈ Q` with `m(|2r Re(q v)|) ≥ c > 0`. Its one number-field step,
  a uniform selection, now comes from the template property: take `S` for
  `Q`; each of the finitely many choices `S → Q` expresses `1` and `i`
  rationally, and clearing denominators gives `D, M > 0` such that, for
  every unit `v`, products `k_j = q s` with `q s v` in the cover satisfy
  `∑ a_j k_j = D`, `∑ b_j k_j = D i` and `∑ |a_j| + |b_j| ≤ M` in integers.

`OAI/Analysis/PlaneSpectrum/Carriers.lean`.

- **The algebraic carrier** (`algebraicCarrier`,
  `templateProperty_algebraic`). Its template property is the source's
  Lemma 3.4. In the number field `N` generated by `Q`, `i` and their real
  and imaginary parts, take `S` in rational general position with
  `|S| > |Q|([N : ℚ] - 1)` (`numberField_general_position`). For a choice,
  pigeonhole gives one `q` chosen on a rational basis `T ⊆ S` of `N`
  (`spanning_selection`), and the rational span of the `q t` is `q N`, which
  contains `1` and `i` (`span_mult_rep`).
- **The carrier of `ℚ(x)`** (`carrierOf`). `E = fieldOf x` and
  `F = realFieldOf x` are the algebraic closures of `ℚ(x)` in `ℂ` and `ℝ`.
  `E` is countable, closed under conjugation, which fixes `ℚ(x)`
  (`conj_mem_fieldOf`), and contains `i`, which gives `mem_iff`; roots stay
  in it (`mem_algebraicClosure_of_root`). The template property is a
  hypothesis.

---

## 4. The label model and the radial spectral measure

`Erdos173/Transfer/LabelModel.lean`.

- **Admissible labelings** (`AvoidsSide`, `Admissible`, `Space`,
  `isClosed_admissible`). Fix a set `R` of sides in `E`; `ζ ∈ E` since
  `√3 ∈ F` (`ζ_mem`). The labelings `η : E → Fin 2` with no monochromatic
  `(p, p + u r, p + u r ζ)`, `p ∈ E`, `u ∈ K`, `r ∈ R`, form a compact
  space.
- **The invariant law** (`trans`, `rotate`, `covariance`, `measure`,
  `trans_preserving`, `rotate_preserving`). Translations by `E` and
  rotations by `K` act, rotation by `b` conjugating translation by `a` to
  translation by `b a`. OpenAI's stationary mean (`StationaryMean.measure`)
  gives, from any labeling `ω₀`, a probability measure invariant under both.
  Their Koopman operators give a unitary representation of `E` and
  rotations with `W_b T_a = T_{b a} W_b` (`representation`, `rotation`,
  `rotation_covariance`).
- **The sign** (`sgnAt`, `corr`, `signVector`, `rotation_signVector`,
  `inner_signVector`, `corr_radial`). The sign `s = ±1` of the origin's
  label is a rotation-fixed unit vector with `⟨s, T_z s⟩ = ρ(z)`, the mean
  of `s(0) s(z)`. Points of `E` of equal modulus differ by an element of
  `K`, so `ρ` is radial.
- **Avoided sides** (`sgn_triangle`, `corr_triangle`, `corr_side`). Three
  signs not all equal have `ab + ac + bc = -1`. Integrated over the
  triangles of a side `r ∈ R`, whose three edges have modulus `r`, this
  gives `ρ(r) = -1/3`.

`Erdos173/Transfer/Spectral.lean`.

- **The spectral measure** (`spectralMeasure`,
  `integral_eval_spectralMeasure`, `isWild_restrict_compl`). OpenAI's
  spectral calculus gives a finite measure `μ` on `D` of mass `‖s‖² = 1`
  with `∫ d(a) dμ = ρ(a)`. It is `K`-invariant as `s` is rotation fixed
  (`vectorMeasure_invariant`), and nonzero scalars preserve `C`
  (`scalar_mem_C_iff`), so the restriction of `μ` off `C` is wild.
- **The radial measure** (`exists_radial_measure`). Let `ν` be the pullback
  of `μ` along the measurable embedding `j : ℂ → D`; its mass is at most
  one. For `a ≠ 0`, `finite_wild_fourier` removes the wild part, so
  `ρ(a) = φ(a)` with `φ(w) = ∫ e^{i⟨ξ, w⟩} dν(ξ)` continuous on `ℂ`.
  Radiality gives `φ(u z) = ρ(z)` for `u ∈ K`, hence for every unit `u`
  since `K` is dense in the circle (`circle_closed_induction`). Averaging
  over the circle, where `e^{i⟨ξ, e^{it} z⟩}` averages to real part
  `J₀(|z| |ξ|)` (`re_integral_direction`, from OpenAI's
  `circleSymbol_integral`), gives `ρ(z) = ∫ J₀(|z| |ξ|) dν(ξ)` for nonzero
  `z ∈ E`.

---

## 5. The Bessel bound and far ratios

`Erdos173/Bessel/Basic.lean`, `Erdos173/Bessel/Taylor.lean`,
`Erdos173/Bessel/Series.lean`.

- **Definition** (`besselJ0`, `besselJ0Deriv`, `besselJ0Deriv2`,
  `besselJ0_ode`). `J₀(x) = (2π)⁻¹ ∫₀^{2π} cos(x cos θ) dθ`. Differentiation
  under the integral gives `J₀'` and `J₀''` as angular integrals and
  Bessel's equation `x J₀'' + J₀' + x J₀ = 0`. Write `J₁ = -J₀'`.
- **Series enclosures** (`abs_cos_sub_cosTaylor_le`,
  `abs_sin_sub_sinTaylor_le`, `abs_besselJ0_sub_j0Partial_le`,
  `abs_besselJ0Deriv_add_j1Partial_le`). The Taylor polynomials of `cos` and
  `sin` err by at most the first omitted term, by induction from one step
  (`abs_le_of_abs_deriv_le`). Integrated against the moments
  `∫₀^{2π} cos^{2k} θ dθ = 2π (2k)!/(4^k k!²)`, they show that `J₀` and
  `J₁` differ from the partial sums of their power series by at most the
  first omitted term.

`Erdos173/Bessel/Values.lean`, `Erdos173/Bessel/Shape.lean`.

- **Values** (`besselJ0_three`, …, `besselJ0Deriv_forty_six_fifths`).
  Rational enclosures of `J₀` or `J₁` at `3, 16/5, 7/2, 15/4, 9/2, 24/5,
  11/2, 13/2, 15/2, 17/2, 9, 46/5`, finite rational sums checked by
  `norm_num`.
- **Shape.** `|J₀''| ≤ 1/2`, so `J₁` is `1/2`-Lipschitz and `J₀` is
  `1`-Lipschitz (`abs_besselJ0Deriv2_le_half`, `abs_besselJ0Deriv_sub_le`,
  `abs_besselJ0_sub_le`). `J₁ ≥ 0` on `[0, π]` from the integrand
  (`besselJ0Deriv_nonpos_of_le_pi`). The energy `J₀² + J₁²` has derivative
  `-2 J₁²/t` and is nonincreasing on `(0, ∞)` (`antitoneOn_besselEnergy`,
  `sq_besselJ0_le_energy`).

`Erdos173/Bessel/PairBound.lean`.

- **The pair bound** (`besselJ0_add_lower`). For `x ≥ 3/2` and `t ≥ 0`,
  `J₀(t) + J₀(x t) ≥ -83/125 > -2/3`.
  - `J₁ ≥ 0` on `[0, 15/4]`, beyond `π` from `J₁(3)`, `J₁(7/2)` and the
    Lipschitz bound; likewise `J₀` increases on `[9/2, 61/10]` and decreases
    on `[8, 46/5]`.
  - `J₀ ≥ -0.403` (`le_besselJ0_of_nonneg`): below `15/4` by monotonicity,
    beyond by the energy at `15/4`.
  - `J₀ ≥ -0.261` on `[0, 3]` and `[24/5, ∞)` (`le_besselJ0_of_le_three`,
    `le_besselJ0_of_twenty_four_fifths_le`): by monotonicity, by the
    Lipschitz bound from `J₀(13/2), J₀(15/2) ≥ 1/4` on `[61/10, 8]`, and by
    the energy at `46/5`.
  - If `t` or `x t` lies outside `(3, 24/5)`, the sum is at least
    `-0.261 - 0.403 = -83/125`. Otherwise `3 < t < 16/5` and
    `9/2 < x t < 24/5`, and monotonicity bounds both terms by `-0.321`.

`Erdos173/Transfer/Exclusion.lean`.

- **Far ratios** (`far_exclusion`). If `c` avoids the sides `1` and `x`,
  with `x ∈ E`, its restriction to `E` is admissible for `R = {1, x}`
  (`restrict`), and the radial measure has
  `∫ J₀(|ξ|) dν = ∫ J₀(x |ξ|) dν = -1/3`. The pair bound, at `x` or, for
  `x ≤ 2/3`, at `1/x`, gives `-2/3 ≥ -(83/125) ν(ℂ) ≥ -83/125`, which is
  false.

---

## 6. Binary transfer

`Erdos173/Transfer/Sample.lean`.

- **The quadratic form** (`qform`, `qform_nonneg`, `threshold`,
  `not_mono_of_qform`). `Q(a, b, c) = 1 + ab + ac + bc` is `4` on three
  equal signs and `0` otherwise, and
  `2Q = (1 + a)(1 + b)(1 + c) + (1 - a)(1 - b)(1 - c) ≥ 0` on `[-1, 1]³`.
  Three reals with `Q = 0` are not all given one label by thresholding at
  `0`.
- **The projected sign** (`projected`, `clampSign`, `projected_range`,
  `projected_rotation_fixed`). Let `P` project onto the vectors continuous
  under translation and `g = P s`. The clamp `z ↦ max(-1, min(1, Re z))` is
  `1`-Lipschitz, fixes `s`, and preserves continuous vectors
  (`clampSign_mem`, from OpenAI's `nonlinear_mem`). A `1`-Lipschitz map
  preserving a closed subspace and fixing `s` fixes its projection
  (`projection_fixed_of_contraction`), so `g` is real with values in
  `[-1, 1]`. Likewise rotations fix `g` (`projection_covariance_fixed`).
- **Rigidity** (`projected_corr`). `s - g` is rotation fixed and orthogonal
  to the continuous vectors, so `residual_fourier` and
  `projection_coefficient` give `⟨g, T_z g⟩ = ρ(z)` for nonzero `z ∈ E`.
- **The field** (`field`, `field_inner`, `field_range`). The orbit of `g`
  extends to a continuous field `G(y)`, `y ∈ ℂ` (OpenAI's
  `orbitExtension`), with `⟨G(y), G(y + w)⟩ = ⟨g, G(w)⟩` and each `G(y)`
  real in `[-1, 1]`, by density of `E` and continuity of the clamp.
- **Vanishing of `Q`** (`triangle_sum`, `qform_field_ae`). For `r ∈ R` and
  `u ∈ K`, `1 + ⟨g, G(u r)⟩ + ⟨g, G(u r ζ)⟩ + ⟨g, G(u r ζ - u r)⟩` is `1`
  plus three correlations, `0` by rigidity and `corr_triangle`; by
  continuity it vanishes for every unit `u`. It is the mean of
  `Q(G(p), G(p + u r), G(p + u r ζ))`, so `Q` vanishes almost surely on
  every triangle of side in `R`.
- **A measurable field** (`exists_measurable_qform_field`). OpenAI's
  `exists_measurable_field` represents `G` by a jointly measurable
  `F(y, η)`.

`Erdos173/Transfer/Exclusion.lean`.

- **The transfer** (`binary_transfer`). For each placement, almost every
  `η` makes neither triangle at it monochromatic after thresholding `F`. By
  Tonelli (`Measure.ae_ae_comm`) a single `η` serves almost every placement,
  and `y ↦ threshold (Re F(y, η))` is a measurable coloring weakly avoiding
  the sides `1` and `x`.

---

## 7. Circle exclusion

`Erdos173/Measurable/Density.lean`.

- **Density points** (`DensityZero`, `boundary`, `measurableSet_boundary`,
  `volume_boundary`). A set `X` has density zero at `p` when
  `|X ∩ B(p, ρ)| = o(ρ²)`. The *boundary* of `c` is where neither class has
  density zero. Testing along the radii `1/(k + 1)` makes it measurable, and
  Lebesgue's density theorem (`ae_densityZero`) makes it null.
- **Both classes have area** (`volume_ne_zero_of_weaklyAvoids`). If one
  class were null, almost every copy of a weakly avoided triangle would lie
  in the other.

`Erdos173/Measurable/Apex.lean`.

- **The apex lemma** (`apex_density`). Let `c` weakly avoid `(0, a, b)` and
  let the class `X` of `i` have positive upper density `ε` at `p`. Then for
  no direction `u₀` are `p + u₀ a` and `p + u₀ b` both density points of
  `X`. Otherwise take `h` with `|X ∩ B(p, h)| > ε h²` and the arc `T` of
  directions within `h/L` of `u₀`, `L = |a| + |b| + 1`. For `q ∈ B(p, h)`
  and `u ∈ T`, `q + u a` lies in `B(p + u₀ a, 2h)`, where the other class
  has measure `o(h²)`, and likewise at `b`. So the copies with `q` in the
  class and `u ∈ T` that leave it have measure `o(h²) |T|`, out of at least
  `ε h² |T|`, and the rest are monochromatic.

`Erdos173/Measurable/CircleAlternation.lean`.

- **Alternation** (`circle_alternation`). If `R ⊆ Angles` is measurable and
  `R ∩ (R - π/3)`, `Rᶜ ∩ (Rᶜ - π/3)` and `R ∩ (R - γ)` are null, then `γ/π`
  is rational. The first two give `|R| = |Rᶜ|` and then `R - π/3 = Rᶜ` up to
  null sets; the third likewise gives `R - γ = Rᶜ`. So `R` is invariant
  under the rotation by `γ - π/3`, ergodic for irrational `γ/π`
  (`ergodic_add_left_of_denseRange_zsmul`), and `R` would be null or
  conull.

`Erdos173/Measurable/SelfSupport.lean`.

- **No self-supporting null set** (`eq_empty_of_selfSupporting`). If `S` is
  measurable and null, and every `p ∈ S` sees `S` in positive arc length on
  the circle of radius `r` about it, then `S` is empty. For `p ∈ S`, Fubini
  gives positive measure to the `(t, u)` with `p + r e^{it} ∈ S` and
  `p + r e^{it} + r e^{iu} ∈ S`. But `(t, u) ↦ e^{it} + e^{iu}` pulls null
  sets back to null sets (`angularMeasure_prod_add_mem`): after the shear
  `u ↦ t + u` it is `e^{it}(1 + e^{iu})`; by polar coordinates almost every
  circle about `0` meets a null set in null angle
  (`ae_angularMeasure_mul_mem`); and `|1 + e^{iu}| = 2|cos(u/2)|` lies in a
  null set of radii only for null `u`, as `arccos` is differentiable on
  `(-1, 1)` (`angularMeasure_norm_one_add_mem`).

`Erdos173/Measurable/Cyclotomic.lean`.

- **An irrational apex angle** (`irrational_apex_angle`). For
  `2/3 < x < 3/2`, `x ≠ 1`, let `A = arcsin(x/2)` and `B = arcsin(1/(2x))`,
  half the apex angles of the isosceles triangles with sides `1, 1, x` and
  `x, x, 1`. Then `2A/π` or `2B/π` is irrational.
  - Since `sin A sin B = 1/4`, `u = A - B` and `v = A + B` satisfy
    `2 cos u - 2 cos v = 1`. If both are rational, write them as `2πa/m`
    and `2πb/m` modulo `2π` (`exists_nat_cos_eq`).
  - **Galois step** (`two_cos_sub_two_cos_of_coprime`). With `ω = e^{2πi/m}`,
    `P = X^a + X^{(m-1)a} - X^b - X^{(m-1)b} - 1` has
    `P(ω^k) = 2 cos(ku) - 2 cos(kv) - 1`. All primitive `m`-th roots of
    unity share the cyclotomic minimal polynomial, so `P(ω^k) = 0` for `k`
    coprime to `m`.
  - **Arithmetic step** (`exists_coprime_cos_lt`,
    `exists_coprime_middle_third`). In the window `cos u > cos(π/5)` and
    `cos u ≠ 1`, so `u/2π` has reduced denominator `m₁ ≥ 11`. Some unit `j`
    has `m₁ < 3j < 2m₁`, and some `k` coprime to `m` carries `u` to
    `2πj/m₁`, where the cosine is below `-1/2`; then
    `2 cos(ku) - 2 cos(kv) < 1`.

`Erdos173/Measurable/Boundary.lean`.

- **A boundary point** (`exists_not_densityZero`). Let `A` be measurable,
  `Aᶜ` of density zero at `a` and `A` at `b`. Small squares at `a` and `b`
  are mostly in `A` and in `Aᶜ`, and the measure of `A` in a square moves
  continuously with it, so some square between them is half in `A`
  (`exists_balanced_mem_segment`). Its quadrants average one half, so
  sliding a half-side square from a quadrant at least half in `A` to one
  at least half in `Aᶜ` gives a balanced subsquare
  (`exists_balanced_subsquare`). The nested balanced squares shrink to a
  point at which neither `A` nor `Aᶜ` has density zero.

`Erdos173/Measurable/Circle.lean`.

- **The core** (`circle_core`). No measurable `c` weakly avoids both the
  equilateral template of side `r` and `(0, r, r e^{iγ})` with `γ/π`
  irrational. Let `S` be the boundary, measurable and null; at `p ∈ S` both
  classes have positive upper density. If the circle of radius `r` about
  `p` met `S` in null angle, let `R` be its angles at density points of the
  class `0`; off `R` and the density points of the class `1` lie only
  angles of `S`. The apex lemma with both templates makes the three
  intersections of `circle_alternation` null, which is impossible. So `S`
  is empty by `eq_empty_of_selfSupporting`. But both classes have area,
  hence density points, and `exists_not_densityZero` puts a point in `S`.
- **Ratios near one** (`circle_exclusion`). Let `2/3 < x < 3/2`, `x ≠ 1`,
  and let a measurable `c` weakly avoid the sides `1` and `x`. Take
  `γ = 2A` with leg `1` or `γ = 2B` with leg `x` from
  `irrational_apex_angle`. The isosceles triangle has sides in `{1, x}`, so
  part (ii) of §1 makes `c` weakly avoid it, and `circle_core` applies.

---

## 8. The transcendental template property

`Erdos173/Template/GeneralPosition.lean`, `Erdos173/Template/Density.lean`,
`Erdos173/Template/Algebraic.lean`.

Here `x` is transcendental, `L = fieldOf x`, and functionals are `𝔸`-linear
maps `ℓ : ℂ → 𝔸`.

- **General position** (`GeneralFamily`, `exists_generalFamily`). A set
  meeting the complement of every finite union of proper subspaces contains
  families of every length whose subfamilies of at most `dim V` members are
  independent.
- **Zariski density** (`ZariskiDense`, `ZariskiDense.inter`,
  `ZariskiDense.prod`, `ZariskiDense.exists_of_cover`). A set is dense when
  every polynomial function vanishing on it vanishes. Density survives
  removing a hypersurface and passes to products, and a finite cover of a
  dense set has a dense member.
- **The parameter plane** (`Ω`, `Ω_unit`, `zariskiDense_Ω`). `Ω` is the set
  of `(a, h) ∈ 𝔸²` with `a ≠ 0`, `|a| ≠ 1` and `h = a - 1/ā`; for a unit
  `T`, `a(1 + h/(T - a))` is a unit. `Ω` is dense: for rational `r > 1` it
  contains `(r w, (1 - r⁻²) r w)` for the infinitely many units
  `w = (1 + si)/(1 - si)`, `s ∈ ℚ` (`cayA`), so a polynomial vanishing on
  `Ω` vanishes on infinitely many lines through `0`, then on the lines
  `a = const ≠ 0`, then everywhere, each by a univariate restriction
  (`exists_poly_comp`).

`Erdos173/Template/CayleyEscape.lean`.

- **Cayley escape** (`RealStructure`, `cay`, `cay_finite_avoid`,
  `cay_subspaces_avoid`). Let `R` be a commutative algebra integral over a
  field of characteristic zero, with `ι² = -1` and real elements, closed
  under sums and rational multiples, with units `1 - ι r`. If every
  functional killing all real `r` and `ι r` is zero, then some Cayley
  transform `(1 + ι r)(1 - ι r)⁻¹` escapes any finitely many nonzero
  functionals, or proper subspaces. Integrality makes `(1 - b t)⁻¹` rational
  in `t` with no rational pole (`reciprocal_denominator`); along a Cayley
  curve the first three coefficients annihilate `1`, `b`, `b²`
  (`cayley_annihilation`); and rational lines join escapes from single
  hyperplanes (`finite_hyperplanes_avoid`).

`Erdos173/Template/FunctionField.lean`, `Erdos173/Template/Branches.lean`.

- **Cauchy frames** (`CauchyFrame`, `exists_general_units`,
  `exists_frame`). Let `T` be a unit transcendental over `𝔸` and `N` a
  finite extension of `𝔸(T)` in `ℂ` spanned by its units. Cayley escape
  over `𝔸(T)` (`realStructure_span`) gives units in general position. Take
  `n = |Q|(d - 1) + d` of them as `s_k`, `d = [N : 𝔸(T)]`, the first `d` as
  a basis `b_l`, and clear denominators (`exists_common_denom`):
  `κ(T) q s_k = ∑_l p_{qkl}(T) b_l`, with every `d` rows of nonzero
  determinant.
- **Covered functionals** (`Covered`, `cauchy`, `cover_single`). `ℓ` is
  covered when every unit `u` has `q ∈ Q` with `ℓ(q u) = 0`. Its Cauchy
  transform is `F(a) = (ℓ(b_l/(T - a)))_l`. The cover at
  `s_k a(1 + h/(T - a))` gives a `q` with `ℓ(q s_k) + h ℓ(q s_k/(T - a)) = 0`,
  and divided differences (`divDiff`, `κ_mul_H`) write
  `κ(a) ℓ(q s_k/(T - a))` as `p_{qk}(a) · F(a)` plus a polynomial.
- **Branches** (`Branch`, `cover_branches`, `branch_formula`). Some `d`
  indices `k` share their `q`; inverting their matrix by its adjugate gives
  `δ_β(a) h F(a) = h R_β(a) + S_β(a)` on the branch `β`, with polynomial
  vectors and `δ_β` the determinant.
- **Dense branches** (`double_branch`, `double_coefficients`,
  `dense_branches`). For two dense branches, the cover at `s_k` times two
  multipliers gives an identity on a dense subset of `𝔸⁴`, so one factor
  vanishes identically; comparing coefficients in the independent `h`, `h'`
  gives `S_β = 0` and `δ_γ R_β = δ_β R_γ`.
- **Rationality** (`Δ`, `degBound`, `Gen`, `Tame`, `tame_of_covered`).
  Generically on `Ω`, `Δ(a) F(a)` equals a polynomial vector of degree at
  most `degBound`, with `Δ = ∏_β δ_β`.

`Erdos173/Template/Annihilator.lean`.

- **An annihilating polynomial** (`covered_twist`, `Tame.shift`, `Φ`,
  `Λ_eq_zero`, `ker_Φ_stable`, `exists_annihilator`). Let `A` be the
  `𝔸`-span of the units. For a unit `v`, `z ↦ ℓ(v z)` is covered, with a
  unique generic numerator vector `P_v`, linear in `v`; this gives a linear
  map `Φ` from `A` to a finite-dimensional space. As
  `P_{Tv} = X P_v + Δ (ℓ(v b_l))_l`, if `P_v = 0` but some `ℓ(v b_l) ≠ 0`
  then `P_{T^m v}` has degree at least `m - 1` for all `m`, against
  `degBound`. So `ker Φ` kills `v ↦ (ℓ(v b_l))_l` and is stable under `T`,
  and the characteristic polynomial `p` of `T` on `A / ker Φ` satisfies
  `ℓ(p(T) v b_l) = 0` for `v ∈ A`.

`Erdos173/Template/Cover.lean`.

- **No finite cover** (`cover_impossible`). No `ℓ` with `ℓ(1) = 1` is
  covered by a finite set of units of `N`.
  - **Finite quotient** (`annihilator_of_cover`, `reduce_relation`,
    `good_of_ne_zero`, `finiteDimensional_quotA`). `ℓ(p(T) A) = 0`.
    `A / (T - a) A` is finite-dimensional: a relation over `𝔸(T)`, cleared of
    denominators and of the largest common power of `X - a`, reduces to a
    nontrivial relation over `𝔸`. As `p` splits over `𝔸`, induction on its
    linear factors makes `A / p(T) A` finite-dimensional, hence also the
    quotient `R` of `A` by the ideal `{v : ℓ(v A) = 0}` (`annIdeal`,
    `quotA`), through which `ℓ` factors (`ℓbar`).
  - **Escape** (`quotReal_span`, `cayley_mem`,
    `escape_of_finiteDimensional`). Real elements of `A` and `i` span `A`,
    and Cayley transforms of real elements are units. The functionals
    `x ↦ ℓ(q x)` on `R` are nonzero, as `ℓ(q q̄) = 1`, so Cayley escape in
    `R` gives a unit `u` with `ℓ(q u) ≠ 0` for every `q ∈ Q`.

`Erdos173/Template/Scale.lean`.

- **The scale** (`cayX`, `transcendental_cayX`, `fieldN`,
  `span_units_fieldN`, `cover_impossible_fieldOf`). `T = (x + i)/(x - i)`
  is a unit of `L`, transcendental over `𝔸`, with `𝔸(T) = 𝔸(x)`. For a
  finite set `Q` of units of `L`, `N = 𝔸(T)(Q) ⊆ L` is finite over `𝔸(T)`
  and spanned by monomials in `Q`, which are units. So no `ℓ` with
  `ℓ(1) = 1` has every unit of `L` in some `q⁻¹ ker ℓ`, `q ∈ Q`.

`Erdos173/Template/Transcendental.lean`.

- **Algebraic coefficients** (`algebraic_template`). For every finite `Q`
  there is a finite set `P` of units of `L` such that every choice
  `p ↦ q_p ∈ Q` has `1` in the `𝔸`-span of the `q_p p`. Otherwise the
  choices `K_L → Q` whose span on a finite `P` misses `1` form nonempty
  closed sets, directed in `P`, in a compact space (Tychonoff). A choice in
  all of them has span missing `1`, and a dual functional vanishing on that
  span with `g(1) ≠ 0` (`Submodule.exists_dual_map_eq_bot_of_notMem`),
  normalized, is covered by `Q`, contrary to `cover_impossible_fieldOf`.
- **Rational coefficients** (`templateProperty_fieldOf`). Let `N` be the
  number field of all these coefficients, with `i` and real and imaginary
  parts, and `S` in rational general position with
  `|S| > |Q|([N : ℚ] - 1)` (`numberField_general_position`). The template
  is `P S`: for a choice, pigeonhole in each block `p S`
  (`spanning_selection`) gives `q_p` chosen on a rational basis of `N`, so
  the rational span contains `N q_p p` for every `p`, hence `1` and `i`.

---

## 9. Relation to the original argument

The original argument is Plasma AI's unpublished write-up; this blueprint is
the first public presentation of the proof. The original proves the same
conclusion by the same route: finite forcing, the carrier, the unit template,
Haar rigidity, binary transfer, measurable exclusion and assembly. The Lean
route makes these changes:

- **Scope.** The formal statements use nondegenerate `Affine.Triangle`s,
  as `formal-conjectures` does. The original argument also treats collinear
  triples of distinct points. With part (i) of the configuration (§1), which
  holds for any apex `z`, `erdos_173` implies the collinear case too, but no
  Lean theorem states it.
- **Rigidity.** The original argument adapts OpenAI's prose proof lemma by
  lemma to `F_x(i)`, `F_x` the real closure of `ℚ(x)`, the same field as
  `fieldOf x`. The Lean route generalizes OpenAI's Lean proof over the class
  `Carrier`, whose axioms supply every field operation used, and isolates
  the one number-field step as the template property; the source's
  Lemma 3.4 becomes the template property of `algebraicCarrier`.
- **Far ratios.** The original argument applies the Bessel bound to the
  measurable coloring from the transfer, through Plancherel on disks and a
  weak-star limit. The Lean route applies it to the label model, whose
  radial measure comes from the spectral measure of the sign and
  `finite_wild_fourier` rather than Bochner's theorem.
- **The Bessel bound.** The original argument locates the zeros of `J₁` by
  their spacing (Wirtinger's inequality) and encloses values by the
  alternating series. The Lean route uses Taylor enclosures through the
  angular integral, the sign of `J₁` on `[0, π]`, Lipschitz bounds on `J₁`
  and `J₀` with values at more points, and the energy `J₀² + J₁²`.
- **Binary transfer.** The original argument bounds `P s` by identifying
  the continuous vectors with `L²` of a σ-algebra, making `P` a conditional
  expectation. The Lean route uses only that `P` commutes with a
  `1`-Lipschitz map preserving the subspace. It works with `±1` signs and
  the clamp to `[-1, 1]`, where OpenAI's transfer uses color indicators and
  the clamp to `[0, 1]`, and one Tonelli step serves both sides.
- **Alternation on a circle.** The original argument shows invariance under
  the closed subgroup generated by `2π/3` and `γ - π/3`. The Lean route
  uses ergodicity of the irrational rotation by `γ - π/3`.
- **Self-support.** The original argument applies the area formula with
  Jacobian `r² sin(φ - θ)` on an at most two-to-one map. The Lean route
  uses a shear and polar coordinates.
- **The cyclotomic lemma.** The original argument classifies `x ∈ (1/2, 2)`
  with both apex angles rational, through Ramanujan sums. The Lean route
  proves only the weak form needed, for `2/3 < x < 3/2`, from cyclotomic
  minimal polynomials and a unit `j` with `m < 3j < 2m`.
- **The nonempty boundary.** The original argument shows by Federer's
  criterion for finite perimeter that an empty boundary makes a class null
  or conull. The Lean route finds a boundary point by nested squares of red
  proportion one half.
- **The Cauchy-transform algebra.** The original argument works with
  rational coordinates and a finite-dimensional space of rational vectors.
  The Lean route clears common denominators, inverts branches by
  adjugates, and states rationality as generic agreement with a polynomial
  vector of bounded degree. Density of the parameter plane comes from
  univariate restrictions to lines rather than a change of coordinates.
- **The finite quotient.** The original argument annihilates
  multiplication by `T` on the image of `Φ`, after showing each `Φ(v)` is
  strictly proper. The Lean route shows `ker Φ` is `T`-stable and takes the
  characteristic polynomial on `A / ker Φ`. Finite dimension of
  `A / p(T) A` follows by induction on linear factors, not by filtration
  and the Chinese remainder theorem.
- **Cayley escape.** The original argument escapes by formal derivatives
  on grids of real parameters, both in the quotient and for general position
  over `𝔸(T)`. The Lean route proves one escape lemma for integral algebras
  with rational parameters, adapting the source's algebraic Cayley lemmas.
- **From covers to templates.** The original argument uses König's lemma
  on consistent finite linear systems and compactness of linear systems.
  The Lean route uses compactness of the space of choices and a dual
  functional. The step to rational coefficients is the original's.
