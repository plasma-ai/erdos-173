# Erdős Problem 173: monochromatic triangles in two-colorings of the plane

This Lean 4 project proves the statement of [Erdős Problem 173](https://www.erdosproblems.com/173), as cataloged by Thomas F. Bloom: in every two-coloring of the plane, every triangle with at most one exception has a monochromatic congruent copy. More precisely, we prove

- every non-equilateral triangle has a monochromatic congruent copy in every two-coloring of the plane, and
- no two-coloring of the plane misses the monochromatic equilateral triangles of two different side lengths.

So a two-coloring misses at most one triangle up to congruence, and that triangle is equilateral. The exception can occur: alternating half-open strips of width `√3/2` contain no monochromatic equilateral triangle of side one. The colorings are arbitrary; no measurability is assumed.

To our knowledge, this result is new: it settles the conjecture of Erdős, Graham, Montgomery, Rothschild, Spencer and Straus that every non-equilateral triangle has a monochromatic copy in every two-coloring of the plane, and answers Erdős Problem 173.

The statements are copied verbatim from [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/7db2ea3b91bfbd0ab620215163e6c488bbb916d5/FormalConjectures/ErdosProblems/173.lean): the problem itself (`erdos_173`), Shader's right-triangle theorem (`erdos_173.variants.right_triangle`), and the existence of an exceptional equilateral triangle (`erdos_173.variants.equilateral_exception`).

## Literature and scope

Erdős, Graham, Montgomery, Rothschild, Spencer and Straus, *Euclidean Ramsey theorems, III* (Infinite and Finite Sets, Colloq. Math. Soc. János Bolyai 10, 1975, 559–583), conjectured that every non-equilateral triangle has a monochromatic copy in every two-coloring of the plane, and proved it for several families of triangles. Their Theorem 1 reduces the problem to equilateral triangles: a coloring misses a triangle with sides `a, b, c` exactly when it misses the equilateral triangles of all three sides. Shader, [*All right triangles are Ramsey in E²!*](https://doi.org/10.1016/0097-3165(76)90036-4) (J. Combin. Theory Ser. A 20, 1976), proved the conjecture for right triangles. Jelínek, Kynčl, Stolař and Valla, [*Monochromatic triangles in two-colored plane*](https://doi.org/10.1007/s00493-009-2291-y) (Combinatorica 29, 2009), proved it for colorings whose classes are closed and open, and for polygonal colorings. Currier, Moore and Yip, [*Any two-coloring of the plane contains monochromatic 3-term arithmetic progressions*](https://doi.org/10.1007/s00493-024-00122-2) (Combinatorica 44, 2024), settled further families, including degenerate ones. Graham's survey chapter *Euclidean Ramsey theory* (Handbook of Discrete and Computational Geometry, 3rd edition, 2017) states the problem as Conjecture 11.1.1. Its stronger Conjecture 11.1.2, that a single class of every two-coloring contains every triangle with the possible exception of one equilateral triangle, is not addressed here.

The "to our knowledge" novelty claim reflects a targeted search on October 17, 2026 of Bloom's problem entry (listed as open, with no proof claims) and its discussion thread, the formal-conjectures issue and pull request for the problem, arXiv abstracts on monochromatic triangles and Euclidean Ramsey theory in two-colorings of the plane, the openai/math preprint release, and the web. That search found no proof of the conjecture beyond the special families above.

The step from arbitrary to measurable colorings uses the spectral rigidity theorem of OpenAI's [*The Euclidean plane is not five-colorable*](https://github.com/openai/math/tree/main/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026) (23 September 2026) and its Lean formalization. That theorem is stated over the field of algebraic numbers. This project extends it to the algebraic closure of `ℚ(x)` for every real `x`, which is what makes transcendental ratios of side lengths accessible.

The proof is Plasma AI's, building on OpenAI's spectral rigidity theorem. The [blueprint](blueprint/proof.md) states it in prose, following the Lean development module by module.

## The argument

By the eight-point configuration of Lemma 1.3 of Jelínek et al. (taken from Erdős et al.), a monochromatic equilateral triangle of side `a` forces a monochromatic copy of every triangle with a side `a`. So it suffices to show that no coloring avoids the equilateral triangles of two sides, and after rescaling, of sides `1` and `x ≠ 1`.

**The label model.** Restrict an avoiding coloring to a countable dense subfield `L` of `ℂ` containing `x`, closed under conjugation and relatively algebraically closed. Its labelings of `L` with no monochromatic equilateral triangle of side `1` or `x` form a compact space with an invariant probability measure under translations by `L` and rotations by the unit circle of `L`. The spectral rigidity theorem says that a rotation-invariant law on the characters of `L` that gives no mass to the continuous characters is Haar measure. For the sign `f` of the origin it gives `⟪f, T_z f⟫ = ⟪P f, T_z P f⟫` for `z ≠ 0`, where `P` projects onto the vectors continuous under translation.

**Far ratios.** Three signs that are not all equal have pair products summing to `-1`, so the correlation at distances `1` and `x` is `-1/3`. The radial spectral measure `ν` of `P f` has mass at most one and `∫ J₀(t) dν = ∫ J₀(x t) dν = -1/3`. This is impossible when `x ≥ 3/2` or `x ≤ 2/3`, since then `J₀(t) + J₀(x t) ≥ -83/125 > -2/3`. The bound is proved from rational enclosures of the power series of `J₀` and `J₁` at finitely many points, the Lipschitz bound on `J₁`, and the decreasing energy `J₀² + J₁²`.

**Binary transfer.** For two colors on a triangle, `1 + ab + ac + bc` vanishes exactly on the non-monochromatic sign triples and is nonnegative on `[-1, 1]³`. It involves only pair products, which the projection preserves, so the continuous field `P f`, sampled at one labeling and thresholded at zero, is a measurable coloring with almost no monochromatic equilateral triangle of side `1` or `x`.

**Ratios near one.** For `2/3 < x < 3/2`, `x ≠ 1`, one of the apex angles `γ` of the isosceles triangles with sides `1, 1, x` and `x, x, 1` is an irrational multiple of `π` (a cyclotomic argument); let `r` be its leg. At a point where neither color has density zero, the circle of radius `r` either meets that boundary set in positive length, or its red density points `R` satisfy `R + π/3 = Rᶜ` and `R + γ = Rᶜ` up to null sets, which irrational rotation makes impossible. So the null boundary set supports itself on circles, and the map `(θ, φ) ↦ p + r e^{iθ} + r e^{iφ}` then gives it positive area unless it is empty. It is not empty: nested squares in which red has proportion exactly one half shrink to a point where both colors have positive upper density.

**The carrier.** The rigidity theorem's proof uses the number field structure of the algebraic numbers in exactly one step, a selection of unit vectors whose rational span contains `1` and `i`. Every other step uses only that the carrier is countable, dense, relatively algebraically closed and the complexification of its real slice. The development isolates that step as the *template property* of the carrier. For algebraic `x` the carrier is the field of algebraic numbers, where the source's number-field argument gives the template property. For transcendental `x` it is the algebraic closure `L` of `ℚ(x)`, and the template property is proved here: a finite cover of the unit group of `L` by translated kernels of a functional linear over the algebraic numbers would force rational Cauchy transforms in a finite extension of `ℚ̄((x + i)/(x - i))`, then a finite-dimensional quotient algebra, in which Cayley transforms rule out the cover. König's lemma and number-field general position turn this into the template property with rational coefficients.

## Publication layout

`Challenge.lean` states the three theorems using only Mathlib imports. Its three `sorry` proofs are deliberate: this file contains the statements to audit. `HasMonochromaticCopy` and the three statements are copied verbatim from `formal-conjectures` (`FormalConjectures/ErdosProblems/173.lean`, commit `7db2ea3b91`), with its `ℝ²` notation for `EuclideanSpace ℝ (Fin 2)` declared locally. A triangle there is Mathlib's `Affine.Triangle`, whose vertices are affinely independent, and a copy may be reflected and relabelled. `Solution.lean` imports the proof development and supplies the three theorems. `comparator.json` selects their names and the allowed axioms for [Comparator](https://github.com/leanprover/comparator).

The proof development lives under `Erdos173/`:

- `Statement.lean` repeats `HasMonochromaticCopy` for the development. `Basic.lean` defines colorings of `ℂ`, monochromatic copies of a triangle template `(0, a, b)`, and avoidance and weak (almost everywhere) avoidance.
- `Reduction/` holds the eight-point configuration in its pointwise and measure forms (`EightPoint.lean`), the identification of `ℝ²` with `ℂ` and of triangles with templates (`Plane.lean`), and the strip coloring (`Strips.lean`).
- `Bessel/` proves `J₀(t) + J₀(x t) ≥ -83/125` for `x ≥ 3/2`.
- `Transfer/` builds the label model over a carrier, its radial spectral measure, the exclusion of far ratios, and the binary transfer.
- `Measurable/` proves the circle exclusion of ratios near one for measurable colorings.
- `Template/` proves the template property of the algebraic closure of `ℚ(x)` for transcendental `x`.
- `TwoScale.lean` chooses the carrier and combines the two exclusions, and `FinalAssembly.lean` derives the three theorems.

`OAI/` holds 34 modules from the `lean/` directory of [openai/math](https://github.com/openai/math) at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, under its Apache 2.0 license (`OAI/LICENSE`), and two new modules. The 34 are the import closure of `OAI.Analysis.PlaneSpectrum.Ergodicity`, `OAI.Analysis.PlaneSpectrum.CircleDecay`, and `OAI.Geometry.PlaneColoring.BorelTransfer`, under their upstream module names.

- *Porting.* Their `import Mathlib` headers are replaced by the specific Mathlib modules each file needs, and they are converted to the module system: each file starts with `module`, uses `public import`, and declares `@[expose] public section`. Because a public import does not re-export a dependency's private imports, four files import Mathlib modules they previously reached transitively (`InnerProductSpace.Dual` and `InnerProductSpace.Adjoint`, `CStarAlgebra.GelfandDuality`, `LpSpace.InfiniteSum`). Porting to the toolchain and the module system changed these proofs: two `Measurable.piecewise` steps became `Measurable.ite` (in `CompactFactors/Kernels.lean` and `CompactFactors/AlgebraModels.lean`); `PlaneSpectrum/SpectralMeasure.lean` raises `synthInstance.maxHeartbeats` for `adjoin_comm`; `PlaneSpectrum/Representations.lean` uses `lipschitzWith` for a deprecated name; the statements of `wild_line_average_zero` and `wild_line_average_re_zero` pass the bound `B` explicitly; `pickSupport` in `PlaneColoring/BorelTransfer.lean` is no longer `private`, since an exposed definition uses it; one `measurable_const` there names its point explicitly; two `first | rfl | …` alternatives in `PlaneSpectrum/Basic.lean` and one in `PlaneSpectrum/CircleDecay.lean` lost their unused `rfl`; and three deprecated Mathlib imports were renamed.
- *Generalization.* The source fixes its carrier, `E := algebraicClosure ℚ ℂ`. The new module `PlaneSpectrum/Carrier.lean` defines the class `Carrier` of carrier fields (countable, relatively algebraically closed, the complexification of its real slice `F`, with the template property) and the fields `fieldOf x` and `realFieldOf x`, the algebraic closures of `ℚ(x)` in `ℂ` and `ℝ`. The E-dependent modules take a `[Carrier]` argument: `E`, `F` (and `AF` in `InvariantMean.lean`) are the carrier's fields, `K` is its unit circle, and each use of algebraicity is replaced by the corresponding consequence of the carrier's properties (closure under conjugation, `i ∈ E`, real and imaginary parts, square roots, roots of unit vectors, `‖z‖ ∈ F`, countability). Declaration names, statements and proof structure are otherwise upstream, with `[Carrier]` added. `cover_mass_positive` in `PlaneSpectrum/RadialEnergy.lean` obtains its uniform selection from the template property, through the new `uniform_selection_of_template` in `PlaneSpectrum/Selections.lean`, instead of from number-field general position. The new module `PlaneSpectrum/Carriers.lean` defines the two carriers: `algebraicCarrier`, whose template property follows from the source's number-field general position, and `carrierOf x h`, the algebraic closure of `ℚ(x)` given its template property `h`.

`blueprint/proof.md` states the proof in prose, section by section along the development, naming the Lean declarations of each step, and records where the Lean route departs from the original argument.

`formalization.yaml` records the mathematical sources, authorship, AI use, source fidelity, and review status for a registry submission.

The Lean and Mathlib versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The full build includes `Challenge` and therefore reports its intentional `sorry` warnings. The proofs in `Solution` can also be built directly with `lake build Solution`.
