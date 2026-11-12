# OAI source provenance

Of the 36 Lean modules in this directory, 34 are taken from the `lean/`
directory of [openai/math](https://github.com/openai/math) at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (2026-10-06), at the same paths
under `lean/`. As recorded upstream, they were produced by an internal OpenAI
model, and upstream records their review status as unchecked. They are
distributed under the Apache License 2.0, whose full text is in
[LICENSE](LICENSE). Each was changed for this project, as described below, and
begins with a comment saying so.

The 34 are the import closure of `OAI.Analysis.PlaneSpectrum.Ergodicity`,
`OAI.Analysis.PlaneSpectrum.CircleDecay` and
`OAI.Geometry.PlaneColoring.BorelTransfer`, not the whole upstream library, and
keep their upstream module names. They formalize the inputs this project takes
from OpenAI's
[*The Euclidean plane is not five-colorable*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf):

- the rigidity theorem for wild character laws (Theorem 2.3), as
  `finite_wild_fourier` and `residual_fourier` in
  `Analysis/PlaneSpectrum/Ergodicity.lean`;
- its number-field general position (Lemma 3.4) and algebraic Cayley lemmas, in
  `Analysis/PlaneSpectrum/NumberFields.lean` and
  `Analysis/PlaneSpectrum/Selections.lean`;
- the stationary mean, the projection onto continuous vectors and the
  measurable fields of its transfer from proper to weak measurable colorings
  (Lemma 4.1 and Proposition 4.2), in `MeasureTheory/CompactFactors/`,
  `Analysis/PlaneSpectrum/Representations.lean` and
  `Geometry/PlaneColoring/BorelTransfer.lean`.

The other two modules, `Analysis/PlaneSpectrum/Carrier.lean` and
`Analysis/PlaneSpectrum/Carriers.lean`, are new in this repository and are not
part of openai/math. `Carrier.lean` defines the class `Carrier` of carrier
fields and the template property. `Carriers.lean` defines the two carriers
used, `algebraicCarrier` and `carrierOf x h`. It contains upstream code:
`algebraic_complex_iff_coordinates` and the countability proof of
`algebraicCarrier` are moved from upstream's
`Analysis/PlaneSpectrum/Basic.lean`, and `templateProperty_algebraic` adapts
the proof of upstream's `uniform_selection` in
`Analysis/PlaneSpectrum/Selections.lean`.

Three files of the proof development also adapt upstream code, and begin with a
comment saying so:

- `Erdos173/Template/CayleyEscape.lean` generalizes the algebraic Cayley
  section of upstream's `Analysis/PlaneSpectrum/NumberFields.lean` from `ℚ` to
  a base field `K`, keeping its names and following its proofs;
- `Erdos173/Transfer/LabelModel.lean` adapts the label model of upstream's
  `Analysis/PlaneSpectrum/Representations.lean` from proper colorings to
  triangle avoidance;
- `Erdos173/Transfer/Sample.lean` adapts the projected color vectors of
  upstream's `Geometry/PlaneColoring/BorelTransfer.lean` to the projected sign.

## Changes

Upstream pins Lean `v4.34.1` and Mathlib commit `d13f23b`. This project pins
Lean and Mathlib `v4.35.0`. The 34 modules were changed in two ways.

*Porting.* All 34 use the module system: each begins with `module`, imports
with `public import`, and exposes its definitions with
`@[expose] public section`. The nine that imported all of Mathlib import the
Mathlib modules they use instead, and 14 others import Mathlib modules they use
but no longer see, because a module sees only what its imports export. The
port changed these proofs and statements:

- Two `measurable_const.piecewise` steps became `Measurable.ite`, in
  `MeasureTheory/CompactFactors/Kernels.lean` and
  `MeasureTheory/CompactFactors/AlgebraModels.lean`.
- `Analysis/PlaneSpectrum/SpectralMeasure.lean` raises
  `synthInstance.maxHeartbeats` to 80000 for `adjoin_comm`. This is the only
  option added.
- `Analysis/PlaneSpectrum/Representations.lean` uses `lipschitzWith` in place
  of a deprecated name.
- The statements of `wild_line_average_zero`
  (`Analysis/PlaneSpectrum/Multipliers.lean`) and `wild_line_average_re_zero`
  (`Analysis/PlaneSpectrum/FourierTests.lean`) pass the bound `B` explicitly.
- `pickSupport` in `Geometry/PlaneColoring/BorelTransfer.lean` is no longer
  `private`, since an exposed definition uses it, and one `measurable_const`
  there names its point explicitly.
- One `first | rfl | …` in `Analysis/PlaneSpectrum/CircleDecay.lean` lost its
  unused `rfl` alternative.

*Generalization.* Upstream fixes its carrier, `E := algebraicClosure ℚ ℂ`. The
modules that depend on it take a `[Carrier]` argument instead, and the
declarations that do not use it omit the argument. `E`, `F` (and `AF` in
`Analysis/PlaneSpectrum/InvariantMean.lean`) are the carrier's fields, and `K`
is its unit circle. Each use of algebraicity is replaced by a consequence of the
carrier's properties: closure under field operations, `i ∈ E`, real and
imaginary parts, roots, square roots, `‖z‖ ∈ F`, and countability. In
particular:

- `algebraic_norm` in `Geometry/PlaneColoring/BorelTransfer.lean` states
  `(‖z‖ : ℂ) ∈ E` in place of `IsAlgebraic ℚ (‖z‖ : ℂ)`.
- `algebraic_complex_iff_coordinates` moved from
  `Analysis/PlaneSpectrum/Basic.lean` to the new `Carriers.lean`, where its two
  `first | rfl | …` alternatives became their second branch.
- `cover_mass_positive` in `Analysis/PlaneSpectrum/RadialEnergy.lean` obtains
  its uniform selection from the template property, through the new
  `uniform_selection_of_template` in `Analysis/PlaneSpectrum/Selections.lean`,
  instead of from number-field general position.

Declaration names, statements and proof structure are otherwise upstream's,
with `[Carrier]` added. The upstream docstrings still refer to the algebraic
numbers where `E` is now any carrier field. No `sorry` or `axiom` was added.
