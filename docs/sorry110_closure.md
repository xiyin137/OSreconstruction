# Closure of `sorry:110`

## Summary

The original blocker around
`wick_rotated_kernel_mul_zeroDiagonal_integrable`
has been resolved in its intended internal form.

What is now true:

- the local E0 integrability theorem is proved,
- the forward-tube growth bridge
  `hasForwardTubeGrowth_of_wightman`
  is proved,
- the temporary Universal Projection axiom has been eliminated and replaced by
  a theorem,
- the public `wightman_to_os` API is unchanged.

What still remains external on this path:

- the Vladimirov-Tillmann theorem in
  [`OSReconstruction/SCV/VladimirovTillmann.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean)

So the right headline is:

> `sorry:110` is closed modulo Vladimirov-Tillmann, plus pre-existing
> BHW-layer admitted results (`ae_euclidean_points_in_permutedTube`,
> `bhw_translation_invariant`).

## What was fixed

### 1. The target was corrected

The first version of the growth bridge tried to force an unconditional plain
forward-tube polynomial bound in situations where coincidence singularities are
expected.

That was fixed by separating the growth input into the proposition
`HasForwardTubeGrowth` in
[`Core.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/Core.lean),
with the weighted coincidence-locus bound as the real multi-point target.

This kept the additional analytic burden local to the `R -> E` bridge instead
of changing the core `WightmanFunctions` structure.

### 2. The `n ≤ 1` cases were discharged correctly

The easy low-point cases are now handled separately inside
[`SchwingerAxioms.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean):

- for `n ≤ 1`, the coincidence locus is empty, so the weighted statement
  collapses correctly,
- the one-point case is handled without pretending there is a multi-point
  diagonal singularity.

### 3. The zero-diagonal E0 theorem was proved

The theorem
`wick_rotated_kernel_mul_zeroDiagonal_integrable`
now has no local `sorry`.

The proof uses the corrected growth input plus the abstract reduction theorem
for kernels with finite-order coincidence singularities against
`ZeroDiagonalSchwartz`.

This is the direct closure of the original `sorry:110` site.

### 4. The VT bridge was completed

The key internal bridge
`hasForwardTubeGrowth_of_wightman`
is now proved in
[`SchwingerAxioms.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean).

That proof now:

- packages the spectrum-condition analytic continuation into the VT interface,
- uses the BHW rotation/translation/permutation invariance chain,
- relates forward-cone boundary distance to Euclidean distance from the
  coincidence locus,
- performs the final algebraic denominator collapse.

This was the main missing internal bridge between the VT theorem and the E0
integrability statement.

### 5. The Universal Projection axiom was eliminated

During the bridge proof, a temporary geometric axiom was introduced:

- `exists_universal_time_projection`

That axiom is no longer needed.

The file
[`UniversalProjection.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/UniversalProjection.lean)
now proves the full Ruelle-style statement:

> for any finite configuration in `ℝ^(d+1)`, there exists `c > 0` and
> `R ∈ SO(d+1)` such that all pairwise differences have time projection at
> least `c` times their full norm after applying `R`.

In
[`SchwingerAxioms.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean),
the former private axiom has been replaced by a theorem wrapper around this
proved result.

## Net effect on the trust surface

Before this work, `wick_rotated_kernel_mul_zeroDiagonal_integrable` was a
bare `sorry` — no proof structure, no identified dependencies, no reduction
to known mathematical results. The theorem was simply asserted without proof.

After this work, it depends on:

1. `vladimirov_tillmann` — the Vladimirov-Tillmann tube growth theorem
   (a standard, well-referenced SCV result; stated as an axiom in
   `SCV/VladimirovTillmann.lean`, ~800 lines to prove from the structure
   theorem for tempered distributions + Fourier-Laplace representation)
2. Pre-existing upstream `sorryAx` in the BHW infrastructure
   (`ae_euclidean_points_in_permutedTube`, `bhw_translation_invariant`)
   — these are on the sorry:110 path but were already admitted before
   this work; they are not newly introduced dependencies

Everything else in the chain is fully proved:
- The Universal Projection Lemma (Ruelle's Lemma) — proved in
  `UniversalProjection.lean`, zero sorrys, zero axioms
- The VT-to-growth bridge (`hasForwardTubeGrowth_of_wightman`) — proved
- The integrability theorem itself — proved for all n (n=0, n=1, n≥2)
- The public `wightman_to_os` API — unchanged signature, growth input
  discharged internally

The net effect: one opaque sorry replaced by a single new SCV axiom
(Vladimirov-Tillmann) with a clear path to formalization, plus
pre-existing BHW-layer admitted results that were already in the
dependency graph before this work.

## Public API status

The public theorem surface remains unchanged:

- [`wightman_to_os`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/Main.lean)
  is still exposed without adding a new user-facing growth hypothesis.

The growth input is discharged internally through the now-proved bridge.

## Files materially involved

- [`OSReconstruction/Wightman/Reconstruction/Core.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/Core.lean)
- [`OSReconstruction/Wightman/Reconstruction/UniversalProjection.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/UniversalProjection.lean)
- [`OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean)
- [`OSReconstruction/Wightman/Reconstruction/Main.lean`](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/Main.lean)

## Build verification

The following targets build successfully:

- `lake build OSReconstruction.Wightman.Reconstruction.UniversalProjection`
- `lake build OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms`
- `lake build OSReconstruction.Wightman.Reconstruction.Main`

There are still unrelated `sorry`s elsewhere in the repository, but the
`sorry:110` chain itself is no longer one of them.

## PR assessment

Yes, this now deserves a PR, provided it is described accurately.

The strongest honest framing is:

- closes the `sorry:110` zero-diagonal E0 blocker,
- proves the internal Wightman-to-forward-tube growth bridge,
- formalizes and removes the temporary Universal Projection axiom,
- leaves Vladimirov-Tillmann as the only new external input on this path
  (pre-existing BHW-layer admitted results remain),
- preserves the public reconstruction API.

What should not be claimed:

- not a full elimination of all external analytic input in `R -> E`,
- not a globally `sorry`-free reconstruction theorem,
- not a repo-wide zero-axiom result.
