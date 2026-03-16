# Reduced BHW Bridge And Numerical Diagnostics

**Date:** 2026-03-16

This note records why the reduced-coordinate BHW theorem surface is being
treated as acceptable for merge, what bridge is intended from the absolute BHW
theorem, and what numerical diagnostics were run.

## Current theorem surface

Mike's PR introduces a reduced-coordinate BHW interface on successive
difference variables `eta_j = z_{j+1} - z_j`.

The new axiom says, in substance:

- start with a reduced holomorphic input on the reduced forward tube,
- assume reduced real Lorentz covariance and the correct reduced boundary
  values coming from the Wightman family,
- conclude existence and uniqueness of a holomorphic extension on the reduced
  permuted extended tube,
- together with complex Lorentz invariance and reduced permutation invariance.

This is the translation-quotiented form of the ordinary
Bargmann-Hall-Wightman theorem.

## Why this is considered acceptable

The project is allowing this as a strategic axiom because it is believed to be
mathematically true and because it factorizes the remaining Route 1 work into a
cleaner quotient-space theorem surface.

The axiom should be understood as a deferred bridge theorem, not as evidence
that the underlying mathematics is new or speculative.

## Intended bridge from absolute BHW

The long-term goal is to derive the reduced theorem from the absolute BHW
theorem plus translation descent machinery.

At a high level, the intended bridge is:

1. Start from the absolute BHW extension theorem on absolute configurations.
2. Use translation invariance to show the absolute extension is constant on
   fibers of the reduced-difference map.
3. Descend the absolute extension to the quotient by uniform translations.
4. Identify the descended domain with the reduced permuted extended tube.
5. Transport Lorentz invariance, permutation invariance, and uniqueness to the
   reduced setting.

The current repo already contains part of this bridge:

- absolute forward-tube input is packaged in
  `AbsoluteForwardTubeInput`,
- descent to reduced holomorphic data is implemented by
  `descendAbsoluteForwardTubeInput`,
- reduced boundary values for the specific spectrum witness are proved in
  `route1ReducedBoundaryValuesFromSpectrumCondition`.

What is still missing is the converse generic bridge:

- either descend the absolute PET extension through translation fibers, or
- lift a generic reduced input back to an absolute BHW input in a way that
  preserves the boundary-value theorem.

That remaining work is formalization-heavy but does not appear to introduce new
mathematical content beyond the absolute BHW theorem plus quotient descent.

## Numerical diagnostics

Numerical tests were run on 2026-03-16 as assertion-level sanity checks of the
reduced-coordinate geometry behind the theorem surface.

The diagnostics stress-tested the following claims in low-dimensional random
samples:

- uniform translations are invisible to `reducedDiffMap`,
- `reducedDiffSection` is a right inverse to `reducedDiffMap`,
- `safeSection` lands in the absolute forward tube whenever the reduced point
  lies in the reduced forward tube,
- the induced reduced permutation action matches absolute permutation followed
  by quotienting,
- permutation composition behaves correctly,
- adjacent transpositions realize the expected `A_(n-1)` root-action formulas,
- functions pulled back from reduced coordinates are automatically translation
  invariant in absolute coordinates,
- random PET-style samples remain consistent under quotienting and permutation.

All of these randomized checks passed.

## Most informative negative test

A separate diagnostic checked the naive lift strategy:

- choose an arbitrary absolute representative of a reduced point,
- evaluate an absolute function there,
- ask whether the resulting value depends only on the reduced point.

This failed exactly as expected unless the absolute function was already
translation invariant. The test therefore supports the claim that quotient
descent is the genuine issue, not a cosmetic implementation detail.

## Limits of the numerical evidence

These diagnostics do **not** prove the reduced BHW theorem.

They do not establish:

- existence of the holomorphic extension,
- edge-of-the-wedge continuation,
- permutation invariance from locality,
- uniqueness by the identity theorem.

What they do establish is narrower and still useful:

- the reduced difference-coordinate machinery is coherent,
- the induced permutation action behaves as intended,
- the basic quotient geometry in the Route 1 refactor is not obviously wrong,
- naive representative-dependent descent is genuinely unsafe without a proved
  translation-invariance bridge.

## Merge interpretation

Under the project's policy on strategically deferred but mathematically
credible lemmas, the new reduced BHW axiom can be accepted as an explicit
quotient-space placeholder.

What should remain documented after merge is:

- this theorem is deferred, not fully formalized,
- the intended future bridge is from absolute BHW plus translation descent,
- the numerical diagnostics support the quotient geometry but are not a proof.
