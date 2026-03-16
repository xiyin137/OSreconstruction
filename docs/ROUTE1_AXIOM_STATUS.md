# Route 1 Translation Invariance: Axiom and Sorry Status

**Date**: 2026-03-14
**Branch**: `route1-translation-invariance`

## Summary

The Route 1 refactor replaces the logically false `D(c)` overlap-connectivity
approach to BHW translation invariance with an algebraically clean proof via
reduced difference coordinates. The main theorem `bhw_translation_invariant`
is now proved (no sorry) using the Identity Theorem: the Route 1 extension
agrees with the standard BHW extension on the forward tube, both are
holomorphic on the permuted extended tube, therefore they agree everywhere,
and translation invariance transfers algebraically. The remaining trust surface
is the single reduced-BHW axiom recorded below.

### Current inventory

| File | Item | Type | Status |
|------|------|------|--------|
| `BHWReducedExtension.lean` | `reduced_bargmann_hall_wightman_of_input` | axiom | **Open** |
| `BHWReduced.lean` | `schwartzTranslationClassification` | ~~axiom~~ theorem | **Closed** (wired to `TranslationInvariantSchwartz.lean`) |
| `BHWTranslation.lean:1123` | `isPreconnected_baseFiber` | sorry | **Open** (pre-existing, not Route 1) |

### What was eliminated in this session

| Item | Was | Now |
|------|-----|-----|
| `integral_realDiffCoord_change_variables` | axiom | **theorem** (Fubini + CLE measure-preservation) |
| `realDiffCoordCLE_symm_measurePreserving` | sorry | **theorem** (det = 1 via nilpotent charpoly) |
| integrability in `route1ReducedBoundaryIntegral_eq_absoluteBoundaryIntegral` | sorry | **proved** (`forward_tube_bv_integrable`) |
| `schwartzTranslationClassification` | axiom | **theorem** (wired to `TranslationInvariantSchwartz.lean` zero-mean decomposition) |

---

## Axiom 1: `reduced_bargmann_hall_wightman_of_input`

**File**: `BHWReducedExtension.lean:895`

**Statement**: Given a `Route1ReducedAnalyticInput` (holomorphic on the reduced
forward tube, Lorentz-covariant, with distributional boundary values), produce
a full reduced BHW extension: holomorphic on the reduced permuted extended tube,
agreeing on the reduced forward tube, Lorentz-invariant, permutation-invariant,
and unique by the identity theorem.

**Mathematical content**: This is the **Bargmann-Hall-Wightman theorem executed
natively in `(n-1)` reduced difference coordinates**, where permutations act
via `permOnReducedDiff` (the `A_{n-1}` root system reflection) rather than by
naive coordinate reordering.

### Why the absolute-to-reduced bridge is not yet formalized

The natural idea is: lift the reduced function to absolute coordinates, apply
the existing absolute BHW theorem, then project back. In this codebase, that
bridge is not yet available for two concrete reasons:

1. **The safe section fails geometrically.** The safe section
   `safeSection(eta) = (i*e_0, eta_1 + i*e_0, ...)` maps the reduced forward
   tube into the absolute forward tube. But it does NOT map the reduced PET
   into the absolute PET. Complex Lorentz boosts mix real and imaginary parts;
   the fixed basepoint `i*e_0` will be transformed into `Lambda^{-1}(i*e_0)`
   whose imaginary part generically points outside the forward cone. The safe
   section violently ejects points from the absolute domain of holomorphy.

2. **Arbitrary sections require translation invariance.** If you pick any
   `z in PET_abs` projecting to a given `eta in PET_red`, well-definedness of
   `F_ext_red(eta) := F_ext_abs(z)` requires `F_ext_abs(z + c) = F_ext_abs(z)`
   for all uniform translations `c`. But **this is exactly the theorem Route 1
   was built to prove**. You cannot use absolute translation invariance to
   construct the reduced BHW theorem, because you need the reduced BHW theorem
   to prove absolute translation invariance. Perfect logical ouroboros.

**Current verdict**: a direct converse-lift proof is not yet available in Lean.
The present implementation therefore axiomatizes the reduced theorem natively.
An absolute-to-reduced bridge remains a plausible future route once the PET
translation-descent machinery is formalized.

### Why Option 1 (native porting) is correct and feasible

The Edge of the Wedge theorem and the envelope of holomorphy must be executed
natively in the quotient space. This is exactly what Jost and Streater-Wightman
do mathematically. The existing absolute BHW proof in `BHWExtension.lean`
already contains the heaviest Lean machinery (abstract EotW, analytic
continuation along tubes, Lorentz sweeping).

Porting the permutation flow to reduced coordinates is geometrically cleaner
than the absolute version:

- **Locality is scalar**: In reduced coordinates, physical locality for adjacent
  points `k, k+1` is just `xi_k^2 < 0` (spacelike separation), a single
  scalar condition.

- **Clean swap action**: The adjacent transposition `sigma_k` acts on differences
  via `permOnReducedDiff`: `xi_k -> -xi_k` and `xi_{k+1} -> xi_{k+1} + xi_k`.
  This is the `A_{n-1}` root system reflection.

- **Spectator tubes survive**: When crossing the real Jost boundary
  `Im(xi_k) -> 0`, the neighboring variables transform to
  `Im(xi_{k+1}) + 0 = Im(xi_{k+1})`. They perfectly maintain
  `Im(xi_{j != k}) in V+`. The tubes glue together flawlessly across the
  boundary without knocking spectator variables out of the forward light cone.

### Concrete steps to eliminate this axiom

1. **Reduced Jost points**: Define the real region where `xi_k in R`,
   `xi_k^2 < 0`, and `Im(xi_{j != k}) in V+`.

2. **Boundary agreement**: Prove the reduced Wightman distribution commutes
   across this specific spacelike boundary (follows from the distributional
   boundary values in `Route1ReducedAnalyticInput`).

3. **Reduced Edge of the Wedge**: Apply the existing abstract EotW theorem
   across this boundary to glue `FT_red` and `sigma_k(FT_red)`.

4. **Sweep and induct**: Apply the complex Lorentz group to sweep the glued
   domain, and induct over `S_n` (the permutation group).

**Estimated difficulty**: Substantial but bounded. The abstract EotW and
Lorentz-sweeping machinery already exists; the new work is defining the reduced
Jost geometry and wiring the boundary-value argument.

See also `docs/reduced_bhw_bridge_and_numerics.md` for the intended bridge and
for the numerical diagnostics that support the reduced-coordinate geometry.

---

## ~~Axiom 2~~ (CLOSED): `schwartzTranslationClassification`

**File**: `BHWReduced.lean:51`
**Status**: **Eliminated** — now a theorem, wired to `TranslationInvariantSchwartz.lean`.

**Statement**: Every translation-invariant continuous linear functional on
spacetime Schwartz space `S(R^{d+1})` is a scalar multiple of the Lebesgue
integral.

**How it was proved**: The proof in `TranslationInvariantSchwartz.lean` (~2350
lines) uses a zero-mean decomposition approach rather than the Fourier route
originally anticipated. The key insight is that any Schwartz function can be
decomposed into a zero-mean part (in the range of a line-derivative operator)
plus a multiple of a fixed reference function with integral 1. A
translation-invariant functional vanishes on the zero-mean part, leaving only
the scalar multiple of the integral.

**Role in Route 1**: Ensures the reduced Wightman functional is independent of
the choice of normalized basepoint cutoff `chi`. The theorem
`reducedWightman_eq_of_cutoff` uses it to show that any two cutoffs with
integral 1 produce the same reduced functional.

---

## Sorry: `isPreconnected_baseFiber`

**File**: `BHWTranslation.lean:1120`

**Statement**: The base fiber `{z_0 in C^{d+1} : Im(z_0) in V+ and
(z_0, zeta_1, ..., zeta_m) in PET}` is preconnected.

**Status**: Pre-existing sorry, not introduced by Route 1. This is a geometric
fact about the complex forward cone intersected with Lorentz-orbit constraints.
It is used in the Schwinger function construction downstream of
`bhw_translation_invariant` but does not affect the translation invariance
proof itself.

---

## Strategic Assessment

The Route 1 refactor has achieved its structural goal: **translation invariance
is now proved without any sorry**, using a clean algebraic argument via reduced
difference coordinates and the identity theorem. The remaining technical debt
is quarantined into exactly **one axiom**:

1. **`reduced_bargmann_hall_wightman_of_input`**: The correct reduced-coordinate
   BHW theorem. This is the *only* path forward (the converse-lift alternative
   is logically circular). It requires porting the permutation flow to reduced
   coordinates, which is geometrically cleaner than the absolute version but
   still substantial SCV work.

~~2. **`schwartzTranslationClassification`**: Eliminated — now proved via
zero-mean decomposition in `TranslationInvariantSchwartz.lean`.~~

The sole remaining axiom is mathematically a textbook-level reduced-coordinate
Bargmann-Hall-Wightman statement. It has been successfully isolated from the
downstream theory, with the intended future bridge documented separately. The
project is fully unblocked to proceed with Jost's Theorem, Spin-Statistics,
and Osterwalder-Schrader Positivity.

The Route 1 architecture correctly maps the boundary between what can be proved
algebraically (translation invariance, via difference coordinates and the
identity theorem) and what requires native SCV geometry (the reduced BHW
envelope of holomorphy). All technical debt has been pushed into the right
mathematical corner.
