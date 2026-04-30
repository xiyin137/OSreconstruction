/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2Density
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2BaseStep
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Frontier
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43Codomain
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanPositivity
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslationCore
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReducedExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.HermitianBoundaryPairing
import OSReconstruction.Wightman.Reconstruction.WickRotation.BaseFiberInflation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Bridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45CommonEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45CommonChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BranchPullback
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45TraceMembership
import OSReconstruction.Wightman.Reconstruction.WickRotation.WickRotationBridge

/-!
# Wick Rotation and the OS Bridge Theorems

This module develops the infrastructure for the Osterwalder-Schrader bridge theorems:
- **Theorem R→E** (`wightman_to_os_full`): Wightman functions → honest
  zero-diagonal Euclidean Schwinger family via Wick rotation
- **Theorem E'→R'** (`os_to_wightman_full`): OS axioms + linear growth →
  the checked core Wightman package (the corrected OS II reconstruction surface)

The correction to keep in mind throughout this folder is that Euclidean kernels
may have genuine coincidence singularities. The honest OS-I pairing is therefore
on `ZeroDiagonalSchwartz`, whose infinite-order vanishing cancels finite-order
diagonal poles; only the stronger OS-II reconstruction layer adds the separate
linear-growth input needed for the Euclidean-to-Wightman direction.

Equally important: the Euclidean-to-Wightman direction is hard precisely because
it must start from Schwinger data on `ZeroDiagonalSchwartz` and produce full
tempered Wightman distributions on Schwartz space. Any ambient full-Schwartz
Euclidean extension appearing in this folder is auxiliary/provisional structure,
not the honest starting point of OS reconstruction.

## Module Structure

The implementation is split across several files in the `WickRotation/` subfolder:

- `ForwardTubeLorentz.lean`: Forward tube preservation, Lorentz invariance,
  distributional boundary value covariance
- `BHWExtension.lean`: Bargmann-Hall-Wightman extension definition and properties
- `BHWTranslationCore.lean`: Core forward-tube translation invariance, PET
  connectivity, and forward-tube translate nonemptiness
- `BHWReduced.lean`: Reduced `(n-1)`-difference test-lift and cutoff-independence
  shell for the Route 1 translation refactor
- `BHWReducedExtension.lean`: Reduced BHW extension shell and algebraic pullback
  interface for the Route 1 translation refactor
- `BEGTrigonometric.lean`: small trigonometric estimates used in the
  Bros-Epstein-Glaser path geometry
- `BaseFiberInflation.lean`: forward-tube and Lorentz-action inflation helpers
  for the base-fiber connectedness route
- `BHWTranslation.lean`: Translation invariance proof chain, including the
  Route 1 reduced-coordinate argument, raw and zero-diagonal Schwinger function
  constructions
- `SchwingerTemperedness.lean`: the E0 / zero-diagonal pairing front, including
  the remaining temperedness and continuity gaps on the honest OS-I surface
- `SchwingerAxioms.lean`: the later Euclidean-side axioms after the temperedness
  lane has been split out
- `OSToWightmanSemigroup.lean`: E'→R' OS Hilbert-space semigroup and one-variable
  holomorphic bridge
- `OSToWightmanBase.lean`: shared E'→R' geometry, tube domains, flattened
  witness surfaces, and coordinate helpers
- `OSToWightmanK2Density.lean`: route-independent density/cutoff lemmas on
  `ZeroDiagonalSchwartz` reused by the honest OS `k = 2` lane
- `OSToWightmanK2BaseStep.lean`: proved `k = 2` semigroup / Bochner support
  layer on the OS route
- `K2VI1/Frontier.lean`: isolated OS II VI.1 regularization /
  boundary-identification frontier for the remaining `k = 2` base step
- `OSToWightman.lean`: general E'→R' continuation core and base-step wrappers
- `OSToWightmanBoundaryValues.lean`: boundary-value package, axiom transfer,
  and bridge theorems
- `WickRotationBridge.lean`: one-variable Wick-rotation identities transporting
  `{Re z > 0}` holomorphicity to `{Im u > 0}`

## References

* Osterwalder-Schrader I (1973), "Axioms for Euclidean Green's Functions"
  for the Wick-rotation geometry and the honest zero-diagonal Euclidean side
* Osterwalder-Schrader II (1975), "Axioms for Euclidean Green's Functions II"
  for the corrected reconstruction theorem with linear growth
* Glimm-Jaffe, "Quantum Physics", Chapter 19
-/
