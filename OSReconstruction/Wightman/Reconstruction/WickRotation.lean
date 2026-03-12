/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues

/-!
# Wick Rotation and the OS Bridge Theorems

This module develops the infrastructure for the Osterwalder-Schrader bridge theorems:
- **Theorem R→E** (`wightman_to_os_full`): Wightman functions → honest
  zero-diagonal Euclidean Schwinger family via Wick rotation
- **Theorem E'→R'** (`os_to_wightman_full`): OS axioms + linear growth →
  Wightman functions (the corrected OS II reconstruction surface)

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
- `BHWTranslation.lean`: Translation invariance proof chain, raw and zero-diagonal
  Schwinger function constructions
- `SchwingerAxioms.lean`: zero-diagonal Euclidean-side proofs and remaining
  Schwinger-side analytic gaps
- `OSToWightmanSemigroup.lean`: E'→R' OS Hilbert-space semigroup and one-variable
  holomorphic bridge
- `OSToWightman.lean`: E'→R' analytic-continuation core and live base-step blocker
- `OSToWightmanBoundaryValues.lean`: boundary-value package, axiom transfer,
  and bridge theorems

## References

* Osterwalder-Schrader I (1973), "Axioms for Euclidean Green's Functions"
  for the Wick-rotation geometry and the honest zero-diagonal Euclidean side
* Osterwalder-Schrader II (1975), "Axioms for Euclidean Green's Functions II"
  for the corrected reconstruction theorem with linear growth
* Glimm-Jaffe, "Quantum Physics", Chapter 19
-/
