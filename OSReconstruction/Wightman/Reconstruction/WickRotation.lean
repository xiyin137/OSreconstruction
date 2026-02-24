/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman

/-!
# Wick Rotation and the OS Bridge Theorems

This module develops the infrastructure for the Osterwalder-Schrader bridge theorems:
- **Theorem R→E** (`wightman_to_os_full`): Wightman functions → Schwinger functions (OS I, §5)
- **Theorem E'→R'** (`os_to_wightman_full`): Schwinger functions → Wightman functions (OS II, §IV-V)

## Module Structure

The implementation is split across several files in the `WickRotation/` subfolder:

- `ForwardTubeLorentz.lean`: Forward tube preservation, Lorentz invariance,
  distributional boundary value covariance
- `BHWExtension.lean`: Bargmann-Hall-Wightman extension definition and properties
- `BHWTranslation.lean`: Translation invariance proof chain, Schwinger function construction
- `SchwingerAxioms.lean`: E0-E4 axiom proofs for constructed Schwinger functions
- `OSToWightman.lean`: E'→R' direction, bridge theorems

## References

* Osterwalder-Schrader I (1973), "Axioms for Euclidean Green's Functions"
* Osterwalder-Schrader II (1975), "Axioms for Euclidean Green's Functions II"
* Glimm-Jaffe, "Quantum Physics", Chapter 19
-/
