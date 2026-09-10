/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanEuclideanLorentz
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanClusterSection43
import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEWickPair









open scoped Classical NNReal
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]

/-
Deprecated route note:

The hypothesis `hschw` below is mathematically false on the intended theorem
surface. The left-hand side is the Euclidean/OS time-shifted Schwinger pairing,
whose free-field momentum-space form carries the Laplace factor `e^{-ω_p t}`;
the right-hand side is the reconstructed Wightman boundary-value pairing
against a real Minkowski time translation, whose free-field momentum-space form
carries the oscillatory factor `e^{-i ω_p t}`.

So this theorem is a logically valid implication from a false premise. It
remains harmless compiled legacy infrastructure, but it is no longer part of
the endorsed theorem-3 route. -/



/-- Compatibility bridge retaining the continuous-linear-family statement.
The full OS record is supplied separately by `wightman_to_os_axioms`. -/
theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W := by
  refine ⟨constructZeroDiagonalSchwingerFunctions Wfn, ?_, ?_, ?_⟩
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  exact OSReconstruction.constructSchwingerFunctions_isWickRotationPair Wfn

end
