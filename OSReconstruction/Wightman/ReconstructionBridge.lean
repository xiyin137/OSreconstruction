/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation

/-!
# Reconstruction Bridge

This file wires the sorry-free bridge theorems from `WickRotation.lean`
(`wightman_to_os_full`, `os_to_wightman_full`) into the canonical names
(`wightman_to_os`, `os_to_wightman`) that were previously sorry'd stubs
in `Reconstruction.lean`.

The stubs lived in `Reconstruction.lean` but could not call the proofs in
`WickRotation.lean` because WickRotation imports Reconstruction (circular).
This bridge file breaks the cycle: it imports WickRotation and re-exports
the theorems under the original names.
-/

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Theorem R→E (Wightman → OS): A Wightman QFT yields Schwinger functions
    satisfying OS axioms E0-E4.

    The Schwinger functions are related to the Wightman functions by Wick rotation
    (analytic continuation): the Schwinger functions are Euclidean restrictions of the
    analytic continuation whose boundary values are the Wightman functions.

    Proved in `WickRotation.lean` as `wightman_to_os_full`. -/
theorem wightman_to_os (Wfn : WightmanFunctions d) :
    ∃ (OS : OsterwalderSchraderAxioms d),
      IsWickRotationPair OS.S Wfn.W :=
  wightman_to_os_full Wfn

/-- Theorem E'→R' (OS II): Schwinger functions satisfying the linear growth
    condition E0' together with E1-E4 can be analytically continued to
    Wightman distributions satisfying R0-R5.

    Proved in `WickRotation.lean` as `os_to_wightman_full`. -/
theorem os_to_wightman (OS : OsterwalderSchraderAxioms d)
    (linear_growth : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      IsWickRotationPair OS.S Wfn.W :=
  os_to_wightman_full OS linear_growth

end
