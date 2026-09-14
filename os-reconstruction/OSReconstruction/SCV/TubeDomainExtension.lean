/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Basic
import OSReconstruction.SCV.IteratedCauchyIntegral
import OSReconstruction.SCV.EdgeOfWedge
import OSReconstruction.SCV.Analyticity
import Init
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import OSReconstruction.SCV.SeparatelyAnalytic





































noncomputable section

open Complex MeasureTheory Topology Metric Set SCV

namespace SCV



/-- The tube domain `T(C) = { z ∈ ℂᵐ : Im(z) ∈ C }` where `C ⊂ ℝᵐ` is an
    open convex cone. This is the natural domain of holomorphic extension
    for functions with boundary values on `ℝᵐ`. -/
def TubeDomain {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℂ) :=
  { z | (fun i => (z i).im) ∈ C }

/-- The tube domain is open when the cone is open. -/
theorem tubeDomain_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (TubeDomain C) := by
  -- TubeDomain C = Im⁻¹(C) where Im : ℂᵐ → ℝᵐ is continuous
  exact hC.preimage (continuous_pi (fun i => Complex.continuous_im.comp (continuous_apply i)))

/-- The embedding of ℝᵐ into the real subspace of ℂᵐ. -/
def realEmbed {m : ℕ} (x : Fin m → ℝ) : Fin m → ℂ :=
  fun i => (x i : ℂ)





-- rudin_mean_value_pos and rudin_mean_value_neg have been moved to
-- deprecated/rudin_mean_value_pos_neg.lean (they are no longer called;
-- the 1D line argument in rudin_orthant_extension bypasses them).





end SCV

end

-- Realize the half-plane equations eagerly for reproducible elaboration.
run_cmd Lean.Elab.Command.liftTermElabM do
  let _ ← Lean.Meta.getEqnsFor? ``EOW.UpperHalfPlane
  let _ ← Lean.Meta.getEqnsFor? ``EOW.LowerHalfPlane
  pure ()
