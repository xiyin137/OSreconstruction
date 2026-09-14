/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.ConeDefs
import OSReconstruction.GeneralResults.SmoothCutoff
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.PiL2























open scoped Classical ContDiff
noncomputable section

variable {m : ℕ}









/-- A smooth cutoff adapted to a closed set S ⊆ ℝ^m.
    Equals 1 on an ε-neighborhood of S, vanishes outside a 1-neighborhood,
    and has globally bounded derivatives.

    Construction: `χ₁ = 1_A * φ` where `A = {ξ : dist(ξ,S) ≤ 1/2}` and
    `φ ∈ C_c^∞(B_{1/2}(0))` with `∫ φ = 1` (convolution mollifier).
    Do NOT compose `smoothTransition` with `infDist` — `infDist` is not C^∞. -/
structure FixedConeCutoff (S : Set (Fin m → ℝ)) where
  /-- The smooth cutoff function. -/
  val : (Fin m → ℝ) → ℝ
  /-- The cutoff is smooth (C^∞). -/
  smooth : ContDiff ℝ ∞ val
  /-- The cutoff equals 1 on an open neighborhood of S. -/
  one_on_neighborhood : ∃ ε > 0, ∀ ξ, Metric.infDist ξ S < ε → val ξ = 1
  /-- The cutoff vanishes far from S. -/
  support_bound : ∀ ξ, Metric.infDist ξ S > 1 → val ξ = 0
  /-- All iterated derivatives are globally bounded. -/
  deriv_bound : ∀ k : ℕ, ∃ C : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k val ξ‖ ≤ C
  /-- Values are in [0,1]. -/
  val_nonneg : ∀ ξ, 0 ≤ val ξ
  val_le_one : ∀ ξ, val ξ ≤ 1

/-- Existence of a cone-adapted cutoff for any closed set.
    Proved by convolution of the indicator of the 1/2-neighborhood with a smooth bump.
    Uses `MeasureTheory.convolution` from Mathlib. -/
theorem fixedConeCutoff_exists (S : Set (Fin m → ℝ)) (hS : IsClosed S) :
    Nonempty (FixedConeCutoff S) := by
  obtain ⟨χ, hsmooth, hone, hsupp, hderiv, hnn, hle⟩ :=
    exists_smooth_cutoff_of_closed S hS
  exact ⟨⟨χ, hsmooth, hone, hsupp, hderiv, hnn, hle⟩⟩

end
