/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernelFactorization










noncomputable section

open Complex MeasureTheory

namespace SCV

@[simp]
theorem translateSchwartz_zero {m : ℕ}
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    translateSchwartz (0 : Fin m → ℝ) ψ = ψ := by
  ext t
  simp [translateSchwartz_apply]

end SCV
