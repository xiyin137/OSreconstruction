/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.SCV.IteratedCauchyIntegral
import OSReconstruction.SCV.Polydisc









noncomputable section

open Complex MeasureTheory Topology Metric Set SCV

namespace SCV





/-- Tube domains over convex real sets are convex as subsets of `ℂ^m` viewed as a real
    vector space. -/
theorem tubeDomain_convex {m : ℕ} {C : Set (Fin m → ℝ)} (hC : Convex ℝ C) :
    Convex ℝ (TubeDomain C) := by
  intro z hz w hw a b ha hb hab
  simp only [TubeDomain, Set.mem_setOf_eq] at hz hw ⊢
  have himag :
      (fun i => ((a • z + b • w) i).im) =
        a • (fun i => (z i).im) + b • (fun i => (w i).im) := by
    ext i
    simp [Pi.smul_apply, Complex.add_im]
  rw [himag]
  exact hC hz hw ha hb hab












end SCV

end
