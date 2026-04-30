/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalEOWChartEnvelope
import OSReconstruction.SCV.DistributionalEOWKernelRecovery

/-!
# Strict-Side Approximate Identities for the Local EOW Chart

This file records the strict chart-side approximate-identity inputs used by
the one-chart distributional EOW envelope.  The side domains are the strict
positive and negative coordinate balls from `LocalEOWChartEnvelope`, while the
limit theorem is the checked real-mollifier recovery theorem from
`DistributionalEOWKernelRecovery`.
-/

noncomputable section

open Complex Filter Metric Set

namespace SCV

variable {m : ℕ}

/-- Strict positive chart-side balls are monotone in their radius. -/
theorem StrictPositiveImagBall_mono {R R' : ℝ}
    (hR : R ≤ R') :
    StrictPositiveImagBall (m := m) R ⊆ StrictPositiveImagBall (m := m) R' := by
  intro w hw
  exact ⟨Metric.ball_subset_ball hR hw.1, hw.2⟩

/-- Strict negative chart-side balls are monotone in their radius. -/
theorem StrictNegativeImagBall_mono {R R' : ℝ}
    (hR : R ≤ R') :
    StrictNegativeImagBall (m := m) R ⊆ StrictNegativeImagBall (m := m) R' := by
  intro w hw
  exact ⟨Metric.ball_subset_ball hR hw.1, hw.2⟩

/-- On a strict positive chart-side ball, real mollification by a shrinking
normalized kernel recovers the original continuous side function. -/
theorem tendsto_realMollifyLocal_strictPositiveImagBall
    {Rcore Rside : ℝ} (hR : Rcore ≤ Rside)
    (F : ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hF_cont : ContinuousOn F (StrictPositiveImagBall (m := m) Rside))
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ StrictPositiveImagBall (m := m) Rcore,
      Tendsto (fun n => realMollifyLocal F (ψn n) z) atTop (nhds (F z)) := by
  exact
    regularizedEnvelope_kernelLimit_from_representation
      (StrictPositiveImagBall (m := m) Rcore)
      (StrictPositiveImagBall (m := m) Rside)
      F (fun ψ => realMollifyLocal F ψ) ψn
      (isOpen_StrictPositiveImagBall Rside)
      (StrictPositiveImagBall_mono hR)
      hF_cont
      (by intro n z hz; rfl)
      hψ_nonneg hψ_real hψ_norm hψ_support

/-- On a strict negative chart-side ball, real mollification by a shrinking
normalized kernel recovers the original continuous side function. -/
theorem tendsto_realMollifyLocal_strictNegativeImagBall
    {Rcore Rside : ℝ} (hR : Rcore ≤ Rside)
    (F : ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hF_cont : ContinuousOn F (StrictNegativeImagBall (m := m) Rside))
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ StrictNegativeImagBall (m := m) Rcore,
      Tendsto (fun n => realMollifyLocal F (ψn n) z) atTop (nhds (F z)) := by
  exact
    regularizedEnvelope_kernelLimit_from_representation
      (StrictNegativeImagBall (m := m) Rcore)
      (StrictNegativeImagBall (m := m) Rside)
      F (fun ψ => realMollifyLocal F ψ) ψn
      (isOpen_StrictNegativeImagBall Rside)
      (StrictNegativeImagBall_mono hR)
      hF_cont
      (by intro n z hz; rfl)
      hψ_nonneg hψ_real hψ_norm hψ_support

end SCV
