/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalEOWChartApproxIdentity
import OSReconstruction.SCV.LocalProductRecovery

/-!
# One-Chart Scaled Recovery for Distributional EOW

This file specializes the checked local product-kernel recovery theorem to the
one-chart radii selected by `exists_oneChartRecoveryScale`: core radius `σ`,
descent radius `4 * σ`, covariance radius `8 * σ`, and holomorphy window
`δ / 2`.  It also discharges the side approximate-identity hypotheses from the
strict-side convergence lemmas.
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped BigOperators LineDeriv

namespace SCV

variable {m : ℕ}

/-- Local product-kernel recovery instantiated with the one-chart scale
`Rcore = r = rη = σ`, `Rdesc = 4 * σ`, and `Rcov = 8 * σ`.

The remaining hypotheses are the genuine analytic inputs: local covariance,
holomorphy and product-test representation for `Gchart`, the approximate
identity sequence, side identities for the regularized chart family, and
continuity of the two side functions on the strict side neighborhoods. -/
theorem regularizedEnvelope_chartEnvelope_from_oneChartScale
    {δ σ : ℝ}
    (hm : 0 < m) (hσ : 0 < σ) (hδ : 128 * σ ≤ δ)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Gchart : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη_norm : ∫ t : Fin m → ℝ, η t = 1)
    (hη_support : KernelSupportWithin η σ)
    (hcov : ProductKernelRealTranslationCovariantLocal K
      (Metric.ball (0 : ComplexChartSpace m) (8 * σ)) (σ + σ))
    (hG_holo : ∀ ψ, KernelSupportWithin ψ σ →
      DifferentiableOn ℂ (Gchart ψ)
        (Metric.ball (0 : ComplexChartSpace m) (δ / 2)))
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ)
          (Metric.ball (0 : ComplexChartSpace m) (8 * σ)) →
        KernelSupportWithin ψ σ →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, Gchart ψ z * φ z)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support_shrink :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ)))
    (hψ_support_r : ∀ n, KernelSupportWithin (ψn n) σ)
    (hψ_approx :
      ∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
        Tendsto
          (fun n => realConvolutionTest θ (ψn n))
          atTop
          (nhds θ))
    (hG_plus :
      ∀ᶠ n in atTop, ∀ z ∈
        Metric.ball (0 : ComplexChartSpace m) σ ∩
          StrictPositiveImagBall (m := m) σ,
        Gchart (ψn n) z = realMollifyLocal Fplus (ψn n) z)
    (hG_minus :
      ∀ᶠ n in atTop, ∀ z ∈
        Metric.ball (0 : ComplexChartSpace m) σ ∩
          StrictNegativeImagBall (m := m) σ,
        Gchart (ψn n) z = realMollifyLocal Fminus (ψn n) z)
    (hFplus_cont : ContinuousOn Fplus (StrictPositiveImagBall (m := m) (4 * σ)))
    (hFminus_cont : ContinuousOn Fminus (StrictNegativeImagBall (m := m) (4 * σ))) :
    ∃ H : ComplexChartSpace m → ℂ,
      DifferentiableOn ℂ H (Metric.ball (0 : ComplexChartSpace m) (4 * σ)) ∧
      ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ,
        RepresentsDistributionOnComplexDomain Hdist H
          (Metric.ball (0 : ComplexChartSpace m) (4 * σ)) ∧
        (∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m → ℝ) ℂ),
          SupportsInOpen (φ : ComplexChartSpace m → ℂ)
            (Metric.ball (0 : ComplexChartSpace m) (4 * σ)) →
          KernelSupportWithin ψ σ →
            K (schwartzTensorProduct₂ φ ψ) =
              Hdist (realConvolutionTest φ ψ)) ∧
        (∀ z ∈ Metric.ball (0 : ComplexChartSpace m) σ ∩
            StrictPositiveImagBall (m := m) σ, H z = Fplus z) ∧
        (∀ z ∈ Metric.ball (0 : ComplexChartSpace m) σ ∩
            StrictNegativeImagBall (m := m) σ, H z = Fminus z) := by
  have happrox_plus :
      ∀ z ∈ Metric.ball (0 : ComplexChartSpace m) σ ∩
          StrictPositiveImagBall (m := m) σ,
        Tendsto (fun n => realMollifyLocal Fplus (ψn n) z)
          atTop (nhds (Fplus z)) := by
    intro z hz
    exact tendsto_realMollifyLocal_strictPositiveImagBall
      (m := m) (Rcore := σ) (Rside := 4 * σ)
      (by nlinarith : σ ≤ 4 * σ)
      Fplus ψn hFplus_cont hψ_nonneg hψ_real hψ_norm
      hψ_support_shrink z hz.2
  have happrox_minus :
      ∀ z ∈ Metric.ball (0 : ComplexChartSpace m) σ ∩
          StrictNegativeImagBall (m := m) σ,
        Tendsto (fun n => realMollifyLocal Fminus (ψn n) z)
          atTop (nhds (Fminus z)) := by
    intro z hz
    exact tendsto_realMollifyLocal_strictNegativeImagBall
      (m := m) (Rcore := σ) (Rside := 4 * σ)
      (by nlinarith : σ ≤ 4 * σ)
      Fminus ψn hFminus_cont hψ_nonneg hψ_real hψ_norm
      hψ_support_shrink z hz.2
  exact
    regularizedEnvelope_chartEnvelope_from_localCovariantProductKernel
      (m := m) (r := σ) (rη := σ) hm K Gchart
      (Metric.ball (0 : ComplexChartSpace m) σ)
      (Metric.ball (0 : ComplexChartSpace m) (4 * σ))
      (Metric.ball (0 : ComplexChartSpace m) (8 * σ))
      (Metric.ball (0 : ComplexChartSpace m) (δ / 2))
      (StrictPositiveImagBall (m := m) σ)
      (StrictNegativeImagBall (m := m) σ)
      Fplus Fminus ψn
      Metric.isOpen_ball Metric.isOpen_ball
      (Metric.ball_subset_ball (by nlinarith : σ ≤ 4 * σ))
      (Metric.ball_subset_ball (by nlinarith : 4 * σ ≤ 8 * σ))
      (oneChartRecoveryScale_cov_ball_subset_half (m := m) hσ hδ)
      (by
        intro z hz t ht
        exact oneChartRecoveryScale_core_translate_mem_desc
          (m := m) hσ hz ht)
      hσ.le hσ.le η hη_norm hη_support
      (by
        intro z hz t ht
        exact oneChartRecoveryScale_desc_translate_mem_cov
          (m := m) hσ hz ht)
      hcov hG_holo hK_rep hψ_nonneg hψ_real hψ_norm
      hψ_support_shrink hψ_support_r hψ_approx hG_plus hG_minus
      happrox_plus happrox_minus

end SCV
