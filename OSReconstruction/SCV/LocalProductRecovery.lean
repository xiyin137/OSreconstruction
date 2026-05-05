/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernelRecovery
import OSReconstruction.SCV.LocalProductDescentIntegrals

/-!
# Local product-kernel recovery

This file contains the local recovery consumer after local product-test
descent.  It reuses the checked global recovery helpers while keeping the
domains separated: `Ucore` for the pointwise conclusion, `Udesc` for the
recovered distribution and Fubini step, and `Ucov`/`U0` for the product-kernel
representation and holomorphy window.
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped BigOperators LineDeriv

namespace SCV

/-- Pointwise representation of the regularized local product kernel.  This is
the local analogue of `regularizedEnvelope_pointwiseRepresentation_of_productKernel`:
descent and representation are only required on tests supported in the declared
local domains. -/
theorem regularizedEnvelope_pointwiseRepresentation_of_localProductKernel
    {m : ℕ} {r : ℝ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Gchart : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (H : ComplexChartSpace m → ℂ)
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    (Ucore Udesc Ucov U0 : Set (ComplexChartSpace m))
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hUcore_open : IsOpen Ucore)
    (hUdesc_open : IsOpen Udesc)
    (hcore_desc : Ucore ⊆ Udesc)
    (hdesc_cov : Udesc ⊆ Ucov)
    (hcov_window : Ucov ⊆ U0)
    (hmargin_core :
      ∀ z ∈ Ucore, ∀ t : Fin m → ℝ, ‖t‖ ≤ r →
        z + realEmbed t ∈ Udesc)
    (hψ_support : KernelSupportWithin ψ r)
    (hG_holo : DifferentiableOn ℂ (Gchart ψ) U0)
    (hH_holo : DifferentiableOn ℂ H Udesc)
    (hRep : RepresentsDistributionOnComplexDomain Hdist H Udesc)
    (hdesc_local :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (η : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc →
        KernelSupportWithin η r →
          K (schwartzTensorProduct₂ φ η) =
            Hdist (realConvolutionTest φ η))
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (η : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucov →
        KernelSupportWithin η r →
          K (schwartzTensorProduct₂ φ η) =
            ∫ z : ComplexChartSpace m, Gchart η z * φ z) :
    ∀ z ∈ Ucore,
      Gchart ψ z = ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t := by
  let Hψ : ComplexChartSpace m → ℂ :=
    fun z => ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t
  have hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ) :=
    KernelSupportWithin_hasCompactSupport hψ_support
  have hmargin :
      ∀ z ∈ Ucore, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Udesc := by
    intro z hz t ht
    have ht_norm : ‖t‖ ≤ r := by
      simpa [KernelSupportWithin, Metric.mem_closedBall, dist_eq_norm]
        using hψ_support ht
    exact hmargin_core z hz t ht_norm
  have hG_cont_core : ContinuousOn (Gchart ψ) Ucore :=
    hG_holo.continuousOn.mono
      (hcore_desc.trans (hdesc_cov.trans hcov_window))
  have hHψ_cont : ContinuousOn Hψ Ucore := by
    simpa [Hψ] using
      continuousOn_realMollifyLocal_of_translate_margin
        H ψ Ucore Udesc hUdesc_open hH_holo.continuousOn hψ_compact hmargin
  have hG_int :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          Integrable fun z : ComplexChartSpace m => Gchart ψ z * φ z := by
    intro φ hφ
    exact integrable_continuousOn_mul_schwartz_of_supportsInOpen
      hUcore_open hG_cont_core hφ
  have hH_int :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          Integrable fun z : ComplexChartSpace m => Hψ z * φ z := by
    intro φ hφ
    exact integrable_continuousOn_mul_schwartz_of_supportsInOpen
      hUcore_open hHψ_cont hφ
  have htest_eq :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          (∫ z : ComplexChartSpace m, Gchart ψ z * φ z) =
            ∫ z : ComplexChartSpace m, Hψ z * φ z := by
    intro φ hφ
    have hφ_desc : SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc :=
      ⟨hφ.1, hφ.2.trans hcore_desc⟩
    have hφ_cov : SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucov :=
      ⟨hφ.1, hφ.2.trans (hcore_desc.trans hdesc_cov)⟩
    have hconv_support :
        SupportsInOpen
          (realConvolutionTest φ ψ : ComplexChartSpace m → ℂ) Udesc :=
      realConvolutionTest_supportsInOpen_of_translate_margin
        φ ψ Ucore Udesc hφ hψ_compact hmargin
    calc
      (∫ z : ComplexChartSpace m, Gchart ψ z * φ z) =
          K (schwartzTensorProduct₂ φ ψ) := by
            exact (hK_rep φ ψ hφ_cov hψ_support).symm
      _ = Hdist (realConvolutionTest φ ψ) :=
            hdesc_local φ ψ hφ_desc hψ_support
      _ = ∫ y : ComplexChartSpace m,
            H y * realConvolutionTest φ ψ y :=
            hRep (realConvolutionTest φ ψ) hconv_support
      _ = ∫ z : ComplexChartSpace m,
            (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t) * φ z :=
          realConvolutionTest_pairing_eq_mollifier_pairing
            H φ ψ Ucore Udesc hUdesc_open hH_holo.continuousOn
            hφ hψ_compact hmargin
      _ = ∫ z : ComplexChartSpace m, Hψ z * φ z := by
          rfl
  exact regularizedEnvelope_pointwise_eq_of_test_integral_eq
    Ucore (Gchart ψ) Hψ hUcore_open hG_cont_core hHψ_cont
    hG_int hH_int htest_eq

/-- Final local chart-envelope assembly from local product-test descent, local
distributional holomorphy, pointwise kernel recovery, and the side
approximate-identity limits.  This consumes the local CR theorem as an explicit
input; proving that CR statement belongs to the preceding local
product-kernel-to-distributional-holomorphy step. -/
theorem regularizedEnvelope_chartEnvelope_from_localProductKernel
    {m : ℕ} {r : ℝ}
    (hm : 0 < m)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Gchart : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (Ucore Udesc Ucov U0 DplusSmall DminusSmall :
      Set (ComplexChartSpace m))
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hUcore_open : IsOpen Ucore)
    (hUdesc_open : IsOpen Udesc)
    (hcore_desc : Ucore ⊆ Udesc)
    (hdesc_cov : Udesc ⊆ Ucov)
    (hcov_window : Ucov ⊆ U0)
    (hmargin_core :
      ∀ z ∈ Ucore, ∀ t : Fin m → ℝ, ‖t‖ ≤ r →
        z + realEmbed t ∈ Udesc)
    (hG_holo : ∀ ψ, KernelSupportWithin ψ r →
      DifferentiableOn ℂ (Gchart ψ) U0)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (η : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucov →
        KernelSupportWithin η r →
          K (schwartzTensorProduct₂ φ η) =
            ∫ z : ComplexChartSpace m, Gchart η z * φ z)
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    (hdesc_local :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (η : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc →
        KernelSupportWithin η r →
          K (schwartzTensorProduct₂ φ η) =
            Hdist (realConvolutionTest φ η))
    (hCR : IsDistributionalHolomorphicOn Hdist Udesc)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support_shrink :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ)))
    (hψ_support_r : ∀ n, KernelSupportWithin (ψn n) r)
    (hG_plus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DplusSmall,
        Gchart (ψn n) z = realMollifyLocal Fplus (ψn n) z)
    (hG_minus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DminusSmall,
        Gchart (ψn n) z = realMollifyLocal Fminus (ψn n) z)
    (happrox_plus :
      ∀ z ∈ Ucore ∩ DplusSmall,
        Tendsto (fun n => realMollifyLocal Fplus (ψn n) z)
          atTop (nhds (Fplus z)))
    (happrox_minus :
      ∀ z ∈ Ucore ∩ DminusSmall,
        Tendsto (fun n => realMollifyLocal Fminus (ψn n) z)
          atTop (nhds (Fminus z))) :
    ∃ H : ComplexChartSpace m → ℂ,
      DifferentiableOn ℂ H Udesc ∧
      RepresentsDistributionOnComplexDomain Hdist H Udesc ∧
      (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
      (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z) := by
  obtain ⟨H, hH_holo, hRep⟩ :=
    distributionalHolomorphic_regular Hdist hm hUdesc_open hCR
  have hH_rep :
      ∀ n, ∀ z ∈ Ucore,
        Gchart (ψn n) z =
          ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t := by
    intro n
    exact
      regularizedEnvelope_pointwiseRepresentation_of_localProductKernel
        K Gchart H Hdist Ucore Udesc Ucov U0 (ψn n)
        hUcore_open hUdesc_open hcore_desc hdesc_cov hcov_window
        hmargin_core (hψ_support_r n)
        (hG_holo (ψn n) (hψ_support_r n))
        hH_holo hRep hdesc_local hK_rep
  have hkernel_limit :
      ∀ z ∈ Ucore, Tendsto (fun n => Gchart (ψn n) z) atTop (nhds (H z)) :=
    regularizedEnvelope_kernelLimit_from_representation
      Ucore Udesc H Gchart ψn hUdesc_open hcore_desc
      hH_holo.continuousOn hH_rep
      hψ_nonneg hψ_real hψ_norm hψ_support_shrink
  obtain ⟨hplus, hminus⟩ :=
    regularizedEnvelope_deltaLimit_agreesOnWedges
      Ucore Gchart Fplus Fminus H DplusSmall DminusSmall ψn
      hG_plus hG_minus happrox_plus happrox_minus hkernel_limit
  exact ⟨H, hH_holo, hRep, hplus, hminus⟩

/-- Local covariant product-kernel recovery.  This assembles local product-test
descent, the localized `∂bar` annihilation theorem, distributional
holomorphy, and the checked local chart-envelope recovery theorem. -/
theorem regularizedEnvelope_chartEnvelope_from_localCovariantProductKernel
    {m : ℕ} {r rη : ℝ}
    (hm : 0 < m)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Gchart : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (Ucore Udesc Ucov U0 DplusSmall DminusSmall :
      Set (ComplexChartSpace m))
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hUcore_open : IsOpen Ucore)
    (hUdesc_open : IsOpen Udesc)
    (hcore_desc : Ucore ⊆ Udesc)
    (hdesc_cov : Udesc ⊆ Ucov)
    (hcov_window : Ucov ⊆ U0)
    (hmargin_core :
      ∀ z ∈ Ucore, ∀ t : Fin m → ℝ, ‖t‖ ≤ r →
        z + realEmbed t ∈ Udesc)
    (hr_nonneg : 0 ≤ r)
    (hrη_nonneg : 0 ≤ rη)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη_norm : ∫ t : Fin m → ℝ, η t = 1)
    (hη_support : KernelSupportWithin η rη)
    (hmargin_desc_cov :
      ∀ z ∈ Udesc, ∀ t : Fin m → ℝ, ‖t‖ ≤ r + rη →
        z + realEmbed t ∈ Ucov)
    (hcov : ProductKernelRealTranslationCovariantLocal K Ucov (r + rη))
    (hG_holo : ∀ ψ, KernelSupportWithin ψ r →
      DifferentiableOn ℂ (Gchart ψ) U0)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucov →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, Gchart ψ z * φ z)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support_shrink :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ)))
    (hψ_support_r : ∀ n, KernelSupportWithin (ψn n) r)
    (hψ_approx :
      ∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
        Tendsto
          (fun n => realConvolutionTest θ (ψn n))
          atTop
          (nhds θ))
    (hG_plus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DplusSmall,
        Gchart (ψn n) z = realMollifyLocal Fplus (ψn n) z)
    (hG_minus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DminusSmall,
        Gchart (ψn n) z = realMollifyLocal Fminus (ψn n) z)
    (happrox_plus :
      ∀ z ∈ Ucore ∩ DplusSmall,
        Tendsto (fun n => realMollifyLocal Fplus (ψn n) z)
          atTop (nhds (Fplus z)))
    (happrox_minus :
      ∀ z ∈ Ucore ∩ DminusSmall,
        Tendsto (fun n => realMollifyLocal Fminus (ψn n) z)
          atTop (nhds (Fminus z))) :
    ∃ H : ComplexChartSpace m → ℂ,
      DifferentiableOn ℂ H Udesc ∧
      ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ,
        RepresentsDistributionOnComplexDomain Hdist H Udesc ∧
        (∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m → ℝ) ℂ),
          SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc →
          KernelSupportWithin ψ r →
            K (schwartzTensorProduct₂ φ ψ) =
              Hdist (realConvolutionTest φ ψ)) ∧
        (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
        (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z) := by
  obtain ⟨Hdist, hdesc_local⟩ :=
    translationCovariantProductKernel_descends_local
      K Udesc Ucov r rη hr_nonneg hrη_nonneg η hη_norm hη_support
      hmargin_desc_cov hcov
  have hK_dbar_zero :
      ∀ (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0 := by
    intro j φ ψ hφ hψ
    exact
      regularizedEnvelope_productKernel_dbar_eq_zero_local
        K Gchart Udesc Ucov U0 hUdesc_open hdesc_cov hcov_window
        hG_holo hK_rep j φ hφ ψ hψ
  have hCR : IsDistributionalHolomorphicOn Hdist Udesc :=
    translationCovariantKernel_distributionalHolomorphic_local
      (Hdist := Hdist) (K := K) (Udesc := Udesc) (ψι := ψn)
      (hψ_support := Filter.Eventually.of_forall hψ_support_r)
      (hψ_approx := hψ_approx)
      (hdesc_local := hdesc_local)
      (hK_dbar_zero := hK_dbar_zero)
  obtain ⟨H, hH_holo, hRep, hplus, hminus⟩ :=
    regularizedEnvelope_chartEnvelope_from_localProductKernel
      hm K Gchart Ucore Udesc Ucov U0 DplusSmall DminusSmall
      Fplus Fminus ψn hUcore_open hUdesc_open hcore_desc hdesc_cov
      hcov_window hmargin_core hG_holo hK_rep Hdist hdesc_local hCR
      hψ_nonneg hψ_real hψ_norm hψ_support_shrink hψ_support_r
      hG_plus hG_minus happrox_plus happrox_minus
  exact ⟨H, hH_holo, Hdist, hRep, hdesc_local, hplus, hminus⟩

end SCV
