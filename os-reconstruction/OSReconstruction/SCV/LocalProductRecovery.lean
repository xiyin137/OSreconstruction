/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernelRecovery
import OSReconstruction.SCV.LocalProductDescentIntegrals











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

/-- The analytic core of local product-kernel recovery, without the two
edge-of-wedge side functions.

Local real-translation covariance descends the mixed product kernel to a
complex-chart distribution. Fixed-test holomorphy makes that distribution
distributionally holomorphic, Weyl regularity supplies a genuine holomorphic
representative, and the product-test identity recovers the original family as
real-fiber convolution against that representative. -/
theorem localCovariantProductKernel_holomorphicRepresentative
    {m : ℕ} {r rη : ℝ}
    (hm : 0 < m)
    (hr : 0 < r)
    (hrη_nonneg : 0 ≤ rη)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Gchart : SchwartzMap (Fin m → ℝ) ℂ →
      ComplexChartSpace m → ℂ)
    (Ucore Udesc Ucov U0 : Set (ComplexChartSpace m))
    (hUcore_open : IsOpen Ucore)
    (hUdesc_open : IsOpen Udesc)
    (hcore_desc : Ucore ⊆ Udesc)
    (hdesc_cov : Udesc ⊆ Ucov)
    (hcov_window : Ucov ⊆ U0)
    (hmargin_core :
      ∀ z ∈ Ucore, ∀ t : Fin m → ℝ, ‖t‖ ≤ r →
        z + realEmbed t ∈ Udesc)
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
            ∫ z : ComplexChartSpace m, Gchart ψ z * φ z) :
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
        ∀ (ψ : SchwartzMap (Fin m → ℝ) ℂ),
          KernelSupportWithin ψ r →
          ∀ z ∈ Ucore,
            Gchart ψ z =
              ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t := by
  obtain ⟨Hdist, hdesc_local⟩ :=
    translationCovariantProductKernel_descends_local
      K Udesc Ucov r rη hr.le hrη_nonneg η hη_norm hη_support
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
  obtain ⟨ψn, _hψ_norm, _hψ_min, hψ_support, hψ_approx⟩ :=
    exists_realConvolutionTest_approxIdentity (m := m) hr
  have hCR : IsDistributionalHolomorphicOn Hdist Udesc :=
    translationCovariantKernel_distributionalHolomorphic_local
      (Hdist := Hdist) (K := K) (Udesc := Udesc) (ψι := ψn)
      (hψ_support := Filter.Eventually.of_forall hψ_support)
      (hψ_approx := hψ_approx)
      (hdesc_local := hdesc_local)
      (hK_dbar_zero := hK_dbar_zero)
  obtain ⟨H, hH_holo, hRep⟩ :=
    distributionalHolomorphic_regular Hdist hm hUdesc_open hCR
  refine ⟨H, hH_holo, Hdist, hRep, hdesc_local, ?_⟩
  intro ψ hψ z hz
  exact
    regularizedEnvelope_pointwiseRepresentation_of_localProductKernel
      K Gchart H Hdist Ucore Udesc Ucov U0 ψ
      hUcore_open hUdesc_open hcore_desc hdesc_cov hcov_window
      hmargin_core hψ (hG_holo ψ hψ) hH_holo hRep
      hdesc_local hK_rep z hz

/-- Uniform local recovery for a family of product kernels with explicit
descended distributions.  A common finite Schwartz-seminorm bound on the
descended family yields canonical holomorphic representatives uniformly
bounded on a prescribed compact subset of the descent domain. -/
theorem localProductKernel_holomorphicRepresentative_uniform_compact
    {m : ℕ} {r : ℝ}
    (hm : 0 < m)
    (hr : 0 < r)
    (K : ℕ →
      SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Gchart : ℕ → SchwartzMap (Fin m → ℝ) ℂ →
      ComplexChartSpace m → ℂ)
    (Hdist : ℕ → SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    (Ucore Udesc Ucov U0 Kcompact : Set (ComplexChartSpace m))
    (hUcore_open : IsOpen Ucore)
    (hUdesc_open : IsOpen Udesc)
    (hcore_desc : Ucore ⊆ Udesc)
    (hdesc_cov : Udesc ⊆ Ucov)
    (hcov_window : Ucov ⊆ U0)
    (hKcompact_compact : IsCompact Kcompact)
    (hKcompact_subset : Kcompact ⊆ Udesc)
    (hmargin_core :
      ∀ z ∈ Ucore, ∀ t : Fin m → ℝ, ‖t‖ ≤ r →
        z + realEmbed t ∈ Udesc)
    (hG_holo : ∀ level ψ, KernelSupportWithin ψ r →
      DifferentiableOn ℂ (Gchart level ψ) U0)
    (hK_rep :
      ∀ level
        (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucov →
        KernelSupportWithin ψ r →
          K level (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, Gchart level ψ z * φ z)
    (hdesc_local :
      ∀ level
        (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc →
        KernelSupportWithin ψ r →
          K level (schwartzTensorProduct₂ φ ψ) =
            Hdist level (realConvolutionTest φ ψ))
    (s : Finset (ℕ × ℕ))
    (C : ℝ)
    (hC : 0 ≤ C)
    (hHdist_bound :
      ∀ level (φ : SchwartzMap (ComplexChartSpace m) ℂ),
        ‖Hdist level φ‖ ≤
          C * s.sup
            (schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ) φ) :
    ∃ H : ℕ → ComplexChartSpace m → ℂ,
      (∀ level, DifferentiableOn ℂ (H level) Udesc) ∧
      (∀ level,
        RepresentsDistributionOnComplexDomain
          (Hdist level) (H level) Udesc) ∧
      (∀ level (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        KernelSupportWithin ψ r →
        ∀ z ∈ Ucore,
          Gchart level ψ z =
            ∫ t : Fin m → ℝ, H level (z + realEmbed t) * ψ t) ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ level z, z ∈ Kcompact → ‖H level z‖ ≤ M := by
  have hK_dbar_zero :
      ∀ level (j : Fin m)
        (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc →
        KernelSupportWithin ψ r →
          K level (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0 := by
    intro level j φ ψ hφ hψ
    exact
      regularizedEnvelope_productKernel_dbar_eq_zero_local
        (K level) (Gchart level) Udesc Ucov U0
        hUdesc_open hdesc_cov hcov_window
        (hG_holo level) (hK_rep level) j φ hφ ψ hψ
  obtain ⟨ψn, _hψ_norm, _hψ_min, hψ_support, hψ_approx⟩ :=
    exists_realConvolutionTest_approxIdentity (m := m) hr
  have hCR :
      ∀ level, IsDistributionalHolomorphicOn (Hdist level) Udesc := by
    intro level
    exact
      translationCovariantKernel_distributionalHolomorphic_local
        (Hdist := Hdist level) (K := K level)
        (Udesc := Udesc) (ψι := ψn)
        (hψ_support := Filter.Eventually.of_forall hψ_support)
        (hψ_approx := hψ_approx)
        (hdesc_local := hdesc_local level)
        (hK_dbar_zero := hK_dbar_zero level)
  obtain ⟨H, hH_holo, hH_rep, M, hM, hH_bound⟩ :=
    distributionalHolomorphic_regular_uniform_compact_bound
      Hdist hm hUdesc_open hKcompact_compact hKcompact_subset
      s C hC hHdist_bound hCR
  refine ⟨H, hH_holo, hH_rep, ?_, M, hM, hH_bound⟩
  intro level ψ hψ z hz
  exact
    regularizedEnvelope_pointwiseRepresentation_of_localProductKernel
      (K level) (Gchart level) (H level) (Hdist level)
      Ucore Udesc Ucov U0 ψ
      hUcore_open hUdesc_open hcore_desc hdesc_cov hcov_window
      hmargin_core hψ (hG_holo level ψ hψ)
      (hH_holo level) (hH_rep level)
      (hdesc_local level) (hK_rep level) z hz

end SCV
