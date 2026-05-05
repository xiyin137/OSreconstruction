/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWCutoff
import OSReconstruction.SCV.IdentityTheorem

/-!
# Local Schwartz Representatives for Holomorphic Factors

This file proves the zero-extension, smooth-to-Schwartz, and local
Cauchy-Riemann parts of the local holomorphic `∂bar` bridge.  Given a
holomorphic function on an open chart set and a compactly supported Schwartz
test inside that set, we construct a global Schwartz function that agrees with
the holomorphic factor near the test support and is `∂bar`-closed on that
support.
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped Manifold Topology

namespace SCV

variable {m : ℕ}

/-- A holomorphic factor on an open chart can be cut off to a global Schwartz
representative that agrees with it on an open neighborhood of the topological
support of a local Schwartz test. -/
theorem exists_local_schwartz_representative_eq_on_open
    (U : Set (ComplexChartSpace m))
    (hU_open : IsOpen U)
    (F : ComplexChartSpace m → ℂ)
    (hF_holo : DifferentiableOn ℂ F U)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U) :
    ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
      ∃ V : Set (ComplexChartSpace m),
        IsOpen V ∧
        tsupport (φ : ComplexChartSpace m → ℂ) ⊆ V ∧
        V ⊆ U ∧
        Set.EqOn (G : ComplexChartSpace m → ℂ) F V := by
  obtain ⟨χ, hχ_contDiff, hχ_compact, hχ_tsupport_U, _hχrange,
      V, hV_open, hK_sub_V, hV_U, hχ_eq_one_V⟩ :=
    exists_smooth_cutoff_eq_one_near_tsupport_of_supportsInOpen
      U hU_open φ hφ
  let H : ComplexChartSpace m → ℂ := fun z => (χ z : ℂ) * F z
  have hχC_contDiff :
      ContDiff ℝ (⊤ : ℕ∞) (fun z : ComplexChartSpace m => (χ z : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hχ_contDiff
  have hF_contDiffR_on_U : ContDiffOn ℝ (⊤ : ℕ∞) F U := by
    have hF_contDiffC : ContDiffOn ℂ (⊤ : ℕ∞) F U := by
      exact
        (hF_holo.analyticOnNhd_of_finiteDimensional
          hU_open).contDiffOn_of_completeSpace
    exact hF_contDiffC.restrict_scalars ℝ
  have hH_smooth : ContDiff ℝ (⊤ : ℕ∞) H := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hzU : z ∈ U
    · have hF_at : ContDiffAt ℝ (⊤ : ℕ∞) F z :=
        (hF_contDiffR_on_U z hzU).contDiffAt (hU_open.mem_nhds hzU)
      exact hχC_contDiff.contDiffAt.mul hF_at
    · have hz_not_tsupport : z ∉ tsupport χ := by
        intro hzχ
        exact hzU (hχ_tsupport_U hzχ)
      have hχ0 : χ =ᶠ[nhds z] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at hz_not_tsupport
      have hH0 : H =ᶠ[nhds z] fun _ => 0 := by
        filter_upwards [hχ0] with y hy
        simp [H, hy]
      exact (contDiff_const.contDiffAt (x := z)).congr_of_eventuallyEq hH0
  have hH_tsupport_subset : tsupport H ⊆ tsupport χ := by
    rw [tsupport]
    exact closure_mono (by
      intro z hz
      by_contra hzχ
      have hχz : χ z = 0 := by
        simpa [Function.mem_support] using hzχ
      exact hz (by simp [H, hχz]))
  have hH_compact : HasCompactSupport H := by
    exact IsCompact.of_isClosed_subset hχ_compact (isClosed_tsupport H)
      hH_tsupport_subset
  let G : SchwartzMap (ComplexChartSpace m) ℂ :=
    hH_compact.toSchwartzMap hH_smooth
  have hG_apply : ∀ z, G z = H z :=
    HasCompactSupport.toSchwartzMap_toFun hH_compact hH_smooth
  refine ⟨G, V, hV_open, hK_sub_V, hV_U, ?_⟩
  intro z hzV
  have hχz : χ z = 1 := hχ_eq_one_V hzV
  rw [hG_apply z]
  simp [H, hχz]

/-- Support-only corollary of
`exists_local_schwartz_representative_eq_on_open`. -/
theorem exists_local_schwartz_representative_eq_on_tsupport
    (U : Set (ComplexChartSpace m))
    (hU_open : IsOpen U)
    (F : ComplexChartSpace m → ℂ)
    (hF_holo : DifferentiableOn ℂ F U)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U) :
    ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
      ∀ z ∈ tsupport (φ : ComplexChartSpace m → ℂ), G z = F z := by
  obtain ⟨G, V, _hV_open, hK_sub_V, _hV_U, hGF⟩ :=
    exists_local_schwartz_representative_eq_on_open U hU_open F hF_holo φ hφ
  exact ⟨G, fun z hz => hGF (hK_sub_V hz)⟩

/-- If a Schwartz representative agrees locally with a holomorphic function,
then its test-function `∂/∂bar z_j` vanishes pointwise on that local agreement
set. -/
theorem dbarSchwartzCLM_eq_zero_on_of_eqOn_holomorphic
    (U V : Set (ComplexChartSpace m))
    (hU_open : IsOpen U)
    (F : ComplexChartSpace m → ℂ)
    (hF_holo : DifferentiableOn ℂ F U)
    (G : SchwartzMap (ComplexChartSpace m) ℂ)
    (hV_open : IsOpen V)
    (hV_U : V ⊆ U)
    (hGF : Set.EqOn (G : ComplexChartSpace m → ℂ) F V)
    (j : Fin m) {z : ComplexChartSpace m} (hzV : z ∈ V) :
    (dbarSchwartzCLM j G) z = 0 := by
  have hzU : z ∈ U := hV_U hzV
  have hGF_eventually : (G : ComplexChartSpace m → ℂ) =ᶠ[nhds z] F := by
    filter_upwards [hV_open.mem_nhds hzV] with y hy
    exact hGF hy
  have hfderiv_eq :
      fderiv ℝ (G : ComplexChartSpace m → ℂ) z = fderiv ℝ F z := by
    exact hGF_eventually.fderiv_eq
  have hF_atC : DifferentiableAt ℂ F z :=
    hF_holo.differentiableAt (hU_open.mem_nhds hzU)
  have hF_real : fderiv ℝ F z = (fderiv ℂ F z).restrictScalars ℝ := by
    exact hF_atC.fderiv_restrictScalars ℝ
  have himag_dir : complexImagDir j = Complex.I • complexRealDir j := by
    ext k
    by_cases hkj : k = j
    · simp [complexImagDir, complexRealDir, hkj]
    · simp [complexImagDir, complexRealDir, hkj]
  have hCR :
      fderiv ℝ (G : ComplexChartSpace m → ℂ) z (complexImagDir j) =
        Complex.I *
          fderiv ℝ (G : ComplexChartSpace m → ℂ) z (complexRealDir j) := by
    rw [hfderiv_eq, hF_real]
    rw [himag_dir]
    simp [smul_eq_mul]
  simp [dbarSchwartzCLM, directionalDerivSchwartzCLM,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, hCR]
  set a := (fderiv ℝ (G : ComplexChartSpace m → ℂ) z) (complexRealDir j)
  change 2⁻¹ * a + 2⁻¹ * (Complex.I * (Complex.I * a)) = 0
  rw [← mul_assoc Complex.I Complex.I a, Complex.I_mul_I]
  ring

/-- A local holomorphic factor admits a Schwartz representative agreeing on
`tsupport (∂bar φ)` and `∂bar`-closed on `tsupport φ`. -/
theorem exists_local_dbarClosed_schwartz_representative
    (U : Set (ComplexChartSpace m))
    (hU_open : IsOpen U)
    (F : ComplexChartSpace m → ℂ)
    (hF_holo : DifferentiableOn ℂ F U)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U)
    (j : Fin m) :
    ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
      (∀ z ∈ tsupport
          ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
            ComplexChartSpace m → ℂ), F z = G z) ∧
      (∀ z ∈ tsupport (φ : ComplexChartSpace m → ℂ),
          (dbarSchwartzCLM j G) z = 0) := by
  obtain ⟨G, V, hV_open, hK_sub_V, hV_U, hGF⟩ :=
    exists_local_schwartz_representative_eq_on_open U hU_open F hF_holo φ hφ
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    have hzK : z ∈ tsupport (φ : ComplexChartSpace m → ℂ) :=
      dbarSchwartzCLM_tsupport_subset j φ hz
    exact (hGF (hK_sub_V hzK)).symm
  · intro z hz
    exact
      dbarSchwartzCLM_eq_zero_on_of_eqOn_holomorphic
        U V hU_open F hF_holo G hV_open hV_U hGF j (hK_sub_V hz)

/-- Local holomorphic factors pair trivially with `∂bar` derivatives of
Schwartz tests supported in the holomorphicity domain. -/
theorem integral_holomorphic_mul_dbarSchwartz_eq_zero
    (U : Set (ComplexChartSpace m))
    (hU_open : IsOpen U)
    (F : ComplexChartSpace m → ℂ)
    (hF_holo : DifferentiableOn ℂ F U)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U)
    (j : Fin m) :
    (∫ z : ComplexChartSpace m, F z * (dbarSchwartzCLM j φ) z) = 0 := by
  obtain ⟨G, hFG, hG_dbar_zero⟩ :=
    exists_local_dbarClosed_schwartz_representative
      U hU_open F hF_holo φ hφ j
  exact
    integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz
      F G φ j hFG hG_dbar_zero

/-- A product-kernel represented by local holomorphic scalar kernels kills
product tests whose complex-chart factor is a `∂bar` derivative. -/
theorem regularizedEnvelope_productKernel_dbar_eq_zero
    {r : ℝ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (U0 : Set (ComplexChartSpace m))
    (hU0_open : IsOpen U0)
    (hG_holo :
      ∀ ψ, KernelSupportWithin ψ r → DifferentiableOn ℂ (G ψ) U0)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, G ψ z * φ z)
    (j : Fin m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ : KernelSupportWithin ψ r) :
    K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0 := by
  rw [hK_rep (dbarSchwartzCLM j φ) ψ (hφ.dbar j) hψ]
  exact
    integral_holomorphic_mul_dbarSchwartz_eq_zero
      U0 hU0_open (G ψ) (hG_holo ψ hψ) φ hφ j

/-- Localized version of `regularizedEnvelope_productKernel_dbar_eq_zero`
where the product-kernel representation is valid on a covariance window and
the holomorphic scalar kernel is known on a larger fixed window. -/
theorem regularizedEnvelope_productKernel_dbar_eq_zero_local
    {r : ℝ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (Udesc Ucov U0 : Set (ComplexChartSpace m))
    (hUdesc_open : IsOpen Udesc)
    (hdesc_cov : Udesc ⊆ Ucov)
    (hcov_window : Ucov ⊆ U0)
    (hG_holo :
      ∀ ψ, KernelSupportWithin ψ r → DifferentiableOn ℂ (G ψ) U0)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucov →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, G ψ z * φ z)
    (j : Fin m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ : KernelSupportWithin ψ r) :
    K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0 := by
  have hdbar_desc :
      SupportsInOpen
        ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
          ComplexChartSpace m → ℂ) Udesc :=
    hφ.dbar j
  have hdbar_cov :
      SupportsInOpen
        ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
          ComplexChartSpace m → ℂ) Ucov :=
    ⟨hdbar_desc.1, hdbar_desc.2.trans hdesc_cov⟩
  rw [hK_rep (dbarSchwartzCLM j φ) ψ hdbar_cov hψ]
  exact
    integral_holomorphic_mul_dbarSchwartz_eq_zero
      Udesc hUdesc_open (G ψ)
      ((hG_holo ψ hψ).mono (hdesc_cov.trans hcov_window)) φ hφ j

/-- If the descended product kernel kills all `∂bar` product tests against a
fixed compact-supported approximate identity, then the descended distribution
is distributionally holomorphic on the chart domain. -/
theorem translationCovariantKernel_distributionalHolomorphic
    {r : ℝ} {ι : Type*} {l : Filter ι} [NeBot l]
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (ψι : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_support : ∀ᶠ i in l, KernelSupportWithin (ψι i) r)
    (hψ_approx :
      ∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
        Tendsto
          (fun i => realConvolutionTest θ (ψι i))
          l
          (nhds θ))
    (hdesc :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        K (schwartzTensorProduct₂ φ ψ) =
          Hdist (realConvolutionTest φ ψ))
    (hK_dbar_zero :
      ∀ (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0) :
    IsDistributionalHolomorphicOn Hdist U0 := by
  intro j φ hφ
  let θ : SchwartzMap (ComplexChartSpace m) ℂ := dbarSchwartzCLM j φ
  have hlim :
      Tendsto (fun i => Hdist (realConvolutionTest θ (ψι i)))
        l (nhds (Hdist θ)) :=
    (Hdist.continuous.tendsto θ).comp (hψ_approx θ)
  have hzero_eventually :
      ∀ᶠ i in l, Hdist (realConvolutionTest θ (ψι i)) = 0 := by
    filter_upwards [hψ_support] with i hi
    have hK0 := hK_dbar_zero j φ (ψι i) hφ hi
    have hdesc_i := hdesc θ (ψι i)
    rw [← hdesc_i]
    exact hK0
  have heq :
      (fun i => Hdist (realConvolutionTest θ (ψι i))) =ᶠ[l]
        fun _ => (0 : ℂ) :=
    hzero_eventually
  have hlim0 :
      Tendsto (fun i => Hdist (realConvolutionTest θ (ψι i)))
        l (nhds (0 : ℂ)) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique hlim hlim0

/-- Local product-test descent version of
`translationCovariantKernel_distributionalHolomorphic`.  The descent identity
is only required for complex-chart tests supported in the local domain. -/
theorem translationCovariantKernel_distributionalHolomorphic_local
    {r : ℝ} {ι : Type*} {l : Filter ι} [NeBot l]
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Udesc : Set (ComplexChartSpace m))
    (ψι : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_support : ∀ᶠ i in l, KernelSupportWithin (ψι i) r)
    (hψ_approx :
      ∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
        Tendsto
          (fun i => realConvolutionTest θ (ψι i))
          l
          (nhds θ))
    (hdesc_local :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            Hdist (realConvolutionTest φ ψ))
    (hK_dbar_zero :
      ∀ (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0) :
    IsDistributionalHolomorphicOn Hdist Udesc := by
  intro j φ hφ
  let θ : SchwartzMap (ComplexChartSpace m) ℂ := dbarSchwartzCLM j φ
  have hθ_support :
      SupportsInOpen (θ : ComplexChartSpace m → ℂ) Udesc := by
    simpa [θ] using hφ.dbar j
  have hlim :
      Tendsto (fun i => Hdist (realConvolutionTest θ (ψι i)))
        l (nhds (Hdist θ)) :=
    (Hdist.continuous.tendsto θ).comp (hψ_approx θ)
  have hzero_eventually :
      ∀ᶠ i in l, Hdist (realConvolutionTest θ (ψι i)) = 0 := by
    filter_upwards [hψ_support] with i hi
    have hK0 := hK_dbar_zero j φ (ψι i) hφ hi
    have hdesc_i := hdesc_local θ (ψι i) hθ_support hi
    rw [← hdesc_i]
    exact hK0
  have heq :
      (fun i => Hdist (realConvolutionTest θ (ψι i))) =ᶠ[l]
        fun _ => (0 : ℂ) :=
    hzero_eventually
  have hlim0 :
      Tendsto (fun i => Hdist (realConvolutionTest θ (ψι i)))
        l (nhds (0 : ℂ)) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique hlim hlim0

end SCV
