/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWSupport
import OSReconstruction.SCV.LocalDescentSupport
import OSReconstruction.SCV.VaryingKernelContinuity

/-!
# Mixed Pairing CLM for Local Distributional EOW

This file contains the local product-kernel pairing construction used by the
Streater-Wightman/Jost regularization route.  The construction integrates the
actual cutoff envelope on a compact chart ball, using the chart-kernel value
CLM only for linearity and finite-seminorm bounds.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

variable {m : ℕ}

/-- Build the mixed Schwartz continuous linear functional for the fixed local
EOW window once the chart-kernel value CLM and the actual cutoff-envelope
continuity theorem are available. -/
theorem regularizedLocalEOW_pairingCLM_of_fixedWindow
    (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (δ Rcov Rcut r : ℝ)
    (hRcov_pos : 0 < Rcov) (hRcov_cut : Rcov < Rcut)
    (hRcut_window :
      Metric.closedBall (0 : ComplexChartSpace m) Rcut ⊆
        Metric.ball (0 : ComplexChartSpace m) (δ / 2))
    (χU : SchwartzMap (ComplexChartSpace m) ℂ)
    (χr χψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hχU_one :
      ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcov,
        χU z = 1)
    (Gorig : SchwartzMap (Fin m → ℝ) ℂ →
      ComplexChartSpace m → ℂ)
    (Lchart : ComplexChartSpace m →
      SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hLchart_cutoff :
      ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        Lchart z ψ =
          Gorig
            (SchwartzMap.smulLeftCLM ℂ
              (χψ : (Fin m → ℝ) → ℂ)
              (localEOWRealLinearKernelPushforwardCLM ys hli
                (SchwartzMap.smulLeftCLM ℂ
                  (χr : (Fin m → ℝ) → ℂ) ψ))) z)
    (hLchart_value :
      ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        KernelSupportWithin ψ r →
          Lchart z ψ =
            Gorig (localEOWRealLinearKernelPushforwardCLM ys hli ψ) z)
    (hLchart_bound :
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          ‖Lchart z ψ‖ ≤
            C * s.sup
              (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ)
    (hcont_integrand :
      ∀ F : SchwartzMap
          (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
        ContinuousOn
          (fun z : ComplexChartSpace m =>
            χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : (Fin m → ℝ) → ℂ)
                  (localEOWRealLinearKernelPushforwardCLM ys hli
                    (SchwartzMap.smulLeftCLM ℂ
                      (χr : (Fin m → ℝ) → ℂ)
                      (schwartzPartialEval₁CLM z F)))) z)
          (Metric.closedBall (0 : ComplexChartSpace m) Rcut))
    (hG_holo :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        KernelSupportWithin ψ r →
          DifferentiableOn ℂ
            (Gorig (localEOWRealLinearKernelPushforwardCLM ys hli ψ))
            (Metric.ball (0 : ComplexChartSpace m) (δ / 2))) :
    let Ucov := Metric.ball (0 : ComplexChartSpace m) Rcov
    let Gchart : SchwartzMap (Fin m → ℝ) ℂ →
        ComplexChartSpace m → ℂ :=
      fun ψ => Gorig (localEOWRealLinearKernelPushforwardCLM ys hli ψ)
    ∃ K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ,
      (∀ ψ, KernelSupportWithin ψ r →
        DifferentiableOn ℂ (Gchart ψ)
          (Metric.ball (0 : ComplexChartSpace m) (δ / 2))) ∧
      (∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucov →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, Gchart ψ z * φ z) := by
  classical
  let D := Fin m → ℝ
  let X := ComplexChartSpace m
  let P : SchwartzMap D ℂ →L[ℂ] SchwartzMap D ℂ :=
    localEOWRealLinearKernelPushforwardCLM ys hli
  let sball : Set X := Metric.closedBall (0 : X) Rcut
  let pMixed :=
    schwartzSeminormFamily ℂ (ComplexChartSpace m × (Fin m → ℝ)) ℂ
  let A : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ → ℂ := fun F =>
    ∫ z in sball,
      χU z *
        Gorig
          (SchwartzMap.smulLeftCLM ℂ
            (χψ : D → ℂ)
            (P (SchwartzMap.smulLeftCLM ℂ
              (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z
  have hs_compact : IsCompact sball := by
    simpa [sball, X] using
      (isCompact_closedBall (0 : ComplexChartSpace m) Rcut)
  have hs_meas : MeasurableSet sball := hs_compact.measurableSet
  have hs_fin : volume sball < ⊤ := by
    simpa [sball, X] using
      (measure_closedBall_lt_top
        (x := (0 : ComplexChartSpace m)) (r := Rcut))
  have hA_integrable :
      ∀ F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
        Integrable
          (fun z : X =>
            χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z)
          (volume.restrict sball) := by
    intro F
    exact ContinuousOn.integrableOn_compact hs_compact
      (by simpa [sball, X, D, P] using hcont_integrand F)
  have hadd :
      ∀ F H : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
        A (F + H) = A F + A H := by
    intro F H
    have hpoint :
        EqOn
          (fun z : X =>
            χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ)
                    (schwartzPartialEval₁CLM z (F + H))))) z)
          (fun z : X =>
            χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z +
            χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ) (schwartzPartialEval₁CLM z H)))) z)
          sball := by
      intro z hz
      calc
        χU z *
            Gorig
              (SchwartzMap.smulLeftCLM ℂ
                (χψ : D → ℂ)
                (P (SchwartzMap.smulLeftCLM ℂ
                  (χr : D → ℂ)
                  (schwartzPartialEval₁CLM z (F + H))))) z
            =
          χU z * Lchart z (schwartzPartialEval₁CLM z (F + H)) := by
            rw [hLchart_cutoff z (by simpa [sball, X] using hz)]
        _ =
          χU z *
            (Lchart z (schwartzPartialEval₁CLM z F) +
              Lchart z (schwartzPartialEval₁CLM z H)) := by
            simp
        _ =
          χU z * Lchart z (schwartzPartialEval₁CLM z F) +
            χU z * Lchart z (schwartzPartialEval₁CLM z H) := by
            ring
        _ =
          χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z +
            χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ) (schwartzPartialEval₁CLM z H)))) z := by
            rw [hLchart_cutoff z (by simpa [sball, X] using hz)
                (schwartzPartialEval₁CLM z F)]
            rw [hLchart_cutoff z (by simpa [sball, X] using hz)
                (schwartzPartialEval₁CLM z H)]
    calc
      A (F + H)
          =
        ∫ z in sball,
          (χU z *
            Gorig
              (SchwartzMap.smulLeftCLM ℂ
                (χψ : D → ℂ)
                (P (SchwartzMap.smulLeftCLM ℂ
                  (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z +
          χU z *
            Gorig
              (SchwartzMap.smulLeftCLM ℂ
                (χψ : D → ℂ)
                (P (SchwartzMap.smulLeftCLM ℂ
                  (χr : D → ℂ) (schwartzPartialEval₁CLM z H)))) z) := by
          apply MeasureTheory.setIntegral_congr_fun hs_meas hpoint
      _ = A F + A H := by
          simpa [A] using
            (MeasureTheory.integral_add
              (μ := volume.restrict sball)
              (f := fun z : X =>
                χU z *
                  Gorig
                    (SchwartzMap.smulLeftCLM ℂ
                      (χψ : D → ℂ)
                      (P (SchwartzMap.smulLeftCLM ℂ
                        (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z)
              (g := fun z : X =>
                χU z *
                  Gorig
                    (SchwartzMap.smulLeftCLM ℂ
                      (χψ : D → ℂ)
                      (P (SchwartzMap.smulLeftCLM ℂ
                        (χr : D → ℂ) (schwartzPartialEval₁CLM z H)))) z)
              (hA_integrable F) (hA_integrable H))
  have hsmul :
      ∀ (c : ℂ) (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ),
        A (c • F) = c • A F := by
    intro c F
    have hpoint :
        EqOn
          (fun z : X =>
            χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ)
                    (schwartzPartialEval₁CLM z (c • F))))) z)
          (fun z : X =>
            c *
              (χU z *
                Gorig
                  (SchwartzMap.smulLeftCLM ℂ
                    (χψ : D → ℂ)
                    (P (SchwartzMap.smulLeftCLM ℂ
                      (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z))
          sball := by
      intro z hz
      calc
        χU z *
            Gorig
              (SchwartzMap.smulLeftCLM ℂ
                (χψ : D → ℂ)
                (P (SchwartzMap.smulLeftCLM ℂ
                  (χr : D → ℂ)
                  (schwartzPartialEval₁CLM z (c • F))))) z
            =
          χU z * Lchart z (schwartzPartialEval₁CLM z (c • F)) := by
            rw [hLchart_cutoff z (by simpa [sball, X] using hz)]
        _ = χU z * (c * Lchart z (schwartzPartialEval₁CLM z F)) := by
            simp [smul_eq_mul]
        _ = c *
            (χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z) := by
            rw [hLchart_cutoff z (by simpa [sball, X] using hz)
                (schwartzPartialEval₁CLM z F)]
            ring
    calc
      A (c • F)
          =
        ∫ z in sball,
          c *
            (χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z) := by
          apply MeasureTheory.setIntegral_congr_fun hs_meas hpoint
      _ = c • A F := by
          simpa [A, smul_eq_mul] using
            (MeasureTheory.integral_const_mul
              (μ := volume.restrict sball) c
              (fun z : X =>
                χU z *
                  Gorig
                    (SchwartzMap.smulLeftCLM ℂ
                      (χψ : D → ℂ)
                      (P (SchwartzMap.smulLeftCLM ℂ
                        (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z))
  have hbound_exists :
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
          ‖A F‖ ≤ C * s.sup pMixed F := by
    rcases hLchart_bound with ⟨sL, CL, hCL, hLbound⟩
    have hRcut_nonneg : 0 ≤ Rcut := by
      exact le_of_lt (lt_trans hRcov_pos hRcov_cut)
    obtain ⟨sPE, CPE, hCPE, hPE⟩ :=
      schwartzPartialEval₁CLM_compactSeminormBound (m := m)
        Rcut hRcut_nonneg sL
    obtain ⟨M, hM⟩ :=
      hs_compact.exists_bound_of_continuousOn
        (f := fun z : X => ‖χU z‖)
        (by simpa [sball, X] using
          ((continuous_norm.comp χU.continuous).continuousOn))
    let Mχ : ℝ := max M 0
    have hMχ_nonneg : 0 ≤ Mχ := by
      simp [Mχ]
    let Cpoint : ℝ := Mχ * CL * CPE
    let Cfinal : ℝ := Cpoint * (volume sball).toReal
    refine ⟨sPE, Cfinal, ?_, ?_⟩
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg hMχ_nonneg hCL) hCPE)
        ENNReal.toReal_nonneg
    · intro F
      have hsup_nonneg : 0 ≤ sPE.sup pMixed F := apply_nonneg _ _
      have hpoint_bound :
          ∀ z ∈ sball,
            ‖χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z‖
              ≤ Cpoint * sPE.sup pMixed F := by
        intro z hz
        have hχ_bound : ‖χU z‖ ≤ Mχ := by
          have hMz : ‖χU z‖ ≤ M := by
            simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (χU z))]
              using hM z hz
          exact hMz.trans (le_max_left M 0)
        have hcut :
            Gorig
              (SchwartzMap.smulLeftCLM ℂ
                (χψ : D → ℂ)
                (P (SchwartzMap.smulLeftCLM ℂ
                  (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z =
              Lchart z (schwartzPartialEval₁CLM z F) := by
          exact (hLchart_cutoff z (by simpa [sball, X] using hz)
            (schwartzPartialEval₁CLM z F)).symm
        have hL :
            ‖Lchart z (schwartzPartialEval₁CLM z F)‖ ≤
              CL * sL.sup (schwartzSeminormFamily ℂ D ℂ)
                (schwartzPartialEval₁CLM z F) :=
          hLbound z (by simpa [sball, X] using hz) (schwartzPartialEval₁CLM z F)
        have hPE' :
            sL.sup (schwartzSeminormFamily ℂ D ℂ)
                (schwartzPartialEval₁CLM z F) ≤
              CPE * sPE.sup pMixed F := by
          simpa [D, X, pMixed] using hPE z
            (by simpa [sball, X] using hz) F
        have hLmix :
            ‖Lchart z (schwartzPartialEval₁CLM z F)‖ ≤
              (CL * CPE) * sPE.sup pMixed F := by
          calc
            ‖Lchart z (schwartzPartialEval₁CLM z F)‖
                ≤ CL *
                    sL.sup (schwartzSeminormFamily ℂ D ℂ)
                      (schwartzPartialEval₁CLM z F) := hL
            _ ≤ CL * (CPE * sPE.sup pMixed F) := by
                exact mul_le_mul_of_nonneg_left hPE' hCL
            _ = (CL * CPE) * sPE.sup pMixed F := by ring
        calc
          ‖χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ
                  (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ
                    (χr : D → ℂ) (schwartzPartialEval₁CLM z F)))) z‖
              = ‖χU z‖ * ‖Lchart z (schwartzPartialEval₁CLM z F)‖ := by
                rw [hcut, norm_mul]
          _ ≤ Mχ * ((CL * CPE) * sPE.sup pMixed F) := by
              exact mul_le_mul hχ_bound hLmix
                (norm_nonneg _) hMχ_nonneg
          _ = Cpoint * sPE.sup pMixed F := by
              ring
      calc
        ‖A F‖
            ≤ (Cpoint * sPE.sup pMixed F) * (volume sball).toReal := by
              simpa [A, Cpoint] using
                (MeasureTheory.norm_setIntegral_le_of_norm_le_const
                  (μ := volume) hs_fin hpoint_bound)
        _ = Cfinal * sPE.sup pMixed F := by
            ring
  let K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) A hadd hsmul hbound_exists
  let Ucov : Set (ComplexChartSpace m) :=
    Metric.ball (0 : ComplexChartSpace m) Rcov
  let Gchart : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
    fun ψ => Gorig (P ψ)
  refine ⟨K, ?_, ?_⟩
  · intro ψ hψ
    simpa [Gchart, P] using hG_holo ψ hψ
  · intro φ ψ hφ hψ
    have hUcov_open : IsOpen Ucov := by
      change IsOpen (Metric.ball (0 : ComplexChartSpace m) Rcov)
      exact Metric.isOpen_ball
    have hUcov_closedBall : Ucov ⊆ sball := by
      intro z hz
      have hz_closed :
          z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcov :=
        Metric.ball_subset_closedBall hz
      exact
        (Metric.closedBall_subset_closedBall (le_of_lt hRcov_cut) hz_closed)
    have hUcov_window :
        Ucov ⊆ Metric.ball (0 : ComplexChartSpace m) (δ / 2) := by
      intro z hz
      exact hRcut_window (by simpa [sball, X] using hUcov_closedBall hz)
    have hG_cont : ContinuousOn (Gchart ψ) Ucov := by
      have hdiff :
          DifferentiableOn ℂ (Gchart ψ)
            (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) := by
        simpa [Gchart, P] using hG_holo ψ hψ
      exact hdiff.continuousOn.mono hUcov_window
    have hpure_set :
        A (schwartzTensorProduct₂ φ ψ) =
          ∫ z in sball, Gchart ψ z * φ z := by
      apply MeasureTheory.setIntegral_congr_fun hs_meas
      intro z hz
      calc
        χU z *
            Gorig
              (SchwartzMap.smulLeftCLM ℂ
                (χψ : D → ℂ)
                (P (SchwartzMap.smulLeftCLM ℂ
                  (χr : D → ℂ)
                  (schwartzPartialEval₁CLM z
                    (schwartzTensorProduct₂ φ ψ))))) z
            =
          χU z * Lchart z
            (schwartzPartialEval₁CLM z (schwartzTensorProduct₂ φ ψ)) := by
            rw [hLchart_cutoff z (by simpa [sball, X] using hz)]
        _ = χU z * Lchart z (φ z • ψ) := by
            rw [schwartzPartialEval₁CLM_tensorProduct₂]
        _ = Gchart ψ z * φ z := by
            by_cases hzφ : z ∈ tsupport (φ : ComplexChartSpace m → ℂ)
            · have hχ : χU z = 1 := by
                exact hχU_one z (Metric.ball_subset_closedBall (hφ.2 hzφ))
              have hLval : Lchart z ψ = Gchart ψ z := by
                simpa [Gchart, P] using
                  hLchart_value z (by simpa [sball, X] using hz) ψ hψ
              rw [map_smul, hχ, hLval]
              simp [smul_eq_mul]
              ring
            · have hφz : φ z = 0 := by
                have hz_support :
                    z ∉ Function.support
                      (φ : ComplexChartSpace m → ℂ) := by
                  intro hsupp
                  exact hzφ (subset_closure hsupp)
                simpa [Function.mem_support] using hz_support
              simp [hφz]
    have hset_all :
        (∫ z in sball, Gchart ψ z * φ z) =
          ∫ z : ComplexChartSpace m, Gchart ψ z * φ z := by
      simpa [Ucov, sball, Gchart, P] using
        closedBall_setIntegral_mul_eq_integral_of_supportsInOpen
          (m := m) hUcov_open hUcov_closedBall (Gchart ψ) φ hG_cont hφ
    calc
      K (schwartzTensorProduct₂ φ ψ)
          = A (schwartzTensorProduct₂ φ ψ) := rfl
      _ = ∫ z in sball, Gchart ψ z * φ z := hpure_set
      _ = ∫ z : ComplexChartSpace m, Gchart ψ z * φ z := hset_all

/-- The mixed pairing CLM is locally covariant under real translations on the
declared support window. -/
theorem regularizedLocalEOW_pairingCLM_localCovariant
    {m : ℕ} {δ : ℝ}
    (hm : 0 < m) (hδ : 0 < δ)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Gchart : SchwartzMap (Fin m → ℝ) ℂ →
      ComplexChartSpace m → ℂ)
    (Rcov r : ℝ)
    (hRcov_small : 2 * Rcov < δ / 4)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ)
          (Metric.ball (0 : ComplexChartSpace m) Rcov) →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, Gchart ψ z * φ z)
    (hG_cont :
      ∀ ψ, KernelSupportWithin ψ r →
        ContinuousOn (Gchart ψ)
          (Metric.ball (0 : ComplexChartSpace m) Rcov))
    (hG_cov :
      ∀ a ψ,
        KernelSupportWithin ψ r →
        KernelSupportWithin (translateSchwartz a ψ) r →
        (∃ z0, z0 ∈ localEOWShiftedWindow (m := m) δ a ∧
          (∀ j, 0 < (z0 j).im)) →
        ∀ w ∈ localEOWShiftedWindow (m := m) δ a,
          Gchart (translateSchwartz a ψ) w =
            Gchart ψ (w - realEmbed a)) :
    ProductKernelRealTranslationCovariantLocal K
      (Metric.ball (0 : ComplexChartSpace m) Rcov) r := by
  intro a φ ψ hφ hφ_shift hψ hψ_shift
  by_cases hφ_zero : φ = 0
  · have hleft := hK_rep (complexTranslateSchwartz a φ) ψ hφ_shift hψ
    have hright := hK_rep φ (translateSchwartz a ψ) hφ hψ_shift
    calc
      K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ)
          = ∫ z : ComplexChartSpace m,
              Gchart ψ z * complexTranslateSchwartz a φ z := hleft
      _ = 0 := by
          simp [hφ_zero, complexTranslateSchwartz_apply]
      _ = ∫ z : ComplexChartSpace m,
              Gchart (translateSchwartz a ψ) z * φ z := by
          simp [hφ_zero]
      _ = K (schwartzTensorProduct₂ φ (translateSchwartz a ψ)) := hright.symm
  · have hφ_nonzero_point :
        ∃ u : ComplexChartSpace m, φ u ≠ 0 := by
      by_contra hnone
      apply hφ_zero
      ext u
      have hu_not : ¬ φ u ≠ 0 := (not_exists.mp hnone) u
      exact not_not.mp hu_not
    rcases hφ_nonzero_point with ⟨u, hu_ne⟩
    have hu_support :
        u ∈ Function.support (φ : ComplexChartSpace m → ℂ) := by
      simpa [Function.mem_support] using hu_ne
    have hu_tsupport :
        u ∈ tsupport (φ : ComplexChartSpace m → ℂ) :=
      subset_closure hu_support
    have hu_U :
        u ∈ Metric.ball (0 : ComplexChartSpace m) Rcov :=
      hφ.2 hu_tsupport
    have hu_shift_ne :
        complexTranslateSchwartz a φ (u - realEmbed a) ≠ 0 := by
      have harg : u - realEmbed a + realEmbed a = u := by
        ext i
        simp
      simpa [complexTranslateSchwartz_apply, harg] using hu_ne
    have hu_shift_support :
        u - realEmbed a ∈
          Function.support
            (complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) := by
      simpa [Function.mem_support] using hu_shift_ne
    have hu_shift_tsupport :
        u - realEmbed a ∈
          tsupport
            (complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) :=
      subset_closure hu_shift_support
    have hu_shift_U :
        u - realEmbed a ∈ Metric.ball (0 : ComplexChartSpace m) Rcov :=
      hφ_shift.2 hu_shift_tsupport
    have hu_norm : ‖u‖ < Rcov := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu_U
    have hu_shift_norm : ‖u - realEmbed a‖ < Rcov := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu_shift_U
    have ha_complex : ‖realEmbed a‖ < 2 * Rcov := by
      calc
        ‖realEmbed a‖ = ‖u - (u - realEmbed a)‖ := by
          congr 1
          ext i
          simp
        _ ≤ ‖u‖ + ‖u - realEmbed a‖ := by
          simpa using norm_sub_le u (u - realEmbed a)
        _ < Rcov + Rcov := add_lt_add hu_norm hu_shift_norm
        _ = 2 * Rcov := by ring
    have ha : ‖a‖ < δ / 4 := by
      rw [← norm_realEmbed_eq (m := m) a]
      exact lt_trans ha_complex hRcov_small
    have hseed :
        ∃ z0, z0 ∈ localEOWShiftedWindow (m := m) δ a ∧
          (∀ j, 0 < (z0 j).im) :=
      exists_positive_imag_mem_localEOWShiftedWindow_of_norm_lt hm hδ ha
    have hshift_support :
        ∀ z ∈ tsupport (φ : ComplexChartSpace m → ℂ),
          z - realEmbed a ∈ Metric.ball (0 : ComplexChartSpace m) Rcov := by
      intro z hz
      exact hφ_shift.2
        (tsupport_subset_preimage_tsupport_complexTranslateSchwartz a φ hz)
    have hleft := hK_rep (complexTranslateSchwartz a φ) ψ hφ_shift hψ
    have hright := hK_rep φ (translateSchwartz a ψ) hφ hψ_shift
    have hintegral :
        (∫ z : ComplexChartSpace m,
          Gchart ψ z * complexTranslateSchwartz a φ z) =
          ∫ z : ComplexChartSpace m,
            Gchart (translateSchwartz a ψ) z * φ z := by
      calc
        (∫ z : ComplexChartSpace m,
          Gchart ψ z * complexTranslateSchwartz a φ z)
            =
          ∫ z : ComplexChartSpace m, Gchart ψ (z - realEmbed a) * φ z := by
            exact
              integral_mul_complexTranslateSchwartz_eq_shift_of_support
                (Gchart ψ) φ a (Metric.ball (0 : ComplexChartSpace m) Rcov)
                (hG_cont ψ hψ) hφ.1 hφ_shift hshift_support
        _ = ∫ z : ComplexChartSpace m,
              Gchart (translateSchwartz a ψ) z * φ z := by
            apply integral_congr_ae
            filter_upwards with z
            by_cases hzφ : φ z = 0
            · simp [hzφ]
            · have hz_support :
                  z ∈ Function.support (φ : ComplexChartSpace m → ℂ) := by
                simpa [Function.mem_support] using hzφ
              have hz_tsupport :
                  z ∈ tsupport (φ : ComplexChartSpace m → ℂ) :=
                subset_closure hz_support
              have hz_U :
                  z ∈ Metric.ball (0 : ComplexChartSpace m) Rcov :=
                hφ.2 hz_tsupport
              have hz_shift_U :
                  z - realEmbed a ∈
                    Metric.ball (0 : ComplexChartSpace m) Rcov :=
                hshift_support z hz_tsupport
              have hRcov_delta : Rcov ≤ δ / 2 := by
                linarith [hRcov_small, hδ]
              have hz_window :
                  z ∈ localEOWShiftedWindow (m := m) δ a := by
                constructor
                · have hz_norm : ‖z‖ < Rcov := by
                    simpa [Metric.mem_ball, dist_eq_norm] using hz_U
                  exact Metric.mem_ball.mpr (by
                    simpa [dist_eq_norm] using
                      (lt_of_lt_of_le hz_norm hRcov_delta))
                · have hz_shift_norm : ‖z - realEmbed a‖ < Rcov := by
                    simpa [Metric.mem_ball, dist_eq_norm] using hz_shift_U
                  change z - realEmbed a ∈
                    Metric.ball (0 : ComplexChartSpace m) (δ / 2)
                  exact Metric.mem_ball.mpr (by
                    simpa [dist_eq_norm] using
                      (lt_of_lt_of_le hz_shift_norm hRcov_delta))
              have hcov := hG_cov a ψ hψ hψ_shift hseed z hz_window
              rw [← hcov]
    calc
      K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ)
          = ∫ z : ComplexChartSpace m,
              Gchart ψ z * complexTranslateSchwartz a φ z := hleft
      _ = ∫ z : ComplexChartSpace m,
              Gchart (translateSchwartz a ψ) z * φ z := hintegral
      _ = K (schwartzTensorProduct₂ φ (translateSchwartz a ψ)) := hright.symm

/-- Local covariance for the mixed pairing CLM in the fixed-window EOW
instantiation.

This combines the pointwise shifted-overlap covariance theorem for the explicit
fixed-window family with the support budget for chart-kernel pushforward.  The
two kernel support hypotheses supplied by
`ProductKernelRealTranslationCovariantLocal` are used separately; no step
asserts that translating a chart kernel preserves a fixed support radius. -/
theorem regularizedLocalEOW_pairingCLM_localCovariant_from_fixedWindow
    {Cplus Cminus : Set (Fin m → ℝ)} {rψ ρ r δ Rcov Rmix σ : ℝ}
    (hm : 0 < m) (hδ : 0 < δ)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωplus)
    (hminus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (hli : LinearIndependent ℝ ys)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (hRcov_small : 2 * Rcov < δ / 4)
    (hRmix_le : Rmix ≤ 4 * σ)
    (hA4 :
      ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          (4 * σ) ≤ rψ)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ)
          (Metric.ball (0 : ComplexChartSpace m) Rcov) →
        KernelSupportWithin ψ Rmix →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m,
              (localRudinEnvelope δ x0 ys
                (realMollifyLocal Fplus
                  (localEOWRealLinearKernelPushforwardCLM ys hli ψ))
                (realMollifyLocal Fminus
                  (localEOWRealLinearKernelPushforwardCLM ys hli ψ)) z) *
                φ z)
    (hG_cont :
      ∀ ψ, KernelSupportWithin ψ Rmix →
        ContinuousOn
          (fun z : ComplexChartSpace m =>
            localRudinEnvelope δ x0 ys
              (realMollifyLocal Fplus
                (localEOWRealLinearKernelPushforwardCLM ys hli ψ))
              (realMollifyLocal Fminus
                (localEOWRealLinearKernelPushforwardCLM ys hli ψ)) z)
          (Metric.ball (0 : ComplexChartSpace m) Rcov)) :
    ProductKernelRealTranslationCovariantLocal K
      (Metric.ball (0 : ComplexChartSpace m) Rcov) Rmix := by
  let Gchart : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
    fun ψ z =>
      localRudinEnvelope δ x0 ys
        (realMollifyLocal Fplus
          (localEOWRealLinearKernelPushforwardCLM ys hli ψ))
        (realMollifyLocal Fminus
          (localEOWRealLinearKernelPushforwardCLM ys hli ψ)) z
  apply regularizedLocalEOW_pairingCLM_localCovariant
    (m := m) hm hδ K Gchart Rcov Rmix hRcov_small
  · intro φ ψ hφ hψ
    simpa [Gchart] using hK_rep φ ψ hφ hψ
  · intro ψ hψ
    simpa [Gchart] using hG_cont ψ hψ
  · intro a ψ hψ hψ_shift hseed w hw
    have hPψ :
        KernelSupportWithin
          (localEOWRealLinearKernelPushforwardCLM ys hli ψ) rψ :=
      KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_of_le_four_mul
        ys hli hψ hRmix_le hA4
    have hPψ_shift :
        KernelSupportWithin
          (localEOWRealLinearKernelPushforwardCLM ys hli
            (translateSchwartz a ψ)) rψ :=
      KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_of_le_four_mul
        ys hli hψ_shift hRmix_le hA4
    simpa [Gchart] using
      regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap
        (m := m) (Cplus := Cplus) (Cminus := Cminus) (rψ := rψ)
        (ρ := ρ) (r := r) (δ := δ) hm Ωplus Ωminus Dplus Dminus E
        hΩplus_open hΩminus_open hDplus_open hDminus_open hE_open
        Fplus Fminus hFplus_diff hFminus_diff hplus_margin hminus_margin
        hDplus_sub hDminus_sub Tplus Tminus Tchart hplus_eval hminus_eval
        hplus_limit hminus_limit x0 ys hδ hδρ hδsum hE_mem hplus hminus
        hli ψ a hPψ hPψ_shift hseed w hw

end SCV
