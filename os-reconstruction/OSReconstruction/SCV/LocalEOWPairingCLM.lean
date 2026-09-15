/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWSupport
import OSReconstruction.SCV.LocalDescentSupport
import Init
import OSReconstruction.SCV.LocalDistributionalEOW










noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

variable {m : ℕ}

/-- Build a mixed Schwartz continuous linear functional from a locally
holomorphic family of continuous linear functionals on the real fiber.

The predicate `Good` records the support condition under which `G` agrees
with the globally controlled family `L`.  This separates the functional-
analytic construction from the geometric chart pushforward used by the EOW
application below. -/
theorem localHolomorphicFamily_pairingCLM_of_fixedWindow
    (Rcov Rcut : ℝ)
    (hRcov_pos : 0 < Rcov) (hRcov_cut : Rcov < Rcut)
    (Uhol : Set (ComplexChartSpace m))
    (hUcov_hol :
      Metric.ball (0 : ComplexChartSpace m) Rcov ⊆ Uhol)
    (χU : SchwartzMap (ComplexChartSpace m) ℂ)
    (hχU_one :
      ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcov,
        χU z = 1)
    (Good : SchwartzMap (Fin m → ℝ) ℂ → Prop)
    (G : SchwartzMap (Fin m → ℝ) ℂ →
      ComplexChartSpace m → ℂ)
    (L : ComplexChartSpace m →
      SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hL_value :
      ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        Good ψ → L z ψ = G ψ z)
    (hL_bound :
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          ‖L z ψ‖ ≤
            C * s.sup
              (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ)
    (hcont_integrand :
      ∀ F : SchwartzMap
          (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
        ContinuousOn
          (fun z : ComplexChartSpace m =>
            χU z * L z (schwartzPartialEval₁CLM z F))
          (Metric.closedBall (0 : ComplexChartSpace m) Rcut))
    (hG_holo :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        Good ψ → DifferentiableOn ℂ (G ψ) Uhol) :
    ∃ K : SchwartzMap
        (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ,
      (∀ ψ, Good ψ → DifferentiableOn ℂ (G ψ) Uhol) ∧
      (∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ)
          (Metric.ball (0 : ComplexChartSpace m) Rcov) →
        Good ψ →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, G ψ z * φ z) ∧
      ∀ F : SchwartzMap
          (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
        K F =
          ∫ z in Metric.closedBall
              (0 : ComplexChartSpace m) Rcut,
            χU z * L z (schwartzPartialEval₁CLM z F) := by
  classical
  let D := Fin m → ℝ
  let X := ComplexChartSpace m
  let sball : Set X := Metric.closedBall (0 : X) Rcut
  let pMixed :=
    schwartzSeminormFamily ℂ (ComplexChartSpace m × (Fin m → ℝ)) ℂ
  let A : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ → ℂ := fun F =>
    ∫ z in sball, χU z * L z (schwartzPartialEval₁CLM z F)
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
          (fun z : X => χU z * L z (schwartzPartialEval₁CLM z F))
          (volume.restrict sball) := by
    intro F
    exact ContinuousOn.integrableOn_compact hs_compact
      (by simpa [sball, X] using hcont_integrand F)
  have hadd :
      ∀ F H : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
        A (F + H) = A F + A H := by
    intro F H
    have hpoint :
        (fun z : X =>
            χU z * L z (schwartzPartialEval₁CLM z (F + H))) =
          fun z : X =>
            χU z * L z (schwartzPartialEval₁CLM z F) +
              χU z * L z (schwartzPartialEval₁CLM z H) := by
      funext z
      simp [mul_add]
    calc
      A (F + H) =
          ∫ z in sball,
            (χU z * L z (schwartzPartialEval₁CLM z F) +
              χU z * L z (schwartzPartialEval₁CLM z H)) := by
        simp only [A]
        rw [hpoint]
      _ = A F + A H := by
        simpa [A] using
          (MeasureTheory.integral_add
            (hA_integrable F) (hA_integrable H))
  have hsmul :
      ∀ (c : ℂ) (F : SchwartzMap
          (ComplexChartSpace m × (Fin m → ℝ)) ℂ),
        A (c • F) = c • A F := by
    intro c F
    have hpoint :
        (fun z : X =>
            χU z * L z (schwartzPartialEval₁CLM z (c • F))) =
          fun z : X =>
            c * (χU z * L z (schwartzPartialEval₁CLM z F)) := by
      funext z
      simp [smul_eq_mul]
      ring
    calc
      A (c • F) =
          ∫ z in sball,
            c * (χU z * L z (schwartzPartialEval₁CLM z F)) := by
        simp only [A]
        rw [hpoint]
      _ = c • A F := by
        simpa [A, smul_eq_mul] using
          (MeasureTheory.integral_const_mul
            (μ := volume.restrict sball) c
            (fun z : X =>
              χU z * L z (schwartzPartialEval₁CLM z F)))
  have hbound_exists :
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ F : SchwartzMap
            (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
          ‖A F‖ ≤ C * s.sup pMixed F := by
    rcases hL_bound with ⟨sL, CL, hCL, hLbound⟩
    have hRcut_nonneg : 0 ≤ Rcut :=
      le_of_lt (lt_trans hRcov_pos hRcov_cut)
    obtain ⟨sPE, CPE, hCPE, hPE⟩ :=
      schwartzPartialEval₁CLM_compactSeminormBound (m := m)
        Rcut hRcut_nonneg sL
    have hχ_cont : Continuous (fun z : X => ‖χU z‖) := by
      fun_prop
    obtain ⟨M, hM⟩ :=
      hs_compact.exists_bound_of_continuousOn
        (f := fun z : X => ‖χU z‖) hχ_cont.continuousOn
    let Mχ : ℝ := max M 0
    let Cpoint : ℝ := Mχ * CL * CPE
    let Cfinal : ℝ := Cpoint * (volume sball).toReal
    refine ⟨sPE, Cfinal, ?_, ?_⟩
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by simp [Mχ]) hCL) hCPE)
        ENNReal.toReal_nonneg
    · intro F
      have hpoint_bound :
          ∀ z ∈ sball,
            ‖χU z * L z (schwartzPartialEval₁CLM z F)‖ ≤
              Cpoint * sPE.sup pMixed F := by
        intro z hz
        have hχ_bound : ‖χU z‖ ≤ Mχ := by
          have hMz : ‖χU z‖ ≤ M := by
            simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (χU z))]
              using hM z hz
          exact hMz.trans (le_max_left M 0)
        have hL :
            ‖L z (schwartzPartialEval₁CLM z F)‖ ≤
              CL * sL.sup (schwartzSeminormFamily ℂ D ℂ)
                (schwartzPartialEval₁CLM z F) :=
          hLbound z (by simpa [sball, X] using hz)
            (schwartzPartialEval₁CLM z F)
        have hPE' :
            sL.sup (schwartzSeminormFamily ℂ D ℂ)
                (schwartzPartialEval₁CLM z F) ≤
              CPE * sPE.sup pMixed F := by
          simpa [D, X, pMixed] using
            hPE z (by simpa [sball, X] using hz) F
        have hLmix :
            ‖L z (schwartzPartialEval₁CLM z F)‖ ≤
              (CL * CPE) * sPE.sup pMixed F := by
          calc
            ‖L z (schwartzPartialEval₁CLM z F)‖
                ≤ CL * sL.sup (schwartzSeminormFamily ℂ D ℂ)
                    (schwartzPartialEval₁CLM z F) := hL
            _ ≤ CL * (CPE * sPE.sup pMixed F) := by
                exact mul_le_mul_of_nonneg_left hPE' hCL
            _ = (CL * CPE) * sPE.sup pMixed F := by ring
        calc
          ‖χU z * L z (schwartzPartialEval₁CLM z F)‖
              = ‖χU z‖ * ‖L z (schwartzPartialEval₁CLM z F)‖ :=
                norm_mul _ _
          _ ≤ Mχ * ((CL * CPE) * sPE.sup pMixed F) := by
              exact mul_le_mul hχ_bound hLmix
                (norm_nonneg _) (by simp [Mχ])
          _ = Cpoint * sPE.sup pMixed F := by ring
      calc
        ‖A F‖ ≤
            (Cpoint * sPE.sup pMixed F) * (volume sball).toReal := by
          rw [← Measure.real_def]
          simpa only [A] using
            (MeasureTheory.norm_setIntegral_le_of_norm_le_const
              (μ := volume) hs_fin hpoint_bound)
        _ = Cfinal * sPE.sup pMixed F := by ring
  let K : SchwartzMap
      (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) A hadd hsmul hbound_exists
  refine ⟨K, hG_holo, ?_, ?_⟩
  · intro φ ψ hφ hψ
    let Ucov : Set (ComplexChartSpace m) :=
      Metric.ball (0 : ComplexChartSpace m) Rcov
    have hUcov_open : IsOpen Ucov := Metric.isOpen_ball
    have hUcov_closedBall : Ucov ⊆ sball := by
      intro z hz
      exact Metric.closedBall_subset_closedBall (le_of_lt hRcov_cut)
        (Metric.ball_subset_closedBall hz)
    have hG_cont : ContinuousOn (G ψ) Ucov :=
      (hG_holo ψ hψ).continuousOn.mono hUcov_hol
    have hpure_set :
        A (schwartzTensorProduct₂ φ ψ) =
          ∫ z in sball, G ψ z * φ z := by
      apply MeasureTheory.setIntegral_congr_fun hs_meas
      intro z hz
      change
        χU z * L z
            (schwartzPartialEval₁CLM z (schwartzTensorProduct₂ φ ψ)) =
          G ψ z * φ z
      rw [schwartzPartialEval₁CLM_tensorProduct₂]
      by_cases hzφ : z ∈ tsupport (φ : ComplexChartSpace m → ℂ)
      · have hχ : χU z = 1 :=
          hχU_one z (Metric.ball_subset_closedBall (hφ.2 hzφ))
        have hLval : L z ψ = G ψ z :=
          hL_value z (by simpa [sball, X] using hz) ψ hψ
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
        (∫ z in sball, G ψ z * φ z) =
          ∫ z : ComplexChartSpace m, G ψ z * φ z := by
      simpa [Ucov, sball] using
        closedBall_setIntegral_mul_eq_integral_of_supportsInOpen
          (m := m) hUcov_open hUcov_closedBall (G ψ) φ hG_cont hφ
    calc
      K (schwartzTensorProduct₂ φ ψ)
          = A (schwartzTensorProduct₂ φ ψ) := rfl
      _ = ∫ z in sball, G ψ z * φ z := hpure_set
      _ = ∫ z : ComplexChartSpace m, G ψ z * φ z := hset_all
  · intro F
    rfl

/-- A mixed pairing CLM inherits local product-kernel covariance directly
from small real-shift covariance of its scalar family.

The support of a nonzero chart test and its translate bounds the translation
norm by twice the chart radius. This is the only geometric input needed
outside the specialized EOW shifted-window setting. -/
theorem localHolomorphicFamily_pairingCLM_localCovariant
    {m : ℕ} {ρ : ℝ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Gchart : SchwartzMap (Fin m → ℝ) ℂ →
      ComplexChartSpace m → ℂ)
    (Rcov r : ℝ)
    (hRcov_small : 2 * Rcov < ρ)
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
        ‖a‖ < ρ →
        KernelSupportWithin ψ r →
        KernelSupportWithin (translateSchwartz a ψ) r →
        ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) Rcov,
          w - realEmbed a ∈
            Metric.ball (0 : ComplexChartSpace m) Rcov →
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
      exact not_not.mp ((not_exists.mp hnone) u)
    rcases hφ_nonzero_point with ⟨u, hu_ne⟩
    have hu_tsupport :
        u ∈ tsupport (φ : ComplexChartSpace m → ℂ) :=
      subset_closure (by simpa [Function.mem_support] using hu_ne)
    have hu_U :
        u ∈ Metric.ball (0 : ComplexChartSpace m) Rcov :=
      hφ.2 hu_tsupport
    have hu_shift_ne :
        complexTranslateSchwartz a φ (u - realEmbed a) ≠ 0 := by
      have harg : u - realEmbed a + realEmbed a = u := by
        ext i
        simp
      simpa [complexTranslateSchwartz_apply, harg] using hu_ne
    have hu_shift_tsupport :
        u - realEmbed a ∈
          tsupport
            (complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) :=
      subset_closure
        (by simpa [Function.mem_support] using hu_shift_ne)
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
    have ha : ‖a‖ < ρ := by
      rw [← norm_realEmbed_eq (m := m) a]
      exact ha_complex.trans hRcov_small
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
            · have hz_tsupport :
                  z ∈ tsupport (φ : ComplexChartSpace m → ℂ) :=
                subset_closure
                  (by simpa [Function.mem_support] using hzφ)
              have hz_U := hφ.2 hz_tsupport
              have hz_shift_U := hshift_support z hz_tsupport
              rw [← hG_cov a ψ ha hψ hψ_shift z hz_U hz_shift_U]
    calc
      K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ)
          = ∫ z : ComplexChartSpace m,
              Gchart ψ z * complexTranslateSchwartz a φ z := hleft
      _ = ∫ z : ComplexChartSpace m,
              Gchart (translateSchwartz a ψ) z * φ z := hintegral
      _ = K (schwartzTensorProduct₂ φ (translateSchwartz a ψ)) := hright.symm

end SCV
