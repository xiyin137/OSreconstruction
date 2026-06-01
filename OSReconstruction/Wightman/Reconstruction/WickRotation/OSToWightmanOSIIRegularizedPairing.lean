/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIRegularizer
import OSReconstruction.SCV.EuclideanWeylPairing

/-!
# OS II Step 4 Regularized Pairing

This file formalizes the convolution/Fubini bridge in the monograph Step 4:
the compact smooth kernel `g_rho` is a Schwartz test, its convolution is the
`k_rho` kernel, and the finite-probe distribution-pairing theorem identifies
`T(k_rho)` with the scalar integral of the translated `g_rho` tests.  This is
the checked substrate needed to build the regularized left/right OS smearing
vectors before quotienting.
-/

open MeasureTheory
open scoped Classical Convolution Pointwise

noncomputable section

namespace OSReconstruction

def osiiStep4RegularizerGSchwartz
    (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  let f : (Fin m → ℝ) → ℂ := fun x =>
    (osiiStep4RegularizerG m rho hrho x : ℂ)
  have hf_compact : HasCompactSupport f :=
    (osiiStep4RegularizerG_hasCompactSupport m hrho).comp_left
      Complex.ofReal_zero
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp
      (osiiStep4RegularizerG_contDiff m hrho)
  hf_compact.toSchwartzMap hf_smooth

theorem osiiStep4RegularizerGSchwartz_apply
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) (x : Fin m → ℝ) :
    osiiStep4RegularizerGSchwartz m rho hrho x =
      (osiiStep4RegularizerG m rho hrho x : ℂ) := by
  dsimp [osiiStep4RegularizerGSchwartz]

theorem osiiStep4RegularizerGSchwartz_compact
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport
      (osiiStep4RegularizerGSchwartz m rho hrho :
        (Fin m → ℝ) → ℂ) := by
  dsimp [osiiStep4RegularizerGSchwartz]
  simpa [HasCompactSupport.toSchwartzMap] using
    (osiiStep4RegularizerG_hasCompactSupport m hrho).comp_left
      Complex.ofReal_zero

/-- Monograph Vol IV Ch 2 Step 4 (lines 1099-1135): after the regularized
scalar has been split as a `g_rho`-weighted integral, a supportwise scalar
bound gives the whole integral bound because `g_rho` is nonnegative and has
total mass one.

This is the neutral kernel estimate below the OS scalar-product bound: the
OS-specific work is exactly to prove `hbound` for the BVT time-shell pairing on
the support of `g_rho`. -/
theorem osiiStep4_GSchwartz_weighted_integral_norm_le_of_support_bound
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (T : (Fin m → ℝ) → ℂ) {B : ℝ}
    (hT_int :
      Integrable
        (fun x : Fin m → ℝ =>
          T x * osiiStep4RegularizerGSchwartz m rho hrho x) volume)
    (hB : 0 ≤ B)
    (hbound :
      ∀ x ∈ Function.support
          (osiiStep4RegularizerGSchwartz m rho hrho :
            (Fin m → ℝ) → ℂ),
        ‖T x‖ ≤ B) :
    ‖∫ x : Fin m → ℝ,
        T x * osiiStep4RegularizerGSchwartz m rho hrho x‖ ≤ B := by
  have hg_int :
      Integrable
        (fun x : Fin m → ℝ =>
          B * osiiStep4RegularizerG m rho hrho x) volume := by
    exact (osiiStep4RegularizerG_integrable m hrho).const_mul B
  have hpoint :
      ∀ᵐ x : Fin m → ℝ ∂volume,
        ‖T x * osiiStep4RegularizerGSchwartz m rho hrho x‖ ≤
          B * osiiStep4RegularizerG m rho hrho x := by
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx :
        x ∈ Function.support
          (osiiStep4RegularizerGSchwartz m rho hrho :
            (Fin m → ℝ) → ℂ)
    · have hgnonneg : 0 ≤ osiiStep4RegularizerG m rho hrho x :=
        osiiStep4RegularizerG_nonneg m hrho x
      have hg_norm :
          ‖osiiStep4RegularizerGSchwartz m rho hrho x‖ =
            osiiStep4RegularizerG m rho hrho x := by
        rw [osiiStep4RegularizerGSchwartz_apply m hrho x]
        exact Complex.norm_of_nonneg hgnonneg
      calc
        ‖T x * osiiStep4RegularizerGSchwartz m rho hrho x‖
            = ‖T x‖ * ‖osiiStep4RegularizerGSchwartz m rho hrho x‖ := norm_mul _ _
        _ = ‖T x‖ * osiiStep4RegularizerG m rho hrho x := by rw [hg_norm]
        _ ≤ B * osiiStep4RegularizerG m rho hrho x := by
            exact mul_le_mul_of_nonneg_right (hbound x hx) hgnonneg
    · have hg_zero :
          osiiStep4RegularizerGSchwartz m rho hrho x = 0 := by
        simpa [Function.mem_support] using hx
      have hgnonneg : 0 ≤ osiiStep4RegularizerG m rho hrho x :=
        osiiStep4RegularizerG_nonneg m hrho x
      calc
        ‖T x * osiiStep4RegularizerGSchwartz m rho hrho x‖ = 0 := by
          simp [hg_zero]
        _ ≤ B * osiiStep4RegularizerG m rho hrho x :=
          mul_nonneg hB hgnonneg
  calc
    ‖∫ x : Fin m → ℝ,
        T x * osiiStep4RegularizerGSchwartz m rho hrho x‖
        ≤ ∫ x : Fin m → ℝ,
            ‖T x * osiiStep4RegularizerGSchwartz m rho hrho x‖ ∂volume :=
          norm_integral_le_integral_norm
            (fun x : Fin m → ℝ =>
              T x * osiiStep4RegularizerGSchwartz m rho hrho x)
    _ ≤ ∫ x : Fin m → ℝ,
          B * osiiStep4RegularizerG m rho hrho x ∂volume := by
        exact integral_mono_ae hT_int.norm hg_int hpoint
    _ = B := by
        rw [integral_const_mul, osiiStep4RegularizerG_integral_one m hrho,
          mul_one]

def osiiStep4RegularizerKSchwartz
    (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  let f : (Fin m → ℝ) → ℂ := fun x =>
    (osiiStep4RegularizerK m rho hrho x : ℂ)
  have hf_compact : HasCompactSupport f :=
    (osiiStep4RegularizerK_hasCompactSupport m hrho).comp_left
      Complex.ofReal_zero
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp
      (osiiStep4RegularizerK_contDiff m hrho)
  hf_compact.toSchwartzMap hf_smooth

theorem osiiStep4RegularizerKSchwartz_apply
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) (x : Fin m → ℝ) :
    osiiStep4RegularizerKSchwartz m rho hrho x =
      (osiiStep4RegularizerK m rho hrho x : ℂ) := by
  dsimp [osiiStep4RegularizerKSchwartz]

theorem osiiStep4RegularizerKSchwartz_compact
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport
      (osiiStep4RegularizerKSchwartz m rho hrho :
        (Fin m → ℝ) → ℂ) := by
  dsimp [osiiStep4RegularizerKSchwartz]
  simpa [HasCompactSupport.toSchwartzMap] using
    (osiiStep4RegularizerK_hasCompactSupport m hrho).comp_left
      Complex.ofReal_zero

theorem osiiStep4RegularizerKSchwartz_tsupport_subset_closedBall
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    tsupport (osiiStep4RegularizerKSchwartz m rho hrho : (Fin m → ℝ) → ℂ) ⊆
      Metric.closedBall (0 : Fin m → ℝ) (rho / 4) := by
  have hsupport :
      Function.support
          (osiiStep4RegularizerKSchwartz m rho hrho :
            (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (rho / 4) := by
    intro x hx
    have hxK :
        x ∈ Function.support (osiiStep4RegularizerK m rho hrho) := by
      simpa [Function.mem_support, osiiStep4RegularizerKSchwartz_apply] using hx
    exact osiiStep4RegularizerK_support_subset m hrho hxK
  refine closure_minimal ?_ (isCompact_closedBall
    (0 : Fin m → ℝ) (rho / 4)).isClosed
  intro x hx
  exact Metric.ball_subset_closedBall (hsupport hx)

theorem osiiStep4RegularizerKSchwartz_supportsInOpen_of_closedBall_subset
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) {U : Set (Fin m → ℝ)}
    (hU : Metric.closedBall (0 : Fin m → ℝ) (rho / 4) ⊆ U) :
    SCV.SupportsInOpen
      (osiiStep4RegularizerKSchwartz m rho hrho : (Fin m → ℝ) → ℂ) U := by
  exact ⟨osiiStep4RegularizerKSchwartz_compact m hrho,
    (osiiStep4RegularizerKSchwartz_tsupport_subset_closedBall
      m hrho).trans hU⟩

def osiiStep4RegularizerGSchwartzEuc
    (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e)
    (osiiStep4RegularizerGSchwartz m rho hrho)

theorem osiiStep4RegularizerGSchwartzEuc_apply
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (x : EuclideanSpace ℝ (Fin m)) :
    osiiStep4RegularizerGSchwartzEuc m rho hrho x =
      (osiiStep4RegularizerG m rho hrho
        ((EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)) x) : ℂ) := by
  simp [osiiStep4RegularizerGSchwartzEuc,
    osiiStep4RegularizerGSchwartz_apply]

theorem osiiStep4RegularizerGSchwartzEuc_compact
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport
      (osiiStep4RegularizerGSchwartzEuc m rho hrho :
        EuclideanSpace ℝ (Fin m) → ℂ) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  simpa [osiiStep4RegularizerGSchwartzEuc, e,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
    (osiiStep4RegularizerGSchwartz_compact m hrho).comp_homeomorph
      e.toHomeomorph

def osiiStep4RegularizerKSchwartzEuc
    (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e)
    (osiiStep4RegularizerKSchwartz m rho hrho)

theorem osiiStep4RegularizerKSchwartzEuc_apply
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (x : EuclideanSpace ℝ (Fin m)) :
    osiiStep4RegularizerKSchwartzEuc m rho hrho x =
      (osiiStep4RegularizerK m rho hrho
        ((EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)) x) : ℂ) := by
  simp [osiiStep4RegularizerKSchwartzEuc,
    osiiStep4RegularizerKSchwartz_apply]

theorem osiiStep4_regularizedDistribution_pairing_G
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (T : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ] ℂ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : EuclideanSpace ℝ (Fin m) → ℂ)) :
    ∫ x : EuclideanSpace ℝ (Fin m),
        T (SCV.euclideanReflectedTranslate x
          (osiiStep4RegularizerGSchwartzEuc m rho hrho)) *
          φ x =
      T (SCV.euclideanConvolutionTest φ
        (osiiStep4RegularizerGSchwartzEuc m rho hrho)) := by
  exact
    SCV.regularizedDistribution_integral_pairing
      T (osiiStep4RegularizerGSchwartzEuc m rho hrho) φ
      (osiiStep4RegularizerGSchwartzEuc_compact m hrho) hφ_compact

/-- Monograph Step 4: after transporting to Mathlib's Euclidean coordinates,
the convolution test of the two `g_rho` factors is exactly the transported
`k_rho = g_rho * g_rho` kernel. -/
theorem osiiStep4_G_convolutionTest_eq_K
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    SCV.euclideanConvolutionTest
        (osiiStep4RegularizerGSchwartzEuc m rho hrho)
        (osiiStep4RegularizerGSchwartzEuc m rho hrho) =
      osiiStep4RegularizerKSchwartzEuc m rho hrho := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  ext x
  rw [SCV.euclideanConvolutionTest_apply]
  rw [osiiStep4RegularizerKSchwartzEuc_apply]
  rw [osiiStep4RegularizerK_apply]
  have hchange :=
    (((PiLp.volume_preserving_toLp (ι := Fin m)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding
      (fun y : EuclideanSpace ℝ (Fin m) =>
        ((osiiStep4RegularizerG m rho hrho (e y) *
          osiiStep4RegularizerG m rho hrho (e x - e y) : ℝ) : ℂ))).symm)
  calc
    ∫ y : EuclideanSpace ℝ (Fin m),
        osiiStep4RegularizerGSchwartzEuc m rho hrho y *
          osiiStep4RegularizerGSchwartzEuc m rho hrho (x - y)
        = ∫ y : EuclideanSpace ℝ (Fin m),
            ((osiiStep4RegularizerG m rho hrho (e y) *
              osiiStep4RegularizerG m rho hrho (e x - e y) : ℝ) : ℂ) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [osiiStep4RegularizerGSchwartzEuc_apply]
          rw [osiiStep4RegularizerGSchwartzEuc_apply]
          rw [map_sub]
          norm_cast
    _ = ∫ y : Fin m → ℝ,
            ((osiiStep4RegularizerG m rho hrho y *
              osiiStep4RegularizerG m rho hrho (e x - y) : ℝ) : ℂ) := by
          simpa [e, PiLp.coe_symm_continuousLinearEquiv] using hchange
    _ = ((∫ y : Fin m → ℝ,
            osiiStep4RegularizerG m rho hrho y *
              osiiStep4RegularizerG m rho hrho (e x - y) ∂volume : ℝ) : ℂ) := by
          rw [integral_complex_ofReal]

/-- Monograph Step 4 in scalar distribution form: pairing a distribution with
`k_rho` is the same as integrating the distribution applied to translated
`g_rho` tests against the second `g_rho` factor.  This is the precise
pre-quotient smearing identity needed for the future OS Hilbert-vector
factorization. -/
theorem osiiStep4_regularizedDistribution_pairing_GG_eq_K
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (T : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ] ℂ) :
    ∫ x : EuclideanSpace ℝ (Fin m),
        T (SCV.euclideanReflectedTranslate x
          (osiiStep4RegularizerGSchwartzEuc m rho hrho)) *
          osiiStep4RegularizerGSchwartzEuc m rho hrho x =
      T (osiiStep4RegularizerKSchwartzEuc m rho hrho) := by
  rw [← osiiStep4_G_convolutionTest_eq_K m hrho]
  exact
    osiiStep4_regularizedDistribution_pairing_G
      m hrho T (osiiStep4RegularizerGSchwartzEuc m rho hrho)
      (osiiStep4RegularizerGSchwartzEuc_compact m hrho)

def osiiStep4RegularizerGReflectedTranslate
    (m : ℕ) (rho : ℝ) (hrho : 0 < rho) (x : Fin m → ℝ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
    (SCV.euclideanReflectedTranslate (e.symm x)
      (osiiStep4RegularizerGSchwartzEuc m rho hrho))

theorem osiiStep4RegularizerGReflectedTranslate_apply
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (x y : Fin m → ℝ) :
    osiiStep4RegularizerGReflectedTranslate m rho hrho x y =
      (osiiStep4RegularizerG m rho hrho (y - x) : ℂ) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  simp [osiiStep4RegularizerGReflectedTranslate,
    SCV.euclideanReflectedTranslate_apply,
    osiiStep4RegularizerGSchwartzEuc_apply,
    PiLp.coe_continuousLinearEquiv]

theorem osiiStep4RegularizerGReflectedTranslate_support_subset_ball
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) (x : Fin m → ℝ) :
    Function.support
        (osiiStep4RegularizerGReflectedTranslate m rho hrho x :
          (Fin m → ℝ) → ℂ) ⊆
      Metric.ball x (rho / 8) := by
  intro y hy
  have hyG :
      y - x ∈ Function.support (osiiStep4RegularizerG m rho hrho) := by
    simpa [Function.mem_support, osiiStep4RegularizerGReflectedTranslate_apply]
      using hy
  have hball := osiiStep4RegularizerG_support_subset m hrho hyG
  simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hball

theorem osiiStep4RegularizerGReflectedTranslate_tsupport_subset_closedBall
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) (x : Fin m → ℝ) :
    tsupport
        (osiiStep4RegularizerGReflectedTranslate m rho hrho x :
          (Fin m → ℝ) → ℂ) ⊆
      Metric.closedBall x (rho / 8) := by
  refine closure_minimal ?_ (isCompact_closedBall x (rho / 8)).isClosed
  intro y hy
  exact Metric.ball_subset_closedBall
    (osiiStep4RegularizerGReflectedTranslate_support_subset_ball
      m hrho x hy)

theorem osiiStep4RegularizerGReflectedTranslate_hasCompactSupport
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) (x : Fin m → ℝ) :
    HasCompactSupport
      (osiiStep4RegularizerGReflectedTranslate m rho hrho x :
        (Fin m → ℝ) → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall x (rho / 8)) ?_
  intro y hy
  exact Metric.ball_subset_closedBall
    (osiiStep4RegularizerGReflectedTranslate_support_subset_ball
      m hrho x hy)

theorem osiiStep4RegularizerGReflectedTranslate_supportsInOpen_of_closedBall_subset
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) (x : Fin m → ℝ)
    {U : Set (Fin m → ℝ)}
    (hU : Metric.closedBall x (rho / 8) ⊆ U) :
    SCV.SupportsInOpen
      (osiiStep4RegularizerGReflectedTranslate m rho hrho x :
        (Fin m → ℝ) → ℂ) U := by
  exact ⟨osiiStep4RegularizerGReflectedTranslate_hasCompactSupport
      m hrho x,
    (osiiStep4RegularizerGReflectedTranslate_tsupport_subset_closedBall
      m hrho x).trans hU⟩

/-- The two `g_rho` support balls in the Step-4 split fit inside the original
`k_rho` ball: if the outer integration center lies in the support of the
second `g_rho`, then the support collar of the translated first `g_rho` is
contained in the `rho/4` kernel collar. -/
theorem osiiStep4RegularizerGSchwartz_closedBall_subset_K_closedBall
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    {x : Fin m → ℝ}
    (hx : x ∈ Function.support
      (osiiStep4RegularizerGSchwartz m rho hrho : (Fin m → ℝ) → ℂ)) :
    Metric.closedBall x (rho / 8) ⊆
      Metric.closedBall (0 : Fin m → ℝ) (rho / 4) := by
  intro y hy
  have hxG :
      x ∈ Function.support (osiiStep4RegularizerG m rho hrho) := by
    rw [Function.mem_support] at hx ⊢
    intro hzero
    apply hx
    rw [osiiStep4RegularizerGSchwartz_apply, hzero]
    norm_num
  have hxball := osiiStep4RegularizerG_support_subset m hrho hxG
  rw [Metric.mem_ball, dist_zero_right] at hxball
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  have hlt : ‖y‖ < rho / 4 := by
    calc
      ‖y‖ = ‖(y - x) + x‖ := by abel_nf
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le (y - x) x
      _ < rho / 8 + rho / 8 := add_lt_add_of_le_of_lt hy hxball
      _ = rho / 4 := by ring
  exact le_of_lt hlt

/-- A single `rho/4` source-current collar controls every translated
`g_rho` test appearing in the OS-II Step-4 split. -/
theorem osiiStep4RegularizerGReflectedTranslate_supportsInOpen_of_K_closedBall_subset
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) {U : Set (Fin m → ℝ)}
    (hU : Metric.closedBall (0 : Fin m → ℝ) (rho / 4) ⊆ U)
    {x : Fin m → ℝ}
    (hx : x ∈ Function.support
      (osiiStep4RegularizerGSchwartz m rho hrho : (Fin m → ℝ) → ℂ)) :
    SCV.SupportsInOpen
      (osiiStep4RegularizerGReflectedTranslate m rho hrho x :
        (Fin m → ℝ) → ℂ) U := by
  exact
    osiiStep4RegularizerGReflectedTranslate_supportsInOpen_of_closedBall_subset
      m hrho x
      ((osiiStep4RegularizerGSchwartz_closedBall_subset_K_closedBall
        m hrho hx).trans hU)

/-- The translated `g_rho` test varies continuously in the flat translation
center after applying any continuous Schwartz functional.  This is the
integrability input for the Step-4 `g_rho`-weighted BVT scalar. -/
theorem continuous_osiiStep4RegularizerGReflectedTranslate_apply
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    Continuous
      (fun x : Fin m → ℝ =>
        T (osiiStep4RegularizerGReflectedTranslate m rho hrho x)) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let TE : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ] ℂ :=
    T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
  have hE :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin m) =>
          TE (SCV.euclideanReflectedTranslate x
            (osiiStep4RegularizerGSchwartzEuc m rho hrho))) :=
    SCV.continuous_apply_euclideanReflectedTranslate_of_isCompactSupport
      TE (osiiStep4RegularizerGSchwartzEuc m rho hrho)
      (osiiStep4RegularizerGSchwartzEuc_compact m hrho)
  have hflat :
      (fun x : Fin m → ℝ =>
        T (osiiStep4RegularizerGReflectedTranslate m rho hrho x)) =
      fun x : Fin m → ℝ =>
        TE (SCV.euclideanReflectedTranslate (e.symm x)
          (osiiStep4RegularizerGSchwartzEuc m rho hrho)) := by
    ext x
    simp [TE, osiiStep4RegularizerGReflectedTranslate, e]
  rw [hflat]
  exact hE.comp e.symm.continuous

/-- Monograph Vol IV Ch 2 Step 4 (lines 1099-1135): for fixed regularization
scale, the translated `g_rho` scalar family is bounded on the compact
`g_rho` support.

This is only the compactness half of the Step-4 bound.  The later OS
linear-growth argument still has to replace this existential bound by a
uniform polynomial estimate in `rho`. -/
theorem exists_bound_osiiStep4RegularizerGReflectedTranslate_apply_on_support
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ Function.support
          (osiiStep4RegularizerGSchwartz m rho hrho : (Fin m → ℝ) → ℂ),
        ‖T (osiiStep4RegularizerGReflectedTranslate m rho hrho x)‖ ≤ B := by
  let F : (Fin m → ℝ) → ℝ := fun x =>
    ‖T (osiiStep4RegularizerGReflectedTranslate m rho hrho x)‖
  have hF_cont : Continuous F :=
    (continuous_osiiStep4RegularizerGReflectedTranslate_apply
      m hrho T).norm
  let K : Set (Fin m → ℝ) :=
    tsupport (osiiStep4RegularizerGSchwartz m rho hrho :
      (Fin m → ℝ) → ℂ)
  have hK_compact : IsCompact K :=
    (osiiStep4RegularizerGSchwartz_compact m hrho).isCompact
  rcases hK_compact.bddAbove_image hF_cont.continuousOn with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x hx
  have hxK : x ∈ K := subset_tsupport _ hx
  have hFxC : F x ≤ C := hC ⟨x, hxK, rfl⟩
  exact hFxC.trans (le_max_left C 0)

/-- The `g_rho`-weighted translated-kernel pairing is integrable for every
continuous Schwartz functional.  The compact support comes from the second
`g_rho` factor, exactly as in OS II Step 4. -/
theorem integrable_osiiStep4RegularizerGSchwartz_weighted_CLM
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    Integrable
      (fun x : Fin m → ℝ =>
        T (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
          osiiStep4RegularizerGSchwartz m rho hrho x) volume := by
  have hcont :
      Continuous
        (fun x : Fin m → ℝ =>
          T (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
            osiiStep4RegularizerGSchwartz m rho hrho x) :=
    (continuous_osiiStep4RegularizerGReflectedTranslate_apply
      m hrho T).mul (osiiStep4RegularizerGSchwartz m rho hrho).continuous
  have hcompact :
      HasCompactSupport
        (fun x : Fin m → ℝ =>
          T (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
            osiiStep4RegularizerGSchwartz m rho hrho x) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (osiiStep4RegularizerGSchwartz_compact m hrho).isCompact ?_
    intro x hx
    rw [Function.mem_support] at hx
    have hxG :
        osiiStep4RegularizerGSchwartz m rho hrho x ≠ 0 := by
      intro hzero
      exact hx (by simp [hzero])
    exact subset_closure hxG
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- Flat-coordinate version of the regularized pairing identity.  This is the
form consumed by the OS source-current modules, whose test functions live on
`Fin m -> R` rather than Mathlib's `EuclideanSpace`. -/
theorem osiiStep4_regularizedDistribution_pairing_GG_eq_K_flat
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∫ x : Fin m → ℝ,
        T (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
          osiiStep4RegularizerGSchwartz m rho hrho x =
      T (osiiStep4RegularizerKSchwartz m rho hrho) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let TE : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ] ℂ :=
    T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
  have hE := osiiStep4_regularizedDistribution_pairing_GG_eq_K m hrho TE
  have hleft_change :=
    (((PiLp.volume_preserving_toLp (ι := Fin m)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding
      (fun x : EuclideanSpace ℝ (Fin m) =>
        TE (SCV.euclideanReflectedTranslate x
          (osiiStep4RegularizerGSchwartzEuc m rho hrho)) *
          osiiStep4RegularizerGSchwartzEuc m rho hrho x)).symm)
  have hleft :
      ∫ x : EuclideanSpace ℝ (Fin m),
          TE (SCV.euclideanReflectedTranslate x
            (osiiStep4RegularizerGSchwartzEuc m rho hrho)) *
            osiiStep4RegularizerGSchwartzEuc m rho hrho x =
        ∫ x : Fin m → ℝ,
          T (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
            osiiStep4RegularizerGSchwartz m rho hrho x := by
    calc
      ∫ x : EuclideanSpace ℝ (Fin m),
          TE (SCV.euclideanReflectedTranslate x
            (osiiStep4RegularizerGSchwartzEuc m rho hrho)) *
            osiiStep4RegularizerGSchwartzEuc m rho hrho x
          = ∫ x : Fin m → ℝ,
              TE (SCV.euclideanReflectedTranslate (e.symm x)
                (osiiStep4RegularizerGSchwartzEuc m rho hrho)) *
                osiiStep4RegularizerGSchwartzEuc m rho hrho (e.symm x) := by
            simpa [e, PiLp.coe_symm_continuousLinearEquiv] using hleft_change
      _ = ∫ x : Fin m → ℝ,
              T (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
                osiiStep4RegularizerGSchwartz m rho hrho x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            have hT :
                TE (SCV.euclideanReflectedTranslate (e.symm x)
                    (osiiStep4RegularizerGSchwartzEuc m rho hrho)) =
                  T (osiiStep4RegularizerGReflectedTranslate
                    m rho hrho x) := by
              simp [TE, osiiStep4RegularizerGReflectedTranslate, e]
            have hG :
                osiiStep4RegularizerGSchwartzEuc m rho hrho (e.symm x) =
                  osiiStep4RegularizerGSchwartz m rho hrho x := by
              simp [osiiStep4RegularizerGSchwartzEuc_apply,
                osiiStep4RegularizerGSchwartz_apply, e,
                PiLp.coe_continuousLinearEquiv]
            rw [hT, hG]
  have hright :
      TE (osiiStep4RegularizerKSchwartzEuc m rho hrho) =
        T (osiiStep4RegularizerKSchwartz m rho hrho) := by
    have harg :
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
            (osiiStep4RegularizerKSchwartzEuc m rho hrho) =
          osiiStep4RegularizerKSchwartz m rho hrho := by
      ext x
      simp [osiiStep4RegularizerKSchwartzEuc,
        osiiStep4RegularizerKSchwartz_apply, e,
        PiLp.coe_continuousLinearEquiv]
    simp [TE, harg]
  rw [hleft, hright] at hE
  exact hE

end OSReconstruction
