/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# OS II Step 4 Regularizer Package

Monograph Vol IV Ch 2 Step 4 (lines 1052-1075) starts the VI.1 real-domain
bound with a normalized smooth kernel `g_rho`, its convolution
`k_rho = g_rho * g_rho`, and the probability-average estimate that converts the
regularized mean-value identity into a support supremum bound.

This file contains only those neutral analytic leaves:

* construction and support/mass facts for `g_rho`;
* support/mass/smoothness/nonnegativity facts for `k_rho`;
* the probability-average-to-support-bound estimate used after the
  regularized mean-value identity.

The OS-specific next step is to define `T_{k,rho}` and prove the pairing-vector
identity before quotienting.
-/

open MeasureTheory
open scoped Classical Convolution Pointwise

noncomputable section

namespace OSReconstruction

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-- Monograph Vol IV Ch 2 Step 4 (lines 1052-1058): the normalized smooth
regularizer bump with outer support radius `rho / 8`. -/
def osiiStep4RegularizerBump (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    ContDiffBump (0 : Fin m → ℝ) :=
  { rIn := rho / 16
    rOut := rho / 8
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }

/-- The normalized `g_rho` kernel as an ordinary real-valued function. -/
def osiiStep4RegularizerG (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    (Fin m → ℝ) → ℝ :=
  (osiiStep4RegularizerBump m rho hrho).normed
    (volume : Measure (Fin m → ℝ))

theorem osiiStep4RegularizerG_contDiff
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ContDiff ℝ (⊤ : ℕ∞) (osiiStep4RegularizerG m rho hrho) := by
  simpa [osiiStep4RegularizerG] using
    (osiiStep4RegularizerBump m rho hrho).contDiff_normed (n := (⊤ : ℕ∞))

theorem osiiStep4RegularizerG_hasCompactSupport
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport (osiiStep4RegularizerG m rho hrho) := by
  simpa [osiiStep4RegularizerG] using
    (osiiStep4RegularizerBump m rho hrho).hasCompactSupport_normed

theorem osiiStep4RegularizerG_integrable
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Integrable (osiiStep4RegularizerG m rho hrho)
      (volume : Measure (Fin m → ℝ)) := by
  exact
    (osiiStep4RegularizerG_contDiff m hrho).continuous.integrable_of_hasCompactSupport
      (osiiStep4RegularizerG_hasCompactSupport m hrho)

theorem osiiStep4RegularizerG_nonneg
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∀ x : Fin m → ℝ, 0 ≤ osiiStep4RegularizerG m rho hrho x := by
  simpa [osiiStep4RegularizerG] using
    (osiiStep4RegularizerBump m rho hrho).nonneg_normed

/-- Monograph Vol IV Ch 2 Step 4 (lines 1052-1058): `g_rho` has total mass one. -/
theorem osiiStep4RegularizerG_integral_one
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∫ x, osiiStep4RegularizerG m rho hrho x ∂volume = 1 := by
  simpa [osiiStep4RegularizerG] using
    (osiiStep4RegularizerBump m rho hrho).integral_normed

/-- Monograph Vol IV Ch 2 Step 4 (lines 1052-1058): `g_rho` is supported in
the ball of radius `rho / 8`. -/
theorem osiiStep4RegularizerG_support_subset
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Function.support (osiiStep4RegularizerG m rho hrho) ⊆
      Metric.ball (0 : Fin m → ℝ) (rho / 8) := by
  dsimp [osiiStep4RegularizerG]
  rw [(osiiStep4RegularizerBump m rho hrho).support_normed_eq]
  simp [osiiStep4RegularizerBump]

/-- Pointwise size control for the normalized kernel `g_rho`.  This is the
zeroth-order part of the kernel bounds used in the Step-4 OS quadratic-form
estimate. -/
theorem osiiStep4RegularizerG_le_inv_ball_volume
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (x : Fin m → ℝ) :
    osiiStep4RegularizerG m rho hrho x ≤
      1 / (volume : Measure (Fin m → ℝ)).real
        (Metric.closedBall (0 : Fin m → ℝ) (rho / 16)) := by
  simpa [osiiStep4RegularizerG, osiiStep4RegularizerBump] using
    (osiiStep4RegularizerBump m rho hrho).normed_le_div_measure_closedBall_rIn
      (μ := (volume : Measure (Fin m → ℝ))) x

/-- Monograph Vol IV Ch 2 Step 4 (lines 1059-1060): the convolution kernel
`k_rho = g_rho * g_rho`. -/
def osiiStep4RegularizerK (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    (Fin m → ℝ) → ℝ :=
  osiiStep4RegularizerG m rho hrho ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    osiiStep4RegularizerG m rho hrho

/-- Pointwise convolution formula for the OS-II kernel
`k_ρ = g_ρ * g_ρ`.  This is the kernel factorization used later to build the
left and right regularized OS smearing vectors from the same `g_ρ` factors
that define the `T_{k,ρ}` average. -/
theorem osiiStep4RegularizerK_apply
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (x : Fin m → ℝ) :
    osiiStep4RegularizerK m rho hrho x =
      ∫ y : Fin m → ℝ,
        osiiStep4RegularizerG m rho hrho y *
          osiiStep4RegularizerG m rho hrho (x - y) ∂volume := by
  dsimp [osiiStep4RegularizerK]
  simp [MeasureTheory.convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

private theorem support_convolution_subset_ball_add_real
    {m : ℕ} {f g : (Fin m → ℝ) → ℝ} {r s : ℝ}
    (hf : Function.support f ⊆ Metric.ball (0 : Fin m → ℝ) r)
    (hg : Function.support g ⊆ Metric.ball (0 : Fin m → ℝ) s) :
    Function.support (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) ⊆
      Metric.ball (0 : Fin m → ℝ) (r + s) := by
  intro x hx
  have hxsum : x ∈ Function.support f + Function.support g :=
    support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) hx
  rcases hxsum with ⟨u, hu, v, hv, rfl⟩
  have hu_ball := hf hu
  have hv_ball := hg hv
  rw [Metric.mem_ball, dist_zero_right] at hu_ball hv_ball ⊢
  calc
    ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
    _ < r + s := add_lt_add hu_ball hv_ball

/-- Monograph Vol IV Ch 2 Step 4 (lines 1059-1060): `k_rho` is supported in
the ball of radius `rho / 4`. -/
theorem osiiStep4RegularizerK_support_subset
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Function.support (osiiStep4RegularizerK m rho hrho) ⊆
      Metric.ball (0 : Fin m → ℝ) (rho / 4) := by
  have hg := osiiStep4RegularizerG_support_subset m hrho
  have hk := support_convolution_subset_ball_add_real
    (m := m) (f := osiiStep4RegularizerG m rho hrho)
    (g := osiiStep4RegularizerG m rho hrho) hg hg
  simpa [osiiStep4RegularizerK, show rho / 8 + rho / 8 = rho / 4 by ring] using hk

theorem osiiStep4RegularizerK_hasCompactSupport
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport (osiiStep4RegularizerK m rho hrho) := by
  simpa [osiiStep4RegularizerK] using
    (osiiStep4RegularizerG_hasCompactSupport m hrho).convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (osiiStep4RegularizerG_hasCompactSupport m hrho)

theorem osiiStep4RegularizerK_contDiff
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ContDiff ℝ (⊤ : ℕ∞) (osiiStep4RegularizerK m rho hrho) := by
  have hG_smooth := osiiStep4RegularizerG_contDiff m hrho
  have hG_li := (osiiStep4RegularizerG_integrable m hrho).locallyIntegrable
  simpa [osiiStep4RegularizerK] using
    (osiiStep4RegularizerG_hasCompactSupport m hrho).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) hG_smooth hG_li

theorem osiiStep4RegularizerK_nonneg
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∀ x : Fin m → ℝ, 0 ≤ osiiStep4RegularizerK m rho hrho x := by
  intro x
  dsimp [osiiStep4RegularizerK]
  simp [MeasureTheory.convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact integral_nonneg fun y =>
    mul_nonneg (osiiStep4RegularizerG_nonneg m hrho y)
      (osiiStep4RegularizerG_nonneg m hrho (x - y))

/-- Monograph Vol IV Ch 2 Step 4 (lines 1059-1060): `k_rho` has total mass one. -/
theorem osiiStep4RegularizerK_integral_one
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∫ x, osiiStep4RegularizerK m rho hrho x ∂volume = 1 := by
  have hg_int := osiiStep4RegularizerG_integrable m hrho
  have hconv := MeasureTheory.integral_convolution
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hg_int hg_int
  have hg_mass := osiiStep4RegularizerG_integral_one m hrho
  simpa [osiiStep4RegularizerK, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, hg_mass] using hconv

/-- The convolution kernel `k_rho` is integrable. -/
theorem osiiStep4RegularizerK_integrable
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Integrable (osiiStep4RegularizerK m rho hrho)
      (volume : Measure (Fin m → ℝ)) := by
  exact
    (osiiStep4RegularizerK_contDiff m hrho).continuous.integrable_of_hasCompactSupport
      (osiiStep4RegularizerK_hasCompactSupport m hrho)

/-- Monograph Vol IV Ch 2 Step 4 (lines 1059-1070): the probability measure
`nu_rho = k_rho(y) dy` used in the regularized mean-value identity. -/
def osiiStep4RegularizerMeasure (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    Measure (Fin m → ℝ) :=
  volume.withDensity fun x => ENNReal.ofReal (osiiStep4RegularizerK m rho hrho x)

/-- The regularizer measure has total mass one. -/
theorem osiiStep4RegularizerMeasure_isProbability
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    IsProbabilityMeasure (osiiStep4RegularizerMeasure m rho hrho) := by
  refine ⟨?_⟩
  rw [osiiStep4RegularizerMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (osiiStep4RegularizerK_integrable m hrho) ?_]
  · rw [osiiStep4RegularizerK_integral_one]
    norm_num
  · filter_upwards with x
    exact osiiStep4RegularizerK_nonneg m hrho x

/-- The measure `nu_rho` is concentrated on the `rho / 4` support ball of
`k_rho`.  This is the support input for the Step-4 supremum bound. -/
theorem osiiStep4RegularizerMeasure_support_ae
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∀ᵐ x ∂osiiStep4RegularizerMeasure m rho hrho,
      x ∈ Metric.ball (0 : Fin m → ℝ) (rho / 4) := by
  rw [ae_iff]
  show osiiStep4RegularizerMeasure m rho hrho
      ((Metric.ball (0 : Fin m → ℝ) (rho / 4))ᶜ) = 0
  rw [osiiStep4RegularizerMeasure,
    withDensity_apply _ (Metric.isOpen_ball.measurableSet.compl)]
  apply MeasureTheory.lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure (Fin m → ℝ)))
    (Metric.isOpen_ball.measurableSet.compl)] with x hxcomp
  have hx_not_ball : x ∉ Metric.ball (0 : Fin m → ℝ) (rho / 4) := by
    simpa using hxcomp
  have hx_not_support : x ∉ Function.support (osiiStep4RegularizerK m rho hrho) := by
    intro hsupp
    exact hx_not_ball (osiiStep4RegularizerK_support_subset m hrho hsupp)
  have hK_zero : osiiStep4RegularizerK m rho hrho x = 0 := by
    simpa [Function.mem_support] using hx_not_support
  simp [hK_zero]

/-- Pointwise zeroth-order size control for the convolution kernel `k_rho`. -/
theorem osiiStep4RegularizerK_le_inv_ball_volume
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (x : Fin m → ℝ) :
    osiiStep4RegularizerK m rho hrho x ≤
      1 / (volume : Measure (Fin m → ℝ)).real
        (Metric.closedBall (0 : Fin m → ℝ) (rho / 16)) := by
  let C : ℝ :=
    1 / (volume : Measure (Fin m → ℝ)).real
      (Metric.closedBall (0 : Fin m → ℝ) (rho / 16))
  change osiiStep4RegularizerK m rho hrho x ≤ C
  let G : (Fin m → ℝ) → ℝ := osiiStep4RegularizerG m rho hrho
  have hG_nonneg : ∀ y, 0 ≤ G y := osiiStep4RegularizerG_nonneg m hrho
  have hG_le : ∀ y, G y ≤ C := by
    intro y
    simpa [G, C] using osiiStep4RegularizerG_le_inv_ball_volume m hrho y
  have hupper_int : Integrable (fun y => C * G y) (volume : Measure (Fin m → ℝ)) :=
    (osiiStep4RegularizerG_integrable m hrho).const_mul C
  dsimp [osiiStep4RegularizerK]
  simp [MeasureTheory.convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  calc
    ∫ y, G y * G (x - y) ∂volume ≤ ∫ y, C * G y ∂volume := by
      apply integral_mono_of_nonneg
      · filter_upwards with y
        exact mul_nonneg (hG_nonneg y) (hG_nonneg (x - y))
      · exact hupper_int
      · filter_upwards with y
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_right (hG_le (x - y)) (hG_nonneg y)
    _ = C := by
      rw [integral_const_mul, osiiStep4RegularizerG_integral_one m hrho, mul_one]

/-! ### Mean-value leaves -/

/-- Monograph Vol IV Ch 2 Step 4 (line 1060): the one-coordinate mean-value
leaf used before blockwise insertion of the regularizer.

For a holomorphic coordinate slice, the value at the center is its circle
average.  The full `T_{k,ρ}` identity iterates this statement over the
regularized OS-II coordinates and then reorganizes the resulting averages by
Fubini. -/
theorem osiiStep4_coordinate_circleAverage_eq_center
    {m : ℕ}
    (F : (Fin m → ℂ) → ℂ)
    (z : Fin m → ℂ) (j : Fin m) (R : ℝ)
    (hF : DiffContOnCl ℂ
      (fun w : ℂ => F (Function.update z j w))
      (Metric.ball (z j) |R|)) :
    Real.circleAverage
        (fun w : ℂ => F (Function.update z j w)) (z j) R =
      F z := by
  calc
    Real.circleAverage
        (fun w : ℂ => F (Function.update z j w)) (z j) R =
        (fun w : ℂ => F (Function.update z j w)) (z j) := by
          exact hF.circleAverage
    _ = F z := by
          simp

/-- Norm bound for the circle-average mean-value leaf.  This is the
one-coordinate analytic form of the VI.1 passage from a mean-value identity to
a supremum bound before replacing circle averages by the book's compact
regularizer. -/
theorem osiiStep4_norm_circleAverage_le_of_sphere_bound
    {f : ℂ → ℂ} {c : ℂ} {R B : ℝ}
    (hR : 0 ≤ R)
    (hB : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ B) :
    ‖Real.circleAverage f c R‖ ≤ B := by
  by_cases hR0 : R = 0
  · subst R
    simpa using hB c (by simp)
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    have hbound :
        ∀ z ∈ Metric.sphere c R, ‖(z - c)⁻¹ • f z‖ ≤ R⁻¹ * B := by
      intro z hz
      have hz_norm : ‖z - c‖ = R := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hfactor : ‖(z - c)⁻¹‖ = R⁻¹ := by
        rw [norm_inv, hz_norm]
      calc
        ‖(z - c)⁻¹ • f z‖ = R⁻¹ * ‖f z‖ := by
          rw [norm_smul, hfactor]
        _ ≤ R⁻¹ * B := by
          exact mul_le_mul_of_nonneg_left (hB z hz) (inv_nonneg.mpr hR)
    calc
      ‖Real.circleAverage f c R‖ =
          ‖(2 * ↑Real.pi * Complex.I : ℂ)⁻¹ •
              (∮ z in C(c, R), (z - c)⁻¹ • f z)‖ := by
            rw [Real.circleAverage_eq_circleIntegral hR0]
      _ ≤ R * (R⁻¹ * B) := by
            exact
              circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
                hR hbound
      _ = B := by
            field_simp [hR0]

/-- One-coordinate VI.1 estimate: a holomorphic coordinate slice is bounded at
the center by any uniform bound on the surrounding circle.  Iterating this
leaf is the analytic core of the blockwise mean-value estimate before the
OS-specific `T_{k,ρ}` scalar-product bound is inserted. -/
theorem osiiStep4_coordinate_center_norm_le_sphere_bound
    {m : ℕ}
    (F : (Fin m → ℂ) → ℂ)
    (z : Fin m → ℂ) (j : Fin m) {R B : ℝ}
    (hR : 0 ≤ R)
    (hF : DiffContOnCl ℂ
      (fun w : ℂ => F (Function.update z j w))
      (Metric.ball (z j) |R|))
    (hB : ∀ w ∈ Metric.sphere (z j) R,
      ‖F (Function.update z j w)‖ ≤ B) :
    ‖F z‖ ≤ B := by
  rw [← osiiStep4_coordinate_circleAverage_eq_center F z j R hF]
  exact osiiStep4_norm_circleAverage_le_of_sphere_bound hR hB

/-- Finite blockwise circle average used by the OS-II VI.1 regularized
mean-value argument.  This is the formal bookkeeping object for the book's
"apply the mean-value theorem blockwise" step, before the resulting iterated
circle averages are reorganized into the compact `T_{k,ρ}` regularizer. -/
def osiiStep4IteratedCircleAverage {m : ℕ}
    (coords : List (Fin m)) (R : Fin m → ℝ)
    (F : (Fin m → ℂ) → ℂ) : (Fin m → ℂ) → ℂ
  | z =>
      match coords with
      | [] => F z
      | j :: js =>
          Real.circleAverage
            (fun w : ℂ =>
              osiiStep4IteratedCircleAverage js R F
                (Function.update z j w))
            (z j) (R j)

/-- Finite blockwise mean-value identity: iterating the one-coordinate circle
mean-value theorem recovers the center value.  The hypothesis is stated for
the intermediate averaged slices because the OS-II construction subsequently
proves those slice holomorphy facts by the same local chart and Fubini
machinery used to define `T_{k,ρ}`. -/
theorem osiiStep4_iteratedCircleAverage_eq_center
    {m : ℕ}
    (coords : List (Fin m)) (R : Fin m → ℝ)
    (F : (Fin m → ℂ) → ℂ)
    (hdiff : ∀ (coords' : List (Fin m)) (z : Fin m → ℂ) (j : Fin m),
      DiffContOnCl ℂ
        (fun w : ℂ =>
          osiiStep4IteratedCircleAverage coords' R F
            (Function.update z j w))
        (Metric.ball (z j) |R j|))
    (z : Fin m → ℂ) :
    osiiStep4IteratedCircleAverage coords R F z = F z := by
  induction coords generalizing z with
  | nil =>
      rfl
  | cons j js ih =>
      calc
        osiiStep4IteratedCircleAverage (j :: js) R F z =
            osiiStep4IteratedCircleAverage js R F z := by
              exact
                osiiStep4_coordinate_circleAverage_eq_center
                  (osiiStep4IteratedCircleAverage js R F)
                  z j (R j) (hdiff js z j)
        _ = F z := ih z

/-- Integrating against `nu_rho = k_rho(y) dy` is the same as the book's
weighted Lebesgue integral. -/
theorem osiiStep4_integral_regularizerMeasure_eq_kernel_mul
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (T : (Fin m → ℝ) → ℂ) :
    (∫ x, T x ∂osiiStep4RegularizerMeasure m rho hrho) =
      ∫ x, (osiiStep4RegularizerK m rho hrho x : ℂ) * T x ∂volume := by
  rw [osiiStep4RegularizerMeasure]
  have hK_meas : Measurable fun x : Fin m → ℝ =>
      ENNReal.ofReal (osiiStep4RegularizerK m rho hrho x) := by
    exact ENNReal.measurable_ofReal.comp
      (osiiStep4RegularizerK_contDiff m hrho).continuous.measurable
  have hK_lt_top : ∀ᵐ x : Fin m → ℝ ∂volume,
      ENNReal.ofReal (osiiStep4RegularizerK m rho hrho x) < ⊤ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hK_meas hK_lt_top T]
  refine integral_congr_ae ?_
  filter_upwards with x
  have hK_nonneg : 0 ≤ osiiStep4RegularizerK m rho hrho x :=
    osiiStep4RegularizerK_nonneg m hrho x
  rw [ENNReal.toReal_ofReal hK_nonneg]
  rfl

/-- Probability-average-to-support-bound estimate used in OS II VI.1 after the
regularized mean-value identity.  In the OS-specific application `mu = nu_rho`,
`K` is the small imaginary support box, and `T y = T_{k,rho}(xi + eta + i y)`. -/
theorem osiiStep4_regularized_average_le_support_bound
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu]
    (T : α → ℂ) {K : Set α} {B : ℝ}
    (hT_int : Integrable T mu)
    (hsupp : ∀ᵐ y ∂mu, y ∈ K)
    (hbound : ∀ y ∈ K, ‖T y‖ ≤ B) :
    ‖∫ y, T y ∂mu‖ ≤ B := by
  have hnorm_ae : ∀ᵐ y ∂mu, ‖T y‖ ≤ B := by
    filter_upwards [hsupp] with y hy
    exact hbound y hy
  calc
    ‖∫ y, T y ∂mu‖ ≤ ∫ y, ‖T y‖ ∂mu := norm_integral_le_integral_norm T
    _ ≤ ∫ _y, B ∂mu := by
      exact integral_mono_ae hT_int.norm (integrable_const B) hnorm_ae
    _ = B := by
      simp

/-- Monograph Vol IV Ch 2 Step 4 (lines 1061-1075): if the regularized
mean-value identity has already been proved, the Schwinger value is bounded by
the regularized kernel bound on the support of the probability measure. -/
theorem osiiStep4_meanValue_le_support_bound
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu]
    (S : ℂ) (T : α → ℂ) {K : Set α} {B : ℝ}
    (hmean : S = ∫ y, T y ∂mu)
    (hT_int : Integrable T mu)
    (hsupp : ∀ᵐ y ∂mu, y ∈ K)
    (hbound : ∀ y ∈ K, ‖T y‖ ≤ B) :
    ‖S‖ ≤ B := by
  rw [hmean]
  exact osiiStep4_regularized_average_le_support_bound mu T hT_int hsupp hbound

/-- Monograph Vol IV Ch 2 Step 4 (lines 1061-1075) in the exact kernel-integral
form: once the regularized mean-value identity is stated using `k_rho(y) dy`,
the value is bounded by the supremum of the regularized function on the
`rho / 4` support ball. -/
theorem osiiStep4_kernelMeanValue_le_regularizer_support_bound
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (S : ℂ) (T : (Fin m → ℝ) → ℂ) {B : ℝ}
    (hmean :
      S = ∫ x, (osiiStep4RegularizerK m rho hrho x : ℂ) * T x ∂volume)
    (hT_int : Integrable T (osiiStep4RegularizerMeasure m rho hrho))
    (hbound : ∀ y ∈ Metric.ball (0 : Fin m → ℝ) (rho / 4), ‖T y‖ ≤ B) :
    ‖S‖ ≤ B := by
  letI : IsProbabilityMeasure (osiiStep4RegularizerMeasure m rho hrho) :=
    osiiStep4RegularizerMeasure_isProbability m hrho
  have hmean_mu : S = ∫ x, T x ∂osiiStep4RegularizerMeasure m rho hrho := by
    rw [osiiStep4_integral_regularizerMeasure_eq_kernel_mul]
    exact hmean
  exact
    osiiStep4_meanValue_le_support_bound
      (osiiStep4RegularizerMeasure m rho hrho) S T hmean_mu hT_int
      (osiiStep4RegularizerMeasure_support_ae m hrho) hbound

end OSReconstruction
