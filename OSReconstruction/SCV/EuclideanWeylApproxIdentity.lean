/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeylPairing
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Euclidean Approximate Identities

This file contains the compact approximate-identity theorem for
`euclideanConvolutionTest`.  It is the Euclidean counterpart of the checked
real-direction approximate identity in `DistributionalEOWApproxIdentity`.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter intervalIntegral
open scoped LineDeriv Convolution

namespace SCV

/-! ### Pointwise convolution and kernel mass -/

/-- Euclidean Schwartz convolution in the symmetric approximate-identity
form: `(φ * ρ)(x) = ∫ t, φ (x - t) * ρ t`. -/
theorem euclideanConvolutionTest_apply_swap
    {ι : Type*} [Fintype ι]
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    euclideanConvolutionTest φ ρ x =
      ∫ t : EuclideanSpace ℝ ι, φ (x - t) * ρ t := by
  rw [euclideanConvolutionTest, SchwartzMap.convolution_apply]
  change (φ ⋆[ContinuousLinearMap.lsmul ℂ ℂ] ρ) x =
    ∫ t : EuclideanSpace ℝ ι, φ (x - t) * ρ t
  rw [MeasureTheory.convolution_lsmul_swap]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp [smul_eq_mul]

/-- A Euclidean kernel supported in a closed ball vanishes outside that ball. -/
theorem euclideanKernel_eq_zero_of_not_mem_closedBall
    {ι : Type*} [Fintype ι]
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) {r : ℝ}
    {t : EuclideanSpace ℝ ι}
    (hρ : tsupport (ρ : EuclideanSpace ℝ ι → ℂ) ⊆
      Metric.closedBall 0 r)
    (ht : t ∉ Metric.closedBall (0 : EuclideanSpace ℝ ι) r) :
    ρ t = 0 := by
  exact image_eq_zero_of_notMem_tsupport (fun htρ => ht (hρ htρ))

/-- A real-valued nonnegative normalized Euclidean Schwartz kernel has `L¹`
mass one. -/
theorem integral_norm_eq_one_of_euclidean_real_nonneg_normalized
    {ι : Type*} [Fintype ι]
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_nonneg : ∀ t : EuclideanSpace ℝ ι, 0 ≤ (ρ t).re)
    (hρ_real : ∀ t : EuclideanSpace ℝ ι, (ρ t).im = 0)
    (hρ_norm : ∫ t : EuclideanSpace ℝ ι, ρ t = 1) :
    ∫ t : EuclideanSpace ℝ ι, ‖ρ t‖ = 1 := by
  have hnorm_point : ∀ t : EuclideanSpace ℝ ι, ‖ρ t‖ = (ρ t).re := by
    intro t
    have hz : ρ t = ((ρ t).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hρ_real t]
    calc
      ‖ρ t‖ = ‖((ρ t).re : ℂ)‖ := congrArg norm hz
      _ = ‖(ρ t).re‖ := Complex.norm_real _
      _ = |(ρ t).re| := Real.norm_eq_abs _
      _ = (ρ t).re := abs_of_nonneg (hρ_nonneg t)
  calc
    ∫ t : EuclideanSpace ℝ ι, ‖ρ t‖ =
        ∫ t : EuclideanSpace ℝ ι, (ρ t).re := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall hnorm_point)
    _ = (∫ t : EuclideanSpace ℝ ι, ρ t).re := by
          exact integral_re ρ.integrable
    _ = 1 := by
          rw [hρ_norm]
          norm_num

/-! ### Differentiating Euclidean convolution tests -/

/-- The translated `l`-th derivative field, multiplied by a Euclidean
Schwartz kernel, is Bochner integrable in the kernel variable. -/
theorem integrable_smul_iteratedFDeriv_euclideanTranslate
    {ι : Type*} [Fintype ι]
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ))
    (l : ℕ) (z : EuclideanSpace ℝ ι) :
    Integrable (fun t : EuclideanSpace ℝ ι =>
      (ρ t) • iteratedFDeriv ℝ l
        (φ : EuclideanSpace ℝ ι → ℂ) (z - t)) := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 l φ
  have hmajor : Integrable (fun t : EuclideanSpace ℝ ι => C * ‖ρ t‖) := by
    exact ρ.integrable.norm.const_mul C
  refine hmajor.mono' ?_ ?_
  · have hsub : Continuous fun t : EuclideanSpace ℝ ι => z - t :=
      continuous_const.sub continuous_id
    have hcontD : Continuous fun t : EuclideanSpace ℝ ι =>
        iteratedFDeriv ℝ l
          (φ : EuclideanSpace ℝ ι → ℂ) (z - t) :=
      ((φ.smooth l).continuous_iteratedFDeriv le_rfl).comp hsub
    have hcont : Continuous fun t : EuclideanSpace ℝ ι =>
        (ρ t) • iteratedFDeriv ℝ l
          (φ : EuclideanSpace ℝ ι → ℂ) (z - t) :=
      ρ.continuous.smul hcontD
    have hsupport :
        Function.support (fun t : EuclideanSpace ℝ ι =>
          (ρ t) • iteratedFDeriv ℝ l
            (φ : EuclideanSpace ℝ ι → ℂ) (z - t)) ⊆
        tsupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
      intro t ht
      by_contra htρ
      have hzero : ρ t = 0 := image_eq_zero_of_notMem_tsupport htρ
      rw [Function.mem_support] at ht
      exact ht (by simp [hzero])
    exact (hcont.stronglyMeasurable_of_support_subset_isCompact
      hρ_compact hsupport).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_smul]
    have hD :
        ‖iteratedFDeriv ℝ l
          (φ : EuclideanSpace ℝ ι → ℂ) (z - t)‖ ≤ C := by
      simpa [C] using
        SchwartzMap.norm_iteratedFDeriv_le_seminorm
          (𝕜 := ℂ) φ l (z - t)
    nlinarith [norm_nonneg (ρ t)]

/-- All-orders Euclidean derivative-through-convolution formula in the
approximate-identity coordinates. -/
theorem iteratedFDeriv_euclideanConvolutionTest_eq_integral
    {ι : Type*} [Fintype ι]
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ))
    (l : ℕ) (z : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ l
      (euclideanConvolutionTest φ ρ : EuclideanSpace ℝ ι → ℂ) z =
      ∫ t : EuclideanSpace ℝ ι,
        (ρ t) • iteratedFDeriv ℝ l
          (φ : EuclideanSpace ℝ ι → ℂ) (z - t) := by
  ext u
  rw [ContinuousMultilinearMap.integral_apply
    (integrable_smul_iteratedFDeriv_euclideanTranslate φ ρ hρ_compact l z) u]
  calc
    iteratedFDeriv ℝ l
        (euclideanConvolutionTest φ ρ : EuclideanSpace ℝ ι → ℂ) z u =
        (∂^{u} (euclideanConvolutionTest φ ρ)) z := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := euclideanConvolutionTest φ ρ) (m := u) (x := z)).symm
    _ = euclideanConvolutionTest (∂^{u} φ) ρ z := by
      rw [iteratedLineDerivOp_euclideanConvolutionTest_left]
    _ = ∫ t : EuclideanSpace ℝ ι, (∂^{u} φ) (z - t) * ρ t := by
      rw [euclideanConvolutionTest_apply_swap]
    _ = ∫ t : EuclideanSpace ℝ ι,
          (ρ t) * iteratedFDeriv ℝ l
            (φ : EuclideanSpace ℝ ι → ℂ) (z - t) u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
      ring
    _ = ∫ t : EuclideanSpace ℝ ι,
          ((ρ t) • iteratedFDeriv ℝ l
            (φ : EuclideanSpace ℝ ι → ℂ) (z - t)) u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      simp [smul_eq_mul]

/-- All-orders formula for the difference between a Euclidean convolution test
and the original test. -/
theorem iteratedFDeriv_euclideanConvolutionTest_sub_eq_integral
    {ι : Type*} [Fintype ι]
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ))
    (hρ_norm : ∫ t : EuclideanSpace ℝ ι, ρ t = 1)
    (l : ℕ) (z : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ l
      (euclideanConvolutionTest φ ρ - φ :
        EuclideanSpace ℝ ι → ℂ) z =
      ∫ t : EuclideanSpace ℝ ι,
        (ρ t) •
          (iteratedFDeriv ℝ l
            (φ : EuclideanSpace ℝ ι → ℂ) (z - t) -
           iteratedFDeriv ℝ l
             (φ : EuclideanSpace ℝ ι → ℂ) z) := by
  let D :
      EuclideanSpace ℝ ι →
        ContinuousMultilinearMap ℝ
          (fun _ : Fin l => EuclideanSpace ℝ ι) ℂ :=
    fun w => iteratedFDeriv ℝ l (φ : EuclideanSpace ℝ ι → ℂ) w
  have hsub_fun :
      (euclideanConvolutionTest φ ρ : EuclideanSpace ℝ ι → ℂ) -
          (φ : EuclideanSpace ℝ ι → ℂ) =
        (euclideanConvolutionTest φ ρ : EuclideanSpace ℝ ι → ℂ) +
          fun w => -φ w := by
    funext w
    simp [sub_eq_add_neg]
  have hleft :
      iteratedFDeriv ℝ l
        (euclideanConvolutionTest φ ρ - φ :
          EuclideanSpace ℝ ι → ℂ) z =
      iteratedFDeriv ℝ l
        (euclideanConvolutionTest φ ρ :
          EuclideanSpace ℝ ι → ℂ) z - D z := by
    change (iteratedFDeriv ℝ l
      ((euclideanConvolutionTest φ ρ : EuclideanSpace ℝ ι → ℂ) -
        (φ : EuclideanSpace ℝ ι → ℂ)) z) =
      iteratedFDeriv ℝ l
        (euclideanConvolutionTest φ ρ :
          EuclideanSpace ℝ ι → ℂ) z - D z
    rw [hsub_fun]
    rw [iteratedFDeriv_add_apply
      ((euclideanConvolutionTest φ ρ).smooth l).contDiffAt
      ((φ.smooth l).neg).contDiffAt]
    rw [show (fun w : EuclideanSpace ℝ ι => -φ w) =
        -(φ : EuclideanSpace ℝ ι → ℂ) by rfl]
    rw [iteratedFDeriv_neg_apply]
    simp [D, sub_eq_add_neg]
  have hconv := iteratedFDeriv_euclideanConvolutionTest_eq_integral
    φ ρ hρ_compact l z
  rw [hleft, hconv]
  have hconst :
      ∫ t : EuclideanSpace ℝ ι, (ρ t) • D z = D z := by
    calc
      ∫ t : EuclideanSpace ℝ ι, (ρ t) • D z =
          (∫ t : EuclideanSpace ℝ ι, ρ t) • D z := by
        exact integral_smul_const
          (fun t : EuclideanSpace ℝ ι => ρ t) (D z)
      _ = D z := by
        rw [hρ_norm]
        simp
  have h1 : Integrable (fun t : EuclideanSpace ℝ ι =>
      (ρ t) • D (z - t)) :=
    integrable_smul_iteratedFDeriv_euclideanTranslate φ ρ hρ_compact l z
  have h2 : Integrable (fun t : EuclideanSpace ℝ ι =>
      (ρ t) • D z) := by
    simpa [D] using ρ.integrable.smul_const (D z)
  calc
    (∫ t : EuclideanSpace ℝ ι, (ρ t) • D (z - t)) - D z =
        (∫ t : EuclideanSpace ℝ ι, (ρ t) • D (z - t)) -
          ∫ t : EuclideanSpace ℝ ι, (ρ t) • D z := by
      rw [hconst]
    _ = ∫ t : EuclideanSpace ℝ ι,
          (ρ t) • D (z - t) - (ρ t) • D z := by
      rw [← integral_sub h1 h2]
    _ = ∫ t : EuclideanSpace ℝ ι,
          (ρ t) • (D (z - t) - D z) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      simp [smul_sub]

/-! ### Approximate-identity convergence -/

/-- A global first-order translation estimate for the weighted `l`-th
Euclidean Schwartz derivative field.  One small Euclidean translation costs
one extra Schwartz derivative. -/
theorem exists_weighted_iteratedFDeriv_euclideanTranslate_sub_le_linear
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z t : EuclideanSpace ℝ ι),
        ‖t‖ ≤ 1 →
          ‖z‖ ^ k *
            ‖iteratedFDeriv ℝ l
                (φ : EuclideanSpace ℝ ι → ℂ) (z - t) -
              iteratedFDeriv ℝ l
                (φ : EuclideanSpace ℝ ι → ℂ) z‖ ≤ C * ‖t‖ := by
  let C : ℝ :=
    2 ^ (k - 1) *
      (SchwartzMap.seminorm ℂ k (l + 1) φ +
        SchwartzMap.seminorm ℂ 0 (l + 1) φ)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro z t ht
  let D : EuclideanSpace ℝ ι →
      ContinuousMultilinearMap ℝ
        (fun _ : Fin l => EuclideanSpace ℝ ι) ℂ :=
    fun w => iteratedFDeriv ℝ l (φ : EuclideanSpace ℝ ι → ℂ) w
  let γ : ℝ →
      ContinuousMultilinearMap ℝ
        (fun _ : Fin l => EuclideanSpace ℝ ι) ℂ :=
    fun s => ‖z‖ ^ k • D (z - s • t)
  have hD_diff : Differentiable ℝ D := by
    simpa [D] using
      (φ.smooth (l + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self l)
  have hγ_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt γ
          (‖z‖ ^ k • (fderiv ℝ D (z - s • t) (-t))) s := by
    intro s
    have hpath :
        HasDerivAt (fun r : ℝ => z - r • t) (-t) s := by
      let L : ℝ →L[ℝ] EuclideanSpace ℝ ι :=
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) t
      have hL : HasDerivAt (fun r : ℝ => r • t) t s := by
        simpa [L, ContinuousLinearMap.smulRight_apply, one_smul] using
          L.hasDerivAt
      have hneg : HasDerivAt (fun r : ℝ => -(r • t)) (-t) s := hL.neg
      simpa [sub_eq_add_neg] using hneg.const_add z
    have hcomp :
        HasDerivAt (fun r : ℝ => D (z - r • t))
          ((fderiv ℝ D (z - s • t)) (-t)) s :=
      (hD_diff (z - s • t)).hasFDerivAt.comp_hasDerivAt s hpath
    simpa [γ] using hcomp.const_smul (‖z‖ ^ k)
  have hγ_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖‖z‖ ^ k • (fderiv ℝ D (z - s • t) (-t))‖ ≤ C * ‖t‖ := by
    intro s hs
    have hs_abs : |s| ≤ 1 := by
      rw [abs_of_nonneg hs.1]
      exact le_of_lt hs.2
    have hst_norm : ‖s • t‖ ≤ 1 := by
      calc
        ‖s • t‖ = |s| * ‖t‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * 1 := by
          gcongr
        _ = 1 := by norm_num
    let w : EuclideanSpace ℝ ι := z - s • t
    have hz_le : ‖z‖ ≤ ‖w‖ + 1 := by
      have hz_eq : w + s • t = z := by
        simp [w, sub_eq_add_neg, add_assoc]
      calc
        ‖z‖ = ‖w + s • t‖ := by rw [hz_eq]
        _ ≤ ‖w‖ + ‖s • t‖ := norm_add_le _ _
        _ ≤ ‖w‖ + 1 := by gcongr
    have hweight :
        ‖z‖ ^ k *
            ‖iteratedFDeriv ℝ (l + 1)
              (φ : EuclideanSpace ℝ ι → ℂ) w‖ ≤ C := by
      calc
        ‖z‖ ^ k *
            ‖iteratedFDeriv ℝ (l + 1)
              (φ : EuclideanSpace ℝ ι → ℂ) w‖
            ≤ (‖w‖ + 1) ^ k *
                ‖iteratedFDeriv ℝ (l + 1)
                  (φ : EuclideanSpace ℝ ι → ℂ) w‖ := by
              gcongr
        _ ≤ (2 ^ (k - 1) * (‖w‖ ^ k + 1 ^ k)) *
                ‖iteratedFDeriv ℝ (l + 1)
                  (φ : EuclideanSpace ℝ ι → ℂ) w‖ := by
              have hpow :
                  (‖w‖ + 1) ^ k ≤
                    2 ^ (k - 1) * (‖w‖ ^ k + 1 ^ k) := by
                simpa [add_comm] using
                  add_pow_le (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1) k
              exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ =
            2 ^ (k - 1) *
              (‖w‖ ^ k *
                  ‖iteratedFDeriv ℝ (l + 1)
                    (φ : EuclideanSpace ℝ ι → ℂ) w‖ +
                ‖iteratedFDeriv ℝ (l + 1)
                  (φ : EuclideanSpace ℝ ι → ℂ) w‖) := by
              ring
        _ ≤
            2 ^ (k - 1) *
              (SchwartzMap.seminorm ℂ k (l + 1) φ +
                SchwartzMap.seminorm ℂ 0 (l + 1) φ) := by
              gcongr
              · exact SchwartzMap.le_seminorm ℂ k (l + 1) φ w
              · simpa using
                  SchwartzMap.norm_iteratedFDeriv_le_seminorm
                    (𝕜 := ℂ) φ (l + 1) w
        _ = C := rfl
    calc
      ‖‖z‖ ^ k • (fderiv ℝ D (z - s • t) (-t))‖
          = ‖z‖ ^ k * ‖(fderiv ℝ D (z - s • t)) (-t)‖ := by
              rw [norm_smul, Real.norm_eq_abs]
              exact congrArg
                (fun r => r * ‖(fderiv ℝ D (z - s • t)) (-t)‖)
                (abs_of_nonneg (pow_nonneg (norm_nonneg z) k))
      _ ≤ ‖z‖ ^ k * (‖fderiv ℝ D (z - s • t)‖ * ‖t‖) := by
              gcongr
              simpa using ContinuousLinearMap.le_opNorm
                (fderiv ℝ D (z - s • t)) (-t)
      _ = (‖z‖ ^ k * ‖fderiv ℝ D (z - s • t)‖) * ‖t‖ := by ring
      _ =
          (‖z‖ ^ k *
            ‖iteratedFDeriv ℝ (l + 1)
              (φ : EuclideanSpace ℝ ι → ℂ) (z - s • t)‖) * ‖t‖ := by
            rw [norm_fderiv_iteratedFDeriv]
      _ ≤ C * ‖t‖ := by
            exact mul_le_mul_of_nonneg_right (by simpa [w] using hweight)
              (norm_nonneg t)
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := γ)
      (f' := fun s => ‖z‖ ^ k • (fderiv ℝ D (z - s • t) (-t)))
      (fun s _ => (hγ_hasDeriv s).hasDerivWithinAt)
      hγ_bound
  have hγ_diff :
      γ 1 - γ 0 = ‖z‖ ^ k • (D (z - t) - D z) := by
    have h1 : (1 : ℝ) • t = t := one_smul ℝ t
    have h0 : (0 : ℝ) • t = 0 := zero_smul ℝ t
    rw [show γ 1 = ‖z‖ ^ k • D (z - t) by
        simp only [γ]
        rw [h1],
      show γ 0 = ‖z‖ ^ k • D z by
        simp only [γ]
        rw [h0, sub_zero]]
    exact (smul_sub (‖z‖ ^ k) (D (z - t)) (D z)).symm
  calc
    ‖z‖ ^ k *
        ‖iteratedFDeriv ℝ l
            (φ : EuclideanSpace ℝ ι → ℂ) (z - t) -
          iteratedFDeriv ℝ l
            (φ : EuclideanSpace ℝ ι → ℂ) z‖
        = ‖γ 1 - γ 0‖ := by
            rw [hγ_diff]
            simp [D, norm_smul]
    _ ≤ C * ‖t‖ := hmv

/-- Uniform smallness of weighted Euclidean translated derivative
differences. -/
theorem weighted_iteratedFDeriv_euclideanTranslate_sub_tendsto_zero
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k l : ℕ) :
    ∀ ε > 0, ∃ δ > 0, ∀ (z t : EuclideanSpace ℝ ι),
      ‖t‖ < δ →
        ‖z‖ ^ k *
          ‖iteratedFDeriv ℝ l
              (φ : EuclideanSpace ℝ ι → ℂ) (z - t) -
            iteratedFDeriv ℝ l
              (φ : EuclideanSpace ℝ ι → ℂ) z‖ < ε := by
  intro ε hε
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_weighted_iteratedFDeriv_euclideanTranslate_sub_le_linear φ k l
  let δ : ℝ := min 1 (ε / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ_pos : 0 < δ := by
    exact lt_min zero_lt_one (div_pos hε hC1)
  refine ⟨δ, hδ_pos, ?_⟩
  intro z t htδ
  have ht_one : ‖t‖ ≤ 1 := by
    exact le_trans (le_of_lt htδ) (min_le_left _ _)
  have hlin := hC z t ht_one
  have hsmall : C * ‖t‖ < ε := by
    have ht_eps : ‖t‖ < ε / (C + 1) :=
      lt_of_lt_of_le htδ (min_le_right _ _)
    calc
      C * ‖t‖ ≤ (C + 1) * ‖t‖ := by
        gcongr
        linarith
      _ < (C + 1) * (ε / (C + 1)) := by
        exact mul_lt_mul_of_pos_left ht_eps hC1
      _ = ε := by field_simp [hC1.ne']
  exact lt_of_le_of_lt hlin hsmall

/-- Normalized Euclidean real nonnegative kernels with support shrinking like
`1/(n+1)` form an approximate identity for `euclideanConvolutionTest` in the
Schwartz topology. -/
theorem tendsto_euclideanConvolutionTest_of_shrinking_normalized_support
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (ρn : ℕ → SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_nonneg : ∀ n t, 0 ≤ (ρn n t).re)
    (hρ_real : ∀ n t, (ρn n t).im = 0)
    (hρ_norm : ∀ n, ∫ t : EuclideanSpace ℝ ι, ρn n t = 1)
    (hρ_support : ∀ n,
      tsupport (ρn n : EuclideanSpace ℝ ι → ℂ) ⊆
        Metric.closedBall 0 (1 / (n + 1 : ℝ))) :
    Filter.Tendsto
      (fun n => euclideanConvolutionTest φ (ρn n))
      Filter.atTop
      (nhds φ) := by
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ ι) ℂ).tendsto_nhds_atTop _ _]
  intro p ε hε
  obtain ⟨k, l⟩ := p
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    weighted_iteratedFDeriv_euclideanTranslate_sub_tendsto_zero
      φ k l (ε / 2) hε2
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ_pos
  refine ⟨N, ?_⟩
  intro n hn
  have hρ_compact : HasCompactSupport (ρn n : EuclideanSpace ℝ ι → ℂ) := by
    exact IsCompact.of_isClosed_subset
      (isCompact_closedBall (0 : EuclideanSpace ℝ ι) (1 / (n + 1 : ℝ)))
      (isClosed_tsupport _) (hρ_support n)
  have hsmall : 1 / (n + 1 : ℝ) < δ := by
    have hmono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      have hNle : (N + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ hn
      exact one_div_le_one_div_of_le (by positivity) hNle
    exact lt_of_le_of_lt hmono hN
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℂ k l
    (euclideanConvolutionTest φ (ρn n) - φ) (by positivity) ?_
  intro z
  let Δ : EuclideanSpace ℝ ι →
      ContinuousMultilinearMap ℝ
        (fun _ : Fin l => EuclideanSpace ℝ ι) ℂ :=
    fun t =>
      iteratedFDeriv ℝ l
          (φ : EuclideanSpace ℝ ι → ℂ) (z - t) -
        iteratedFDeriv ℝ l
          (φ : EuclideanSpace ℝ ι → ℂ) z
  have hformula :=
    iteratedFDeriv_euclideanConvolutionTest_sub_eq_integral
      φ (ρn n) hρ_compact (hρ_norm n) l z
  have hbound : ∀ t : EuclideanSpace ℝ ι,
      ‖‖z‖ ^ k • ((ρn n t) • Δ t)‖ ≤
        (ε / 2) * ‖ρn n t‖ := by
    intro t
    by_cases htball :
        t ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) (1 / (n + 1 : ℝ))
    · have ht_norm : ‖t‖ < δ := by
        have ht_le : ‖t‖ ≤ 1 / (n + 1 : ℝ) := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using htball
        exact lt_of_le_of_lt ht_le hsmall
      have htrans := hδ z t ht_norm
      calc
        ‖‖z‖ ^ k • ((ρn n t) • Δ t)‖
            = ‖ρn n t‖ * (‖z‖ ^ k * ‖Δ t‖) := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs,
                  abs_of_nonneg (pow_nonneg (norm_nonneg z) k)]
                ring
        _ ≤ ‖ρn n t‖ * (ε / 2) := by
                exact mul_le_mul_of_nonneg_left (le_of_lt htrans) (norm_nonneg _)
        _ = (ε / 2) * ‖ρn n t‖ := by ring
    · have hzero : ρn n t = 0 :=
        euclideanKernel_eq_zero_of_not_mem_closedBall
          (ρn n) (hρ_support n) htball
      calc
        ‖‖z‖ ^ k • ((ρn n t) • Δ t)‖ = 0 := by
          rw [hzero]
          rw [zero_smul ℂ (Δ t)]
          rw [norm_smul, norm_zero, mul_zero]
        _ ≤ (ε / 2) * ‖ρn n t‖ := by positivity
  have hnorm_int : ∫ t : EuclideanSpace ℝ ι, ‖ρn n t‖ = 1 :=
    integral_norm_eq_one_of_euclidean_real_nonneg_normalized
      (ρn n) (hρ_nonneg n) (hρ_real n) (hρ_norm n)
  calc
    ‖z‖ ^ k *
        ‖iteratedFDeriv ℝ l
          (euclideanConvolutionTest φ (ρn n) - φ :
            EuclideanSpace ℝ ι → ℂ) z‖
        =
        ‖‖z‖ ^ k •
          iteratedFDeriv ℝ l
            (euclideanConvolutionTest φ (ρn n) - φ :
              EuclideanSpace ℝ ι → ℂ) z‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact congrArg
            (fun r => r *
              ‖iteratedFDeriv ℝ l
                (euclideanConvolutionTest φ (ρn n) - φ :
                  EuclideanSpace ℝ ι → ℂ) z‖)
            (abs_of_nonneg (pow_nonneg (norm_nonneg z) k)).symm
    _ =
        ‖‖z‖ ^ k •
          ∫ t : EuclideanSpace ℝ ι, (ρn n t) • Δ t‖ := by
          rw [hformula]
    _ =
        ‖∫ t : EuclideanSpace ℝ ι, ‖z‖ ^ k • ((ρn n t) • Δ t)‖ := by
          rw [MeasureTheory.integral_smul]
    _ ≤ ∫ t : EuclideanSpace ℝ ι, ‖‖z‖ ^ k • ((ρn n t) • Δ t)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ t : EuclideanSpace ℝ ι, (ε / 2) * ‖ρn n t‖ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact (((SchwartzMap.integrable (ρn n)).norm).const_mul (ε / 2))
          · exact Filter.Eventually.of_forall hbound
    _ = (ε / 2) * ∫ t : EuclideanSpace ℝ ι, ‖ρn n t‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = ε / 2 := by
          simp [hnorm_int]

/-- Explicit shrinking normalized Euclidean Weyl bump sequence. -/
theorem exists_shrinking_normalized_euclideanWeylBump_sequence
    {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : 0 < r) :
    ∃ ρn : ℕ → SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      (∀ n t, 0 ≤ (ρn n t).re) ∧
      (∀ n t, (ρn n t).im = 0) ∧
      (∀ n, ∫ t : EuclideanSpace ℝ ι, ρn n t = 1) ∧
      (∀ n,
        tsupport (ρn n : EuclideanSpace ℝ ι → ℂ) ⊆
          Metric.closedBall 0 (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
      (∀ n,
        tsupport (ρn n : EuclideanSpace ℝ ι → ℂ) ⊆
          Metric.closedBall 0 r) := by
  let εn : ℕ → ℝ := fun n => min (r / 2) (1 / (n + 1 : ℝ))
  have hεn_pos : ∀ n, 0 < εn n := by
    intro n
    exact lt_min (by linarith) (by positivity)
  let ρn : ℕ → SchwartzMap (EuclideanSpace ℝ ι) ℂ := fun n =>
    euclideanWeylBump (εn n) (hεn_pos n)
  refine ⟨ρn, ?_, ?_, ?_, ?_, ?_⟩
  · intro n t
    exact euclideanWeylBump_nonneg_re (εn n) (hεn_pos n) t
  · intro n t
    exact euclideanWeylBump_im_eq_zero (εn n) (hεn_pos n) t
  · intro n
    exact euclideanWeylBump_normalized (εn n) (hεn_pos n)
  · intro n
    simpa [ρn, εn] using
      euclideanWeylBump_support (ι := ι) (εn n) (hεn_pos n)
  · intro n t ht
    have ht' := euclideanWeylBump_support (ι := ι) (εn n) (hεn_pos n) ht
    rw [Metric.mem_closedBall] at ht' ⊢
    have hle : εn n ≤ r := by
      calc
        εn n ≤ r / 2 := min_le_left _ _
        _ ≤ r := by linarith
    exact le_trans ht' hle

/-- Public compact Euclidean approximate-identity package for the Weyl
regularization route. -/
theorem exists_euclideanConvolutionTest_approxIdentity
    {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : 0 < r) :
    ∃ ρn : ℕ → SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      (∀ n, ∫ t : EuclideanSpace ℝ ι, ρn n t = 1) ∧
      (∀ n,
        tsupport (ρn n : EuclideanSpace ℝ ι → ℂ) ⊆
          Metric.closedBall 0 (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
      (∀ n,
        tsupport (ρn n : EuclideanSpace ℝ ι → ℂ) ⊆
          Metric.closedBall 0 r) ∧
      (∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        Filter.Tendsto
          (fun n => euclideanConvolutionTest φ (ρn n))
          Filter.atTop
          (nhds φ)) := by
  obtain ⟨ρn, hnonneg, hreal, hnorm, hmin, hradius⟩ :=
    exists_shrinking_normalized_euclideanWeylBump_sequence (ι := ι) hr
  refine ⟨ρn, hnorm, hmin, hradius, ?_⟩
  intro φ
  refine tendsto_euclideanConvolutionTest_of_shrinking_normalized_support
    φ ρn hnonneg hreal hnorm ?_
  intro n t ht
  have htmin := hmin n ht
  rw [Metric.mem_closedBall] at htmin ⊢
  exact le_trans htmin (min_le_right _ _)

end SCV
