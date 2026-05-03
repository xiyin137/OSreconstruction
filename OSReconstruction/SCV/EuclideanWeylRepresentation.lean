/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeylApproxIdentity
import OSReconstruction.SCV.DistributionalEOWRegularity

/-!
# Euclidean Weyl Representation

This file assembles the checked Euclidean Weyl scale-invariance, scalar
pairing, and approximate-identity packages into the local representation theorem
on a smaller ball.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter intervalIntegral
open scoped LineDeriv Convolution

namespace SCV

/-- The canonical Weyl ball representative represents the harmonic distribution
on every smaller ball.  This is the non-existential form needed for the
open-set patching theorem. -/
theorem euclideanWeylBallRepresentative_represents_on_ball
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (c : EuclideanSpace ℝ ι) {r R : ℝ}
    (_hr : 0 < r) (hrR : r < R)
    (hΔ :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) (Metric.ball c R) →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
    RepresentsEuclideanDistributionOn T
      (euclideanWeylBallRepresentative T c R) (Metric.ball c r) := by
  let H : EuclideanSpace ℝ ι → ℂ :=
    euclideanWeylBallRepresentative T c R
  let η : ℝ := (R - r) / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hηR : η + r < R := by
    dsimp [η]
    linarith
  intro φ hφ
  let εn : ℕ → ℝ := fun n => min (η / 2) (1 / (n + 1 : ℝ))
  have hεn_pos : ∀ n, 0 < εn n := by
    intro n
    exact lt_min (by linarith) (by positivity)
  let ρn : ℕ → SchwartzMap (EuclideanSpace ℝ ι) ℂ := fun n =>
    euclideanWeylBump (εn n) (hεn_pos n)
  have hρn_support_shrink :
      ∀ n,
        tsupport (ρn n : EuclideanSpace ℝ ι → ℂ) ⊆
          Metric.closedBall 0 (1 / (n + 1 : ℝ)) := by
    intro n x hx
    have hxε := euclideanWeylBump_support (ι := ι) (εn n) (hεn_pos n) hx
    rw [Metric.mem_closedBall] at hxε ⊢
    exact le_trans hxε (min_le_right _ _)
  have happrox :
      Tendsto (fun n => euclideanConvolutionTest φ (ρn n))
        atTop (𝓝 φ) := by
    refine tendsto_euclideanConvolutionTest_of_shrinking_normalized_support
      φ ρn ?_ ?_ ?_ hρn_support_shrink
    · intro n x
      exact euclideanWeylBump_nonneg_re (εn n) (hεn_pos n) x
    · intro n x
      exact euclideanWeylBump_im_eq_zero (εn n) (hεn_pos n) x
    · intro n
      exact euclideanWeylBump_normalized (εn n) (hεn_pos n)
  have hpair :
      ∀ n,
        (∫ x : EuclideanSpace ℝ ι, H x * φ x) =
          T (euclideanConvolutionTest φ (ρn n)) := by
    intro n
    have hρ_compact :
        HasCompactSupport (ρn n : EuclideanSpace ℝ ι → ℂ) := by
      exact IsCompact.of_isClosed_subset
        (isCompact_closedBall (0 : EuclideanSpace ℝ ι) (εn n))
        (isClosed_tsupport _)
        (by
          intro x hx
          simpa [ρn] using
            euclideanWeylBump_support (ι := ι) (εn n) (hεn_pos n) hx)
    have hH_eq :
        ∀ x ∈ tsupport (φ : EuclideanSpace ℝ ι → ℂ),
          H x = T (euclideanReflectedTranslate x (ρn n)) := by
      intro x hx
      have hx_ball : x ∈ Metric.ball c r := hφ.2 hx
      have hε_le_η : εn n ≤ η := by
        calc
          εn n ≤ η / 2 := min_le_left _ _
          _ ≤ η := by linarith
      have hxε : Metric.closedBall x (εn n) ⊆ Metric.ball c R := by
        exact closedBall_subset_ball_of_uniform_margin hx_ball (by linarith)
      simpa [H, ρn] using
        euclideanWeylBallRepresentative_eq_regularized T hΔ
          (hεn_pos n) hxε
    calc
      (∫ x : EuclideanSpace ℝ ι, H x * φ x) =
          ∫ x : EuclideanSpace ℝ ι,
            T (euclideanReflectedTranslate x (ρn n)) * φ x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            by_cases hx : x ∈ tsupport (φ : EuclideanSpace ℝ ι → ℂ)
            · rw [hH_eq x hx]
            · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
              simp [hφx]
      _ = T (euclideanConvolutionTest φ (ρn n)) := by
            exact regularizedDistribution_integral_pairing
              T (ρn n) φ hρ_compact hφ.1
  have hTend :
      Tendsto (fun n => T (euclideanConvolutionTest φ (ρn n)))
        atTop (𝓝 (T φ)) :=
    T.continuous.tendsto φ |>.comp happrox
  have hconst :
      Tendsto (fun _ : ℕ => ∫ x : EuclideanSpace ℝ ι, H x * φ x)
        atTop (𝓝 (T φ)) := by
    have hseq :
        (fun n : ℕ => T (euclideanConvolutionTest φ (ρn n))) =
          fun _ : ℕ => ∫ x : EuclideanSpace ℝ ι, H x * φ x := by
      funext n
      exact (hpair n).symm
    simpa [hseq] using hTend
  exact (tendsto_nhds_unique tendsto_const_nhds hconst).symm

/-- Local Euclidean Weyl representation on a smaller ball.  If a Schwartz
functional annihilates all Laplacians of tests supported in `ball c R`, then on
each smaller ball `ball c r` it is represented by the smooth Weyl ball
representative. -/
theorem euclidean_laplacian_distribution_regular_on_ball
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (c : EuclideanSpace ℝ ι) {r R : ℝ}
    (_hr : 0 < r) (hrR : r < R)
    (hΔ :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) (Metric.ball c R) →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
    ∃ H : EuclideanSpace ℝ ι → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball c r) ∧
      RepresentsEuclideanDistributionOn T H (Metric.ball c r) := by
  let H : EuclideanSpace ℝ ι → ℂ :=
    euclideanWeylBallRepresentative T c R
  let η : ℝ := (R - r) / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hηR : η + r < R := by
    dsimp [η]
    linarith
  have hH_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball c r) := by
    simpa [H] using
      contDiffOn_euclideanWeylBallRepresentative T hη_pos hηR hΔ
  refine ⟨H, hH_smooth, ?_⟩
  intro φ hφ
  let εn : ℕ → ℝ := fun n => min (η / 2) (1 / (n + 1 : ℝ))
  have hεn_pos : ∀ n, 0 < εn n := by
    intro n
    exact lt_min (by linarith) (by positivity)
  let ρn : ℕ → SchwartzMap (EuclideanSpace ℝ ι) ℂ := fun n =>
    euclideanWeylBump (εn n) (hεn_pos n)
  have hρn_support_shrink :
      ∀ n,
        tsupport (ρn n : EuclideanSpace ℝ ι → ℂ) ⊆
          Metric.closedBall 0 (1 / (n + 1 : ℝ)) := by
    intro n x hx
    have hxε := euclideanWeylBump_support (ι := ι) (εn n) (hεn_pos n) hx
    rw [Metric.mem_closedBall] at hxε ⊢
    exact le_trans hxε (min_le_right _ _)
  have happrox :
      Tendsto (fun n => euclideanConvolutionTest φ (ρn n))
        atTop (𝓝 φ) := by
    refine tendsto_euclideanConvolutionTest_of_shrinking_normalized_support
      φ ρn ?_ ?_ ?_ hρn_support_shrink
    · intro n x
      exact euclideanWeylBump_nonneg_re (εn n) (hεn_pos n) x
    · intro n x
      exact euclideanWeylBump_im_eq_zero (εn n) (hεn_pos n) x
    · intro n
      exact euclideanWeylBump_normalized (εn n) (hεn_pos n)
  have hpair :
      ∀ n,
        (∫ x : EuclideanSpace ℝ ι, H x * φ x) =
          T (euclideanConvolutionTest φ (ρn n)) := by
    intro n
    have hρ_compact :
        HasCompactSupport (ρn n : EuclideanSpace ℝ ι → ℂ) := by
      exact IsCompact.of_isClosed_subset
        (isCompact_closedBall (0 : EuclideanSpace ℝ ι) (εn n))
        (isClosed_tsupport _)
        (by
          intro x hx
          simpa [ρn] using
            euclideanWeylBump_support (ι := ι) (εn n) (hεn_pos n) hx)
    have hH_eq :
        ∀ x ∈ tsupport (φ : EuclideanSpace ℝ ι → ℂ),
          H x = T (euclideanReflectedTranslate x (ρn n)) := by
      intro x hx
      have hx_ball : x ∈ Metric.ball c r := hφ.2 hx
      have hε_le_η : εn n ≤ η := by
        calc
          εn n ≤ η / 2 := min_le_left _ _
          _ ≤ η := by linarith
      have hxε : Metric.closedBall x (εn n) ⊆ Metric.ball c R := by
        exact closedBall_subset_ball_of_uniform_margin hx_ball (by linarith)
      simpa [H, ρn] using
        euclideanWeylBallRepresentative_eq_regularized T hΔ
          (hεn_pos n) hxε
    calc
      (∫ x : EuclideanSpace ℝ ι, H x * φ x) =
          ∫ x : EuclideanSpace ℝ ι,
            T (euclideanReflectedTranslate x (ρn n)) * φ x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            by_cases hx : x ∈ tsupport (φ : EuclideanSpace ℝ ι → ℂ)
            · rw [hH_eq x hx]
            · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
              simp [hφx]
      _ = T (euclideanConvolutionTest φ (ρn n)) := by
            exact regularizedDistribution_integral_pairing
              T (ρn n) φ hρ_compact hφ.1
  have hTend :
      Tendsto (fun n => T (euclideanConvolutionTest φ (ρn n)))
        atTop (𝓝 (T φ)) :=
    T.continuous.tendsto φ |>.comp happrox
  have hconst :
      Tendsto (fun _ : ℕ => ∫ x : EuclideanSpace ℝ ι, H x * φ x)
        atTop (𝓝 (T φ)) := by
    have hseq :
        (fun n : ℕ => T (euclideanConvolutionTest φ (ρn n))) =
          fun _ : ℕ => ∫ x : EuclideanSpace ℝ ι, H x * φ x := by
      funext n
      exact (hpair n).symm
    simpa [hseq] using hTend
  exact (tendsto_nhds_unique tendsto_const_nhds hconst).symm

end SCV
