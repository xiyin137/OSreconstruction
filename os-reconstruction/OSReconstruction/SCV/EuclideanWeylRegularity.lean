/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeylPoisson
import Mathlib.Analysis.Fourier.Convolution

/-!
# Local Euclidean Weyl Representatives

This file contains the first local representative layer after the checked
Euclidean Weyl scale-invariance theorem: on a ball where the distribution is
harmonic, the value obtained by pairing against any sufficiently local normalized
Weyl bump is independent of the bump scale, hence can be represented on smaller
balls by one fixed smooth regularization.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter intervalIntegral
open scoped LineDeriv Convolution

namespace SCV

/-- The half-margin closed ball around a point of `ball c R` stays inside
`ball c R`. -/
theorem closedBall_subset_ball_of_half_margin
    {ι : Type*} [Fintype ι]
    {c x : EuclideanSpace ℝ ι} {R : ℝ}
    (hx : x ∈ Metric.ball c R) :
    Metric.closedBall x ((R - dist x c) / 2) ⊆ Metric.ball c R := by
  intro y hy
  rw [Metric.mem_ball] at hx ⊢
  have hyx : dist y x ≤ (R - dist x c) / 2 := by
    simpa [Metric.mem_closedBall] using hy
  have hyc : dist y c ≤ dist y x + dist x c := dist_triangle y x c
  have hlt : dist y x + dist x c < R := by
    nlinarith
  exact lt_of_le_of_lt hyc hlt

/-- A uniform radius with margin `ε + r < R` gives closed balls around every
point of `ball c r` contained in `ball c R`. -/
theorem closedBall_subset_ball_of_uniform_margin
    {ι : Type*} [Fintype ι]
    {c x : EuclideanSpace ℝ ι} {r R ε : ℝ}
    (hx : x ∈ Metric.ball c r)
    (hεR : ε + r < R) :
    Metric.closedBall x ε ⊆ Metric.ball c R := by
  intro y hy
  rw [Metric.mem_ball] at hx ⊢
  have hyx : dist y x ≤ ε := by
    simpa [Metric.mem_closedBall] using hy
  have hyc : dist y c ≤ dist y x + dist x c := dist_triangle y x c
  have hlt : dist y x + dist x c < R := by
    nlinarith
  exact lt_of_le_of_lt hyc hlt

/-- The local Weyl representative on `ball c R`, defined by choosing the
half-margin bump scale at each interior point and zero outside the ball. -/
noncomputable def euclideanWeylBallRepresentative
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (c : EuclideanSpace ℝ ι) (R : ℝ)
    (x : EuclideanSpace ℝ ι) : ℂ := by
  classical
  exact
    if hx : x ∈ Metric.ball c R then
      let ε := (R - dist x c) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        rw [Metric.mem_ball] at hx
        linarith
      T (euclideanReflectedTranslate x (euclideanWeylBump ε hε))
    else 0

/-- Inside a harmonicity ball, the variable-radius representative agrees with
any fixed normalized bump whose closed support ball stays inside the same
harmonicity ball. -/
theorem euclideanWeylBallRepresentative_eq_regularized
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    {c : EuclideanSpace ℝ ι} {R ε : ℝ}
    (hΔ :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) (Metric.ball c R) →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0)
    {x : EuclideanSpace ℝ ι}
    (hε : 0 < ε)
    (hxε : Metric.closedBall x ε ⊆ Metric.ball c R) :
    euclideanWeylBallRepresentative T c R x =
      T (euclideanReflectedTranslate x (euclideanWeylBump ε hε)) := by
  have hx : x ∈ Metric.ball c R := by
    apply hxε
    simp [Metric.mem_closedBall, hε.le]
  unfold euclideanWeylBallRepresentative
  rw [dif_pos hx]
  apply regularizedDistribution_bump_scale_eq T hΔ
  · exact closedBall_subset_ball_of_half_margin hx
  · exact hxε

/-- On a smaller ball, the variable-radius representative is a fixed smooth
regularization as soon as the fixed bump radius has uniform margin to the larger
ball. -/
theorem euclideanWeylBallRepresentative_eq_regularized_on_ball
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    {c : EuclideanSpace ℝ ι} {r R ε : ℝ}
    (hε : 0 < ε)
    (hεR : ε + r < R)
    (hΔ :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) (Metric.ball c R) →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
    ∀ x ∈ Metric.ball c r,
      euclideanWeylBallRepresentative T c R x =
        T (euclideanReflectedTranslate x (euclideanWeylBump ε hε)) := by
  intro x hx
  exact euclideanWeylBallRepresentative_eq_regularized T hΔ hε
    (closedBall_subset_ball_of_uniform_margin hx hεR)

/-- The Weyl ball representative is smooth on every smaller ball that admits a
fixed bump radius with positive margin. -/
theorem contDiffOn_euclideanWeylBallRepresentative
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    {c : EuclideanSpace ℝ ι} {r R ε : ℝ}
    (hε : 0 < ε)
    (hεR : ε + r < R)
    (hΔ :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) (Metric.ball c R) →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (euclideanWeylBallRepresentative T c R) (Metric.ball c r) := by
  have hreg : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ ι =>
      T (euclideanReflectedTranslate x (euclideanWeylBump ε hε))) :=
    contDiff_regularizedDistribution T (euclideanWeylBump ε hε)
  refine hreg.contDiffOn.congr ?_
  intro x hx
  exact euclideanWeylBallRepresentative_eq_regularized_on_ball T hε hεR hΔ x hx

/-! ### Euclidean convolution tests for the representative identity -/

/-- Euclidean convolution of two Schwartz tests, using Mathlib's Schwartz
convolution.  With Mathlib's convention this is
`x ↦ ∫ y, φ y * ρ (x - y)`, matching the reflected translate
`euclideanReflectedTranslate y ρ x = ρ (x - y)`. -/
noncomputable def euclideanConvolutionTest
    {ι : Type*} [Fintype ι]
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) φ ρ

@[simp]
theorem euclideanConvolutionTest_apply
    {ι : Type*} [Fintype ι]
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    euclideanConvolutionTest φ ρ x =
      ∫ y : EuclideanSpace ℝ ι, φ y * ρ (x - y) := by
  rw [euclideanConvolutionTest, SchwartzMap.convolution_apply]
  rfl

/-- Same convolution formula with the scalar factors commuted. -/
theorem euclideanConvolutionTest_apply_reflected
    {ι : Type*} [Fintype ι]
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    euclideanConvolutionTest φ ρ x =
      ∫ y : EuclideanSpace ℝ ι, ρ (x - y) * φ y := by
  rw [euclideanConvolutionTest_apply]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  ring_nf

/-- Pointwise convolution written in the exact reflected-translate form needed
for the distribution-pairing identity. -/
theorem euclideanConvolutionTest_apply_reflectedTranslate
    {ι : Type*} [Fintype ι]
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (y : EuclideanSpace ℝ ι) :
    euclideanConvolutionTest φ ρ y =
      ∫ x : EuclideanSpace ℝ ι, euclideanReflectedTranslate x ρ y * φ x := by
  rw [euclideanConvolutionTest_apply_reflected]
  rfl

end SCV
