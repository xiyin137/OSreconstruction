/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialConvolution











noncomputable section

open Complex MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

/-- A closed rectangular support containing the two imaginary parameters of
the block-radial partial transform. -/
def osiiStep4PartialConvolutionClosedImaginaryBox
    (q k : ℕ) (rho : ℝ) :
    Set ((Fin (k * q) → ℝ) × (Fin (k * q) → ℝ)) :=
  Metric.closedBall 0 (rho / 4) ×ˢ Metric.closedBall 0 (rho / 8)

theorem osiiStep4PartialConvolutionClosedImaginaryBox_isCompact
    (q k : ℕ) (rho : ℝ) :
    IsCompact (osiiStep4PartialConvolutionClosedImaginaryBox q k rho) :=
  (isCompact_closedBall
    (0 : Fin (k * q) → ℝ) (rho / 4)).prod
      (isCompact_closedBall (0 : Fin (k * q) → ℝ) (rho / 8))

/-- A function supported in a product set vanishes when its first argument
lies outside the first factor. -/
theorem eq_zero_of_support_subset_prod_left
    {α β γ : Type*} [Zero γ]
    (f : α × β → γ) (A : Set α) (B : Set β)
    (hsupport : Function.support f ⊆ A ×ˢ B)
    (x : α) (y : β) (hx : x ∉ A) :
    f (x, y) = 0 := by
  by_contra hne
  exact hx (hsupport hne).1

theorem osiiStep4FullBlockRadialG_imaginary_coord_lt
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (z : Fin (k * q) → ℂ)
    (hz : osiiStep4FullBlockRadialG q k rho z ≠ 0)
    (i : Fin k) (mu : Fin q) :
    |(z (finProdFinEquiv (i, mu))).im| < rho / 8 := by
  have hzblock :=
    osiiStep4FullBlockRadialG_support_subset q k hrho
      (Function.mem_support.mpr hz) i
  rw [osiiStep4ComplexBlockBall, Set.mem_setOf_eq] at hzblock
  let block : Fin q → ℂ :=
    (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i
  calc
    |(z (finProdFinEquiv (i, mu))).im| = |(block mu).im| := by
      simp [block]
    _ ≤ ‖block mu‖ := Complex.abs_im_le_norm _
    _ ≤ ‖osiiStep4ComplexBlockToEuclideanCLE q block‖ := by
      simpa using
        PiLp.norm_apply_le (osiiStep4ComplexBlockToEuclideanCLE q block) mu
    _ < rho / 8 := by simpa [block] using hzblock

theorem osiiStep4PartialConvolutionKernel_eq_zero_of_auxImaginary_coord
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (x y y' : Fin (k * q) → ℝ)
    (i : Fin k) (mu : Fin q)
    (hcoord : rho / 8 ≤ |y' (finProdFinEquiv (i, mu))|) :
    osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y' = 0 := by
  rw [osiiStep4PartialConvolutionKernel]
  apply integral_eq_zero_of_ae
  filter_upwards with x'
  have hgzero : osiiStep4FullBlockRadialG q k rho
      (osiiStep4ComplexOfRealImag x' y') = 0 := by
    by_contra hne
    have hlt := osiiStep4FullBlockRadialG_imaginary_coord_lt
      q k hrho (osiiStep4ComplexOfRealImag x' y') hne i mu
    simp only [osiiStep4ComplexOfRealImag_im] at hlt
    exact (not_lt_of_ge hcoord) hlt
  simp [hgzero]

theorem osiiStep4PartialConvolutionKernel_eq_zero_of_imaginaryDifference_coord
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (x y y' : Fin (k * q) → ℝ)
    (i : Fin k) (mu : Fin q)
    (hcoord : rho / 8 ≤
      |y (finProdFinEquiv (i, mu)) -
        y' (finProdFinEquiv (i, mu))|) :
    osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y' = 0 := by
  rw [osiiStep4PartialConvolutionKernel]
  apply integral_eq_zero_of_ae
  filter_upwards with x'
  have hgzero : osiiStep4FullBlockRadialG q k rho
      (osiiStep4ComplexOfRealImag x y -
        osiiStep4ComplexOfRealImag x' y') = 0 := by
    by_contra hne
    have hlt := osiiStep4FullBlockRadialG_imaginary_coord_lt
      q k hrho
        (osiiStep4ComplexOfRealImag x y -
          osiiStep4ComplexOfRealImag x' y') hne i mu
    simp only [Pi.sub_apply, Complex.sub_im,
      osiiStep4ComplexOfRealImag_im] at hlt
    exact (not_lt_of_ge hcoord) hlt
  simp [hgzero]

/-- The two independent imaginary parameters allowed by the support of the
partial convolution integrand. -/
def osiiStep4PartialConvolutionImaginarySupport
    (q k : ℕ) (rho : ℝ) :
    Set ((Fin (k * q) → ℝ) × (Fin (k * q) → ℝ)) :=
  {p | ∀ i : Fin k, ∀ mu : Fin q,
    |p.2 (finProdFinEquiv (i, mu))| < rho / 8 ∧
    |p.1 (finProdFinEquiv (i, mu)) -
      p.2 (finProdFinEquiv (i, mu))| < rho / 8}

theorem osiiStep4PartialConvolutionTransform_support_subset
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ)
    (c : Fin (k * q) → ℂ) :
    Function.support
        (fun p : (Fin (k * q) → ℝ) × (Fin (k * q) → ℝ) =>
          osiiStep4PartialConvolutionTransform
            (osiiStep4FullBlockRadialG q k rho) F c p.1 p.2) ⊆
      osiiStep4PartialConvolutionImaginarySupport q k rho := by
  intro p hp i mu
  constructor
  · by_contra hnot
    have hge : rho / 8 ≤ |p.2 (finProdFinEquiv (i, mu))| :=
      le_of_not_gt hnot
    apply hp
    unfold osiiStep4PartialConvolutionTransform
    apply integral_eq_zero_of_ae
    filter_upwards with x
    rw [osiiStep4PartialConvolutionKernel_eq_zero_of_auxImaginary_coord
      q k hrho x p.1 p.2 i mu hge]
    simp
  · by_contra hnot
    have hge : rho / 8 ≤
        |p.1 (finProdFinEquiv (i, mu)) -
          p.2 (finProdFinEquiv (i, mu))| :=
      le_of_not_gt hnot
    apply hp
    unfold osiiStep4PartialConvolutionTransform
    apply integral_eq_zero_of_ae
    filter_upwards with x
    rw [osiiStep4PartialConvolutionKernel_eq_zero_of_imaginaryDifference_coord
      q k hrho x p.1 p.2 i mu hge]
    simp

theorem osiiStep4PartialConvolutionTransform_support_imaginary_coord_lt
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ)
    (c : Fin (k * q) → ℂ)
    {p : (Fin (k * q) → ℝ) × (Fin (k * q) → ℝ)}
    (hp : p ∈ Function.support
      (fun p : (Fin (k * q) → ℝ) × (Fin (k * q) → ℝ) =>
        osiiStep4PartialConvolutionTransform
          (osiiStep4FullBlockRadialG q k rho) F c p.1 p.2))
    (i : Fin k) (mu : Fin q) :
    |p.1 (finProdFinEquiv (i, mu))| < rho / 4 := by
  have hsupp := osiiStep4PartialConvolutionTransform_support_subset
    q k hrho F c hp i mu
  calc
    |p.1 (finProdFinEquiv (i, mu))| =
        |(p.1 (finProdFinEquiv (i, mu)) -
            p.2 (finProdFinEquiv (i, mu))) +
          p.2 (finProdFinEquiv (i, mu))| := by ring_nf
    _ ≤ |p.1 (finProdFinEquiv (i, mu)) -
            p.2 (finProdFinEquiv (i, mu))| +
          |p.2 (finProdFinEquiv (i, mu))| := abs_add_le _ _
    _ < rho / 4 := by linarith [hsupp.1, hsupp.2]

end OSReconstruction
