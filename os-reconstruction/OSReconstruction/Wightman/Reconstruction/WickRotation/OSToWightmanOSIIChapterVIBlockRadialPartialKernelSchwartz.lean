import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialConvolution

/-!
# Schwartz slices of the OS-II block partial kernel

The Chapter-V endpoint is distributional in the real spatial variables, so
the pointwise full-complex transform cannot be applied to it directly.  This
module provides the correct bridge: at fixed imaginary parameters, the
partial-convolution kernel is a smooth compactly supported function of all
real spacetime coordinates and therefore an honest Schwartz test.

The proof identifies the partial kernel with the real convolution of two
fixed-imaginary slices of the block-radial density.  Standard convolution
theorems then supply smoothness and compact support.
-/

noncomputable section

open Complex MeasureTheory Metric Set
open scoped Classical Convolution

namespace OSReconstruction

/-- Restrict the full complex block density to a fixed imaginary slice. -/
noncomputable def osiiStep4FullBlockRadialGRealSlice
    (q k : ℕ) (rho : ℝ) (y x : Fin (k * q) → ℝ) : ℝ :=
  osiiStep4FullBlockRadialG q k rho
    (osiiStep4ComplexOfRealImag x y)

theorem osiiStep4FullBlockRadialGRealSlice_contDiff
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y : Fin (k * q) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (osiiStep4FullBlockRadialGRealSlice q k rho y) := by
  apply (osiiStep4FullBlockRadialG_contDiff q k hrho).comp
  rw [contDiff_pi]
  intro a
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Fin (k * q) → ℝ => (x a : ℂ) + (y a : ℂ) * I)
  have hx : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin (k * q) → ℝ => (x a : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.proj
        (R := ℝ)
        (ι := Fin (k * q))
        (φ := fun _ => ℝ) a).contDiff
  exact hx.add contDiff_const

/-- Each real block of a fixed-imaginary slice remains inside the original
block-radial support. -/
theorem osiiStep4FullBlockRadialGRealSlice_support_block_lt
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y x : Fin (k * q) → ℝ)
    (hx : x ∈ Function.support
      (osiiStep4FullBlockRadialGRealSlice q k rho y))
    (i : Fin k) :
    ‖osiiStep4ComplexBlockToEuclideanCLE q
        (fun mu => (x (finProdFinEquiv (i, mu)) : ℂ))‖ < rho / 8 := by
  have hz := osiiStep4FullBlockRadialG_support_subset q k hrho hx
  let block : Fin q → ℂ :=
    (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm
      (osiiStep4ComplexOfRealImag x y) i
  have hblock :
      ‖osiiStep4ComplexBlockToEuclideanCLE q block‖ < rho / 8 := by
    simpa [osiiStep4FullBlockRadialSupport,
      osiiStep4ComplexBlockBall, block] using hz i
  calc
    ‖osiiStep4ComplexBlockToEuclideanCLE q
        (fun mu => (x (finProdFinEquiv (i, mu)) : ℂ))‖ =
        ‖osiiStep4ComplexBlockToEuclideanCLE q
          (fun mu => ((block mu).re : ℂ))‖ := by
      congr 2
      funext mu
      simp [block]
    _ ≤ ‖osiiStep4ComplexBlockToEuclideanCLE q block‖ :=
      osiiStep4ComplexBlockRealPart_norm_le q block
    _ < rho / 8 := hblock

theorem osiiStep4FullBlockRadialGRealSlice_support_subset_closedBall
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y : Fin (k * q) → ℝ) :
    Function.support
        (osiiStep4FullBlockRadialGRealSlice q k rho y) ⊆
      Metric.closedBall (0 : Fin (k * q) → ℝ) (rho / 8) := by
  intro x hx
  have hz := osiiStep4FullBlockRadialG_support_subset q k hrho hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro a
  let i : Fin k := (finProdFinEquiv.symm a).1
  let mu : Fin q := (finProdFinEquiv.symm a).2
  let block : Fin q → ℂ :=
    (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm
      (osiiStep4ComplexOfRealImag x y) i
  have hblock :
      ‖osiiStep4ComplexBlockToEuclideanCLE q block‖ < rho / 8 := by
    simpa [osiiStep4FullBlockRadialSupport,
      osiiStep4ComplexBlockBall, block] using hz i
  have ha : finProdFinEquiv (i, mu) = a := by
    exact finProdFinEquiv.apply_symm_apply a
  rw [Real.norm_eq_abs]
  calc
    |x a| = |x (finProdFinEquiv (i, mu))| := by rw [ha]
    _ = |(block mu).re| := by simp [block]
    _ ≤ ‖block mu‖ := Complex.abs_re_le_norm _
    _ ≤ ‖osiiStep4ComplexBlockToEuclideanCLE q block‖ := by
      simpa using
        PiLp.norm_apply_le (osiiStep4ComplexBlockToEuclideanCLE q block) mu
    _ ≤ rho / 8 := hblock.le

theorem osiiStep4FullBlockRadialGRealSlice_hasCompactSupport
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y : Fin (k * q) → ℝ) :
    HasCompactSupport
      (osiiStep4FullBlockRadialGRealSlice q k rho y) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin (k * q) → ℝ) (rho / 8))
  exact osiiStep4FullBlockRadialGRealSlice_support_subset_closedBall
    q k hrho y

/-- The partial kernel is the real convolution of its two fixed-imaginary
slices. -/
theorem osiiStep4PartialConvolutionKernel_eq_realSlice_convolution
    (q k : ℕ) (rho : ℝ)
    (x y y' : Fin (k * q) → ℝ) :
    osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y' =
      ((osiiStep4FullBlockRadialGRealSlice q k rho y') ⋆
        (osiiStep4FullBlockRadialGRealSlice q k rho (y - y'))) x := by
  rw [osiiStep4PartialConvolutionKernel, MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards with x'
  have hcomplex :
      osiiStep4ComplexOfRealImag x y -
          osiiStep4ComplexOfRealImag x' y' =
        osiiStep4ComplexOfRealImag (x - x') (y - y') := by
    ext a
    simp [osiiStep4ComplexOfRealImag]
    ring
  rw [hcomplex]
  simp only [osiiStep4FullBlockRadialGRealSlice,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

/-- Every real block in the support of the partial kernel lies in the doubled
block-radial support. -/
theorem osiiStep4PartialConvolutionKernel_support_block_lt
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y y' x : Fin (k * q) → ℝ)
    (hx : x ∈ Function.support (fun u : Fin (k * q) → ℝ =>
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag u y) y'))
    (i : Fin k) :
    ‖osiiStep4ComplexBlockToEuclideanCLE q
        (fun mu => (x (finProdFinEquiv (i, mu)) : ℂ))‖ < rho / 4 := by
  rw [show (fun u : Fin (k * q) → ℝ =>
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag u y) y') =
      (osiiStep4FullBlockRadialGRealSlice q k rho y') ⋆
        (osiiStep4FullBlockRadialGRealSlice q k rho (y - y')) by
    funext u
    exact osiiStep4PartialConvolutionKernel_eq_realSlice_convolution
      q k rho u y y'] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    MeasureTheory.support_convolution_subset
      (ContinuousLinearMap.lsmul ℝ ℝ) hx
  have huBlock :=
    osiiStep4FullBlockRadialGRealSlice_support_block_lt
      q k hrho y' u hu i
  have hvBlock :=
    osiiStep4FullBlockRadialGRealSlice_support_block_lt
      q k hrho (y - y') v hv i
  have hfun :
      (fun mu => ((u + v) (finProdFinEquiv (i, mu)) : ℂ)) =
        (fun mu => (u (finProdFinEquiv (i, mu)) : ℂ)) +
          fun mu => (v (finProdFinEquiv (i, mu)) : ℂ) := by
    funext mu
    simp
  rw [hfun, map_add]
  calc
    ‖osiiStep4ComplexBlockToEuclideanCLE q
          (fun mu => (u (finProdFinEquiv (i, mu)) : ℂ)) +
        osiiStep4ComplexBlockToEuclideanCLE q
          (fun mu => (v (finProdFinEquiv (i, mu)) : ℂ))‖ ≤
        ‖osiiStep4ComplexBlockToEuclideanCLE q
          (fun mu => (u (finProdFinEquiv (i, mu)) : ℂ))‖ +
        ‖osiiStep4ComplexBlockToEuclideanCLE q
          (fun mu => (v (finProdFinEquiv (i, mu)) : ℂ))‖ :=
      norm_add_le _ _
    _ < rho / 4 := by linarith

theorem osiiStep4PartialConvolutionKernel_support_subset_closedBall
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y y' : Fin (k * q) → ℝ) :
    Function.support (fun x : Fin (k * q) → ℝ =>
        osiiStep4PartialConvolutionKernel
          (osiiStep4FullBlockRadialG q k rho)
          (osiiStep4ComplexOfRealImag x y) y') ⊆
      Metric.closedBall (0 : Fin (k * q) → ℝ) (rho / 4) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro a
  let i : Fin k := (finProdFinEquiv.symm a).1
  let mu : Fin q := (finProdFinEquiv.symm a).2
  have hblock := osiiStep4PartialConvolutionKernel_support_block_lt
    q k hrho y y' x hx i
  have hcoord := PiLp.norm_apply_le
    (osiiStep4ComplexBlockToEuclideanCLE q
      (fun nu => (x (finProdFinEquiv (i, nu)) : ℂ))) mu
  have ha : finProdFinEquiv (i, mu) = a :=
    finProdFinEquiv.apply_symm_apply a
  rw [Real.norm_eq_abs]
  calc
    |x a| = |x (finProdFinEquiv (i, mu))| := by rw [ha]
    _ = ‖(x (finProdFinEquiv (i, mu)) : ℂ)‖ := by simp
    _ ≤ ‖osiiStep4ComplexBlockToEuclideanCLE q
        (fun nu => (x (finProdFinEquiv (i, nu)) : ℂ))‖ := by
      simpa using hcoord
    _ ≤ rho / 4 := hblock.le

theorem osiiStep4PartialConvolutionKernel_contDiff_real
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y y' : Fin (k * q) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin (k * q) → ℝ =>
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y') := by
  rw [show (fun x : Fin (k * q) → ℝ =>
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y') =
      (osiiStep4FullBlockRadialGRealSlice q k rho y') ⋆
        (osiiStep4FullBlockRadialGRealSlice q k rho (y - y')) by
    funext x
    exact osiiStep4PartialConvolutionKernel_eq_realSlice_convolution
      q k rho x y y']
  exact
    (osiiStep4FullBlockRadialGRealSlice_hasCompactSupport
      q k hrho (y - y')).contDiff_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (osiiStep4FullBlockRadialGRealSlice_contDiff
          q k hrho y').continuous.locallyIntegrable
        (osiiStep4FullBlockRadialGRealSlice_contDiff q k hrho (y - y'))

theorem osiiStep4PartialConvolutionKernel_hasCompactSupport_real
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y y' : Fin (k * q) → ℝ) :
    HasCompactSupport (fun x : Fin (k * q) → ℝ =>
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y') := by
  rw [show (fun x : Fin (k * q) → ℝ =>
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y') =
      (osiiStep4FullBlockRadialGRealSlice q k rho y') ⋆
        (osiiStep4FullBlockRadialGRealSlice q k rho (y - y')) by
    funext x
    exact osiiStep4PartialConvolutionKernel_eq_realSlice_convolution
      q k rho x y y']
  exact
    (osiiStep4FullBlockRadialGRealSlice_hasCompactSupport q k hrho y').convolution
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (osiiStep4FullBlockRadialGRealSlice_hasCompactSupport
        q k hrho (y - y'))

/-- The fixed-imaginary partial kernel as a real full-spacetime Schwartz
test. -/
noncomputable def osiiStep4PartialConvolutionKernelSchwartz
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y y' : Fin (k * q) → ℝ) :
    SchwartzMap (Fin (k * q) → ℝ) ℝ :=
  (osiiStep4PartialConvolutionKernel_hasCompactSupport_real
      q k hrho y y').toSchwartzMap
    (osiiStep4PartialConvolutionKernel_contDiff_real q k hrho y y')

@[simp]
theorem osiiStep4PartialConvolutionKernelSchwartz_apply
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y y' x : Fin (k * q) → ℝ) :
    osiiStep4PartialConvolutionKernelSchwartz q k hrho y y' x =
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y' := by
  exact HasCompactSupport.toSchwartzMap_toFun
    (osiiStep4PartialConvolutionKernel_hasCompactSupport_real
      q k hrho y y')
    (osiiStep4PartialConvolutionKernel_contDiff_real q k hrho y y') x

end OSReconstruction
