/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.NuclearSpaces.ComplexSchwartz
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelSchwartz
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeSpatialCurrying















noncomputable section

open Complex Metric Set
open scoped Classical

namespace OSReconstruction

/-- Complexify the real fixed-imaginary partial kernel without changing its
pointwise values. -/
noncomputable def osiiStep4PartialConvolutionKernelComplexSchwartz
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y y' : Fin (k * q) → ℝ) :
    SchwartzMap (Fin (k * q) → ℝ) ℂ :=
  SchwartzMap.ofRealCLM
    (osiiStep4PartialConvolutionKernelSchwartz q k hrho y y')

@[simp]
theorem osiiStep4PartialConvolutionKernelComplexSchwartz_apply
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y y' x : Fin (k * q) → ℝ) :
    osiiStep4PartialConvolutionKernelComplexSchwartz q k hrho y y' x =
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y' := by
  simp [osiiStep4PartialConvolutionKernelComplexSchwartz]

/-- The fixed-imaginary partial kernel in the canonical `k`-point spacetime
Schwartz space. -/
noncomputable def osiiStep4PartialConvolutionKernelFullSource
    (d k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (y y' : Fin (k * (d + 1)) → ℝ) :
    SchwartzNPoint d k :=
  unflattenSchwartzNPoint (d := d)
    (osiiStep4PartialConvolutionKernelComplexSchwartz
      (d + 1) k hrho y y')

/-- Translate the flat partial-kernel source to a real spacetime center. -/
noncomputable def osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * q) → ℝ) :
    SchwartzMap (Fin (k * q) → ℝ) ℂ :=
  SCV.translateSchwartz (-center)
    (osiiStep4PartialConvolutionKernelComplexSchwartz q k hrho y y')

@[simp]
theorem osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (center y y' x : Fin (k * q) → ℝ) :
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        q k hrho center y y' x =
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag (x - center) y) y' := by
  simp [osiiStep4CenteredPartialConvolutionKernelComplexSchwartz,
    sub_eq_add_neg]

theorem
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_support_subset
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * q) → ℝ) :
    Function.support
        (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          q k hrho center y y' : (Fin (k * q) → ℝ) → ℂ) ⊆
      Metric.closedBall center (rho / 4) := by
  intro x hx
  have hkernel :
      x - center ∈ Function.support (fun u : Fin (k * q) → ℝ =>
        osiiStep4PartialConvolutionKernel
          (osiiStep4FullBlockRadialG q k rho)
          (osiiStep4ComplexOfRealImag u y) y') := by
    simpa [Function.mem_support] using hx
  have hball :=
    osiiStep4PartialConvolutionKernel_support_subset_closedBall
      q k hrho y y' hkernel
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  simpa [Metric.mem_closedBall, dist_eq_norm] using hball

/-- The centered partial kernel transported to the canonical full spacetime
Schwartz space. -/
noncomputable def osiiStep4CenteredPartialConvolutionKernelFullSource
    (d k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → ℝ) :
    SchwartzNPoint d k :=
  unflattenSchwartzNPoint (d := d)
    (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
      (d + 1) k hrho center y y')

@[simp]
theorem flatten_osiiStep4CenteredPartialConvolutionKernelFullSource
    (d k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (center y y' x : Fin (k * (d + 1)) → ℝ) :
    flattenSchwartzNPoint (d := d)
        (osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center y y') x =
      osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          (d + 1) k hrho center y y' x := by
  simp [osiiStep4CenteredPartialConvolutionKernelFullSource]

/-- The canonical flattened full source inherits the real support ball of
the centered partial-convolution kernel. -/
theorem
    flatten_osiiStep4CenteredPartialConvolutionKernelFullSource_support_subset
    (d k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → ℝ) :
    Function.support
        (flattenSchwartzNPoint (d := d)
          (osiiStep4CenteredPartialConvolutionKernelFullSource
            d k hrho center y y')) ⊆
      Metric.closedBall center (rho / 4) := by
  intro x hx
  apply
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_support_subset
      (d + 1) k hrho center y y'
  simpa only [Function.mem_support,
    flatten_osiiStep4CenteredPartialConvolutionKernelFullSource] using hx

@[simp]
theorem osiiStep4CenteredPartialConvolutionKernelFullSource_apply
    (d k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → ℝ)
    (x : NPointDomain d k) :
    osiiStep4CenteredPartialConvolutionKernelFullSource
        d k hrho center y y' x =
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG (d + 1) k rho)
        (osiiStep4ComplexOfRealImag
          ((fun a => x (finProdFinEquiv.symm a).1
            (finProdFinEquiv.symm a).2) - center) y) y' := by
  simp [osiiStep4CenteredPartialConvolutionKernelFullSource]
  congr 2

end OSReconstruction
