/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialLocalMeanValue


















noncomputable section

open Complex MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}

namespace OSIIStep4FullSchwartzAngularContinuationData

/-- Scale-decoupled support-local mean-value identity.  The regularization
radius `sigma` is independent of the larger continuation radius carried by
`D`.  This permits a smaller equation-(6.6) kernel whose complete observed
source support lies strictly inside the established real-edge carrier. -/
theorem
    distributionalPartialConvolutionTransform_meanValue_of_representsOnSupport_atScale
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    {sigma : Real} (hsigma : 0 < sigma)
    (F : (Fin (k * (d + 1)) -> Complex) -> Complex)
    (U : Set (Fin (k * (d + 1)) -> Complex))
    (hrep : D.imaginarySliceFamily.RepresentsOnSupport
      (Metric.closedBall 0 (sigma / 4))
      (Metric.closedBall
        (osiiStep4MultiGapXiHatCenter d k center) (sigma / 4)) F)
    (hF : DifferentiableOn Complex F U)
    (hsupport : forall z,
      z ∈ osiiStep4FullBlockRadialClosedSupport (d + 1) k (3 * sigma) ->
        osiiStep4ComplexOfRealImag
            (osiiStep4MultiGapXiHatCenter d k center) 0 + z ∈ U) :
    F (osiiStep4ComplexOfRealImag
        (osiiStep4MultiGapXiHatCenter d k center) 0) =
      ∫ y' : Fin (k * (d + 1)) -> Real,
        ∫ y : Fin (k * (d + 1)) -> Real,
          osiiStep4DistributionalPartialConvolutionTransform
            D.imaginarySliceFamily hsigma
              (osiiStep4MultiGapXiHatCenter d k center) y y' := by
  let c := osiiStep4ComplexOfRealImag
    (osiiStep4MultiGapXiHatCenter d k center) 0
  have hmean :=
    osiiStep4FullBlockRadialG_partialConvolution_meanValue_local
      (d + 1) k hsigma F c U hF hsupport
  calc
    F c =
        ∫ y' : Fin (k * (d + 1)) -> Real,
          ∫ y : Fin (k * (d + 1)) -> Real,
            osiiStep4PartialConvolutionTransform
              (osiiStep4FullBlockRadialG (d + 1) k sigma) F c y y' :=
      hmean
    _ = ∫ y' : Fin (k * (d + 1)) -> Real,
          ∫ y : Fin (k * (d + 1)) -> Real,
            osiiStep4DistributionalPartialConvolutionTransform
              D.imaginarySliceFamily hsigma
                (osiiStep4MultiGapXiHatCenter d k center) y y' := by
      apply integral_congr_ae
      filter_upwards with y'
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Metric.closedBall
          (0 : Fin (k * (d + 1)) -> Real) (sigma / 4)
      · symm
        apply
          osiiStep4DistributionalPartialConvolutionTransform_eq_partialTransform_of_representsOnSupport
            D.imaginarySliceFamily F
              (Metric.closedBall 0 (sigma / 4))
              (Metric.closedBall
                (osiiStep4MultiGapXiHatCenter d k center) (sigma / 4))
              hrep hsigma
                (osiiStep4MultiGapXiHatCenter d k center) y y' hy
        intro x hx
        apply
          osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_support_subset
            (d + 1) k hsigma
              (osiiStep4MultiGapXiHatCenter d k center) y y'
        simpa only [Function.mem_support,
          flatten_osiiStep4CenteredPartialConvolutionKernelFullSource] using hx
      · have hpoint :=
          osiiStep4PartialConvolutionTransform_eq_zero_of_not_mem_first_closedBall
            (d + 1) k hsigma F c y y' hy
        have hdistribution :=
          osiiStep4DistributionalPartialConvolutionTransform_eq_zero_of_not_mem_first_closedBall
            D.imaginarySliceFamily hsigma
              (osiiStep4MultiGapXiHatCenter d k center) y y' hy
        rw [hpoint, hdistribution]

end OSIIStep4FullSchwartzAngularContinuationData
end OSReconstruction
