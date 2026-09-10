/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelFullSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialConvolutionSupport













noncomputable section

open MeasureTheory
open scoped Classical

namespace OSReconstruction

/-- Pointwise product decomposition of the centered flattened source. -/
theorem osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply_eq_prod
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' x : Fin (k * q) -> Real) :
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        q k hrho center y y' x =
      Finset.univ.prod fun i : Fin k =>
        (osiiStep4ComplexBlockPartialConvolutionKernel q rho
          (osiiStep4ComplexOfRealImag
            (fun mu => x (finProdFinEquiv (i, mu)) -
              center (finProdFinEquiv (i, mu)))
            (fun mu => y (finProdFinEquiv (i, mu))))
          (fun mu => y' (finProdFinEquiv (i, mu))) : Complex) := by
  rw [osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply]
  rw [osiiStep4PartialConvolutionKernel_fullBlock_eq_prod]
  push_cast
  apply Finset.prod_congr rfl
  intro i _hi
  congr 2

/-- Source-level ordered expansion at a distinguished block.  The blocks
before `i0`, the two radial factors carrying the shared integration variable,
and the blocks after `i0` are displayed separately.  This is the exact
pointwise identity needed before assigning the shared block to the two OS
Hilbert vectors. -/
theorem
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply_eq_integral_orderedSelectedBlock
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' x : Fin (k * q) -> Real) (i0 : Fin k) :
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        q k hrho center y y' x =
      ((∫ x' : Fin q -> Real,
        ((Finset.Iio i0).prod fun i : Fin k =>
          osiiStep4ComplexBlockPartialConvolutionKernel q rho
            (osiiStep4ComplexOfRealImag
              (fun mu => x (finProdFinEquiv (i, mu)) -
                center (finProdFinEquiv (i, mu)))
              (fun mu => y (finProdFinEquiv (i, mu))))
            (fun mu => y' (finProdFinEquiv (i, mu)))) *
          osiiStep4ComplexBlockPartialConvolutionIntegrand q rho
            (osiiStep4ComplexOfRealImag
              (fun mu => x (finProdFinEquiv (i0, mu)) -
                center (finProdFinEquiv (i0, mu)))
              (fun mu => y (finProdFinEquiv (i0, mu))))
            (fun mu => y' (finProdFinEquiv (i0, mu))) x' *
          ((Finset.Ioi i0).prod fun i : Fin k =>
            osiiStep4ComplexBlockPartialConvolutionKernel q rho
              (osiiStep4ComplexOfRealImag
                (fun mu => x (finProdFinEquiv (i, mu)) -
                  center (finProdFinEquiv (i, mu)))
                (fun mu => y (finProdFinEquiv (i, mu))))
              (fun mu => y' (finProdFinEquiv (i, mu)))) : Real) : Complex) := by
  rw [osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply]
  rw [osiiStep4PartialConvolutionKernel_fullBlock_eq_integral_orderedSelectedBlock]
  congr 1

end OSReconstruction
