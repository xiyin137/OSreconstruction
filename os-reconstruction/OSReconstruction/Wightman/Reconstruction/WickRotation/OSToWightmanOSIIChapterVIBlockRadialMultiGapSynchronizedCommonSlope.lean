/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialDistributionOrbit
public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetCutoffHullRankField
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetRankField
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceAdapter
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAnchoredAtlas
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicGeneratorDomains
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRealEdge
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBranchGeometry
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTranslation
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedRootedSuccessor
public import OSReconstruction.SCV.TotallyRealIdentity
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitRankGenerator
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedTarget
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceComparison
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDifferenceReducedSupport
public import OSReconstruction.Wightman.Reconstruction.DenseCLM
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceDistribution
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialCoherentTarget
public import OSReconstruction.SCV.SchwartzFiniteSeminormBound
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapTargetGeometry
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]

/-- One common slope for the uniform selected-block packet family and the
sourcewise chronological localization. -/
structure OSIIStep4SynchronizedMultiGapContinuationData
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) where
  uniform : OSIIStep4MultiGapUniformCommonSlopeData
    d k hrho center hcenter
  coherent : OSIIChronologicalCompactLocalizationContinuationData d k
    (osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
      d k rho center)
  slope_eq : coherent.T = uniform.T

namespace OSIIChronologicalCompactLocalizationContinuationData

end OSIIChronologicalCompactLocalizationContinuationData

namespace OSIIStep4SynchronizedMultiGapContinuationData

variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}

/-- The synchronized coherent pairing has the direct centered Schwinger edge
at every smaller radial scale.  The smaller lifted source remains supported
in the original coherent carrier. -/
theorem coherentPairing_centeredPartialKernel_realEdge_atScale
    (hcenterFull : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenterFull))
    {sigma : Real} (hsigma : 0 < sigma) (hscale : sigma <= rho)
    (hcenterSigma : forall i : Fin k,
      sigma / 2 <=
        osiiStep4MultiGapXiHatCenter d k center
          (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (y y' : Fin (k * (d + 1)) -> Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    Z.coherent.pairing OS lgc
        (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
          d k hsigma (osiiStep4MultiGapXiHatCenter d k center) y y')
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      osiiStep4FixedRadiusCenteredSchwinger d OS k hsigma
        (osiiStep4MultiGapXiHatCenter d k center +
          osiiStep4AxisPairGapTranslationFlat d Z.coherent.T x) y y'
        (osiiStep4MultiGapTranslatedCenter_time_lower
          d k (osiiStep4MultiGapXiHatCenter d k center)
            hcenterSigma Z.coherent.T Z.coherent.hT x) := by
  let f := osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
    d k hsigma (osiiStep4MultiGapXiHatCenter d k center) y y'
  have hsupport :
      tsupport (f : NPointDomain d (k + 1) -> Complex) ⊆
        osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
          d k rho (osiiStep4MultiGapXiHatCenter d k center) :=
    (osiiStep4PositiveLiftedCenteredPartialConvolutionKernel_tsupport_subset_commonCarrier
      d k hsigma (osiiStep4MultiGapXiHatCenter d k center) y y').trans
        (osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_mono
          d k hscale (osiiStep4MultiGapXiHatCenter d k center))
  change
    Z.coherent.pairing OS lgc f
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      OS.S (k + 1)
        (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelZeroDiagonal
          d k hsigma
            (osiiStep4MultiGapXiHatCenter d k center +
              osiiStep4AxisPairGapTranslationFlat d Z.coherent.T x) y y'
            (osiiStep4MultiGapTranslatedCenter_time_lower
              d k (osiiStep4MultiGapXiHatCenter d k center)
                hcenterSigma Z.coherent.T Z.coherent.hT x))
  rw [Z.coherent.pairing_realEdge OS lgc x f]
  apply congrArg (OS.S (k + 1))
  apply Subtype.ext
  change
    (Z.coherent.localizedTranslatedZeroSum x f).1 =
      osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
        d k hsigma
          (osiiStep4MultiGapXiHatCenter d k center +
            osiiStep4AxisPairGapTranslationFlat d Z.coherent.T x) y y'
  rw [Z.coherent.localizedTranslatedZeroSum_coe x f hsupport]
  exact
    translateConfiguration_positiveLiftedCenteredPartialKernel_axisPairGaps
      d k hsigma (osiiStep4MultiGapXiHatCenter d k center)
        y y' Z.coherent.T x

/-- At every smaller radial scale, any holomorphic branch with the direct
centered-Schwinger real edge is the synchronized coherent full-source pairing
on the complete first multi-gap carrier. -/
theorem holomorphicCenteredSchwingerExtension_eq_coherentPairing_atScale
    (hcenterFull : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenterFull))
    {sigma : Real} (hsigma : 0 < sigma) (hscale : sigma <= rho)
    (hcenterSigma : forall i : Fin k,
      sigma / 2 <=
        osiiStep4MultiGapXiHatCenter d k center
          (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (y y' : Fin (k * (d + 1)) -> Real)
    (Gamma : (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex)
    (hGamma : DifferentiableOn Complex Gamma
      (osiiAxisPairMultiGapLogDomain d k))
    (hreal : forall x : Fin k -> osiiAxisPairIndex d -> Real,
      Gamma (osiiAxisPairSimultaneousLogRealEmbed x) =
        osiiStep4FixedRadiusCenteredSchwinger d OS k hsigma
          (osiiStep4MultiGapXiHatCenter d k center +
            osiiStep4AxisPairGapTranslationFlat d Z.coherent.T x) y y'
          (osiiStep4MultiGapTranslatedCenter_time_lower
            d k (osiiStep4MultiGapXiHatCenter d k center)
              hcenterSigma Z.coherent.T Z.coherent.hT x)) :
    Set.EqOn Gamma
      (fun z => Z.coherent.pairing OS lgc
        (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
          d k hsigma (osiiStep4MultiGapXiHatCenter d k center) y y') z)
      (osiiAxisPairMultiGapLogDomain d k) := by
  let f := osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
    d k hsigma (osiiStep4MultiGapXiHatCenter d k center) y y'
  apply SCV.holomorphic_eq_of_eq_on_real_of_connected_finite_product
    isOpen_osiiAxisPairMultiGapLogDomain
    isConnected_osiiAxisPairMultiGapLogDomain
    hGamma (Z.coherent.pairing_differentiableOn OS lgc f)
    (x₀ := fun _ _ => 0)
    (osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap (fun _ _ => 0))
  intro x _hx
  change Gamma (osiiAxisPairSimultaneousLogRealEmbed x) =
    Z.coherent.pairing OS lgc f
      (osiiAxisPairSimultaneousLogRealEmbed x)
  rw [hreal x]
  rw [coherentPairing_centeredPartialKernel_realEdge_atScale
    hcenterFull Z hsigma hscale hcenterSigma y y' x]

end OSIIStep4SynchronizedMultiGapContinuationData

namespace OSIIStep4MultiGapUniformCommonSlopeData
namespace FixedAxisAllSplitCutoffHullMZCrossData

variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}

end FixedAxisAllSplitCutoffHullMZCrossData
end OSIIStep4MultiGapUniformCommonSlopeData

end OSReconstruction
