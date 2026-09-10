/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIClosedConeDamping
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEuclideanSpacelikeChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISameWitnessWickPair










noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

def osiiFlatEuclideanHolomorphicDomain (d k : Nat) [NeZero d] :
    Set (Fin (k * (d + 1)) -> Complex) :=
  (fun z => BHW.reducedDiffSection (k + 1) d (BHW.unflattenCfg k d z)) ⁻¹'
    osiiEuclideanHolomorphicDomain d k

theorem isOpen_osiiFlatEuclideanHolomorphicDomain :
    IsOpen (osiiFlatEuclideanHolomorphicDomain d k) :=
  isOpen_osiiEuclideanHolomorphicDomain.preimage
    ((BHW.reducedDiffSection (k + 1) d).continuous.comp (flattenCLEquiv k (d + 1)).symm.continuous)

theorem osiiFlatEuclideanHolomorphicDomain_of_mixedSpacelike
    (j : Fin k) (x y : Fin (k * (d + 1)) -> Real)
    (hx : MinkowskiSpace.IsSpacelike d (BHW.unflattenCfgReal k d x j))
    (hy : BHW.unflattenCfgReal k d y j = 0)
    (hother : ∀ l, l ≠ j -> BHW.InOpenForwardCone d (BHW.unflattenCfgReal k d y l)) :
    (fun a => (x a : Complex) + (y a : Complex) * I) ∈ osiiFlatEuclideanHolomorphicDomain d k := by
  have hdiff := BHW.reducedDiffMap_section (k + 1) d
    (BHW.unflattenCfg k d (fun a => (x a : Complex) + (y a : Complex) * I))
  apply osiiEuclideanHolomorphicDomain_of_mixedSpacelike j
  · rw [hdiff]
    simpa [BHW.unflattenCfg, BHW.unflattenCfgReal] using hx
  · intro mu
    rw [hdiff]
    simpa [BHW.unflattenCfg, BHW.unflattenCfgReal] using congrFun hy mu
  · intro l hl
    rw [hdiff]
    simpa [BHW.unflattenCfg, BHW.unflattenCfgReal] using
      (inOpenForwardCone_iff _).mp (hother l hl)

namespace OSIIReducedForwardTubeBoundaryData

variable {W : SchwartzNPoint d k →L[Complex] Complex}
variable {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}

def flatEuclideanHolomorphicKernel (H : OSIIReducedForwardTubeBoundaryData W)
    (z : Fin (k * (d + 1)) -> Complex) : Complex :=
  H.euclideanHolomorphicKernel (BHW.reducedDiffSection (k + 1) d (BHW.unflattenCfg k d z))

theorem flatEuclideanHolomorphicKernel_holomorphic
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H) :
    DifferentiableOn Complex H.flatEuclideanHolomorphicKernel (osiiFlatEuclideanHolomorphicDomain d k) := by
  apply (H.euclideanHolomorphicKernel_holomorphic Hstage Rstage).comp
    ((BHW.reducedDiffSection (k + 1) d).differentiable.comp ?_).differentiableOn
    (Set.mapsTo_preimage _ _)
  exact (flattenCLEquiv k (d + 1)).symm.differentiable

theorem flatEuclideanHolomorphicKernel_eq_of_mem_tube
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    {z : Fin (k * (d + 1)) -> Complex} (hz : z ∈ osiiReducedForwardFlatDomain d k) :
    H.flatEuclideanHolomorphicKernel z = H.kernel (BHW.unflattenCfg k d z) := by
  rw [flatEuclideanHolomorphicKernel,
    H.euclideanHolomorphicKernel_eq_of_reduced_mem Hstage Rstage]
  · rw [BHW.reducedDiffMap_section]
  · rw [BHW.reducedDiffMap_section]
    exact hz

end OSIIReducedForwardTubeBoundaryData

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {OS : OsterwalderSchraderAxioms d}

def strictGeneratedClosedFacePairing
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat)
    (y : Fin (k * (d + 1)) -> Real) (hy : y ∈ closure (osiiReducedForwardFlatCone d k))
    (u : Real) (f : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) : Complex :=
  osiiCanonicalFrequencyDistribution
    (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
    (osiiClosedConeDampedTest (osiiReducedForwardFlatCone d k) y hy (physicsFourierFlatCLM f) u)

theorem strictGeneratedClosedFacePairing_tendsto
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat)
    (y : Fin (k * (d + 1)) -> Real) (hy : y ∈ closure (osiiReducedForwardFlatCone d k))
    (f : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
    Tendsto (fun u => initial.strictGeneratedClosedFacePairing lgc k y hy u f)
      (𝓝[>] (0 : Real))
      (𝓝 ((initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
        (unflattenSchwartzNPoint (d := d) f))) := by
  simpa only [strictGeneratedClosedFacePairing, osiiCanonicalFrequencyDistribution_physicsFourierFlatCLM,
    osiiFlatReducedBoundaryDistribution, ContinuousLinearMap.comp_apply] using
    osiiClosedConeDampedTest_pairing_tendsto (osiiReducedForwardFlatCone d k) y hy
      _ (initial.strictGeneratedFrequency_support lgc k) (physicsFourierFlatCLM f)

theorem strictGeneratedClosedFacePairing_eq_integral
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat)
    (y : Fin (k * (d + 1)) -> Real) (hy : y ∈ closure (osiiReducedForwardFlatCone d k))
    (f : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) (hf : HasCompactSupport (f : _ -> Complex))
    (hmem : ∀ x ∈ tsupport (f : _ -> Complex),
      (fun a => (x a : Complex) + (y a : Complex) * I) ∈ osiiFlatEuclideanHolomorphicDomain d k) :
    initial.strictGeneratedClosedFacePairing lgc k y hy 1 f =
      ∫ x : Fin (k * (d + 1)) -> Real,
        (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).flatEuclideanHolomorphicKernel
          (fun a => (x a : Complex) + (y a : Complex) * I) * f x := by
  obtain ⟨eta, heta⟩ := osiiReducedForwardFlatCone_nonempty (d := d) (m := k)
  apply osiiFourierLaplace_closedFace_eq_integral (osiiReducedForwardFlatCone d k)
    isOpen_osiiReducedForwardFlatCone osiiReducedForwardFlatCone_convex
    osiiReducedForwardFlatCone_isCone osiiReducedForwardFlatCone_salient
    _ (initial.strictGeneratedFrequency_support lgc k) hy heta f hf
    isOpen_osiiFlatEuclideanHolomorphicDomain
    ((initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).flatEuclideanHolomorphicKernel_holomorphic
      (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
      (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc k)).continuousOn ?_ hmem
  intro z hz
  rw [(initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).flatEuclideanHolomorphicKernel_eq_of_mem_tube
    (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
    (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc k) hz,
    toStrictGeneratedForwardTubeBoundaryDataOfOSII_kernel,
    OSIIReducedForwardTubeSpectralData.kernel, BHW.flatten_unflatten_cfg]
  rfl

theorem strictGeneratedClosedFacePairing_eq_integral_of_mixedSpacelike
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) (j : Fin k)
    (y : Fin (k * (d + 1)) -> Real) (hy : y ∈ closure (osiiReducedForwardFlatCone d k))
    (hzero : BHW.unflattenCfgReal k d y j = 0)
    (hother : ∀ l, l ≠ j -> BHW.InOpenForwardCone d (BHW.unflattenCfgReal k d y l))
    (f : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) (hf : HasCompactSupport (f : _ -> Complex))
    (hsupport : ∀ x ∈ tsupport (f : _ -> Complex),
      MinkowskiSpace.IsSpacelike d (BHW.unflattenCfgReal k d x j)) :
    initial.strictGeneratedClosedFacePairing lgc k y hy 1 f =
      ∫ x : Fin (k * (d + 1)) -> Real,
        (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).flatEuclideanHolomorphicKernel
          (fun a => (x a : Complex) + (y a : Complex) * I) * f x :=
  initial.strictGeneratedClosedFacePairing_eq_integral lgc k y hy f hf
    (fun x hx => osiiFlatEuclideanHolomorphicDomain_of_mixedSpacelike j x y (hsupport x hx) hzero hother)

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
