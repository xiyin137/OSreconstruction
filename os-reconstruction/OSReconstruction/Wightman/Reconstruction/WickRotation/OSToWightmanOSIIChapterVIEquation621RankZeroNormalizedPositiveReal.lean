/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation629Majorant
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarPhysicalCharts
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIWeightedReflectedRankFieldIdentification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorGeneratorBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621Recovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformEquation621Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeBoundedRankInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorAdaptiveShiftHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SourceCoefficientSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open OSIITimeContinuationLadderRealEdgeDensityGrowthData

/-- Every retained recursive-sector stage inherits the normalized VI.1
positive-real edge with the same epsilon-independent coefficient. -/
noncomputable def recursiveSectorRankNormalizedPositiveRealWeightedEdgeData
    {d : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS)
    (E : OSIIEquation621UniformPositiveRealSeedData D lgc)
    (depth rank arity : Nat)
    (harity : 0 < arity)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    OSIIEquation621WeightedPositiveRealEdgeData
      ((((D.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
          lgc depth).recursiveSectorRankInduction lgc rank).pointed.stageLevel.stage
            arity).vi2Equation621NormalizedStage E.exponent epsilon)
      (arity * E.exponent) := by
  let D0 := D.toStrictGeneratedScalarDepthZeroPointedData
  let current :=
    ((D0.depthInduction lgc depth).recursiveSectorRankInduction lgc rank
      ).pointed.stageLevel.stage arity
  let seed := E.normalizedPositiveRealWeightedEdgeData arity harity hepsilon
  refine {
    density := seed.density
    represents := ?_
    constant := seed.constant
    constant_nonneg := seed.constant_nonneg
    bound := seed.bound }
  intro tau chi
  have hshiftedPositive :
      tau.1 + (fun _ => epsilon) ∈
        section43TimeStrictPositiveRegion arity := by
    intro i
    change 0 < tau.1 i + epsilon
    exact add_pos (tau.2 i) hepsilon
  have hcurrent :=
    D0.recursiveSectorRankInduction_distribution_eq_depthZero_of_positiveReal
      lgc depth rank arity
      (tau.1 + fun _ => epsilon) hshiftedPositive
  have hz0 :
      osiiPositiveRealTimeEmbed (tau.1 + fun _ => epsilon) ∈
        (D0.pointed.stageLevel.stage arity).carrier :=
    (D0.pointed.canonicalEdges arity).positiveReal_mem_carrier
      (tau.1 + fun _ => epsilon) hshiftedPositive
  have hfull := D0.toFullTimeContinuationStage_extends_depth
    lgc arity 0 hz0
  have hraw :
      current.distribution
          (osiiPositiveRealTimeEmbed (tau.1 + fun _ => epsilon)) =
        (D.toStrictGeneratedTimeContinuationLadder lgc arity
          ).toFullTimeContinuationStage.distribution
            (osiiPositiveRealTimeEmbed (tau.1 + fun _ => epsilon)) := by
    exact hcurrent.trans hfull.symm
  have hshift :
      osiiVI2Shift arity epsilon (osiiPositiveRealTimeEmbed tau.1) =
        osiiPositiveRealTimeEmbed (tau.1 + fun _ => epsilon) := by
    ext i
    simp [osiiVI2Shift, osiiPositiveRealTimeEmbed]
  calc
    (current.vi2Equation621NormalizedStage E.exponent epsilon
        ).distribution (osiiPositiveRealTimeEmbed tau.1) chi =
      osiiVI2Equation621Normalization E.exponent arity epsilon
          (osiiPositiveRealTimeEmbed tau.1) *
        current.distribution
          (osiiVI2Shift arity epsilon
            (osiiPositiveRealTimeEmbed tau.1)) chi := by
      rw [OSIITimeContinuationStage.vi2Equation621NormalizedStage_distribution_apply]
    _ = osiiVI2Equation621Normalization E.exponent arity epsilon
          (osiiPositiveRealTimeEmbed tau.1) *
        current.distribution
          (osiiPositiveRealTimeEmbed (tau.1 + fun _ => epsilon)) chi := by
      rw [hshift]
    _ = osiiVI2Equation621Normalization E.exponent arity epsilon
          (osiiPositiveRealTimeEmbed tau.1) *
        (D.toStrictGeneratedTimeContinuationLadder lgc arity
          ).toFullTimeContinuationStage.distribution
            (osiiPositiveRealTimeEmbed (tau.1 + fun _ => epsilon)) chi := by
      rw [hraw]
    _ = ((D.toStrictGeneratedTimeContinuationLadder lgc arity
          ).toFullTimeContinuationStage.vi2Equation621NormalizedStage
            E.exponent epsilon).distribution
          (osiiPositiveRealTimeEmbed tau.1) chi := by
      rw [OSIITimeContinuationStage.vi2Equation621NormalizedStage_distribution_apply]
      rw [hshift]
    _ = ∫ x : Fin (arity * d) -> Real,
        OSIISpatialPolynomialGrowthFunction.value (seed.density tau) x *
          (section43SpatialFlatSchwartzCLE d arity chi) x :=
      seed.represents tau chi

namespace ReflectedGramSpatialSourceData

end ReflectedGramSpatialSourceData

namespace VI2Equation621ReflectedSourcePointCoverageData

end VI2Equation621ReflectedSourcePointCoverageData

namespace RecursiveSectorRankZeroPositiveRealSourcePairEnvelopeData

end RecursiveSectorRankZeroPositiveRealSourcePairEnvelopeData

end OSIIChapterV
end OSReconstruction
