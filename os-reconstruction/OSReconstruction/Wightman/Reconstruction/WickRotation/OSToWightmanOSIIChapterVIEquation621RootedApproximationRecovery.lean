/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation629Majorant
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarPhysicalCharts










noncomputable section

open Complex Filter Set
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedTargetHubPointedDirectExtensionData

/-- Point-local shell rows for a rooted target and two lower spatial
distributions.  This is deliberately independent of a represented density
on the target.  The target row is the approximation already retained by the
rooted extension; only the two diagonal rows and their identifications with
lower-stage probe evaluations remain constructor-specific. -/
structure SpatialApproximationRowsFactorizationData
    {d k a b depth : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k}
    {hub : Fin k -> Real}
    {targetPoint : OSIITimeGapSpace k}
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    (D : RootedTargetHubPointedDirectExtensionData
      S depth P lgc i hub targetPoint atlas)
    (targetProbe : OSIIEquation621SpatialApproxIdentityData (k * d))
    (w : OSIITimeGapSpace k)
    (leftDistribution : OSIISpatialDistribution d a)
    (rightDistribution : OSIISpatialDistribution d b)
    (leftProbe : OSIIEquation621SpatialApproxIdentityData (a * d))
    (rightProbe : OSIIEquation621SpatialApproxIdentityData (b * d))
    (split : OSIIEquation621SpatialSplitData d k a b) where
  targetApprox : (Fin (k * d) -> Real) -> Nat -> Nat -> Complex
  leftApprox : (Fin (k * d) -> Real) -> Nat -> Nat -> Complex
  rightApprox : (Fin (k * d) -> Real) -> Nat -> Nat -> Complex
  target_row_tendsto : forall x N,
    Tendsto (targetApprox x N) atTop
      (nhds (targetProbe.smoothedStageValue
        D.extension.toTimeContinuationStage N w x))
  left_row_tendsto : forall x N,
    Tendsto (leftApprox x N) atTop
      (nhds (leftDistribution
        (leftProbe.section43Probe (split.leftPoint x) N)))
  right_row_tendsto : forall x N,
    Tendsto (rightApprox x N) atTop
      (nhds (rightDistribution
        (rightProbe.section43Probe (split.rightPoint x) N)))
  eventually_bound : forall x N, ∀ᶠ scale : Nat in atTop,
    ‖targetApprox x N scale‖ <=
      Real.sqrt
        (‖leftApprox x N scale‖ * ‖rightApprox x N scale‖)

namespace SpatialApproximationRowsFactorizationData

variable
    {d k a b depth : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k}
    {hub : Fin k -> Real}
    {targetPoint : OSIITimeGapSpace k}
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {D : RootedTargetHubPointedDirectExtensionData
      S depth P lgc i hub targetPoint atlas}
    {targetProbe : OSIIEquation621SpatialApproxIdentityData (k * d)}
    {w : OSIITimeGapSpace k}
    {leftDistribution : OSIISpatialDistribution d a}
    {rightDistribution : OSIISpatialDistribution d b}
    {leftProbe : OSIIEquation621SpatialApproxIdentityData (a * d)}
    {rightProbe : OSIIEquation621SpatialApproxIdentityData (b * d)}
    {split : OSIIEquation621SpatialSplitData d k a b}

/-- After the shell limit, the target smoothing is bounded by the geometric
mean of the two exact lower spatial convolutions. -/
theorem norm_smoothedStageValue_le_sqrt_mul
    (R : SpatialApproximationRowsFactorizationData D targetProbe w
      leftDistribution rightDistribution leftProbe rightProbe split)
    (N : Nat) (x : Fin (k * d) -> Real) :
    ‖targetProbe.smoothedStageValue
        D.extension.toTimeContinuationStage N w x‖ <=
      Real.sqrt
        (‖leftDistribution
            (leftProbe.section43Probe (split.leftPoint x) N)‖ *
          ‖rightDistribution
            (rightProbe.section43Probe (split.rightPoint x) N)‖) :=
  OSIISpatialPolynomialGrowthFunction.norm_le_sqrt_mul_of_tendsto
    (R.targetApprox x N) (R.leftApprox x N) (R.rightApprox x N)
    (targetProbe.smoothedStageValue
      D.extension.toTimeContinuationStage N w x)
    (leftDistribution
      (leftProbe.section43Probe (split.leftPoint x) N))
    (rightDistribution
      (rightProbe.section43Probe (split.rightPoint x) N))
    (R.target_row_tendsto x N)
    (R.left_row_tendsto x N) (R.right_row_tendsto x N)
    (R.eventually_bound x N)

end SpatialApproximationRowsFactorizationData

end RootedTargetHubPointedDirectExtensionData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
