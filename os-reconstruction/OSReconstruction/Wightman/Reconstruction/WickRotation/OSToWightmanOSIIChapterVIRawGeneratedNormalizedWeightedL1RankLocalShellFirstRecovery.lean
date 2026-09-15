/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedSafeCenteredRadialChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1RankLocalSourceContract
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedRootedSourceCarrier
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedL1RankSuccessorFlatProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SourceIntegralSegment
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorAdaptiveShiftHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedProductFactorization












noncomputable section

open Complex Set Filter Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedTargetHubPointedDirectExtensionData
namespace SpatialApproximationRowsFactorizationData

theorem norm_distribution_le_weightedL1_mul_of_lowerBounds
    {d k a b depth pLeft pRight pTarget beta M : Nat}
    [NeZero d] [NeZero k] [Nonempty (Fin (k * d))]
    {OS : OsterwalderSchraderAxioms d}
    {Stage : Type*} [CanonicalGeneratorStageLevelProvider OS Stage]
    {S : Stage}
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
    {alpha dLeft dRight dTarget : Real}
    (R : SpatialApproximationRowsFactorizationData D targetProbe w
      leftDistribution rightDistribution leftProbe rightProbe split)
    (halpha : 0 <= alpha)
    (hdLeft : 0 <= dLeft) (hdRight : 0 <= dRight)
    (hleft : forall chi : SchwartzMap (Section43SpatialSpace d a) Complex,
      ‖leftDistribution chi‖ <=
        dLeft * (osiiVI2ArityDepthMajorant alpha beta a M *
          osiiSpatialPolynomialWeightedL1 pLeft
            (section43SpatialFlatSchwartzCLE d a chi)))
    (hright : forall chi : SchwartzMap (Section43SpatialSpace d b) Complex,
      ‖rightDistribution chi‖ <=
        dRight * (osiiVI2ArityDepthMajorant alpha beta b M *
          osiiSpatialPolynomialWeightedL1 pRight
            (section43SpatialFlatSchwartzCLE d b chi)))
    (hdenormalization : Real.sqrt (dLeft * dRight) <= dTarget)
    (hpAverage : pLeft + pRight <= 2 * pTarget)
    (hab : a + b = 2 * k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖D.extension.toTimeContinuationStage.distribution w chi‖ <=
      (osiiVI2ArityDepthMajorant alpha beta k (M + 1) *
        osiiSpatialPolynomialWeightedL1 pTarget
          (section43SpatialFlatSchwartzCLE d k chi)) * dTarget := by
  let Bleft := osiiVI2ArityDepthMajorant alpha beta a M
  let Bright := osiiVI2ArityDepthMajorant alpha beta b M
  let Btarget := osiiVI2ArityDepthMajorant alpha beta k (M + 1)
  let cLeft : Nat -> Real := fun N => (1 + |leftProbe.radius N|) ^ pLeft
  let cRight : Nat -> Real := fun N => (1 + |rightProbe.radius N|) ^ pRight
  let coefficient : Nat -> Real := fun N =>
    Btarget * dTarget * Real.sqrt (cLeft N * cRight N)
  have hcoefficient : Tendsto coefficient atTop (nhds (Btarget * dTarget)) := by
    have hleftCoefficient : Tendsto cLeft atTop (nhds 1) := by
      simpa [cLeft] using
        leftProbe.tendsto_radiusPolynomialCoefficient_one (p := pLeft)
    have hrightCoefficient : Tendsto cRight atTop (nhds 1) := by
      simpa [cRight] using
        rightProbe.tendsto_radiusPolynomialCoefficient_one (p := pRight)
    have hproduct : Tendsto (fun N => cLeft N * cRight N) atTop (nhds 1) := by
      simpa using hleftCoefficient.mul hrightCoefficient
    have hsqrt : Tendsto (fun N => Real.sqrt (cLeft N * cRight N))
        atTop (nhds 1) := by
      simpa [Function.comp_def] using
        (Real.continuous_sqrt.tendsto 1).comp hproduct
    simpa [coefficient] using tendsto_const_nhds.mul hsqrt
  have hbound : forall N x,
      ‖targetProbe.smoothedStageValue
          D.extension.toTimeContinuationStage N w x‖ <=
        coefficient N * osiiSpatialPolynomialWeight pTarget x := by
    intro N x
    let wLeft := osiiSpatialPolynomialWeight pLeft (split.leftPoint x)
    let wRight := osiiSpatialPolynomialWeight pRight (split.rightPoint x)
    have hBleft : 0 <= Bleft :=
      osiiVI2ArityDepthMajorant_nonneg halpha beta a M
    have hBright : 0 <= Bright :=
      osiiVI2ArityDepthMajorant_nonneg halpha beta b M
    have hBtarget : 0 <= Btarget :=
      osiiVI2ArityDepthMajorant_nonneg halpha beta k (M + 1)
    have hcLeft : 0 <= cLeft N := by positivity
    have hcRight : 0 <= cRight N := by positivity
    have hwLeft : 0 <= wLeft :=
      (osiiSpatialPolynomialWeight_pos (split.leftPoint x)).le
    have hwRight : 0 <= wRight :=
      (osiiSpatialPolynomialWeight_pos (split.rightPoint x)).le
    have hleftProbe :
        ‖leftDistribution
            (leftProbe.section43Probe (split.leftPoint x) N)‖ <=
          dLeft * (Bleft * (cLeft N * wLeft)) := by
      calc
        ‖leftDistribution
            (leftProbe.section43Probe (split.leftPoint x) N)‖ <=
            dLeft * (Bleft * osiiSpatialPolynomialWeightedL1 pLeft
              (section43SpatialFlatSchwartzCLE d a
                (leftProbe.section43Probe (split.leftPoint x) N))) :=
          hleft _
        _ <= dLeft * (Bleft * (cLeft N * wLeft)) := by
          apply mul_le_mul_of_nonneg_left _ hdLeft
          apply mul_le_mul_of_nonneg_left _ hBleft
          simpa [cLeft, wLeft] using
            leftProbe.weightedL1_section43Probe_le_radius
              (p := pLeft) N (split.leftPoint x)
    have hrightProbe :
        ‖rightDistribution
            (rightProbe.section43Probe (split.rightPoint x) N)‖ <=
          dRight * (Bright * (cRight N * wRight)) := by
      calc
        ‖rightDistribution
            (rightProbe.section43Probe (split.rightPoint x) N)‖ <=
            dRight * (Bright * osiiSpatialPolynomialWeightedL1 pRight
              (section43SpatialFlatSchwartzCLE d b
                (rightProbe.section43Probe (split.rightPoint x) N))) :=
          hright _
        _ <= dRight * (Bright * (cRight N * wRight)) := by
          apply mul_le_mul_of_nonneg_left _ hdRight
          apply mul_le_mul_of_nonneg_left _ hBright
          simpa [cRight, wRight] using
            rightProbe.weightedL1_section43Probe_le_radius
              (p := pRight) N (split.rightPoint x)
    have hproduct :
        ‖leftDistribution
            (leftProbe.section43Probe (split.leftPoint x) N)‖ *
          ‖rightDistribution
            (rightProbe.section43Probe (split.rightPoint x) N)‖ <=
        (dLeft * (Bleft * (cLeft N * wLeft))) *
          (dRight * (Bright * (cRight N * wRight))) := by
      exact mul_le_mul hleftProbe hrightProbe (norm_nonneg _)
        (mul_nonneg hdLeft (mul_nonneg hBleft (mul_nonneg hcLeft hwLeft)))
    have hmajorant : Real.sqrt (Bleft * Bright) <= Btarget := by
      simpa [Bleft, Bright, Btarget] using
        osiiVI2ArityDepthMajorant_split_sqrt_le alpha halpha beta k M a b
          (Nat.pos_of_ne_zero (NeZero.ne k)) hab
    have hweight : Real.sqrt (wLeft * wRight) <=
        osiiSpatialPolynomialWeight pTarget x := by
      simpa [wLeft, wRight] using
        split.sqrt_mul_weight_le_of_add_le_two_mul hpAverage x
    have hdTarget : 0 <= dTarget :=
      (Real.sqrt_nonneg _).trans hdenormalization
    calc
      ‖targetProbe.smoothedStageValue
          D.extension.toTimeContinuationStage N w x‖ <=
          Real.sqrt
            (‖leftDistribution
                (leftProbe.section43Probe (split.leftPoint x) N)‖ *
              ‖rightDistribution
                (rightProbe.section43Probe (split.rightPoint x) N)‖) :=
        R.norm_smoothedStageValue_le_sqrt_mul N x
      _ <= Real.sqrt
          ((dLeft * (Bleft * (cLeft N * wLeft))) *
            (dRight * (Bright * (cRight N * wRight)))) :=
        Real.sqrt_le_sqrt hproduct
      _ = Real.sqrt (dLeft * dRight) *
          Real.sqrt (Bleft * Bright) *
          Real.sqrt (cLeft N * cRight N) *
          Real.sqrt (wLeft * wRight) := by
        rw [show
          (dLeft * (Bleft * (cLeft N * wLeft))) *
              (dRight * (Bright * (cRight N * wRight))) =
            (dLeft * dRight) * ((Bleft * Bright) *
              ((cLeft N * cRight N) * (wLeft * wRight))) by ring]
        rw [Real.sqrt_mul (mul_nonneg hdLeft hdRight),
          Real.sqrt_mul (mul_nonneg hBleft hBright),
          Real.sqrt_mul (mul_nonneg hcLeft hcRight)]
        ring
      _ <= dTarget * Btarget *
          Real.sqrt (cLeft N * cRight N) *
          osiiSpatialPolynomialWeight pTarget x := by
        gcongr
      _ = coefficient N * osiiSpatialPolynomialWeight pTarget x := by
        dsimp [coefficient]
        ring
  have hflat :=
    targetProbe.norm_flatDistribution_le_weightedL1_of_smoothedStageValue_tendsto_bound
      D.extension.toTimeContinuationStage w coefficient (Btarget * dTarget)
      hcoefficient hbound (section43SpatialFlatSchwartzCLE d k chi)
  simpa [OSIIEquation621WeightedDensityAtlasData.flatDistribution,
    Btarget, mul_assoc, mul_left_comm, mul_comm] using hflat

end SpatialApproximationRowsFactorizationData
end RootedTargetHubPointedDirectExtensionData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
