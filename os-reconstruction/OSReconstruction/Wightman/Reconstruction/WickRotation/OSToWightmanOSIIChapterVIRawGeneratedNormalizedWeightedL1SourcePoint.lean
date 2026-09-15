/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Basic
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPhysicalTestDistribution
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPhysicalLocalTestPartition
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialReducedFlatWickCovariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTestLiftRepresentative
import OSReconstruction.SCV.DistributionalEOWSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIA0LocalSchwinger
import OSReconstruction.SCV.LocalEOWPairingCLM
import OSReconstruction.SCV.LocalProductRecovery
import OSReconstruction.SCV.DistributionalRepresentationUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43WickRotateFourierLaplaceBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRawGeneratedReflectedDiagonalCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRawGeneratedPointedDepthHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedEndpointRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621EndpointProbeRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedTwoPointRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RankZeroNormalizedPositiveReal













noncomputable section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- Every raw logarithmic argument at outer depth zero is the origin.  The
generator is the only depth-raising constructor in the raw recurrence. -/
theorem rawStrictGeneratedArgument_eq_zero_of_depth_zero
    {kind : OSIILogarithmicArgumentKind}
    {n : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n 0 x) :
    x = 0 := by
  generalize hN : (0 : Nat) = N at hx
  induction hx with
  | scalarZero =>
      rfl
  | initialMixedZero =>
      rfl
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      rw [ihx hN, ihy hN, smul_zero, smul_zero, add_zero]
  | mixedHyperrectangle hx y hy ih =>
      funext i
      have hbound : |y i| <= 0 := by
        simpa [ih hN] using hy i
      exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  | generatorMemSucc =>
      omega
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      funext i
      let j : Fin (2 * n - 1) :=
        ⟨n - 1 + i.val, by omega⟩
      have hj := congrFun (ih hN) j
      simpa [j, osiiArgumentDiagonal] using hj

/-- The physical raw scalar carrier at outer depth zero is the complete
strict positive-real edge. -/
theorem exists_positiveReal_eq_of_mem_rawStrictGenerated_scalar_depthZero
    {k : Nat} {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase k 0)) :
    ∃ x : Fin k -> Real,
      x ∈ section43TimeStrictPositiveRegion k ∧
      z = osiiPositiveRealTimeEmbed x := by
  have harg : osiiTimeArgumentVector z = 0 :=
    rawStrictGeneratedArgument_eq_zero_of_depth_zero hz.2
  let x : Fin k -> Real := fun i => (z i).re
  refine ⟨x, re_mem_strictPositive_of_mem_rightHalfPlane hz.1, ?_⟩
  exact eq_positiveRealTimeEmbed_re_of_argumentVector_eq_zero harg

/-- Complete-normalized weighted-L1 control on the raw scalar carrier at one
fixed outer depth.

The coefficient is selected before arity and source point.  Inverting this
state later restores the one full denormalization factor required by the
first-bridge source contract. -/
structure RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS)
    (t beta depth : Nat) where
  alpha : Real
  alpha_nonneg : 0 <= alpha
  pointBound : forall {arity : Nat} [NeZero arity]
    {epsilon : Real}, 0 < epsilon -> forall zeta,
    zeta ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase arity depth) ->
    OSIIEquation621WeightedL1PointBoundData
      ((((D.toStrictGeneratedTimeContinuationLadder lgc arity).stage depth
        ).vi2Equation621TotalNormalizedStage t epsilon).distribution zeta)
      (arity * t) alpha beta depth

namespace RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData

/-- Invert one complete-normalized raw point at its VI.2 shift.  The result
keeps exactly one complete denormalization factor, rather than replacing it
by a uniform raw bound. -/
theorem norm_rawShiftedDistribution_le_mul_denormalization
    {D : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {t beta depth : Nat}
    (P : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      D lgc t beta depth)
    {arity : Nat} [NeZero arity]
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {zeta : OSIITimeGapSpace arity}
    (hzeta : zeta ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase arity depth))
    (chi : SchwartzMap (Section43SpatialSpace d arity) Complex) :
    ‖((D.toStrictGeneratedTimeContinuationLadder lgc arity).stage depth
        ).distribution (osiiVI2Shift arity epsilon zeta) chi‖ <=
      ‖osiiVI2Equation621Denormalization t arity epsilon
          (osiiVI2Shift arity epsilon zeta)‖ *
        (osiiVI2ArityDepthMajorant P.alpha beta arity depth *
          osiiSpatialPolynomialWeightedL1 (arity * t)
            (section43SpatialFlatSchwartzCLE d arity chi)) := by
  let A := (D.toStrictGeneratedTimeContinuationLadder lgc arity).stage depth
  have harity : 0 < arity := Nat.pos_of_ne_zero (NeZero.ne arity)
  have hshiftRight :
      osiiVI2Shift arity epsilon zeta ∈ osiiTimeRightHalfPlane arity := by
    intro i
    change 0 < (zeta i).re + epsilon
    exact add_pos (hzeta.1 i) hepsilon
  have hnormalized := P.pointBound hepsilon zeta hzeta
  rw [A.vi2Equation621TotalNormalizedStage_eq_of_pos harity] at hnormalized
  have hbound :
      ‖(A.vi2Equation621NormalizedStage t epsilon).distribution
          (osiiVI2Unshift arity epsilon
            (osiiVI2Shift arity epsilon zeta)) chi‖ <=
        osiiVI2ArityDepthMajorant P.alpha beta arity depth *
          osiiSpatialPolynomialWeightedL1 (arity * t)
            (section43SpatialFlatSchwartzCLE d arity chi) := by
    simpa [A] using hnormalized.norm_distribution_le chi
  exact A.norm_distribution_le_of_equation621Normalized
    harity t hepsilon hshiftRight chi _ hbound

end RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData

/-- Corrected arity-linear E0' supplies the complete-normalized weighted-L1
base state, with one coefficient fixed before arity. -/
noncomputable def rawStrictGeneratedVI2NormalizedWeightedL1DepthZeroBoundData
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      D lgc
        (D.toEquation621UniformPositiveRealSeedData lgc).exponent
        (osiiEquation621CanonicalSeedArityRate lgc) 0 where
  alpha := osiiEquation621CanonicalSeedArityConstant lgc
  alpha_nonneg := osiiEquation621CanonicalSeedArityConstant_nonneg lgc
  pointBound := by
    intro arity _ epsilon hepsilon zeta hzeta
    let E := D.toEquation621UniformPositiveRealSeedData lgc
    have harity : 0 < arity :=
      Nat.pos_of_ne_zero (NeZero.ne arity)
    obtain ⟨tau, htau, rfl⟩ :=
      exists_positiveReal_eq_of_mem_rawStrictGenerated_scalar_depthZero hzeta
    let edge :=
      recursiveSectorRankNormalizedPositiveRealWeightedEdgeData
        D lgc E 0 0 arity harity hepsilon
    let current :=
      (((D.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
          lgc 0).recursiveSectorRankInduction lgc 0).pointed.stageLevel.stage
        arity)
    have hedge := edge.norm_distribution_le_weightedL1
      ⟨tau, htau⟩
    have hedgeConstant :
        edge.constant =
          E.normalizedPositiveRealWeightedCoefficient arity := by
      rw [OSReconstruction.OSIIEquation621UniformPositiveRealSeedData.normalizedPositiveRealWeightedCoefficient,
        dif_pos harity]
      rfl
    have hcoefficient :
        ‖edge.density ⟨tau, htau⟩‖ <=
          E.normalizedPositiveRealWeightedCoefficient arity := by
      rw [← hedgeConstant]
      exact edge.bound ⟨tau, htau⟩
    have hmajorant :
        E.normalizedPositiveRealWeightedCoefficient arity <=
          osiiVI2ArityDepthMajorant
            (osiiEquation621CanonicalSeedArityConstant lgc)
            (osiiEquation621CanonicalSeedArityRate lgc) arity 0 := by
      simpa [E, osiiVI2ArityDepthMajorant, osiiVI2DepthFactor,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        OSReconstruction.OSIIEquation621UniformPositiveRealSeedData.canonical_normalizedPositiveRealWeightedCoefficient_le_arityMajorant
          D lgc arity harity
    refine {
      alpha_nonneg := osiiEquation621CanonicalSeedArityConstant_nonneg lgc
      norm_distribution_le := ?_ }
    intro chi
    have hL1 :
        0 <= osiiSpatialPolynomialWeightedL1
          (arity * E.exponent)
          (section43SpatialFlatSchwartzCLE d arity chi) :=
      osiiSpatialPolynomialWeightedL1_nonneg _
    have hbound :
        ‖(current.vi2Equation621NormalizedStage E.exponent epsilon).distribution
            (osiiPositiveRealTimeEmbed tau) chi‖ <=
          osiiVI2ArityDepthMajorant
              (osiiEquation621CanonicalSeedArityConstant lgc)
              (osiiEquation621CanonicalSeedArityRate lgc) arity 0 *
            osiiSpatialPolynomialWeightedL1
              (arity * E.exponent)
              (section43SpatialFlatSchwartzCLE d arity chi) := by
      calc
        ‖(current.vi2Equation621NormalizedStage E.exponent epsilon).distribution
            (osiiPositiveRealTimeEmbed tau) chi‖ <=
            ‖edge.density ⟨tau, htau⟩‖ *
              osiiSpatialPolynomialWeightedL1
                (arity * E.exponent)
                (section43SpatialFlatSchwartzCLE d arity chi) :=
          hedge chi
        _ <= E.normalizedPositiveRealWeightedCoefficient arity *
              osiiSpatialPolynomialWeightedL1
                (arity * E.exponent)
                (section43SpatialFlatSchwartzCLE d arity chi) :=
          mul_le_mul_of_nonneg_right hcoefficient hL1
        _ <= osiiVI2ArityDepthMajorant
              (osiiEquation621CanonicalSeedArityConstant lgc)
              (osiiEquation621CanonicalSeedArityRate lgc) arity 0 *
              osiiSpatialPolynomialWeightedL1
                (arity * E.exponent)
                (section43SpatialFlatSchwartzCLE d arity chi) :=
          mul_le_mul_of_nonneg_right hmajorant hL1
    rw [((D.toStrictGeneratedTimeContinuationLadder lgc arity).stage 0
      ).vi2Equation621TotalNormalizedStage_eq_of_pos harity]
    simpa only [E, current,
      InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder,
      StrictGeneratedScalarDepthPointedData.toTimeContinuationLadder,
      timeContinuationLadderOfAngleSectorCover,
      StrictGeneratedScalarDepthPointedData.depthInduction_zero,
      StrictGeneratedScalarDepthPointedData.recursiveSectorRankInduction,
      CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankInduction_zero,
      CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankInductionZero] using hbound

end OSIIChapterV
end OSReconstruction
