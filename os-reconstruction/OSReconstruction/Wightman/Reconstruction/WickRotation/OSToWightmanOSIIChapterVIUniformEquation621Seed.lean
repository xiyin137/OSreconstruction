/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformEquation66ArityGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedSpatialDensity











noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

namespace OSIIChapterV
namespace InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The concrete VI.1 density built with the uniform multi-gap degree record. -/
noncomputable def toStrictGeneratedOSBuiltUniformRealEdgeDensityGrowthData
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D0 : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc))
    (arity : Nat) (harity : 0 < arity) :
    OSIITimeContinuationLadderRealEdgeDensityGrowthData
      (D.toStrictGeneratedTimeContinuationLadder lgc arity) := by
  letI : NeZero arity := ⟨Nat.ne_of_gt harity⟩
  let U := osiiUniformMultiGapCenteredWindowScaleBoundData
    d arity OS lgc D0
  exact
    HasCanonicalReducedCompactStageEdges.toOSBuiltRealEdgeDensityGrowthData
      d OS lgc (D.toStrictGeneratedTimeContinuationLadder lgc arity) 0
      (InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder_stage_zero_hasCanonicalEdges_osBuilt
        D lgc arity)
      U.toScaleBoundData

end InitialGeneratedLogarithmicStageLevelData
end OSIIChapterV

/-- One VI.1 density package at every positive arity, with a normalization
exponent chosen before arity and proofs of both equation-`(6.21)` degree
budgets.  The finite-seminorm real-edge package is derived below; retaining
the density here is essential for the weighted spatial-function induction in
VI.2. -/
structure OSIIEquation621UniformPositiveRealSeedData
    {d : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (D : OSIIChapterV.InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) where
  exponent : Nat
  realEdgeDensityGrowth : ∀ (arity : Nat), 0 < arity ->
    OSIITimeContinuationLadderRealEdgeDensityGrowthData
      (D.toStrictGeneratedTimeContinuationLadder lgc arity)
  timeDegree_le : ∀ (arity : Nat) (harity : 0 < arity),
    (realEdgeDensityGrowth arity harity).timeDegree <= arity * exponent
  densityBoundaryDegree_le : ∀ (arity : Nat) (harity : 0 < arity),
    (realEdgeDensityGrowth arity harity).boundaryDegree <= arity * exponent
  spatialDegree_le : ∀ (arity : Nat) (harity : 0 < arity),
    (realEdgeDensityGrowth arity harity).spatialDegree <= arity * exponent

namespace OSIIUniformMultiGapGrowthData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}

/-- One per-particle exponent absorbs both VI.1 degree budgets. -/
def equation621Exponent (U : OSIIUniformMultiGapGrowthData d OS lgc) : Nat :=
  max (U.scaleRate + U.growthRate) (2 * U.scaleRate)

/-- Uniform packet bounds give the actual non-circular VI.1 density at
every positive arity of the strict-generated Chapter V ladder. -/
noncomputable def toEquation621UniformPositiveRealSeedData
    (U : OSIIUniformMultiGapGrowthData d OS lgc)
    (D : OSIIChapterV.InitialGeneratedLogarithmicStageLevelData (d := d) OS) :
    OSIIEquation621UniformPositiveRealSeedData D lgc := by
  let density : ∀ (arity : Nat), 0 < arity ->
      OSIITimeContinuationLadderRealEdgeDensityGrowthData
        (D.toStrictGeneratedTimeContinuationLadder lgc arity) :=
    fun arity harity => by
      letI : NeZero arity := ⟨Nat.ne_of_gt harity⟩
      exact
        OSIIChapterV.HasCanonicalReducedCompactStageEdges.toOSBuiltRealEdgeDensityGrowthData
          d OS lgc (D.toStrictGeneratedTimeContinuationLadder lgc arity) 0
          (D.toStrictGeneratedTimeContinuationLadder_stage_zero_hasCanonicalEdges_osBuilt
            lgc arity)
          (U.toScaleBoundData arity)
  refine {
    exponent := U.equation621Exponent
    realEdgeDensityGrowth := density
    timeDegree_le := ?_
    densityBoundaryDegree_le := ?_
    spatialDegree_le := ?_ }
  · intro arity harity
    letI : NeZero arity := ⟨Nat.ne_of_gt harity⟩
    change (U.toScaleBoundData arity).scaleDegree +
      (U.toScaleBoundData arity).growthDegree <= arity * U.equation621Exponent
    rw [U.scaleDegree_eq arity, U.growthDegree_eq arity, ← Nat.mul_add]
    exact Nat.mul_le_mul_left arity (Nat.le_max_left _ _)
  · intro arity harity
    letI : NeZero arity := ⟨Nat.ne_of_gt harity⟩
    change 2 * (U.toScaleBoundData arity).scaleDegree <=
      arity * U.equation621Exponent
    rw [U.scaleDegree_eq arity]
    calc
      2 * (arity * U.scaleRate) = arity * (2 * U.scaleRate) := by ac_rfl
      _ <= arity * U.equation621Exponent :=
        Nat.mul_le_mul_left arity (Nat.le_max_right _ _)
  · intro arity harity
    letI : NeZero arity := ⟨Nat.ne_of_gt harity⟩
    change (U.toScaleBoundData arity).scaleDegree +
      (U.toScaleBoundData arity).growthDegree <= arity * U.equation621Exponent
    rw [U.scaleDegree_eq arity, U.growthDegree_eq arity, ← Nat.mul_add]
    exact Nat.mul_le_mul_left arity (Nat.le_max_left _ _)

/-- The uniform seed retains the coefficient of the genuine OS-built
density, so its all-arity bound survives the public packaging. -/
theorem realEdgeDensityConstant_le_arityMajorant
    (U : OSIIUniformMultiGapGrowthData d OS lgc)
    (D : OSIIChapterV.InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (arity : Nat) (harity : 0 < arity) :
    ((U.toEquation621UniformPositiveRealSeedData D
      ).realEdgeDensityGrowth arity harity).constant <=
      U.densityArityConstant * (arity : Real) ^ (arity * U.densityArityRate) := by
  letI : NeZero arity := ⟨Nat.ne_of_gt harity⟩
  change
    OSIIStep4FullSchwartzAngularContinuationData.equation66E0PolynomialConstant
        (U.toScaleBoundData arity) *
      (16 : Real) ^ (2 * (U.toScaleBoundData arity).scaleDegree) + 1 <= _
  exact U.densityConstant_le_arityMajorant arity

end OSIIUniformMultiGapGrowthData

/-- Corrected arity-linear E0' supplies the canonical VI.1 seed, with all
rates and coefficients chosen before arity. -/
noncomputable def OSIIChapterV.InitialGeneratedLogarithmicStageLevelData.toEquation621UniformPositiveRealSeedData
    {d : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (D : OSIIChapterV.InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    OSIIEquation621UniformPositiveRealSeedData D lgc :=
  (osiiArityLinearUniformMultiGapGrowthData d OS lgc
    ).toEquation621UniformPositiveRealSeedData D

/-- Per-particle all-arity rate for the canonical normalized positive-real
VI.2 seed coefficient.  The first summand is the explicit equation-(6.21)
normalization power; the second is the source-native VI.1 density rate. -/
def osiiEquation621CanonicalSeedArityRate
    {d : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS) : Nat :=
  let U := osiiArityLinearUniformMultiGapGrowthData d OS lgc
  2 * U.equation621Exponent + U.densityArityRate

/-- Fixed all-arity coefficient for the canonical normalized positive-real
VI.2 seed coefficient. -/
def osiiEquation621CanonicalSeedArityConstant
    {d : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS) : Real :=
  (osiiArityLinearUniformMultiGapGrowthData d OS lgc).densityArityConstant

theorem osiiEquation621CanonicalSeedArityConstant_nonneg
    {d : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS) :
    0 <= osiiEquation621CanonicalSeedArityConstant lgc := by
  exact (osiiArityLinearUniformMultiGapGrowthData d OS lgc
    ).densityArityConstant_pos.le

namespace OSIIEquation621UniformPositiveRealSeedData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {D : OSIIChapterV.InitialGeneratedLogarithmicStageLevelData (d := d) OS}
variable {lgc : OSLinearGrowthCondition d OS}

/-- Exact Banach-valued positive-real edge package for the normalized stage at
one arity. -/
def normalizedPositiveRealWeightedEdgeData
    (E : OSIIEquation621UniformPositiveRealSeedData D lgc)
    (arity : Nat) (harity : 0 < arity)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    OSIITimeContinuationLadderRealEdgeDensityGrowthData.OSIIEquation621WeightedPositiveRealEdgeData
      ((D.toStrictGeneratedTimeContinuationLadder lgc arity
        ).toFullTimeContinuationStage.vi2Equation621NormalizedStage
          E.exponent epsilon)
      (arity * E.exponent) :=
  (E.realEdgeDensityGrowth arity harity
    ).toVI2Equation621WeightedPositiveRealEdgeData
      E.exponent
      (E.timeDegree_le arity harity)
      (E.densityBoundaryDegree_le arity harity)
      (arity * E.exponent)
      (E.spatialDegree_le arity harity)
      hepsilon

/-- Rank-zero weighted-density coefficient at one arity, extended by zero at
arity zero so it can be summed over finite arity ranges. -/
noncomputable def normalizedPositiveRealWeightedCoefficient
    (E : OSIIEquation621UniformPositiveRealSeedData D lgc)
    (arity : Nat) : Real :=
  if harity : 0 < arity then
    (arity : Real) ^ (2 * (arity * E.exponent)) *
      (E.realEdgeDensityGrowth arity harity).constant
  else
    0

/-- The canonical source-native equation-(6.21) seed coefficient has one
all-arity majorant.  This keeps the normalized positive-real coefficient
quantitative after the density package is wrapped in the public seed API. -/
theorem canonical_normalizedPositiveRealWeightedCoefficient_le_arityMajorant
    (D : OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
      (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) (harity : 0 < arity) :
    (D.toEquation621UniformPositiveRealSeedData lgc
      ).normalizedPositiveRealWeightedCoefficient arity <=
      osiiEquation621CanonicalSeedArityConstant lgc *
        (arity : Real) ^
          (arity * osiiEquation621CanonicalSeedArityRate lgc) := by
  let U := osiiArityLinearUniformMultiGapGrowthData d OS lgc
  have hconstant := U.realEdgeDensityConstant_le_arityMajorant D arity harity
  rw [normalizedPositiveRealWeightedCoefficient, dif_pos harity]
  change
    (arity : Real) ^ (2 * (arity * U.equation621Exponent)) *
        ((U.toEquation621UniformPositiveRealSeedData D
          ).realEdgeDensityGrowth arity harity).constant <=
      U.densityArityConstant *
        (arity : Real) ^
          (arity * (2 * U.equation621Exponent + U.densityArityRate))
  calc
    _ <= (arity : Real) ^ (2 * (arity * U.equation621Exponent)) *
        (U.densityArityConstant *
          (arity : Real) ^ (arity * U.densityArityRate)) :=
      mul_le_mul_of_nonneg_left hconstant (by positivity)
    _ = _ := by
      rw [show 2 * (arity * U.equation621Exponent) =
        arity * (2 * U.equation621Exponent) by ring, Nat.mul_add, pow_add]
      ring

end OSIIEquation621UniformPositiveRealSeedData
end OSReconstruction
