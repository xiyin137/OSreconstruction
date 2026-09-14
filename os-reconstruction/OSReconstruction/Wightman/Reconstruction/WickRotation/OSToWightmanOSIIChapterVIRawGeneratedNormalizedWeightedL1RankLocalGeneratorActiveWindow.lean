/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1RankLocalEndpointShellFirstRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedTwoPointRows
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
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1RankLocalInteriorRankSuccessorTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedWeightedL1CenteredProvenance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedL1CoefficientMZ















noncomputable section

open Complex Set
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

open StrictGeneratedScalarDepthPointedData
open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

namespace TargetHubNormalizedRadialSlackAnchorData

/-- The same common-anchor argument works for every right-half-plane
target whose principal arguments are bounded by one raw generator. -/
theorem exists_rawCenteredGeneratorCoordinatewiseShrinkData_of_argumentBound
    {k depth rank : Nat} [NeZero k]
    {hub : Fin k -> Real}
    {target : OSIITimeGapSpace k}
    {rho radialContraction : Real}
    (hradial_pos : 0 < radialContraction)
    (hradial_lt_one : radialContraction < 1)
    (i : GeneratorIndex k)
    (left : Fin i.n -> Real)
    (hleft_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.n depth left)
    (hleft_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.n depth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.m depth right)
    (hright_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.m depth right)
    (htargetRight : target ∈ osiiTimeRightHalfPlane k)
    (htargetArgument : forall j,
      |osiiTimeArgumentVector target j| <=
        rho * |osiiArgumentGeneratorPoint i left theta right j|)
    (C : TargetHubNormalizedRadialSlackAnchorData
      hub target rho radialContraction)
    (H : PositiveHubFloorData hub) :
    exists epsilonCap : Real, 0 < epsilonCap ∧
      epsilonCap =
        (C.outerContraction * (1 - radialContraction)) *
          rootedTargetHubCanonicalRadius H target ∧
      forall epsilon : Real, 0 <= epsilon -> epsilon <= epsilonCap ->
        osiiVI2Unshift k epsilon
            (target - osiiPositiveRealTimeEmbed C.anchorData.anchor) ∈
            osiiTimeRightHalfPlane k ∧
          Nonempty (RawGeneratorCoordinatewiseShrinkData rank depth i
            (osiiTimeArgumentVector
              (osiiVI2Unshift k epsilon
                (target - osiiPositiveRealTimeEmbed
                  C.anchorData.anchor)))) := by
  let contraction : Real := radialContraction * C.outerContraction
  have hcontraction_pos : 0 < contraction :=
    mul_pos hradial_pos C.outerContraction_pos
  have hcontraction_lt_one : contraction < 1 := by
    dsimp [contraction]
    nlinarith [mul_pos hradial_pos
      (sub_pos.mpr C.outerContraction_lt_one)]
  let expandedArgument : Fin k -> Real :=
    contraction⁻¹ • osiiTimeArgumentVector target
  have hexpandedArgument : forall j,
      |expandedArgument j| <=
        |osiiArgumentGeneratorPoint i left theta right j| := by
    intro j
    have hcontracted :
        |osiiTimeArgumentVector target j| <=
          contraction *
            |osiiArgumentGeneratorPoint i left theta right j| :=
      (htargetArgument j).trans
        (mul_le_mul_of_nonneg_right C.rho_le_radial_mul_outer
          (abs_nonneg _))
    change
      |contraction⁻¹ * osiiTimeArgumentVector target j| <= _
    rw [abs_mul, abs_of_pos (inv_pos.mpr hcontraction_pos)]
    calc
      contraction⁻¹ * |osiiTimeArgumentVector target j| <=
          contraction⁻¹ *
            (contraction *
              |osiiArgumentGeneratorPoint i left theta right j|) :=
        mul_le_mul_of_nonneg_left hcontracted
          (inv_pos.mpr hcontraction_pos).le
      _ = |osiiArgumentGeneratorPoint i left theta right j| := by
        field_simp [hcontraction_pos.ne']
  obtain ⟨E⟩ := nonempty_rawGeneratorCoordinatewiseShrinkData
    i left hleft_rank hleft_raw theta htheta right hright_rank hright_raw
      expandedArgument hexpandedArgument
  let expandedPoint := osiiArgumentGeneratorPoint i
    E.centered.left E.centered.theta E.centered.right
  have hpointExpanded : expandedPoint = expandedArgument :=
    E.centered.point_eq
  have hgeneratorExpanded : IsGeneratorRankSuccessorSeed
      rank k (depth + 1) expandedPoint :=
    ⟨i, depth, E.centered.left, E.centered.theta, E.centered.right,
      rfl, E.centered.left_rank, E.centered.right_rank,
      E.centered.angle_bound, rfl⟩
  let epsilonCap : Real :=
    (C.outerContraction * (1 - radialContraction)) *
      rootedTargetHubCanonicalRadius H target
  have hepsilonCap : 0 < epsilonCap := by
    dsimp [epsilonCap]
    exact mul_pos
      (mul_pos C.outerContraction_pos (sub_pos.mpr hradial_lt_one))
      (rootedTargetHubCanonicalRadius_pos H htargetRight)
  refine ⟨epsilonCap, hepsilonCap, rfl, ?_⟩
  intro epsilon hepsilon hepsilon_le
  have hspent (j : Fin k) :
      C.anchorData.anchor j + epsilon <=
        (1 - contraction) * (target j).re := by
    have htargetRadius :
        rootedTargetHubCanonicalRadius H target <= (target j).re := by
      calc
        rootedTargetHubCanonicalRadius H target <= (target j).re / 2 :=
          rootedTargetHubCanonicalRadius_le_half_target H htargetRight j
        _ <= (target j).re := by linarith [htargetRight j]
    have hepsilonSlack :
        epsilon <=
          (C.outerContraction * (1 - radialContraction)) *
            (target j).re := by
      calc
        epsilon <= epsilonCap := hepsilon_le
        _ = (C.outerContraction * (1 - radialContraction)) *
            rootedTargetHubCanonicalRadius H target := rfl
        _ <= (C.outerContraction * (1 - radialContraction)) *
            (target j).re :=
          mul_le_mul_of_nonneg_left htargetRadius
            (mul_nonneg C.outerContraction_pos.le
              (sub_nonneg.mpr hradial_lt_one.le))
    calc
      C.anchorData.anchor j + epsilon <=
          (1 - C.outerContraction) * (target j).re +
            (C.outerContraction * (1 - radialContraction)) *
              (target j).re :=
        add_le_add (C.anchor_le_outerSlack j) hepsilonSlack
      _ = (1 - contraction) * (target j).re := by
        dsimp [contraction]
        ring
  constructor
  · intro j
    change 0 < (target j).re - C.anchorData.anchor j - epsilon
    have hpositive := mul_pos hcontraction_pos (htargetRight j)
    linarith [hspent j]
  apply nonempty_rawGeneratorCoordinatewiseShrinkData
    i E.centered.left E.centered.left_rank E.left_raw
      E.centered.theta E.centered.angle_bound
      E.centered.right E.centered.right_rank E.right_raw
  intro j
  have hexpanded_strict : |expandedPoint j| < Real.pi / 2 :=
    hgeneratorExpanded.toRankSuccessorSeed.toRankSucc.toStrictGenerated
      |>.coordinate_abs_lt_pi_div_two j
  have htarget_arg : Complex.arg (target j) =
      contraction * expandedPoint j := by
    rw [hpointExpanded]
    change osiiTimeArgumentVector target j =
      contraction *
        (contraction⁻¹ * osiiTimeArgumentVector target j)
    field_simp [hcontraction_pos.ne']
  have harg := abs_arg_sub_ofReal_le_of_radial_contraction
    (htargetRight j) hcontraction_pos hcontraction_lt_one.le
    hexpanded_strict htarget_arg (hspent j)
  change
    |Complex.arg
        ((target j - (C.anchorData.anchor j : Complex)) -
          (epsilon : Complex))| <= |expandedPoint j|
  simpa only [ofReal_add, sub_sub] using harg

/-- A common two-budget anchor retains the original reflected source
centers whenever the target argument is controlled by a raw generator. -/
theorem exists_equation621RawSourceCenters_of_argumentBound
    {k depth rank : Nat} [NeZero k]
    {hub : Fin k -> Real}
    {target : OSIITimeGapSpace k}
    {rho radialContraction : Real}
    (hradial_pos : 0 < radialContraction)
    (hradial_lt_one : radialContraction < 1)
    (i : GeneratorIndex k)
    (left : Fin i.n -> Real)
    (hleft_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.n depth left)
    (hleft_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.n depth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.m depth right)
    (hright_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.m depth right)
    (htargetRight : target ∈ osiiTimeRightHalfPlane k)
    (htargetArgument : forall j,
      |osiiTimeArgumentVector target j| <=
        rho * |osiiArgumentGeneratorPoint i left theta right j|)
    (C : TargetHubNormalizedRadialSlackAnchorData
      hub target rho radialContraction)
    (H : PositiveHubFloorData hub) :
    exists epsilonCap : Real, 0 < epsilonCap ∧
      epsilonCap =
        (C.outerContraction * (1 - radialContraction)) *
          rootedTargetHubCanonicalRadius H target ∧
      forall epsilon : Real, 0 <= epsilon -> epsilon <= epsilonCap ->
        osiiVI2Unshift (i.n - 1) epsilon
            (equation621RootedLeftCenter i C.anchorData.anchor target) ∈
          osiiMixedTailArgumentCarrier
            (osiiRawStrictGeneratedMixedLogarithmicBase
              ((i.n - 1) + 1) depth) ∧
        osiiVI2Unshift (i.m - 1) epsilon
            (equation621RootedRightCenter i C.anchorData.anchor target) ∈
          osiiMixedTailArgumentCarrier
            (osiiRawStrictGeneratedMixedLogarithmicBase
              ((i.m - 1) + 1) depth) := by
  obtain ⟨epsilonCap, hepsilonCap, hcap, hsource⟩ :=
    exists_rawCenteredGeneratorCoordinatewiseShrinkData_of_argumentBound
      hradial_pos hradial_lt_one i left hleft_rank hleft_raw theta htheta
      right hright_rank hright_raw htargetRight htargetArgument C H
  refine ⟨epsilonCap, hepsilonCap, hcap, ?_⟩
  intro epsilon hepsilon hepsilon_le
  obtain ⟨hpositive, ⟨G⟩⟩ := hsource epsilon hepsilon hepsilon_le
  let centered : RootedStrictGeneratedTargetHubChartAtRank k depth rank := {
    generator := i
    left := G.centered.left
    left_rank := G.centered.left_rank
    theta := G.centered.theta
    angle_bound := G.centered.angle_bound
    right := G.centered.right
    right_rank := G.centered.right_rank
    target := osiiVI2Unshift k epsilon
      (target - osiiPositiveRealTimeEmbed C.anchorData.anchor)
    target_mem :=
      ⟨hpositive, Set.mem_singleton_iff.mpr G.centered.point_eq.symm⟩ }
  have hleft :=
    RootedStrictGeneratedTargetHubChartAtRank.rootedLeftBlockTarget_mem_rawMixedTailArgumentCarrier
      centered (by simpa [centered] using G.left_raw)
  have hright :=
    RootedStrictGeneratedTargetHubChartAtRank.rootedRightBlockTarget_mem_rawMixedTailArgumentCarrier
      centered (by simpa [centered] using G.right_raw)
  change rootedLeftBlockTarget i
      (osiiVI2Unshift k epsilon
        (target - osiiPositiveRealTimeEmbed C.anchorData.anchor)) ∈ _
    at hleft
  change rootedRightBlockTarget i
      (osiiVI2Unshift k epsilon
        (target - osiiPositiveRealTimeEmbed C.anchorData.anchor)) ∈ _
    at hright
  rw [rootedLeftBlockTarget_osiiVI2Unshift] at hleft
  rw [rootedRightBlockTarget_osiiVI2Unshift] at hright
  rw [RawStrictGeneratedVI2RankLocalNormalizedWeightedL1DepthBoundData.equation621RootedLeftCenter_eq_rootedLeftBlockTarget_centered]
  rw [RawStrictGeneratedVI2RankLocalNormalizedWeightedL1DepthBoundData.equation621RootedRightCenter_eq_rootedRightBlockTarget_centered]
  exact ⟨hleft, hright⟩

end TargetHubNormalizedRadialSlackAnchorData

namespace NormalizedSafeCenteredMarginPointedDirectExtensionData

end NormalizedSafeCenteredMarginPointedDirectExtensionData

end OSIIChapterV
end OSReconstruction
