import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621PrescribedShiftSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1RankLocalShellFirstRecovery

/-!
# Actual prescribed-shift generator rows

The target row is the existing coherent rooted product row. Its lower rows
are damped at the requested normalization shift and converge to the actual
predecessor stage, with no upper bound tied to the packet cutoff.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

open RootedTargetHubPointedDirectExtensionData

variable {d k depth : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {Stage : Type*} [CanonicalGeneratorStageLevelProvider OS Stage]
variable {S : Stage}

/-- Reserving the prescribed shift in the actual bridge gives the exact
time-average comparison for the damped lower rows. -/
theorem equation621DampedTargetTimePoints_timeAverageSplitCondition
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) (w : OSIITimeGapSpace k)
    {epsilon : Real} (hepsilon : 0 <= epsilon)
    (hcentered : w - osiiPositiveRealTimeEmbed anchor ∈ osiiTimeRightHalfPlane k)
    (hbridge : anchor i.bridgeGlobalIndex + epsilon <= (w i.bridgeGlobalIndex).re) :
    OSIIEquation621TimeAverageSplitCondition
      (equation621DampedReflectedStagePoint epsilon
        (reflectedChronologicalGapMap (i.n - 1)
          (A.rootedLeftBlockAnchor i, A.rootedLeftBlockAnchor i))
        (equation621TargetLeftParameter i (w - osiiPositiveRealTimeEmbed anchor)))
      (equation621DampedReflectedStagePoint epsilon
        (reflectedChronologicalGapMap (i.m - 1)
          (A.rootedRightBlockAnchor i, A.rootedRightBlockAnchor i))
        (equation621TargetRightParameter i (w - osiiPositiveRealTimeEmbed anchor))) w := by
  have hleft : forall j, 0 <= (equation621RootedLeftCenter i anchor w j).re := by
    intro j
    simpa using (hcentered (i.leftGlobalIndex j)).le
  have hright : forall j, 0 <= (equation621RootedRightCenter i anchor w j).re := by
    intro j
    simpa using (hcentered (i.rightGlobalIndex j)).le
  have hnonneg {m : Nat} (tau : Fin (m + 1) -> Real)
      (htau : forall j, 0 <= tau j) (z : Fin m -> Complex)
      (hz : forall j, 0 <= (z j).re) :
      0 <= (1 + ∑ j, equation621DampedReflectedStagePoint epsilon
        (reflectedChronologicalGapMap m (tau, tau)) z j).re := by
    rw [equation621DampedReflectedSourceNumerator]
    simp only [Complex.ofReal_re]
    have hsumz := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hz j)
    have hsumtau := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => htau j)
    positivity
  have hnumerator : OSIIEquation621TimeAverageNumeratorSplitCondition
      (equation621DampedReflectedStagePoint epsilon
        (reflectedChronologicalGapMap (i.n - 1)
          (A.rootedLeftBlockAnchor i, A.rootedLeftBlockAnchor i))
        (equation621RootedLeftCenter i anchor w))
      (equation621DampedReflectedStagePoint epsilon
        (reflectedChronologicalGapMap (i.m - 1)
          (A.rootedRightBlockAnchor i, A.rootedRightBlockAnchor i))
        (equation621RootedRightCenter i anchor w)) w := by
    apply OSIIEquation621TimeAverageNumeratorSplitCondition.of_nonnegativeRealNumerators
    · rw [equation621DampedReflectedSourceNumerator]
      simp
    · rw [equation621DampedReflectedSourceNumerator]
      simp
    · exact hnonneg _ (fun j => (A.rootedLeftBlockAnchor_positive i j).le) _ hleft
    · exact hnonneg _ (fun j => (A.rootedRightBlockAnchor_positive i j).le) _ hright
    · rw [equation621DampedReflectedSourceNumerator,
        equation621DampedReflectedSourceNumerator]
      simp only [Complex.ofReal_re]
      rw [sum_re_equation621RootedLeftCenter,
        sum_re_equation621RootedRightCenter,
        sum_rootedLeftBlockAnchor, sum_rootedRightBlockAnchor,
        i.sum_eq_left_add_bridge_add_right]
      simp
      have hbridge' : anchor i.toGap + epsilon <= (w i.toGap).re := by
        simpa [GeneratorIndex.bridgeGlobalIndex_eq_toGap] using hbridge
      have hanchor : 0 < anchor i.toGap := A.anchor_positive i.toGap
      nlinarith
  exact hnumerator.toTimeAverageSplitCondition (by omega) (by omega)
    (Nat.pos_of_ne_zero (NeZero.ne k))

set_option maxHeartbeats 3000000 in
noncomputable def current_reflectedPrescribedShiftProductApproximationRows
    {rank qLeft qRight : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = (qLeft + 2) + (qRight + 2) - 1}
    {hub : Fin k -> Real} {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {target : OSIITimeGapSpace k}
    {C0 : TargetHubHalfAnchorData hub target}
    {Q : AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth RankP.toAtlasFamily lgc C0.anchor}
    {D : RootedTargetHubAdaptedReflectedGramData
      S depth RankP.toAtlasFamily Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData
        (equation621NontrivialGeneratorIndex qLeft qRight hindex) hub target}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        hub atlas target C0 Q D)
    {Previous : Type*} [CanonicalGeneratorStageLevelProvider OS Previous]
    {previous : Previous} {sourceDepth sourceRank : Nat}
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) previous sourceDepth sourceRank)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hbridge : epsilon <
      ((w - osiiPositiveRealTimeEmbed C0.anchor)
        (equation621NontrivialGeneratorIndex qLeft qRight hindex
          ).bridgeGlobalIndex).re)
    (hleft : osiiVI2Unshift (qLeft + 1) epsilon
      (equation621TargetLeftParameter
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        (w - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qLeft + 1) + 1) sourceDepth sourceRank))
    (hright : osiiVI2Unshift (qRight + 1) epsilon
      (equation621TargetRightParameter
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        (w - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qRight + 1) + 1) sourceDepth sourceRank)) :
    let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
    let v := w - osiiPositiveRealTimeEmbed C0.anchor
    let leftTime := equation621DampedReflectedStagePoint epsilon
      (reflectedChronologicalGapMap (qLeft + 1)
        (Q.packet.rootedLeftBlockAnchor i, Q.packet.rootedLeftBlockAnchor i))
      (equation621TargetLeftParameter i v)
    let rightTime := equation621DampedReflectedStagePoint epsilon
      (reflectedChronologicalGapMap (qRight + 1)
        (Q.packet.rootedRightBlockAnchor i, Q.packet.rootedRightBlockAnchor i))
      (equation621TargetRightParameter i v)
    SpatialApproximationRowsFactorizationData E.current
      (spatialApprox.equation621SplitTargetSpatialApproxIdentity i) w
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous
        ((qLeft + 1) + ((qLeft + 1) + 1))).distribution leftTime)
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous
        ((qRight + 1) + ((qRight + 1) + 1))).distribution rightTime)
      (spatialApprox.generatorLeftBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
      (spatialApprox.generatorRightBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
      (i.equation621TargetAdaptedSpatialSplitData d) := by
  dsimp only
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let H := Q.holomorphic.toContinuousTranslationData
  let DLeft := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth D.adapted Q.packet Q.roots i (q := qLeft) rfl
  let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth D.adapted Q.packet Q.roots i (q := qRight) rfl
  let oldRows := current_reflectedProductApproximationRows E spatialApprox w hw
  let leftField := fun x N scale =>
    rootedReflectedGlobalProductLeftArbitraryField D.adapted Q.packet Q.roots
      H qLeft qRight hindex scale
      (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
        spatialApprox i (equation621SplitTargetSpatialPoint i x) N)
      (equation621TargetLeftParameter i v)
  let rightField := fun x N scale =>
    rootedReflectedGlobalProductRightArbitraryField D.adapted Q.packet Q.roots
      H qLeft qRight hindex scale
      (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
        spatialApprox i (equation621SplitTargetSpatialPoint i x) N)
      (equation621TargetRightParameter i v)
  let diagonal := fun x : OSHilbertSpace OS =>
    @inner Complex (OSHilbertSpace OS) _ x
      (osiiOriginalOSHilbertComplex OS (epsilon : Complex) x)
  have hradial :=
    RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain
      E w hw
  refine {
    targetApprox := oldRows.targetApprox
    leftApprox := fun x N scale => diagonal (leftField x N scale)
    rightApprox := fun x N scale => diagonal (rightField x N scale)
    target_row_tendsto := oldRows.target_row_tendsto
    left_row_tendsto := ?_
    right_row_tendsto := ?_
    eventually_bound := ?_ }
  · intro x N
    let block := spatialApprox.generatorLeftBlockProductApproxIdentity i
    have hsource : forall scale chi,
        UniformCompactTimeSource.source (DLeft.sourceCLM scale chi) =
          (Q.packet.rootedLeftBlockApproximateIdentity Q.roots i
            ).translatedPositiveTimeSpatialSource
            (Q.packet.rootedLeftBlockAnchor i)
            (Q.packet.rootedLeftBlockAnchor_positive i) chi scale := by
      intro scale chi
      simpa [DLeft, i, equation621NontrivialGeneratorIndex,
        rootedLeftNontrivialReflectedGramSpatialSourceData] using
        Q.packet.rootedLeftBlockAnchoredSourceCLM_source_translated Q.roots i scale chi
    have hz : equation621TargetLeftParameter i v ∈
        openZeroConvexKernel DLeft.reflectedGram.atlas.spatialLinearDomain :=
      hradial.2.1
    have hrow := DLeft.tendsto_dampedDiagonal_marginalSpatialProbe P
      (Q.packet.rootedLeftBlockApproximateIdentity Q.roots i)
      (Q.packet.rootedLeftBlockAnchor i)
      (Q.packet.rootedLeftBlockAnchor_positive i) hsource hepsilon lgc block
      (generatorLeftBlockSpatialPoint d i (equation621SplitTargetSpatialPoint i x))
      N (equation621TargetLeftParameter i v) hleft hz
      (H.commonTailStart i) (H.commonTailStart i)
    have hpoint : reflectedSelfPairMarginalSpatialPoint d (qLeft + 1)
        (generatorLeftBlockSpatialPoint d i (equation621SplitTargetSpatialPoint i x)) =
          (i.equation621TargetAdaptedSpatialSplitData d).leftPoint x := by
      simpa [i] using generatorLeftBlockSpatialPoint_reflectedSelfPair
        (d := d) i (equation621SplitTargetSpatialPoint i x)
    rw [hpoint] at hrow
    have htest : block.toEquation621SpatialApproxIdentity.section43Probe
        (generatorLeftBlockSpatialPoint d i (equation621SplitTargetSpatialPoint i x)) N =
          RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
            spatialApprox i (equation621SplitTargetSpatialPoint i x) N := by
      simpa [block, i, equation621NontrivialGeneratorIndex,
        RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest] using
        RootedA0BlockContinuousTranslationData.generatorLeftBlockProbe_eq_positiveTargetTest
          (d := d) spatialApprox i (equation621SplitTargetSpatialPoint i x) N
    apply (tendsto_congr' (Filter.Eventually.of_forall fun scale => ?_)).2 hrow
    apply congrArg diagonal
    exact congrArg (fun chi => DLeft.reflectedGram.atlas.gram.anchoredAtlasField
      DLeft.reflectedGram.atlas.sourceStage.stage
      DLeft.reflectedGram.atlas.sourceStage.germ
      (DLeft.sourceCLM (scale + H.commonTailStart i) chi)
      (equation621TargetLeftParameter i v)) htest.symm
  · intro x N
    let block := spatialApprox.generatorRightBlockProductApproxIdentity i
    have hsource : forall scale chi,
        UniformCompactTimeSource.source (DRight.sourceCLM scale chi) =
          (Q.packet.rootedRightBlockApproximateIdentity Q.roots i
            ).translatedPositiveTimeSpatialSource
            (Q.packet.rootedRightBlockAnchor i)
            (Q.packet.rootedRightBlockAnchor_positive i) chi scale := by
      intro scale chi
      simpa [DRight, i, equation621NontrivialGeneratorIndex,
        rootedRightNontrivialReflectedGramSpatialSourceData] using
        Q.packet.rootedRightBlockAnchoredSourceCLM_source_translated Q.roots i scale chi
    have hz : equation621TargetRightParameter i v ∈
        openZeroConvexKernel DRight.reflectedGram.atlas.spatialLinearDomain :=
      hradial.2.2
    have hrow := DRight.tendsto_dampedDiagonal_marginalSpatialProbe P
      (Q.packet.rootedRightBlockApproximateIdentity Q.roots i)
      (Q.packet.rootedRightBlockAnchor i)
      (Q.packet.rootedRightBlockAnchor_positive i) hsource hepsilon lgc block
      (generatorRightBlockSpatialPoint d i (equation621SplitTargetSpatialPoint i x))
      N (equation621TargetRightParameter i v) hright hz
      (H.commonTailStart i) (H.commonTailStart i)
    have hpoint : reflectedSelfPairMarginalSpatialPoint d (qRight + 1)
        (generatorRightBlockSpatialPoint d i (equation621SplitTargetSpatialPoint i x)) =
          (i.equation621TargetAdaptedSpatialSplitData d).rightPoint x := by
      simpa [i] using generatorRightBlockSpatialPoint_reflectedSelfPair
        (d := d) i (equation621SplitTargetSpatialPoint i x)
    rw [hpoint] at hrow
    have htest : block.toEquation621SpatialApproxIdentity.section43Probe
        (generatorRightBlockSpatialPoint d i (equation621SplitTargetSpatialPoint i x)) N =
          RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
            spatialApprox i (equation621SplitTargetSpatialPoint i x) N := by
      simpa [block, i, equation621NontrivialGeneratorIndex,
        RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest] using
        RootedA0BlockContinuousTranslationData.generatorRightBlockProbe_eq_positiveTargetTest
          (d := d) spatialApprox i (equation621SplitTargetSpatialPoint i x) N
    apply (tendsto_congr' (Filter.Eventually.of_forall fun scale => ?_)).2 hrow
    apply congrArg diagonal
    exact congrArg (fun chi => DRight.reflectedGram.atlas.gram.anchoredAtlasField
      DRight.reflectedGram.atlas.sourceStage.stage
      DRight.reflectedGram.atlas.sourceStage.germ
      (DRight.sourceCLM (scale + H.commonTailStart i) chi)
      (equation621TargetRightParameter i v)) htest.symm
  · intro x N
    filter_upwards [] with scale
    let y := equation621SplitTargetSpatialPoint i x
    have heq := rootedAbsoluteProductReflectedScalarSum_eq_candidate_on_radial
      D.adapted Q.packet Q.roots Q.holomorphic lgc
      qLeft qRight hindex spatialApprox y N scale v hradial
    have htarget : oldRows.targetApprox x N scale =
        rootedReflectedGlobalProductArbitraryCandidate D.adapted Q.packet Q.roots H lgc
          qLeft qRight hindex scale
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
            spatialApprox i y N)
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
            spatialApprox i y N)
          (generatorChronologicalParameterComplexCLE i v) := by
      simpa [oldRows, current_reflectedProductApproximationRows, i, v, y, H] using heq
    rw [htarget]
    simpa [leftField, rightField, diagonal, i, v, y, H] using
      norm_rootedReflectedGlobalProductArbitraryCandidate_le_sqrt_shifted_diagonals
        D.adapted Q.packet Q.roots H lgc qLeft qRight hindex scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i y N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i y N) hepsilon v hbridge

set_option maxHeartbeats 3000000 in
/-- The genuine normalized raw predecessor supplies the sharp two-sided
generator bound at the prescribed shift. The common source rank, shifted
source representatives, reflected factor, and denominator comparison are
all constructed, while the outer depth and coefficient remain unchanged. -/
theorem norm_current_distribution_le_of_rawPredecessor_prescribedShift
    {rank qLeft qRight : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = (qLeft + 2) + (qRight + 2) - 1}
    {hub : Fin k -> Real} {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {target : OSIITimeGapSpace k}
    {C0 : TargetHubHalfAnchorData hub target}
    {Q : AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth RankP.toAtlasFamily lgc C0.anchor}
    {D : RootedTargetHubAdaptedReflectedGramData
      S depth RankP.toAtlasFamily Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData
        (equation621NontrivialGeneratorIndex qLeft qRight hindex) hub target}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        hub atlas target C0 Q D)
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {t beta sourceDepth : Nat}
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta sourceDepth)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hcentered : w - osiiPositiveRealTimeEmbed C0.anchor ∈ osiiTimeRightHalfPlane k)
    (hbridge : epsilon <
      ((w - osiiPositiveRealTimeEmbed C0.anchor)
        (equation621NontrivialGeneratorIndex qLeft qRight hindex
          ).bridgeGlobalIndex).re)
    (hleft : osiiVI2Unshift (qLeft + 1) epsilon
      (equation621TargetLeftParameter
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        (w - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase
          ((qLeft + 1) + 1) sourceDepth))
    (hright : osiiVI2Unshift (qRight + 1) epsilon
      (equation621TargetRightParameter
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        (w - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase
          ((qRight + 1) + 1) sourceDepth))
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖E.current.extension.toTimeContinuationStage.distribution w chi‖ <=
      (osiiVI2ArityDepthMajorant B.alpha beta k (sourceDepth + 1) *
        osiiSpatialPolynomialWeightedL1 (k * t)
          (section43SpatialFlatSchwartzCLE d k chi)) *
        ‖osiiVI2Equation621Denormalization t k epsilon w‖ := by
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let previous := initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
    lgc sourceDepth
  obtain ⟨leftRank, hleftRank⟩ :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.exists_rank hleft.2.toStrictGenerated
  obtain ⟨rightRank, hrightRank⟩ :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.exists_rank hright.2.toStrictGenerated
  let commonRank := max leftRank rightRank
  let P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) previous.pointed sourceDepth commonRank :=
    StageWideStrictGeneratedMixedReflectedGramRankData.ofStrictGeneratedAtRank
      (OS := OS) previous.pointed sourceDepth commonRank (by
        intro arity z hz
        change z ∈ (previous.pointed.stageLevel.stage arity).carrier
        exact previous.strictGeneratedCarrier_subset arity
          ⟨hz.1, hz.2.toStrictGenerated⟩)
  have hleftCommon : osiiVI2Unshift (qLeft + 1) epsilon
      (equation621TargetLeftParameter i v) ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qLeft + 1) + 1) sourceDepth commonRank) :=
    ⟨hleft.1, OSIIStrictGeneratedLogarithmicArgumentAtRank.mono
      (le_max_left _ _) hleftRank⟩
  have hrightCommon : osiiVI2Unshift (qRight + 1) epsilon
      (equation621TargetRightParameter i v) ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qRight + 1) + 1) sourceDepth commonRank) :=
    ⟨hright.1, OSIIStrictGeneratedLogarithmicArgumentAtRank.mono
      (le_max_right _ _) hrightRank⟩
  let leftTime := equation621DampedReflectedStagePoint epsilon
    (reflectedChronologicalGapMap (qLeft + 1)
      (Q.packet.rootedLeftBlockAnchor i, Q.packet.rootedLeftBlockAnchor i))
    (equation621TargetLeftParameter i v)
  let rightTime := equation621DampedReflectedStagePoint epsilon
    (reflectedChronologicalGapMap (qRight + 1)
      (Q.packet.rootedRightBlockAnchor i, Q.packet.rootedRightBlockAnchor i))
    (equation621TargetRightParameter i v)
  let dLeft := ‖osiiVI2Equation621Denormalization t
    ((qLeft + 1) + ((qLeft + 1) + 1)) epsilon leftTime‖
  let dRight := ‖osiiVI2Equation621Denormalization t
    ((qRight + 1) + ((qRight + 1) + 1)) epsilon rightTime‖
  let dTarget := ‖osiiVI2Equation621Denormalization t k epsilon w‖
  have hleftBound (psi : SchwartzMap
      (Section43SpatialSpace d ((qLeft + 1) + ((qLeft + 1) + 1))) Complex) :
      ‖(previous.pointed.stageLevel.stage
          ((qLeft + 1) + ((qLeft + 1) + 1))).distribution leftTime psi‖ <=
        dLeft * (osiiVI2ArityDepthMajorant B.alpha beta
          ((qLeft + 1) + ((qLeft + 1) + 1)) sourceDepth *
          osiiSpatialPolynomialWeightedL1
            (((qLeft + 1) + ((qLeft + 1) + 1)) * t)
            (section43SpatialFlatSchwartzCLE d
              ((qLeft + 1) + ((qLeft + 1) + 1)) psi)) := by
    have htime := reflectedChronologicalGapMap_mem_strictPositive
      (Q.packet.rootedLeftBlockAnchor i) (Q.packet.rootedLeftBlockAnchor i)
      (Q.packet.rootedLeftBlockAnchor_positive i)
      (Q.packet.rootedLeftBlockAnchor_positive i)
    have hpoint := reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier
      htime hleft
    have hbound := B.norm_rawShiftedDistribution_le_mul_denormalization
      hepsilon hpoint psi
    simpa [previous, leftTime, dLeft, i, v, equation621DampedReflectedStagePoint,
      InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder,
      StrictGeneratedScalarDepthPointedData.toTimeContinuationLadder,
      timeContinuationLadderOfAngleSectorCover] using hbound
  have hrightBound (psi : SchwartzMap
      (Section43SpatialSpace d ((qRight + 1) + ((qRight + 1) + 1))) Complex) :
      ‖(previous.pointed.stageLevel.stage
          ((qRight + 1) + ((qRight + 1) + 1))).distribution rightTime psi‖ <=
        dRight * (osiiVI2ArityDepthMajorant B.alpha beta
          ((qRight + 1) + ((qRight + 1) + 1)) sourceDepth *
          osiiSpatialPolynomialWeightedL1
            (((qRight + 1) + ((qRight + 1) + 1)) * t)
            (section43SpatialFlatSchwartzCLE d
              ((qRight + 1) + ((qRight + 1) + 1)) psi)) := by
    have htime := reflectedChronologicalGapMap_mem_strictPositive
      (Q.packet.rootedRightBlockAnchor i) (Q.packet.rootedRightBlockAnchor i)
      (Q.packet.rootedRightBlockAnchor_positive i)
      (Q.packet.rootedRightBlockAnchor_positive i)
    have hpoint := reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier
      htime hright
    have hbound := B.norm_rawShiftedDistribution_le_mul_denormalization
      hepsilon hpoint psi
    simpa [previous, rightTime, dRight, i, v, equation621DampedReflectedStagePoint,
      InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder,
      StrictGeneratedScalarDepthPointedData.toTimeContinuationLadder,
      timeContinuationLadderOfAngleSectorCover] using hbound
  have hbridge' : C0.anchor i.bridgeGlobalIndex + epsilon <=
      (w i.bridgeGlobalIndex).re := by
    have h : epsilon < (w i.bridgeGlobalIndex).re - C0.anchor i.bridgeGlobalIndex := by
      simpa [i, osiiPositiveRealTimeEmbed] using hbridge
    linarith
  have hsplit : OSIIEquation621TimeAverageSplitCondition leftTime rightTime w :=
    equation621DampedTargetTimePoints_timeAverageSplitCondition
      Q.packet i w hepsilon.le hcentered hbridge'
  have hdenormalization : Real.sqrt (dLeft * dRight) <= dTarget := by
    apply Real.sqrt_le_iff.2
    refine ⟨norm_nonneg _, ?_⟩
    exact norm_osiiVI2Equation621Denormalization_split_mul_le_sq
      (a := (qLeft + 1) + ((qLeft + 1) + 1))
      (b := (qRight + 1) + ((qRight + 1) + 1))
      (k := k) (by omega) (by omega)
      (Nat.pos_of_ne_zero (NeZero.ne k)) (by omega) hepsilon hsplit t
  have hab : ((qLeft + 1) + ((qLeft + 1) + 1)) +
      ((qRight + 1) + ((qRight + 1) + 1)) = 2 * k := by omega
  have hpAverage : (((qLeft + 1) + ((qLeft + 1) + 1)) * t) +
      (((qRight + 1) + ((qRight + 1) + 1)) * t) <= 2 * (k * t) := by
    calc
      _ = (((qLeft + 1) + ((qLeft + 1) + 1)) +
        ((qRight + 1) + ((qRight + 1) + 1))) * t := by ring
      _ = 2 * (k * t) := by rw [hab]; ring
      _ <= _ := le_rfl
  let rows := current_reflectedPrescribedShiftProductApproximationRows
    E P spatialApprox w hw hepsilon hbridge hleftCommon hrightCommon
  exact SpatialApproximationRowsFactorizationData.norm_distribution_le_weightedL1_mul_of_lowerBounds
    (pLeft := ((qLeft + 1) + ((qLeft + 1) + 1)) * t)
    (pRight := ((qRight + 1) + ((qRight + 1) + 1)) * t)
    (pTarget := k * t) (beta := beta) (M := sourceDepth)
    (alpha := B.alpha) (dLeft := dLeft) (dRight := dRight)
    (dTarget := dTarget) rows B.alpha_nonneg (norm_nonneg _)
      (norm_nonneg _) hleftBound hrightBound hdenormalization hpAverage hab chi

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
