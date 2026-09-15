import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621PrescribedShiftEndpoints
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedTwoPointRows

/-!
# Prescribed-shift estimates for every generator split

The common normalization calculation is applied to actual reflected packet
rows. One-particle endpoints use their positive-real predecessor, while the
nontrivial blocks use the coherent continued-source limits.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

open RootedTargetHubPointedDirectExtensionData

/-- The same raw predecessor and exact denominator comparison control any
arity-balanced pair of genuine source rows. -/
theorem norm_distribution_le_of_rawPredecessor_prescribedShiftRows
    {d k a b depth sourceDepth t beta : Nat}
    [NeZero d] [NeZero k] [NeZero a] [NeZero b]
    {OS : OsterwalderSchraderAxioms d}
    {Stage : Type*} [CanonicalGeneratorStageLevelProvider OS Stage]
    {S : Stage}
    {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k} {hub : Fin k -> Real}
    {target : OSIITimeGapSpace k} {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {current : RootedTargetHubPointedDirectExtensionData
      S depth P lgc i hub target atlas}
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta sourceDepth)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {left : OSIITimeGapSpace a} {right : OSIITimeGapSpace b}
    (hleft : left ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase a sourceDepth))
    (hright : right ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase b sourceDepth))
    {targetProbe : OSIIEquation621SpatialApproxIdentityData (k * d)}
    {leftProbe : OSIIEquation621SpatialApproxIdentityData (a * d)}
    {rightProbe : OSIIEquation621SpatialApproxIdentityData (b * d)}
    {split : OSIIEquation621SpatialSplitData d k a b}
    {w : OSIITimeGapSpace k}
    (rows : SpatialApproximationRowsFactorizationData current targetProbe w
      (((initial.toStrictGeneratedTimeContinuationLadder lgc a).stage
        sourceDepth).distribution (osiiVI2Shift a epsilon left))
      (((initial.toStrictGeneratedTimeContinuationLadder lgc b).stage
        sourceDepth).distribution (osiiVI2Shift b epsilon right))
      leftProbe rightProbe split)
    (hsplit : OSIIEquation621TimeAverageSplitCondition
      (osiiVI2Shift a epsilon left) (osiiVI2Shift b epsilon right) w)
    (hab : a + b = 2 * k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖current.extension.toTimeContinuationStage.distribution w chi‖ <=
      (osiiVI2ArityDepthMajorant B.alpha beta k (sourceDepth + 1) *
        osiiSpatialPolynomialWeightedL1 (k * t)
          (section43SpatialFlatSchwartzCLE d k chi)) *
        ‖osiiVI2Equation621Denormalization t k epsilon w‖ := by
  let dLeft := ‖osiiVI2Equation621Denormalization t a epsilon
    (osiiVI2Shift a epsilon left)‖
  let dRight := ‖osiiVI2Equation621Denormalization t b epsilon
    (osiiVI2Shift b epsilon right)‖
  let dTarget := ‖osiiVI2Equation621Denormalization t k epsilon w‖
  have hdenormalization : Real.sqrt (dLeft * dRight) <= dTarget := by
    apply Real.sqrt_le_iff.2
    refine ⟨norm_nonneg _, ?_⟩
    exact norm_osiiVI2Equation621Denormalization_split_mul_le_sq
      (Nat.pos_of_ne_zero (NeZero.ne a))
      (Nat.pos_of_ne_zero (NeZero.ne b))
      (Nat.pos_of_ne_zero (NeZero.ne k)) hab hepsilon hsplit t
  have hpAverage : a * t + b * t <= 2 * (k * t) := by
    calc
      _ = (a + b) * t := by ring
      _ = 2 * (k * t) := by rw [hab]; ring
      _ <= _ := le_rfl
  exact SpatialApproximationRowsFactorizationData.norm_distribution_le_weightedL1_mul_of_lowerBounds
    (pLeft := a * t) (pRight := b * t) (pTarget := k * t)
    (alpha := B.alpha) (beta := beta) (M := sourceDepth)
    (dLeft := dLeft) (dRight := dRight) (dTarget := dTarget)
    rows B.alpha_nonneg (norm_nonneg _) (norm_nonneg _)
    (fun psi => B.norm_rawShiftedDistribution_le_mul_denormalization
      hepsilon hleft psi)
    (fun psi => B.norm_rawShiftedDistribution_le_mul_denormalization
      hepsilon hright psi)
    hdenormalization hpAverage hab chi

variable {d k depth : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {Stage : Type*} [CanonicalGeneratorStageLevelProvider OS Stage]
variable {S : Stage}

/-- The empty one-particle tail is a raw mixed predecessor at every depth. -/
theorem emptyTail_mem_rawStrictGeneratedMixed
    (sourceDepth : Nat) (z : Fin 0 -> Complex) :
    z ∈ osiiMixedTailArgumentCarrier
      (osiiRawStrictGeneratedMixedLogarithmicBase 1 sourceDepth) := by
  constructor
  · intro j
    exact Fin.elim0 j
  · have hzero := OSIIRawStrictGeneratedLogarithmicArgument.mixed_zero
      1 sourceDepth (by omega)
    change OSIIRawStrictGeneratedLogarithmicArgument .mixed 1 sourceDepth _
    convert hzero using 1
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl

/-- Positivity of the reflected source times also includes the empty tail. -/
theorem reflectedChronologicalGapMap_mem_strictPositive_all
    {m : Nat} (left right : Fin (m + 1) -> Real)
    (hleft : left ∈ section43TimeStrictPositiveRegion (m + 1))
    (hright : right ∈ section43TimeStrictPositiveRegion (m + 1)) :
    reflectedChronologicalGapMap m (left, right) ∈
      section43TimeStrictPositiveRegion (m + (m + 1)) := by
  intro j
  simp only [reflectedChronologicalGapMap]
  split_ifs with hbefore hbridge
  · exact hleft _
  · exact add_pos (hleft 0) (hright 0)
  · exact hright _

/-- The raw reflected point includes the empty-tail positive-real endpoint. -/
theorem reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier_all
    {m sourceDepth : Nat}
    {tau : Fin (m + (m + 1)) -> Real}
    (htau : tau ∈ section43TimeStrictPositiveRegion (m + (m + 1)))
    {z : Fin m -> Complex}
    (hz : z ∈ osiiMixedTailArgumentCarrier
      (osiiRawStrictGeneratedMixedLogarithmicBase (m + 1) sourceDepth)) :
    reflectedCauchyShiftedStagePoint tau z ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase (m + (m + 1)) sourceDepth) := by
  cases m with
  | zero =>
    have hcenter : reflectedCauchyCenter z = 0 := by
      funext j
      exact Fin.elim0 j
    simpa [reflectedCauchyShiftedStagePoint, hcenter] using
      positiveRealTimeEmbed_mem_rawStrictGenerated (depth := sourceDepth) tau htau
  | succ m =>
    exact reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier htau hz

/-- Select the existing reflected-Gram provider on the actual raw predecessor
at one finite source rank. -/
noncomputable def canonicalRawPredecessorReflectedGramRankData
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (sourceDepth sourceRank : Nat) :
    StageWideStrictGeneratedMixedReflectedGramRankData (OS := OS)
      (initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
        lgc sourceDepth).pointed sourceDepth sourceRank :=
  StageWideStrictGeneratedMixedReflectedGramRankData.ofStrictGeneratedAtRank
    (OS := OS) _ sourceDepth sourceRank (by
      intro arity z hz
      change z ∈ ((initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
        lgc sourceDepth).pointed.stageLevel.stage arity).carrier
      exact (initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
        lgc sourceDepth).strictGeneratedCarrier_subset arity
          ⟨hz.1, hz.2.toStrictGenerated⟩)

set_option maxHeartbeats 3000000 in
/-- The left-endpoint rows use the literal one-particle source on the left
and the continued reflected source on the right, at the same prescribed shift. -/
noncomputable def current_reflectedPrescribedShiftLeftEndpointRows
    {rank qRight : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = 1 + (qRight + 2) - 1}
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
        (equation621LeftEndpointGeneratorIndex qRight hindex) hub target}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (equation621LeftEndpointGeneratorIndex qRight hindex)
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
        (equation621LeftEndpointGeneratorIndex qRight hindex).bridgeGlobalIndex).re)
    (hright : osiiVI2Unshift (qRight + 1) epsilon
      (equation621TargetRightParameter
        (equation621LeftEndpointGeneratorIndex qRight hindex)
        (w - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qRight + 1) + 1) sourceDepth sourceRank)) :
    let i := equation621LeftEndpointGeneratorIndex qRight hindex
    let v := w - osiiPositiveRealTimeEmbed C0.anchor
    let leftTime := equation621DampedReflectedStagePoint epsilon
      (reflectedChronologicalGapMap 0
        (Q.packet.rootedLeftBlockAnchor i, Q.packet.rootedLeftBlockAnchor i)) 0
    let rightTime := equation621DampedReflectedStagePoint epsilon
      (reflectedChronologicalGapMap (qRight + 1)
        (Q.packet.rootedRightBlockAnchor i, Q.packet.rootedRightBlockAnchor i))
      (equation621TargetRightParameter i v)
    SpatialApproximationRowsFactorizationData E.current
      (spatialApprox.equation621SplitTargetSpatialApproxIdentity i) w
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous 1
        ).distribution leftTime)
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous
        ((qRight + 1) + ((qRight + 1) + 1))).distribution rightTime)
      (spatialApprox.generatorLeftBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
      (spatialApprox.generatorRightBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
      (i.equation621TargetAdaptedSpatialSplitData d) := by
  dsimp only
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let H := Q.holomorphic.toContinuousTranslationData
  let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth D.adapted Q.packet Q.roots i (q := qRight) rfl
  let leftTest := fun x N =>
    RootedA0BlockContinuousTranslationData.targetAdaptedLeftBlockSpatialTest
      spatialApprox i x N
  let rightTest := fun x N =>
    RootedA0BlockContinuousTranslationData.targetAdaptedRightBlockSpatialTest
      spatialApprox i x N
  let leftField := fun x N scale =>
    H.leftArbitrarySpatialGeneratorField i scale (leftTest x N) 0
  let rightField := fun x N scale =>
    rootedReflectedGlobalLeftEndpointRightArbitraryField
      D.adapted Q.packet Q.roots H qRight hindex scale (rightTest x N)
      (equation621TargetRightParameter i v)
  let diagonal := fun x : OSHilbertSpace OS =>
    @inner Complex (OSHilbertSpace OS) _ x
      (osiiOriginalOSHilbertComplex OS (epsilon : Complex) x)
  let targetApprox := fun x N scale =>
    let y := equation621SplitTargetSpatialPoint i x
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe y N
    (rootedReflectedGramRootSmearedGlobalFamily
      S depth D.adapted lgc Q.packet Q.roots Q.holomorphic
    ).spatialHermiteScalarSum lgc
      ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
        (d := d) i).comp lift)
      i scale (generatorChronologicalParameterComplexCLE i v) chi
  have hradial :=
    RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain_any
      E w hw
  refine {
    targetApprox := targetApprox
    leftApprox := fun x N scale => diagonal (leftField x N scale)
    rightApprox := fun x N scale => diagonal (rightField x N scale)
    target_row_tendsto := ?_
    left_row_tendsto := ?_
    right_row_tendsto := ?_
    eventually_bound := ?_ }
  · intro x N
    simpa only [targetApprox,
      OSIIEquation621SpatialApproxIdentityData.smoothedStageValue] using
      current_reflectedAbsoluteProductTarget_row_tendsto_any
        E spatialApprox w hw x N
  · intro x N
    have hrow := H.tendsto_leftOneParticle_dampedDiagonal
      (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
        (OS := OS) previous)
      (qRight + 2) (by omega) hindex hepsilon (leftTest x N)
    have hprobe :
        (spatialApprox.generatorLeftBlockProductApproxIdentity i
          ).reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
            ((i.equation621TargetAdaptedSpatialSplitData d).leftPoint x) N =
          osiiMixedSpatialHeadMarginal (leftTest x N) (leftTest x N) := by
      simpa [leftTest, GeneratorIndex.equation621TargetAdaptedSpatialSplitData,
        RootedA0BlockContinuousTranslationData.targetAdaptedLeftBlockSpatialTest,
        RootedA0BlockContinuousTranslationData.generatorLeftBlockProbe_eq_positiveTargetTest]
        using spatialApprox.generatorLeftBlockMarginal_section43Probe_eq
          i (equation621SplitTargetSpatialPoint i x) N
    have hvalue := congrArg
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous 1
        ).distribution (equation621DampedReflectedStagePoint epsilon
          (reflectedChronologicalGapMap 0
            (Q.packet.rootedLeftBlockAnchor i, Q.packet.rootedLeftBlockAnchor i)) 0))
      hprobe
    exact hvalue.symm ▸ hrow
  · intro x N
    let block := spatialApprox.generatorRightBlockProductApproxIdentity i
    have hsource : forall scale chi,
        UniformCompactTimeSource.source (DRight.sourceCLM scale chi) =
          (Q.packet.rootedRightBlockApproximateIdentity Q.roots i
            ).translatedPositiveTimeSpatialSource
            (Q.packet.rootedRightBlockAnchor i)
            (Q.packet.rootedRightBlockAnchor_positive i) chi scale := by
      intro scale chi
      change UniformCompactTimeSource.source
        ((Q.packet.rootedRightBlockAnchoredSourceCLM Q.roots i scale) chi) = _
      exact Q.packet.rootedRightBlockAnchoredSourceCLM_source_translated
        Q.roots i scale chi
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
      apply eq_of_heq
      exact heq_of_eq (generatorRightBlockSpatialPoint_reflectedSelfPair
        (d := d) i (equation621SplitTargetSpatialPoint i x))
    rw [hpoint] at hrow
    have htest : block.toEquation621SpatialApproxIdentity.section43Probe
        (generatorRightBlockSpatialPoint d i (equation621SplitTargetSpatialPoint i x)) N =
          rightTest x N := by
      exact RootedA0BlockContinuousTranslationData.generatorRightBlockProbe_eq_positiveTargetTest
        spatialApprox i (equation621SplitTargetSpatialPoint i x) N
    apply (tendsto_congr' (Filter.Eventually.of_forall fun scale => ?_)).2 hrow
    apply congrArg diagonal
    exact congrArg (fun chi => DRight.reflectedGram.atlas.gram.anchoredAtlasField
      DRight.reflectedGram.atlas.sourceStage.stage
      DRight.reflectedGram.atlas.sourceStage.germ
      (DRight.sourceCLM (scale + H.commonTailStart i) chi)
      (equation621TargetRightParameter i v)) htest.symm
  · intro x N
    filter_upwards [] with scale
    have heq := rootedAbsoluteProductReflectedScalarSum_eq_leftEndpointCandidate_on_radial
      D.adapted Q.packet Q.roots Q.holomorphic lgc qRight hindex
      spatialApprox (equation621SplitTargetSpatialPoint i x) N scale v hradial
    have htarget : targetApprox x N scale =
        rootedReflectedGlobalLeftEndpointArbitraryCandidate
          D.adapted Q.packet Q.roots H lgc qRight hindex scale
            (leftTest x N) (rightTest x N)
            (generatorChronologicalParameterComplexCLE i v) := by
      exact heq
    have hleftZero : equation621TargetLeftParameter i v = 0 := by
      funext j
      exact Fin.elim0 j
    rw [htarget]
    simp only [rootedReflectedGlobalLeftEndpointArbitraryCandidate,
      rootedReflectedGlobalLeftEndpointRootSmearedRightArbitraryField,
      leftField, rightField, diagonal, hleftZero]
    change ‖generatorSemigroupCandidate OS lgc i
      (H.leftArbitrarySpatialGeneratorField i scale (leftTest x N))
      (fun z => (H.semigroupBridgeRootOperator lgc i scale)
        (rootedReflectedGlobalLeftEndpointRightArbitraryField
          D.adapted Q.packet Q.roots H qRight hindex scale (rightTest x N) z))
      (generatorChronologicalParameterComplexCLE i v)‖ <= _
    simpa only [hleftZero] using
      H.norm_generatorSemigroupCandidate_middleRoot_shift_le lgc i scale
      (H.leftArbitrarySpatialGeneratorField i scale (leftTest x N))
      (rootedReflectedGlobalLeftEndpointRightArbitraryField
        D.adapted Q.packet Q.roots H qRight hindex scale (rightTest x N))
      hepsilon v hbridge

set_option maxHeartbeats 3000000 in
/-- Right-endpoint companion, with the same actual predecessor and shift. -/
noncomputable def current_reflectedPrescribedShiftRightEndpointRows
    {rank qLeft : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = (qLeft + 2) + 1 - 1}
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
        (equation621RightEndpointGeneratorIndex qLeft hindex) hub target}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (equation621RightEndpointGeneratorIndex qLeft hindex)
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
        (equation621RightEndpointGeneratorIndex qLeft hindex).bridgeGlobalIndex).re)
    (hleft : osiiVI2Unshift (qLeft + 1) epsilon
      (equation621TargetLeftParameter
        (equation621RightEndpointGeneratorIndex qLeft hindex)
        (w - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qLeft + 1) + 1) sourceDepth sourceRank)) :
    let i := equation621RightEndpointGeneratorIndex qLeft hindex
    let v := w - osiiPositiveRealTimeEmbed C0.anchor
    let leftTime := equation621DampedReflectedStagePoint epsilon
      (reflectedChronologicalGapMap (qLeft + 1)
        (Q.packet.rootedLeftBlockAnchor i, Q.packet.rootedLeftBlockAnchor i))
      (equation621TargetLeftParameter i v)
    let rightTime := equation621DampedReflectedStagePoint epsilon
      (reflectedChronologicalGapMap 0
        (Q.packet.rootedRightBlockAnchor i, Q.packet.rootedRightBlockAnchor i)) 0
    SpatialApproximationRowsFactorizationData E.current
      (spatialApprox.equation621SplitTargetSpatialApproxIdentity i) w
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous
        ((qLeft + 1) + ((qLeft + 1) + 1))).distribution leftTime)
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous 1
        ).distribution rightTime)
      (spatialApprox.generatorLeftBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
      (spatialApprox.generatorRightBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
      (i.equation621TargetAdaptedSpatialSplitData d) := by
  dsimp only
  let i := equation621RightEndpointGeneratorIndex qLeft hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let H := Q.holomorphic.toContinuousTranslationData
  let DLeft := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth D.adapted Q.packet Q.roots i (q := qLeft) rfl
  let leftTest := fun x N =>
    RootedA0BlockContinuousTranslationData.targetAdaptedLeftBlockSpatialTest
      spatialApprox i x N
  let rightTest := fun x N =>
    RootedA0BlockContinuousTranslationData.targetAdaptedRightBlockSpatialTest
      spatialApprox i x N
  let leftField := fun x N scale =>
    rootedReflectedGlobalRightEndpointLeftArbitraryField
      D.adapted Q.packet Q.roots H qLeft hindex scale (leftTest x N)
      (equation621TargetLeftParameter i v)
  let rightField := fun x N scale =>
    H.rightArbitrarySpatialGeneratorField i scale (rightTest x N) 0
  let diagonal := fun x : OSHilbertSpace OS =>
    @inner Complex (OSHilbertSpace OS) _ x
      (osiiOriginalOSHilbertComplex OS (epsilon : Complex) x)
  let targetApprox := fun x N scale =>
    let y := equation621SplitTargetSpatialPoint i x
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe y N
    (rootedReflectedGramRootSmearedGlobalFamily
      S depth D.adapted lgc Q.packet Q.roots Q.holomorphic
    ).spatialHermiteScalarSum lgc
      ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
        (d := d) i).comp lift)
      i scale (generatorChronologicalParameterComplexCLE i v) chi
  have hradial :=
    RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain_any
      E w hw
  refine {
    targetApprox := targetApprox
    leftApprox := fun x N scale => diagonal (leftField x N scale)
    rightApprox := fun x N scale => diagonal (rightField x N scale)
    target_row_tendsto := ?_
    left_row_tendsto := ?_
    right_row_tendsto := ?_
    eventually_bound := ?_ }
  · intro x N
    simpa only [targetApprox,
      OSIIEquation621SpatialApproxIdentityData.smoothedStageValue] using
      current_reflectedAbsoluteProductTarget_row_tendsto_any
        E spatialApprox w hw x N
  · intro x N
    let block := spatialApprox.generatorLeftBlockProductApproxIdentity i
    have hsource : forall scale chi,
        UniformCompactTimeSource.source (DLeft.sourceCLM scale chi) =
          (Q.packet.rootedLeftBlockApproximateIdentity Q.roots i
            ).translatedPositiveTimeSpatialSource
            (Q.packet.rootedLeftBlockAnchor i)
            (Q.packet.rootedLeftBlockAnchor_positive i) chi scale := by
      intro scale chi
      change UniformCompactTimeSource.source
        ((Q.packet.rootedLeftBlockAnchoredSourceCLM Q.roots i scale) chi) = _
      exact Q.packet.rootedLeftBlockAnchoredSourceCLM_source_translated
        Q.roots i scale chi
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
      apply eq_of_heq
      exact heq_of_eq (generatorLeftBlockSpatialPoint_reflectedSelfPair
        (d := d) i (equation621SplitTargetSpatialPoint i x))
    rw [hpoint] at hrow
    have htest : block.toEquation621SpatialApproxIdentity.section43Probe
        (generatorLeftBlockSpatialPoint d i (equation621SplitTargetSpatialPoint i x)) N =
          leftTest x N := by
      exact RootedA0BlockContinuousTranslationData.generatorLeftBlockProbe_eq_positiveTargetTest
        spatialApprox i (equation621SplitTargetSpatialPoint i x) N
    apply (tendsto_congr' (Filter.Eventually.of_forall fun scale => ?_)).2 hrow
    apply congrArg diagonal
    exact congrArg (fun chi => DLeft.reflectedGram.atlas.gram.anchoredAtlasField
      DLeft.reflectedGram.atlas.sourceStage.stage
      DLeft.reflectedGram.atlas.sourceStage.germ
      (DLeft.sourceCLM (scale + H.commonTailStart i) chi)
      (equation621TargetLeftParameter i v)) htest.symm
  · intro x N
    have hrow := H.tendsto_rightOneParticle_dampedDiagonal
      (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
        (OS := OS) previous)
      (qLeft + 2) (by omega) hindex hepsilon (rightTest x N)
    have hprobe :
        (spatialApprox.generatorRightBlockProductApproxIdentity i
          ).reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
            ((i.equation621TargetAdaptedSpatialSplitData d).rightPoint x) N =
          osiiMixedSpatialHeadMarginal (rightTest x N) (rightTest x N) := by
      simpa [rightTest, GeneratorIndex.equation621TargetAdaptedSpatialSplitData,
        RootedA0BlockContinuousTranslationData.targetAdaptedRightBlockSpatialTest,
        RootedA0BlockContinuousTranslationData.generatorRightBlockProbe_eq_positiveTargetTest]
        using spatialApprox.generatorRightBlockMarginal_section43Probe_eq
          i (equation621SplitTargetSpatialPoint i x) N
    have hvalue := congrArg
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous 1
        ).distribution (equation621DampedReflectedStagePoint epsilon
          (reflectedChronologicalGapMap 0
            (Q.packet.rootedRightBlockAnchor i, Q.packet.rootedRightBlockAnchor i)) 0))
      hprobe
    exact hvalue.symm ▸ hrow
  · intro x N
    filter_upwards [] with scale
    have heq := rootedAbsoluteProductReflectedScalarSum_eq_rightEndpointCandidate_on_radial
      D.adapted Q.packet Q.roots Q.holomorphic lgc qLeft hindex
      spatialApprox (equation621SplitTargetSpatialPoint i x) N scale v hradial
    have htarget : targetApprox x N scale =
        rootedReflectedGlobalRightEndpointArbitraryCandidate
          D.adapted Q.packet Q.roots H lgc qLeft hindex scale
            (leftTest x N) (rightTest x N)
            (generatorChronologicalParameterComplexCLE i v) := by
      exact heq
    have hrightZero : equation621TargetRightParameter i v = 0 := by
      funext j
      exact Fin.elim0 j
    rw [htarget]
    simp only [rootedReflectedGlobalRightEndpointArbitraryCandidate,
      RootedA0BlockContinuousTranslationData.rootSmearedRightArbitrarySpatialGeneratorField,
      leftField, rightField, diagonal, hrightZero]
    change ‖generatorSemigroupCandidate OS lgc i
      (rootedReflectedGlobalRightEndpointLeftArbitraryField
        D.adapted Q.packet Q.roots H qLeft hindex scale (leftTest x N))
      (fun z => (H.semigroupBridgeRootOperator lgc i scale)
        (H.rightArbitrarySpatialGeneratorField i scale (rightTest x N) z))
      (generatorChronologicalParameterComplexCLE i v)‖ <= _
    simpa only [hrightZero] using
      H.norm_generatorSemigroupCandidate_middleRoot_shift_le lgc i scale
      (rootedReflectedGlobalRightEndpointLeftArbitraryField
        D.adapted Q.packet Q.roots H qLeft hindex scale (leftTest x N))
      (H.rightArbitrarySpatialGeneratorField i scale (rightTest x N))
      hepsilon v hbridge

set_option maxHeartbeats 3000000 in
/-- The actual left-endpoint source rows give the next-depth normalized
estimate with exactly the raw predecessor's coefficient. -/
theorem norm_current_leftEndpoint_le_of_rawPredecessor_prescribedShift
    {rank qRight : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = 1 + (qRight + 2) - 1}
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
        (equation621LeftEndpointGeneratorIndex qRight hindex) hub target}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (equation621LeftEndpointGeneratorIndex qRight hindex)
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
        (equation621LeftEndpointGeneratorIndex qRight hindex).bridgeGlobalIndex).re)
    (hright : osiiVI2Unshift (qRight + 1) epsilon
      (equation621TargetRightParameter
        (equation621LeftEndpointGeneratorIndex qRight hindex)
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
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let leftBase := reflectedCauchyShiftedStagePoint
    (reflectedChronologicalGapMap 0
      (Q.packet.rootedLeftBlockAnchor
        (equation621LeftEndpointGeneratorIndex qRight hindex),
       Q.packet.rootedLeftBlockAnchor
        (equation621LeftEndpointGeneratorIndex qRight hindex)))
    (osiiVI2Unshift 0 epsilon 0)
  let rightBase := reflectedCauchyShiftedStagePoint
    (reflectedChronologicalGapMap (qRight + 1)
      (Q.packet.rootedRightBlockAnchor
        (equation621LeftEndpointGeneratorIndex qRight hindex),
       Q.packet.rootedRightBlockAnchor
        (equation621LeftEndpointGeneratorIndex qRight hindex)))
    (osiiVI2Unshift (qRight + 1) epsilon
      (equation621TargetRightParameter
        (equation621LeftEndpointGeneratorIndex qRight hindex) v))
  have hleftPoint : leftBase ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase 1 sourceDepth) :=
    reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier_all
      (reflectedChronologicalGapMap_mem_strictPositive_all _ _
        (Q.packet.rootedLeftBlockAnchor_positive i)
        (Q.packet.rootedLeftBlockAnchor_positive i))
      (emptyTail_mem_rawStrictGeneratedMixed sourceDepth _)
  have hrightPoint : rightBase ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase
        ((qRight + 1) + ((qRight + 1) + 1)) sourceDepth) :=
    reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier_all
      (reflectedChronologicalGapMap_mem_strictPositive_all _ _
        (Q.packet.rootedRightBlockAnchor_positive i)
        (Q.packet.rootedRightBlockAnchor_positive i)) hright
  obtain ⟨sourceRank, hrightRank⟩ :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.exists_rank hright.2.toStrictGenerated
  let P := canonicalRawPredecessorReflectedGramRankData
    initial lgc sourceDepth sourceRank
  let rows := current_reflectedPrescribedShiftLeftEndpointRows E P spatialApprox
    w hw hepsilon hbridge ⟨hright.1, hrightRank⟩
  have hbridge' : C0.anchor i.bridgeGlobalIndex + epsilon <=
      (w i.bridgeGlobalIndex).re := by
    have h : epsilon < (w i.bridgeGlobalIndex).re - C0.anchor i.bridgeGlobalIndex := by
      simpa [i, osiiPositiveRealTimeEmbed] using hbridge
    linarith
  have hleftZero : equation621TargetLeftParameter i v = 0 := by
    funext j
    exact Fin.elim0 j
  have hleftTargetZero : rootedLeftBlockTarget
      (equation621LeftEndpointGeneratorIndex qRight hindex)
      (w - osiiPositiveRealTimeEmbed C0.anchor) = 0 := by
    funext j
    exact Fin.elim0 j
  have hempty : (![] : Fin 0 -> Complex) = 0 := by
    funext j
    exact Fin.elim0 j
  have hn : i.n - 1 = 0 := by
    change 1 - 1 = 0
    omega
  have hm : i.m - 1 = qRight + 1 := by
    change qRight + 2 - 1 = qRight + 1
    omega
  dsimp only [i] at *
  have hsplit : OSIIEquation621TimeAverageSplitCondition
      (osiiVI2Shift 1 epsilon leftBase)
      (osiiVI2Shift ((qRight + 1) + ((qRight + 1) + 1)) epsilon rightBase) w := by
    convert equation621DampedTargetTimePoints_timeAverageSplitCondition
      Q.packet (equation621LeftEndpointGeneratorIndex qRight hindex) w
        hepsilon.le hcentered hbridge' using 1 <;>
      simp [v, leftBase, rightBase, equation621DampedReflectedStagePoint,
        equation621LeftEndpointGeneratorIndex, hn, hm, hleftZero]
    all_goals first
      | (change 1 = (1 - 1) + (1 - 1 + 1); omega)
      | (change qRight + 1 + (qRight + 1 + 1) =
          (k - (1 - 1) - 1) + (k - (1 - 1) - 1 + 1); omega)
      | omega
      | (apply congrArg (osiiVI2Shift 1 epsilon)
         apply congrArg (reflectedCauchyShiftedStagePoint _)
         funext j
         exact Fin.elim0 j)
  apply norm_distribution_le_of_rawPredecessor_prescribedShiftRows
    (targetProbe := spatialApprox.equation621SplitTargetSpatialApproxIdentity i)
    (leftProbe := (spatialApprox.generatorLeftBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity)
    (rightProbe := (spatialApprox.generatorRightBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity)
    (split := i.equation621TargetAdaptedSpatialSplitData d)
    B hepsilon hleftPoint hrightPoint _ hsplit (by omega) chi
  have hstage (arity : Nat) :
      CanonicalGeneratorStageLevelProvider.stage (OS := OS)
        (initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
          lgc sourceDepth).pointed arity =
        (initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
          lgc sourceDepth).pointed.stageLevel.stage arity := rfl
  convert rows using 1 <;>
    simp [P, i, v, leftBase, rightBase, equation621DampedReflectedStagePoint,
      InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder,
      StrictGeneratedScalarDepthPointedData.toTimeContinuationLadder,
      timeContinuationLadderOfAngleSectorCover, hstage] <;>
    try { apply propext; constructor <;> intro h <;> exact h }

set_option maxHeartbeats 3000000 in
/-- The right-endpoint estimate preserves the same raw predecessor
coefficient and uses exactly one next-depth factor. -/
theorem norm_current_rightEndpoint_le_of_rawPredecessor_prescribedShift
    {rank qLeft : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = (qLeft + 2) + 1 - 1}
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
        (equation621RightEndpointGeneratorIndex qLeft hindex) hub target}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (equation621RightEndpointGeneratorIndex qLeft hindex)
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
        (equation621RightEndpointGeneratorIndex qLeft hindex).bridgeGlobalIndex).re)
    (hleft : osiiVI2Unshift (qLeft + 1) epsilon
      (equation621TargetLeftParameter
        (equation621RightEndpointGeneratorIndex qLeft hindex)
        (w - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase
          ((qLeft + 1) + 1) sourceDepth))
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖E.current.extension.toTimeContinuationStage.distribution w chi‖ <=
      (osiiVI2ArityDepthMajorant B.alpha beta k (sourceDepth + 1) *
        osiiSpatialPolynomialWeightedL1 (k * t)
          (section43SpatialFlatSchwartzCLE d k chi)) *
        ‖osiiVI2Equation621Denormalization t k epsilon w‖ := by
  let i := equation621RightEndpointGeneratorIndex qLeft hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let leftBase := reflectedCauchyShiftedStagePoint
    (reflectedChronologicalGapMap (qLeft + 1)
      (Q.packet.rootedLeftBlockAnchor
        (equation621RightEndpointGeneratorIndex qLeft hindex),
       Q.packet.rootedLeftBlockAnchor
        (equation621RightEndpointGeneratorIndex qLeft hindex)))
    (osiiVI2Unshift (qLeft + 1) epsilon
      (equation621TargetLeftParameter
        (equation621RightEndpointGeneratorIndex qLeft hindex) v))
  let rightBase := reflectedCauchyShiftedStagePoint
    (reflectedChronologicalGapMap 0
      (Q.packet.rootedRightBlockAnchor
        (equation621RightEndpointGeneratorIndex qLeft hindex),
       Q.packet.rootedRightBlockAnchor
        (equation621RightEndpointGeneratorIndex qLeft hindex)))
    (osiiVI2Unshift 0 epsilon 0)
  have hleftPoint : leftBase ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase
        ((qLeft + 1) + ((qLeft + 1) + 1)) sourceDepth) :=
    reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier_all
      (reflectedChronologicalGapMap_mem_strictPositive_all _ _
        (Q.packet.rootedLeftBlockAnchor_positive i)
        (Q.packet.rootedLeftBlockAnchor_positive i)) hleft
  have hrightPoint : rightBase ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase 1 sourceDepth) :=
    reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier_all
      (reflectedChronologicalGapMap_mem_strictPositive_all _ _
        (Q.packet.rootedRightBlockAnchor_positive i)
        (Q.packet.rootedRightBlockAnchor_positive i))
      (emptyTail_mem_rawStrictGeneratedMixed sourceDepth _)
  obtain ⟨sourceRank, hleftRank⟩ :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.exists_rank hleft.2.toStrictGenerated
  let P := canonicalRawPredecessorReflectedGramRankData
    initial lgc sourceDepth sourceRank
  let rows := current_reflectedPrescribedShiftRightEndpointRows E P spatialApprox
    w hw hepsilon hbridge ⟨hleft.1, hleftRank⟩
  have hbridge' : C0.anchor i.bridgeGlobalIndex + epsilon <=
      (w i.bridgeGlobalIndex).re := by
    have h : epsilon < (w i.bridgeGlobalIndex).re - C0.anchor i.bridgeGlobalIndex := by
      simpa [i, osiiPositiveRealTimeEmbed] using hbridge
    linarith
  have hrightZero : equation621TargetRightParameter i v = 0 := by
    funext j
    exact Fin.elim0 j
  have hrightTargetZero : rootedRightBlockTarget
      (equation621RightEndpointGeneratorIndex qLeft hindex)
      (w - osiiPositiveRealTimeEmbed C0.anchor) = 0 := by
    funext j
    exact Fin.elim0 j
  have hempty : (![] : Fin 0 -> Complex) = 0 := by
    funext j
    exact Fin.elim0 j
  have hn : i.n - 1 = qLeft + 1 := by
    change qLeft + 2 - 1 = qLeft + 1
    omega
  have hm : i.m - 1 = 0 := by
    change 1 - 1 = 0
    omega
  dsimp only [i] at *
  have hsplit : OSIIEquation621TimeAverageSplitCondition
      (osiiVI2Shift ((qLeft + 1) + ((qLeft + 1) + 1)) epsilon leftBase)
      (osiiVI2Shift 1 epsilon rightBase) w := by
    convert equation621DampedTargetTimePoints_timeAverageSplitCondition
      Q.packet (equation621RightEndpointGeneratorIndex qLeft hindex) w
        hepsilon.le hcentered hbridge' using 1 <;>
      simp [v, leftBase, rightBase, equation621DampedReflectedStagePoint,
        equation621RightEndpointGeneratorIndex, hn, hm, hrightZero]
    all_goals first
      | (change 1 = (1 - 1) + (1 - 1 + 1); omega)
      | (change qLeft + 1 + (qLeft + 1 + 1) =
          (qLeft + 2 - 1) + (qLeft + 2 - 1 + 1); omega)
      | (change 1 = (k - (qLeft + 2 - 1) - 1) +
          (k - (qLeft + 2 - 1) - 1 + 1); omega)
      | omega
      | (apply congrArg (osiiVI2Shift 1 epsilon)
         apply congrArg (reflectedCauchyShiftedStagePoint _)
         funext j
         exact Fin.elim0 j)
  apply norm_distribution_le_of_rawPredecessor_prescribedShiftRows
    (targetProbe := spatialApprox.equation621SplitTargetSpatialApproxIdentity i)
    (leftProbe := (spatialApprox.generatorLeftBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity)
    (rightProbe := (spatialApprox.generatorRightBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity)
    (split := i.equation621TargetAdaptedSpatialSplitData d)
    B hepsilon hleftPoint hrightPoint _ hsplit (by omega) chi
  have hstage (arity : Nat) :
      CanonicalGeneratorStageLevelProvider.stage (OS := OS)
        (initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
          lgc sourceDepth).pointed arity =
        (initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
          lgc sourceDepth).pointed.stageLevel.stage arity := rfl
  convert rows using 1 <;>
    simp [P, i, v, leftBase, rightBase, equation621DampedReflectedStagePoint,
      InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder,
      StrictGeneratedScalarDepthPointedData.toTimeContinuationLadder,
      timeContinuationLadderOfAngleSectorCover, hstage] <;>
    try { apply propext; constructor <;> intro h <;> exact h }

set_option maxHeartbeats 3000000 in
/-- At the one-gap corner both lower rows are actual one-particle sources. -/
noncomputable def current_reflectedPrescribedShiftTwoPointRows
    {rank : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = 1 + 1 - 1}
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
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k) hub target}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k)
        hub atlas target C0 Q D)
    {Previous : Type*} [CanonicalGeneratorStageLevelProvider OS Previous]
    (previous : Previous)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hbridge : epsilon <
      ((w - osiiPositiveRealTimeEmbed C0.anchor)
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k).bridgeGlobalIndex).re) :
    let i : GeneratorIndex k := ⟨1, 1, le_rfl, le_rfl, hindex⟩
    let leftTime := equation621DampedReflectedStagePoint epsilon
      (reflectedChronologicalGapMap 0
        (Q.packet.rootedLeftBlockAnchor i, Q.packet.rootedLeftBlockAnchor i)) 0
    let rightTime := equation621DampedReflectedStagePoint epsilon
      (reflectedChronologicalGapMap 0
        (Q.packet.rootedRightBlockAnchor i, Q.packet.rootedRightBlockAnchor i)) 0
    SpatialApproximationRowsFactorizationData E.current
      (spatialApprox.equation621SplitTargetSpatialApproxIdentity i) w
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous 1
        ).distribution leftTime)
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous 1
        ).distribution rightTime)
      (spatialApprox.generatorLeftBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
      (spatialApprox.generatorRightBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
      (i.equation621TargetAdaptedSpatialSplitData d) := by
  dsimp only
  let i : GeneratorIndex k := ⟨1, 1, le_rfl, le_rfl, hindex⟩
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let H := Q.holomorphic.toContinuousTranslationData
  let leftTest := fun x N =>
    RootedA0BlockContinuousTranslationData.targetAdaptedLeftBlockSpatialTest
      spatialApprox i x N
  let rightTest := fun x N =>
    RootedA0BlockContinuousTranslationData.targetAdaptedRightBlockSpatialTest
      spatialApprox i x N
  let leftField := fun x N scale =>
    H.leftArbitrarySpatialGeneratorField i scale (leftTest x N) 0
  let rightField := fun x N scale =>
    H.rightArbitrarySpatialGeneratorField i scale (rightTest x N) 0
  let diagonal := fun x : OSHilbertSpace OS =>
    @inner Complex (OSHilbertSpace OS) _ x
      (osiiOriginalOSHilbertComplex OS (epsilon : Complex) x)
  let targetApprox := fun x N scale =>
    let y := equation621SplitTargetSpatialPoint i x
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe y N
    (rootedReflectedGramRootSmearedGlobalFamily
      S depth D.adapted lgc Q.packet Q.roots Q.holomorphic
    ).spatialHermiteScalarSum lgc
      ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
        (d := d) i).comp lift)
      i scale (generatorChronologicalParameterComplexCLE i v) chi
  have hradial :=
    RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain_any
      E w hw
  refine {
    targetApprox := targetApprox
    leftApprox := fun x N scale => diagonal (leftField x N scale)
    rightApprox := fun x N scale => diagonal (rightField x N scale)
    target_row_tendsto := ?_
    left_row_tendsto := ?_
    right_row_tendsto := ?_
    eventually_bound := ?_ }
  · intro x N
    simpa only [targetApprox,
      OSIIEquation621SpatialApproxIdentityData.smoothedStageValue] using
      current_reflectedAbsoluteProductTarget_row_tendsto_any
        E spatialApprox w hw x N
  · intro x N
    have hrow := H.tendsto_leftOneParticle_dampedDiagonal
      (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
        (OS := OS) previous) 1 le_rfl hindex hepsilon (leftTest x N)
    have hprobe :
        (spatialApprox.generatorLeftBlockProductApproxIdentity i
          ).reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
            ((i.equation621TargetAdaptedSpatialSplitData d).leftPoint x) N =
          osiiMixedSpatialHeadMarginal (leftTest x N) (leftTest x N) := by
      simpa [leftTest, GeneratorIndex.equation621TargetAdaptedSpatialSplitData,
        RootedA0BlockContinuousTranslationData.targetAdaptedLeftBlockSpatialTest,
        RootedA0BlockContinuousTranslationData.generatorLeftBlockProbe_eq_positiveTargetTest]
        using spatialApprox.generatorLeftBlockMarginal_section43Probe_eq
          i (equation621SplitTargetSpatialPoint i x) N
    have hvalue := congrArg
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous 1
        ).distribution (equation621DampedReflectedStagePoint epsilon
          (reflectedChronologicalGapMap 0
            (Q.packet.rootedLeftBlockAnchor i, Q.packet.rootedLeftBlockAnchor i)) 0))
      hprobe
    exact hvalue.symm ▸ hrow
  · intro x N
    have hrow := H.tendsto_rightOneParticle_dampedDiagonal
      (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
        (OS := OS) previous) 1 le_rfl hindex hepsilon (rightTest x N)
    have hprobe :
        (spatialApprox.generatorRightBlockProductApproxIdentity i
          ).reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
            ((i.equation621TargetAdaptedSpatialSplitData d).rightPoint x) N =
          osiiMixedSpatialHeadMarginal (rightTest x N) (rightTest x N) := by
      simpa [rightTest, GeneratorIndex.equation621TargetAdaptedSpatialSplitData,
        RootedA0BlockContinuousTranslationData.targetAdaptedRightBlockSpatialTest,
        RootedA0BlockContinuousTranslationData.generatorRightBlockProbe_eq_positiveTargetTest]
        using spatialApprox.generatorRightBlockMarginal_section43Probe_eq
          i (equation621SplitTargetSpatialPoint i x) N
    have hvalue := congrArg
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous 1
        ).distribution (equation621DampedReflectedStagePoint epsilon
          (reflectedChronologicalGapMap 0
            (Q.packet.rootedRightBlockAnchor i, Q.packet.rootedRightBlockAnchor i)) 0))
      hprobe
    exact hvalue.symm ▸ hrow
  · intro x N
    filter_upwards [] with scale
    have heq :=
      RootedA0BlockContinuousTranslationData.rootedAbsoluteProductReflectedScalarSum_eq_twoPointCandidate_on_radial
        D.adapted Q.packet Q.roots Q.holomorphic lgc hindex
        spatialApprox (equation621SplitTargetSpatialPoint i x) N scale v hradial
    have htarget : targetApprox x N scale =
        H.rootSmearedArbitrarySpatialGeneratorCandidate lgc i scale
          (leftTest x N) (rightTest x N)
          (generatorChronologicalParameterComplexCLE i v) := by
      simpa [leftTest, rightTest,
        RootedA0BlockContinuousTranslationData.targetAdaptedLeftBlockSpatialTest,
        RootedA0BlockContinuousTranslationData.targetAdaptedRightBlockSpatialTest,
        RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest, i] using heq
    have hleftZero : equation621TargetLeftParameter i v = 0 := by
      funext j
      exact Fin.elim0 j
    have hrightZero : equation621TargetRightParameter i v = 0 := by
      funext j
      exact Fin.elim0 j
    rw [htarget]
    simp only [RootedA0BlockContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate,
      RootedA0BlockContinuousTranslationData.rootSmearedRightArbitrarySpatialGeneratorField,
      leftField, rightField, diagonal, hleftZero, hrightZero]
    change ‖generatorSemigroupCandidate OS lgc i
      (H.leftArbitrarySpatialGeneratorField i scale (leftTest x N))
      (fun z => (H.semigroupBridgeRootOperator lgc i scale)
        (H.rightArbitrarySpatialGeneratorField i scale (rightTest x N) z))
      (generatorChronologicalParameterComplexCLE i v)‖ <= _
    simpa only [hleftZero, hrightZero] using
      H.norm_generatorSemigroupCandidate_middleRoot_shift_le lgc i scale
      (H.leftArbitrarySpatialGeneratorField i scale (leftTest x N))
      (H.rightArbitrarySpatialGeneratorField i scale (rightTest x N))
      hepsilon v hbridge

set_option maxHeartbeats 3000000 in
/-- The one-gap generator needs only the two actual positive-real
predecessors; its normalized coefficient is unchanged. -/
theorem norm_current_twoPoint_le_of_rawPredecessor_prescribedShift
    {rank : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = 1 + 1 - 1}
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
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k) hub target}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k)
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
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k).bridgeGlobalIndex).re)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖E.current.extension.toTimeContinuationStage.distribution w chi‖ <=
      (osiiVI2ArityDepthMajorant B.alpha beta k (sourceDepth + 1) *
        osiiSpatialPolynomialWeightedL1 (k * t)
          (section43SpatialFlatSchwartzCLE d k chi)) *
        ‖osiiVI2Equation621Denormalization t k epsilon w‖ := by
  let i : GeneratorIndex k := ⟨1, 1, le_rfl, le_rfl, hindex⟩
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let leftBase := reflectedCauchyShiftedStagePoint
    (reflectedChronologicalGapMap 0
      (Q.packet.rootedLeftBlockAnchor
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k),
       Q.packet.rootedLeftBlockAnchor
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k)))
    (osiiVI2Unshift 0 epsilon 0)
  let rightBase := reflectedCauchyShiftedStagePoint
    (reflectedChronologicalGapMap 0
      (Q.packet.rootedRightBlockAnchor
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k),
       Q.packet.rootedRightBlockAnchor
        (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k)))
    (osiiVI2Unshift 0 epsilon 0)
  have hleftPoint : leftBase ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase 1 sourceDepth) :=
    reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier_all
      (reflectedChronologicalGapMap_mem_strictPositive_all _ _
        (Q.packet.rootedLeftBlockAnchor_positive i)
        (Q.packet.rootedLeftBlockAnchor_positive i))
      (emptyTail_mem_rawStrictGeneratedMixed sourceDepth _)
  have hrightPoint : rightBase ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase 1 sourceDepth) :=
    reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier_all
      (reflectedChronologicalGapMap_mem_strictPositive_all _ _
        (Q.packet.rootedRightBlockAnchor_positive i)
        (Q.packet.rootedRightBlockAnchor_positive i))
      (emptyTail_mem_rawStrictGeneratedMixed sourceDepth _)
  let previous := initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
    lgc sourceDepth
  let rows := current_reflectedPrescribedShiftTwoPointRows E previous.pointed
    spatialApprox w hw hepsilon hbridge
  have hbridge' : C0.anchor i.bridgeGlobalIndex + epsilon <=
      (w i.bridgeGlobalIndex).re := by
    have h : epsilon < (w i.bridgeGlobalIndex).re - C0.anchor i.bridgeGlobalIndex := by
      simpa [i, osiiPositiveRealTimeEmbed] using hbridge
    linarith
  have hleftZero : equation621TargetLeftParameter i v = 0 := by
    funext j
    exact Fin.elim0 j
  have hrightZero : equation621TargetRightParameter i v = 0 := by
    funext j
    exact Fin.elim0 j
  have hleftTargetZero : rootedLeftBlockTarget
      (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k)
      (w - osiiPositiveRealTimeEmbed C0.anchor) = 0 := by
    funext j
    exact Fin.elim0 j
  have hrightTargetZero : rootedRightBlockTarget
      (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k)
      (w - osiiPositiveRealTimeEmbed C0.anchor) = 0 := by
    funext j
    exact Fin.elim0 j
  have hempty : (![] : Fin 0 -> Complex) = 0 := by
    funext j
    exact Fin.elim0 j
  have hn : i.n - 1 = 0 := by
    change 1 - 1 = 0
    omega
  have hm : i.m - 1 = 0 := by
    change 1 - 1 = 0
    omega
  dsimp only [i] at *
  have hsplit : OSIIEquation621TimeAverageSplitCondition
      (osiiVI2Shift 1 epsilon leftBase) (osiiVI2Shift 1 epsilon rightBase) w := by
    convert equation621DampedTargetTimePoints_timeAverageSplitCondition
      Q.packet (⟨1, 1, le_rfl, le_rfl, hindex⟩ : GeneratorIndex k) w
        hepsilon.le hcentered hbridge' using 1 <;>
      simp [v, leftBase, rightBase, equation621DampedReflectedStagePoint,
        hn, hm, hleftZero, hrightZero]
    all_goals first
      | (change 1 = (1 - 1) + (1 - 1 + 1); omega)
      | (change 1 = (k - (1 - 1) - 1) + (k - (1 - 1) - 1 + 1); omega)
      | omega
      | (apply congrArg (osiiVI2Shift 1 epsilon)
         apply congrArg (reflectedCauchyShiftedStagePoint _)
         funext j
         exact Fin.elim0 j)
  apply norm_distribution_le_of_rawPredecessor_prescribedShiftRows
    (targetProbe := spatialApprox.equation621SplitTargetSpatialApproxIdentity i)
    (leftProbe := (spatialApprox.generatorLeftBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity)
    (rightProbe := (spatialApprox.generatorRightBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity)
    (split := i.equation621TargetAdaptedSpatialSplitData d)
    B hepsilon hleftPoint hrightPoint _ hsplit (by omega) chi
  have hstage (arity : Nat) :
      CanonicalGeneratorStageLevelProvider.stage (OS := OS) previous.pointed arity =
        previous.pointed.stageLevel.stage arity := rfl
  convert rows using 1 <;>
    simp [previous, i, v, leftBase, rightBase, equation621DampedReflectedStagePoint,
      InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder,
      StrictGeneratedScalarDepthPointedData.toTimeContinuationLadder,
      timeContinuationLadderOfAngleSectorCover, hstage] <;>
    try { apply propext; constructor <;> intro h <;> exact h }

set_option maxHeartbeats 3000000 in
/-- Every genuine rooted generator split satisfies the prescribed-shift
estimate from the same raw predecessor. The endpoint cases do not change its
coefficient, arity rate, or outer-depth budget. -/
theorem norm_current_allSplits_le_of_rawPredecessor_prescribedShift
    {rank : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k}
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
        Q.holomorphic.toContinuousTranslationData i hub target}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc i hub atlas target C0 Q D)
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {t beta sourceDepth : Nat}
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta sourceDepth)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hcentered : w - osiiPositiveRealTimeEmbed C0.anchor ∈ osiiTimeRightHalfPlane k)
    (hbridge : epsilon <
      ((w - osiiPositiveRealTimeEmbed C0.anchor) i.bridgeGlobalIndex).re)
    (hleft : osiiVI2Unshift (i.n - 1) epsilon
      (equation621TargetLeftParameter i (w - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase ((i.n - 1) + 1) sourceDepth))
    (hright : osiiVI2Unshift (i.m - 1) epsilon
      (equation621TargetRightParameter i (w - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase ((i.m - 1) + 1) sourceDepth))
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖E.current.extension.toTimeContinuationStage.distribution w chi‖ <=
      (osiiVI2ArityDepthMajorant B.alpha beta k (sourceDepth + 1) *
        osiiSpatialPolynomialWeightedL1 (k * t)
          (section43SpatialFlatSchwartzCLE d k chi)) *
        ‖osiiVI2Equation621Denormalization t k epsilon w‖ := by
  rcases i with ⟨n, m, hn, hm, hindex⟩
  cases n with
  | zero => omega
  | succ n =>
    cases m with
    | zero => omega
    | succ m =>
      cases n with
      | zero =>
        cases m with
        | zero =>
          exact norm_current_twoPoint_le_of_rawPredecessor_prescribedShift
            E B spatialApprox w hw hepsilon hcentered hbridge chi
        | succ qRight =>
          exact norm_current_leftEndpoint_le_of_rawPredecessor_prescribedShift
            E B spatialApprox w hw hepsilon hcentered hbridge hright chi
      | succ qLeft =>
        cases m with
        | zero =>
          exact norm_current_rightEndpoint_le_of_rawPredecessor_prescribedShift
            E B spatialApprox w hw hepsilon hcentered hbridge hleft chi
        | succ qRight =>
          exact norm_current_distribution_le_of_rawPredecessor_prescribedShift
            E B spatialApprox w hw hepsilon hcentered hbridge hleft hright chi

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
