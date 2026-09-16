/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedProductRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedProbeRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedSourceAnchorCutoff
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedFactorization










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
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}

theorem current_reflectedLeftDiagonal_row_tendsto
    {rank qLeft qRight : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = (qLeft + 2) + (qRight + 2) - 1}
    {hub : Fin k -> Real}
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {z : OSIITimeGapSpace k}
    {C0 : TargetHubHalfAnchorData hub z}
    {Q : AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth RankP.toAtlasFamily lgc C0.anchor}
    {D : RootedTargetHubAdaptedReflectedGramData
      S depth RankP.toAtlasFamily Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData
        (equation621NontrivialGeneratorIndex qLeft qRight hindex) hub z}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        hub atlas z C0 Q D)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier)
    (x : Fin (k * d) -> Real) (N : Nat) :
    let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
    let v := w - osiiPositiveRealTimeEmbed C0.anchor
    let y := equation621SplitTargetSpatialPoint i x
    let DLeft := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth D.adapted Q.packet Q.roots i (q := qLeft) rfl
    let leftProbe :=
      (spatialApprox.generatorLeftBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
    Tendsto
      (fun scale =>
        rootedReflectedGlobalProductLeftDiagonal D.adapted Q.packet Q.roots
          Q.holomorphic.toContinuousTranslationData qLeft qRight hindex
          scale
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
            spatialApprox i y N)
          (equation621TargetLeftParameter i v))
      atTop
      (nhds (DLeft.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621ReflectedMovingSlicePoint
          (reflectedCauchyCenter (equation621TargetLeftParameter i v))
          (osiiMixedBlockGlobalReducedTime (qLeft + 1)
            (Fin.append (Q.packet.rootedLeftBlockAnchor i)
              (Q.packet.rootedLeftBlockAnchor i))))
        (leftProbe.section43Probe
          ((i.equation621TargetAdaptedSpatialSplitData d).leftPoint x) N))) := by
  dsimp only
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let y := equation621SplitTargetSpatialPoint i x
  let DLeft := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth D.adapted Q.packet Q.roots i (q := qLeft) rfl
  have hradial :=
    RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain
      E w hw
  have hzLeft : equation621TargetLeftParameter i v ∈
      DLeft.reflectedGram.atlas.spatialLinearDomain := by
    have hleft := hradial.2.1
    change equation621TargetLeftParameter i v ∈
      openZeroConvexKernel DLeft.reflectedGram.atlas.spatialLinearDomain at hleft
    rcases hleft with ⟨V, _hVOpen, _hVConvex, _hzero, hV, hzV⟩
    exact hV hzV
  have hcutoff : DLeft.reflectedGram.atlas.sourceStage.germ.η
      (osiiMixedBlockGlobalReducedTime (qLeft + 1)
        (Fin.append (Q.packet.rootedLeftBlockAnchor i)
          (Q.packet.rootedLeftBlockAnchor i))) = 1 := by
    simpa [i, DLeft, equation621NontrivialGeneratorIndex] using
      rootedLeftNontrivialReflectedGram_cutoff_eq_one
        D.adapted Q.packet Q.roots qLeft (qRight + 2)
          i.hn i.hm i.hnm
  have hrow :=
    tendsto_rootedLeftNontrivialDiagonalScalar_to_distribution_generatorProbe_adapted
      D.adapted Q.packet Q.roots qLeft (qRight + 2)
      i.hn i.hm i.hnm spatialApprox x N
      (equation621TargetLeftParameter i v)
      (by simpa [i, DLeft, equation621NontrivialGeneratorIndex] using hzLeft)
      (osiiMixedBlockGlobalReducedTime (qLeft + 1)
        (Fin.append (Q.packet.rootedLeftBlockAnchor i)
          (Q.packet.rootedLeftBlockAnchor i))) rfl hcutoff
      (Q.holomorphic.toContinuousTranslationData.commonTailStart i)
      (Q.holomorphic.toContinuousTranslationData.commonTailStart i)
  dsimp only at hrow
  rw [RootedA0BlockContinuousTranslationData.generatorLeftBlockProbe_eq_positiveTargetTest]
    at hrow
  convert hrow using 1 <;>
    simp [i, v, rootedReflectedGlobalProductLeftDiagonal,
      equation621NontrivialGeneratorIndex,
      RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest] <;>
    congr 1

theorem current_reflectedRightDiagonal_row_tendsto
    {rank qLeft qRight : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = (qLeft + 2) + (qRight + 2) - 1}
    {hub : Fin k -> Real}
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {z : OSIITimeGapSpace k}
    {C0 : TargetHubHalfAnchorData hub z}
    {Q : AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth RankP.toAtlasFamily lgc C0.anchor}
    {D : RootedTargetHubAdaptedReflectedGramData
      S depth RankP.toAtlasFamily Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData
        (equation621NontrivialGeneratorIndex qLeft qRight hindex) hub z}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        hub atlas z C0 Q D)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier)
    (x : Fin (k * d) -> Real) (N : Nat) :
    let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
    let v := w - osiiPositiveRealTimeEmbed C0.anchor
    let y := equation621SplitTargetSpatialPoint i x
    let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
      S depth D.adapted Q.packet Q.roots i (q := qRight) rfl
    let rightProbe :=
      (spatialApprox.generatorRightBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
    Tendsto
      (fun scale =>
        rootedReflectedGlobalProductRightDiagonal D.adapted Q.packet Q.roots
          Q.holomorphic.toContinuousTranslationData qLeft qRight hindex
          scale
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
            spatialApprox i y N)
          (equation621TargetRightParameter i v))
      atTop
      (nhds (DRight.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621ReflectedMovingSlicePoint
          (reflectedCauchyCenter (equation621TargetRightParameter i v))
          (osiiMixedBlockGlobalReducedTime (qRight + 1)
            (Fin.append (Q.packet.rootedRightBlockAnchor i)
              (Q.packet.rootedRightBlockAnchor i))))
        (rightProbe.section43Probe
          ((i.equation621TargetAdaptedSpatialSplitData d).rightPoint x) N))) := by
  dsimp only
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let y := equation621SplitTargetSpatialPoint i x
  let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth D.adapted Q.packet Q.roots i (q := qRight) rfl
  have hradial :=
    RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain
      E w hw
  have hzRight : equation621TargetRightParameter i v ∈
      DRight.reflectedGram.atlas.spatialLinearDomain := by
    have hright := hradial.2.2
    change equation621TargetRightParameter i v ∈
      openZeroConvexKernel DRight.reflectedGram.atlas.spatialLinearDomain at hright
    rcases hright with ⟨V, _hVOpen, _hVConvex, _hzero, hV, hzV⟩
    exact hV hzV
  have hcutoff : DRight.reflectedGram.atlas.sourceStage.germ.η
      (osiiMixedBlockGlobalReducedTime (qRight + 1)
        (Fin.append (Q.packet.rootedRightBlockAnchor i)
          (Q.packet.rootedRightBlockAnchor i))) = 1 := by
    simpa [i, DRight, equation621NontrivialGeneratorIndex] using
      rootedRightNontrivialReflectedGram_cutoff_eq_one
        D.adapted Q.packet Q.roots (qLeft + 2) qRight
          i.hn i.hm i.hnm
  have hrow :=
    tendsto_rootedRightNontrivialDiagonalScalar_to_distribution_generatorProbe_adapted
      D.adapted Q.packet Q.roots (qLeft + 2) qRight
      i.hn i.hm i.hnm spatialApprox x N
      (equation621TargetRightParameter i v)
      (by simpa [i, DRight, equation621NontrivialGeneratorIndex] using hzRight)
      (osiiMixedBlockGlobalReducedTime (qRight + 1)
        (Fin.append (Q.packet.rootedRightBlockAnchor i)
          (Q.packet.rootedRightBlockAnchor i))) rfl hcutoff
      (Q.holomorphic.toContinuousTranslationData.commonTailStart i)
      (Q.holomorphic.toContinuousTranslationData.commonTailStart i)
  dsimp only at hrow
  rw [RootedA0BlockContinuousTranslationData.generatorRightBlockProbe_eq_positiveTargetTest]
    at hrow
  convert hrow using 1 <;>
    simp [i, v, rootedReflectedGlobalProductRightDiagonal,
      equation621NontrivialGeneratorIndex,
      RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest] <;>
    congr 1

noncomputable def current_reflectedProductApproximationRows
    {rank qLeft qRight : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hindex : k = (qLeft + 2) + (qRight + 2) - 1}
    {hub : Fin k -> Real}
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {z : OSIITimeGapSpace k}
    {C0 : TargetHubHalfAnchorData hub z}
    {Q : AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth RankP.toAtlasFamily lgc C0.anchor}
    {D : RootedTargetHubAdaptedReflectedGramData
      S depth RankP.toAtlasFamily Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData
        (equation621NontrivialGeneratorIndex qLeft qRight hindex) hub z}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        hub atlas z C0 Q D)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier) :
    let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
    let v := w - osiiPositiveRealTimeEmbed C0.anchor
    let DLeft := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth D.adapted Q.packet Q.roots i (q := qLeft) rfl
    let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
      S depth D.adapted Q.packet Q.roots i (q := qRight) rfl
    let targetProbe := spatialApprox.equation621SplitTargetSpatialApproxIdentity i
    let leftProbe :=
      (spatialApprox.generatorLeftBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
    let rightProbe :=
      (spatialApprox.generatorRightBlockProductApproxIdentity i
        ).reflectedSelfPairMarginalSpatialApproxIdentity
    SpatialApproximationRowsFactorizationData E.current targetProbe w
      (DLeft.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621TargetLeftTimePoint Q.packet i v))
      (DRight.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621TargetRightTimePoint Q.packet i v))
      leftProbe rightProbe (i.equation621TargetAdaptedSpatialSplitData d) := by
  dsimp only
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let DLeft := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth D.adapted Q.packet Q.roots i (q := qLeft) rfl
  let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth D.adapted Q.packet Q.roots i (q := qRight) rfl
  let targetProbe := spatialApprox.equation621SplitTargetSpatialApproxIdentity i
  let leftProbe :=
    (spatialApprox.generatorLeftBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity
  let rightProbe :=
    (spatialApprox.generatorRightBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity
  let targetApprox : (Fin (k * d) -> Real) -> Nat -> Nat -> Complex :=
    fun x N scale =>
      let y := equation621SplitTargetSpatialPoint i x
      let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
      let chi :=
        spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe y N
      (rootedReflectedGramRootSmearedGlobalFamily
        S depth D.adapted lgc Q.packet Q.roots Q.holomorphic
      ).spatialHermiteScalarSum lgc
        ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i).comp lift)
        i scale (generatorChronologicalParameterComplexCLE i v) chi
  let leftApprox : (Fin (k * d) -> Real) -> Nat -> Nat -> Complex :=
    fun x N scale =>
      let y := equation621SplitTargetSpatialPoint i x
      rootedReflectedGlobalProductLeftDiagonal D.adapted Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData qLeft qRight hindex scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i y N)
        (equation621TargetLeftParameter i v)
  let rightApprox : (Fin (k * d) -> Real) -> Nat -> Nat -> Complex :=
    fun x N scale =>
      let y := equation621SplitTargetSpatialPoint i x
      rootedReflectedGlobalProductRightDiagonal D.adapted Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData qLeft qRight hindex scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i y N)
        (equation621TargetRightParameter i v)
  refine
    { targetApprox := targetApprox
      leftApprox := leftApprox
      rightApprox := rightApprox
      target_row_tendsto := ?_
      left_row_tendsto := ?_
      right_row_tendsto := ?_
      eventually_bound := ?_ }
  · intro x N
    simpa [targetApprox, targetProbe,
      OSIIEquation621SpatialApproxIdentityData.smoothedStageValue,
      i, v] using
      current_reflectedAbsoluteProductTarget_row_tendsto
        E spatialApprox w hw x N
  · intro x N
    simpa [leftApprox, leftProbe, DLeft, i, v,
      equation621NontrivialGeneratorIndex, equation621TargetLeftTimePoint] using
      current_reflectedLeftDiagonal_row_tendsto
        E spatialApprox w hw x N
  · intro x N
    simpa [rightApprox, rightProbe, DRight, i, v,
      equation621NontrivialGeneratorIndex, equation621TargetRightTimePoint] using
      current_reflectedRightDiagonal_row_tendsto
        E spatialApprox w hw x N
  · intro x N
    filter_upwards [] with scale
    let y := equation621SplitTargetSpatialPoint i x
    have hradial : v ∈
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth D.adapted Q.packet Q.roots
            Q.holomorphic.toContinuousTranslationData
        ).radialChronologicalDomain i := by
      exact
        RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain
          E w hw
    have heq := rootedAbsoluteProductReflectedScalarSum_eq_candidate_on_radial
      D.adapted Q.packet Q.roots Q.holomorphic lgc
      qLeft qRight hindex spatialApprox y N scale v hradial
    have hbound :=
      norm_rootedReflectedGlobalProductArbitraryCandidate_le_sqrt_diagonals
        D.adapted Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData lgc qLeft qRight hindex
        scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i y N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i y N)
        v hradial
    rw [show targetApprox x N scale =
        rootedReflectedGlobalProductArbitraryCandidate D.adapted Q.packet Q.roots
          Q.holomorphic.toContinuousTranslationData lgc qLeft qRight hindex
          scale
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
            spatialApprox i y N)
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
            spatialApprox i y N)
          (generatorChronologicalParameterComplexCLE i v) by
      simpa [targetApprox, i, v, y] using heq]
    simpa [leftApprox, rightApprox, i, v, y] using hbound

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
