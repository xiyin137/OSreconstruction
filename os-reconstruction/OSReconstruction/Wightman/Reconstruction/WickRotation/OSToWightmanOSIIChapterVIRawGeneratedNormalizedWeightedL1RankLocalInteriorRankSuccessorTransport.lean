/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1RankLocalInteriorProducer
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedL1RankSuccessorFlatProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorAdaptiveShiftHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedPointedInduction











noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

theorem rootedExtension_distribution_eq_rankSuccessor_target
    {depth rank q : Nat}
    (R : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (a : RootedStrictGeneratedTargetHubChartAtRank (q + 1) depth rank)
    (D : RootedTargetHubPointedDirectExtensionData
      R.pointed depth R.sourceReflectedGramRankData.toAtlasFamily lgc
      a.generator (R.pointed.hub q) a.target
      (R.pointed.pointedAtlas q)) :
    D.extension.toTimeContinuationStage.distribution a.target =
      ((R.next lgc).pointed.stageLevel.stage (q + 1)).distribution
        a.target := by
  let selected := selectedRootedTargetHubPointedDirectExtensionAtRank
    R.pointed depth rank R.sourceReflectedGramRankData lgc
      (R.pointed.hub q) (R.pointed.hub_positive q)
      (R.pointed.pointedAtlas q) a
  let atlas := R.pointed.rootedInsertionRankConvexCoreAtlas
    depth rank R.sourceReflectedGramRankData lgc q
  have hcurrent :
      D.extension.toTimeContinuationStage.distribution a.target =
        D.extension.distribution a.generator a.target :=
    D.extension.newStage_eqOn_generatorDomain a.generator
      (D.carrier_subset_extensionDomain D.target_mem_carrier)
  have hcompare :
      D.extension.distribution a.generator a.target =
        selected.extension.distribution a.generator a.target := by
    simpa [selected] using
      (StrictGeneratedScalarDepthPointedData.rootedTargetHubPointedDirectExtension_distribution_eq_selectedAtRank_target
        (P := R.sourceReflectedGramRankData)
        (R.pointed.hub_positive q) a D)
  have hcanonical :
      atlas.successorStage.distribution a.target =
        selected.extension.distribution a.generator a.target :=
    atlas.successorStage_eqOn_extensionCarrier a selected.target_mem_carrier
  have htarget : a.target ∈ atlas.successorStage.carrier :=
    atlas.carrier_subset_successorCarrier a selected.target_mem_carrier
  have hrooted :
      a.target ∈ ((R.pointed.rootedInsertionRankStageLevel
        depth rank R.sourceReflectedGramRankData lgc).stage (q + 1)).carrier := by
    simpa [atlas] using htarget
  have hnext :
      ((R.next lgc).pointed.stageLevel.stage (q + 1)).distribution a.target =
        atlas.successorStage.distribution a.target := by
    simpa [atlas] using R.next_extends_rootedInsertion lgc (q + 1) hrooted
  exact hcurrent.trans (hcompare.trans (hcanonical.symm.trans hnext.symm))

theorem norm_normalizedRankSuccessor_le_of_rootedExtension
    {depth rank q t : Nat}
    (R : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (a : RootedStrictGeneratedTargetHubChartAtRank (q + 1) depth rank)
    (D : RootedTargetHubPointedDirectExtensionData
      R.pointed depth R.sourceReflectedGramRankData.toAtlasFamily lgc
      a.generator (R.pointed.hub q) a.target
      (R.pointed.pointedAtlas q))
    (epsilon : Real)
    (chi : SchwartzMap (Section43SpatialSpace d (q + 1)) Complex)
    (B : Real)
    (hbound :
      ‖(D.extension.toTimeContinuationStage.vi2Equation621NormalizedStage
          t epsilon).distribution
          (osiiVI2Unshift (q + 1) epsilon a.target) chi‖ <= B) :
    ‖(((R.next lgc).pointed.stageLevel.stage (q + 1)
        ).vi2Equation621NormalizedStage t epsilon).distribution
        (osiiVI2Unshift (q + 1) epsilon a.target) chi‖ <= B := by
  simp only [OSIITimeContinuationStage.vi2Equation621NormalizedStage_distribution_apply,
    osiiVI2Shift_unshift] at hbound ⊢
  rw [← rootedExtension_distribution_eq_rankSuccessor_target R lgc a D]
  exact hbound

end OSIIChapterV
end OSReconstruction
