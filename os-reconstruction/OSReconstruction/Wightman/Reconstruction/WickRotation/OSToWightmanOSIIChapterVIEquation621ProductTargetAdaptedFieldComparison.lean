/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedProbeRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIWeightedReflectedRankFieldIdentification











noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k depth : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}

/-- The synchronized arbitrary left target field is the source-native
reflected-Gram field at the common packet tail. -/
theorem rootedLeftArbitrarySpatialField_eq_reflectedGram
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (q m : Nat)
    (hn : 1 <= q + 2)
    (hm : 1 <= m)
    (hnm : k = q + 2 + m - 1)
    (scale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (z : Fin (q + 1) -> Complex)
    (hz :
      let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
      let D := rootedLeftNontrivialReflectedGramSpatialSourceData
        S depth P A R i (q := q) rfl
      z ∈ openZeroConvexKernel
        (D.reflectedGram.atlas.spatialLinearDomain ∩ (H.left i).domain)) :
    let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    let D := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
    D.reflectedGram.atlas.gram.anchoredAtlasField
        D.reflectedGram.atlas.sourceStage.stage
        D.reflectedGram.atlas.sourceStage.germ
        (D.sourceCLM
          (scale + H.toContinuousTranslationData.commonTailStart i) chi) z =
      H.toContinuousTranslationData.leftArbitrarySpatialGeneratorField
        i scale chi z := by
  let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let D := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := q) rfl
  let T := H.toContinuousTranslationData
  have hsource : forall u,
      localPositiveTimeParameterTranslate
          (UniformCompactTimeSource.source
            (D.sourceCLM (scale + T.commonTailStart i) chi))
          (fun r : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) r) u =
        (fun N u' chi' =>
          A.rootedLeftBlockTranslatedSpatialSource R i
            (N + H.leftTailStart i) u' chi')
          (T.leftCofinalIndex i scale) u chi := by
    intro u
    change
      A.rootedLeftBlockTranslatedSpatialSource R i
          (scale + T.commonTailStart i) u chi =
        A.rootedLeftBlockTranslatedSpatialSource R i
          (T.leftCofinalIndex i scale + T.leftTailStart i) u chi
    rw [T.leftCofinalIndex_add_tailStart]
  have heq :=
    D.anchoredAtlasField_eq_holomorphicTranslationField_on_commonKernel
      (H.left i) (scale + T.commonTailStart i)
      (T.leftCofinalIndex i scale) chi hsource z (by
        simpa [D, i] using hz)
  simpa [D, i, T,
    RootedA0BlockContinuousTranslationData.leftArbitrarySpatialGeneratorField]
    using heq

/-- The synchronized arbitrary right target field is the source-native
reflected-Gram field at the common packet tail. -/
theorem rootedRightArbitrarySpatialField_eq_reflectedGram
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (n q : Nat)
    (hn : 1 <= n)
    (hm : 1 <= q + 2)
    (hnm : k = n + (q + 2) - 1)
    (scale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (z : Fin (q + 1) -> Complex)
    (hz :
      let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
      let D := rootedRightNontrivialReflectedGramSpatialSourceData
        S depth P A R i (q := q) rfl
      z ∈ openZeroConvexKernel
        (D.reflectedGram.atlas.spatialLinearDomain ∩ (H.right i).domain)) :
    let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
    let D := rootedRightNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
    D.reflectedGram.atlas.gram.anchoredAtlasField
        D.reflectedGram.atlas.sourceStage.stage
        D.reflectedGram.atlas.sourceStage.germ
        (D.sourceCLM
          (scale + H.toContinuousTranslationData.commonTailStart i) chi) z =
      H.toContinuousTranslationData.rightArbitrarySpatialGeneratorField
        i scale chi z := by
  let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
  let D := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := q) rfl
  let T := H.toContinuousTranslationData
  have hsource : forall u,
      localPositiveTimeParameterTranslate
          (UniformCompactTimeSource.source
            (D.sourceCLM (scale + T.commonTailStart i) chi))
          (fun r : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) r) u =
        (fun N u' chi' =>
          A.rootedRightBlockTranslatedSpatialSource R i
            (N + H.rightTailStart i) u' chi')
          (T.rightCofinalIndex i scale) u chi := by
    intro u
    change
      A.rootedRightBlockTranslatedSpatialSource R i
          (scale + T.commonTailStart i) u chi =
        A.rootedRightBlockTranslatedSpatialSource R i
          (T.rightCofinalIndex i scale + T.rightTailStart i) u chi
    rw [T.rightCofinalIndex_add_tailStart]
  have heq :=
    D.anchoredAtlasField_eq_holomorphicTranslationField_on_commonKernel
      (H.right i) (scale + T.commonTailStart i)
      (T.rightCofinalIndex i scale) chi hsource z (by
        simpa [D, i] using hz)
  simpa [D, i, T,
    RootedA0BlockContinuousTranslationData.rightArbitrarySpatialGeneratorField]
    using heq

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
