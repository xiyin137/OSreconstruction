import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedRootedSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedSourceIntegral

/-!
# Exact producer geometry for selected rooted product rows

The pointed-extension interface hides its source producer behind a dependent
provenance package.  The ranked construction retains a reverse recursor for
that package.  This file uses it to recover the exact reflected radial-domain
membership needed by the shell-first equation (6.21) row.

The eventual product row must be formed from the reflected global fields on
this domain.  The selected chart does not, in general, assert membership in
the original local rooted-field domains.
-/

noncomputable section

open Complex Filter Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedTargetHubPointedDirectExtensionConstructionDataAtRank

variable {d k depth rank : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}
variable {iota : Type*}

/-- Recover the exact producer-facing radial-domain membership for an
arbitrary generator split.  The construction record retains precisely the
dependent source provenance needed to undo the public package's hiding. -/
theorem current_parameter_mem_exact_radialNativeDomain_any
    {P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k}
    {hub : Fin k -> Real}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {z : OSIITimeGapSpace k}
    {C0 : TargetHubHalfAnchorData hub z}
    {Q : AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth P.toAtlasFamily lgc C0.anchor}
    {D : RootedTargetHubAdaptedReflectedGramData
      S depth P.toAtlasFamily Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData i hub z}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank P lgc i hub atlas z C0 Q D)
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier) :
    generatorChronologicalParameterComplexCLE i
        (w - osiiPositiveRealTimeEmbed C0.anchor) ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth D.adapted Q.packet Q.roots
          Q.holomorphic.toContinuousTranslationData
      ).radialNativeDomain i := by
  let motive := fun
      (I' : Section43ProductTimeApproximateIdentity k)
      (anchor' : Fin k -> Real)
      (A' : AnchoredPacketTimeShellFamilyData (d := d) I' anchor')
      (R' : TripleConvolutionRootData I')
      (H' : RootedA0BlockContinuousTranslationData OS A' R')
      (P' : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth) =>
    generatorChronologicalParameterComplexCLE i
        (w - osiiPositiveRealTimeEmbed anchor') ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P' A' R' H'
      ).radialNativeDomain i
  apply E.current_sourceProvenance_rec_rev motive
  have hpoint :=
    E.current.approximation_parameter_mem_unsmeared_radialNativeDomain w hw
  have hanchor :
      E.current.unsmearedSourceProvenance.anchor =
        E.current.anchorData.anchor :=
    E.current.unsmearedSourceProvenance_anchor_eq
  have hpoint' :
      generatorChronologicalParameterComplexCLE i
          (w - osiiPositiveRealTimeEmbed
            E.current.unsmearedSourceProvenance.anchor) ∈
        E.current.unsmearedFieldData.radialNativeDomain i := by
    simpa [hanchor] using hpoint
  exact
    (congrArg
      (fun F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k =>
        generatorChronologicalParameterComplexCLE i
            (w - osiiPositiveRealTimeEmbed
              E.current.unsmearedSourceProvenance.anchor) ∈
          F.radialNativeDomain i)
      E.current.unsmearedSourceProvenance.family_eq).mp hpoint'

/-- Recover the exact producer-facing radial-domain membership hidden by the
ordinary pointed-extension interface. -/
theorem current_parameter_mem_exact_radialNativeDomain
    {P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {qLeft qRight : Nat}
    {hindex : k = (qLeft + 2) + (qRight + 2) - 1}
    {hub : Fin k -> Real}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {z : OSIITimeGapSpace k}
    {C0 : TargetHubHalfAnchorData hub z}
    {Q : AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth P.toAtlasFamily lgc C0.anchor}
    {D : RootedTargetHubAdaptedReflectedGramData
      S depth P.toAtlasFamily Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData
        (equation621NontrivialGeneratorIndex qLeft qRight hindex) hub z}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank P lgc
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        hub atlas z C0 Q D)
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier) :
    generatorChronologicalParameterComplexCLE
        (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        (w - osiiPositiveRealTimeEmbed C0.anchor) ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth D.adapted Q.packet Q.roots
          Q.holomorphic.toContinuousTranslationData
      ).radialNativeDomain
        (equation621NontrivialGeneratorIndex qLeft qRight hindex) := by
  exact current_parameter_mem_exact_radialNativeDomain_any E w hw

end RootedTargetHubPointedDirectExtensionConstructionDataAtRank
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
