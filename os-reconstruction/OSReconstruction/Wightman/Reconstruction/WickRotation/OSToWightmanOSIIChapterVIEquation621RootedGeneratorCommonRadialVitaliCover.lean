/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramCommonRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedStageMatchedRepresentedGenerator
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedFactorization
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedTwoScaleFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali











noncomputable section

open Complex Set Topology
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

def equation621CommonRadialCarrier
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) : Set (OSIITimeGapSpace k) :=
  (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData).radialChronologicalDomain i ∩
    (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      A R H).radialChronologicalDomain i

structure Equation621CommonRadialRealSeedData
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) where
  realRegion : Set (Fin k -> Real)
  realRegion_open : IsOpen realRegion
  realRegion_nonempty : realRegion.Nonempty
  realRegion_automatic : realRegion ⊆
    rootedReflectedGramChronologicalCommonRealAutomaticSet S depth P A R H
  realRegion_positive : realRegion ⊆ section43TimeStrictPositiveRegion k

noncomputable def selectedEquation621CommonRadialRealSeedData
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    Equation621CommonRadialRealSeedData P A R H := by
  let U := rootedReflectedGramChronologicalCommonRealAutomaticSet
    S depth P A R H
  let hV := mem_nhds_iff.mp
    (rootedReflectedGramChronologicalCommonRealAutomaticSet_mem_nhds
      S depth P A R H)
  let V : Set (Fin k -> Real) := Classical.choose hV
  have hVspec := Classical.choose_spec hV
  exact {
    realRegion := V ∩ section43TimeStrictPositiveRegion k
    realRegion_open := hVspec.2.1.inter
      (isOpen_section43TimeStrictPositiveRegion k)
    realRegion_nonempty :=
      GeneratorHermiteHilbertFieldFamilyData.open_inter_strictPositive_nonempty
        V hVspec.2.1 hVspec.2.2
    realRegion_automatic := fun _ h => hVspec.1 h.1
    realRegion_positive := fun _ h => h.2
  }

namespace Equation621StageMatchedCommonRadialRealSeedData

end Equation621StageMatchedCommonRadialRealSeedData

theorem positiveReal_mem_localRootedRadial_of_commonAutomatic
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (tau : Fin k -> Real)
    (hpositive : tau ∈ section43TimeStrictPositiveRegion k)
    (hautomatic : generatorChronologicalParameter i tau ∈
      (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
        S depth P A R H).commonRealAutomaticSet) :
    osiiPositiveRealTimeEmbed tau ∈
      (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        A R H).radialChronologicalDomain i := by
  let F := rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData A R H
  let xi := generatorChronologicalParameter i tau
  change generatorChronologicalParameterComplexCLE i
      (osiiPositiveRealTimeEmbed tau) ∈ F.radialNativeDomain i
  rw [generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed]
  refine ⟨?_, ?_, ?_⟩
  · change 0 < xi i.bridgeGlobalIndex
    dsimp [xi]
    rw [generatorChronologicalParameter_bridge]
    exact hpositive i.bridgeGlobalIndex
  · have hpoint : SCV.realToComplex (i.leftRealCoordinates xi) ∈
        (H.left i).domain := by
      have hmem := F.leftRealToComplex_mem_domain i
        (i.leftRealCoordinates xi) (hautomatic.2 i).1
      simpa [F] using hmem
    have hradial : SCV.realToComplex (i.leftRealCoordinates xi) ∈
        openZeroConvexKernel (H.left i).domain := by
      apply mem_openZeroConvexKernel_of_segment_subset (H.left i).domain_open
      exact (H.left i).domain_convex.segment_subset
        (H.toContinuousTranslationData.left i).zero_mem_domain hpoint
    change star (i.splitCoordinatesCLM
      (osiiPositiveRealTimeEmbed xi)).2.1 ∈ F.radialLeftDomain i
    change star (i.splitCoordinatesCLM
      (osiiPositiveRealTimeEmbed xi)).2.1 ∈
        openZeroConvexKernel (F.leftDomain i)
    rw [rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_leftDomain]
    have heq : star (i.splitCoordinatesCLM
        (osiiPositiveRealTimeEmbed xi)).2.1 =
        SCV.realToComplex (i.leftRealCoordinates xi) := by
      ext a
      exact i.splitCoordinatesCLM_positiveReal_left xi a
    rw [heq]
    exact hradial
  · have hpoint : SCV.realToComplex (i.rightRealCoordinates xi) ∈
        (H.right i).domain := by
      have hmem := F.rightRealToComplex_mem_domain i
        (i.rightRealCoordinates xi) (hautomatic.2 i).2
      simpa [F] using hmem
    have hradial : SCV.realToComplex (i.rightRealCoordinates xi) ∈
        openZeroConvexKernel (H.right i).domain := by
      apply mem_openZeroConvexKernel_of_segment_subset (H.right i).domain_open
      exact (H.right i).domain_convex.segment_subset
        (H.toContinuousTranslationData.right i).zero_mem_domain hpoint
    change (i.splitCoordinatesCLM
      (osiiPositiveRealTimeEmbed xi)).2.2 ∈ F.radialRightDomain i
    change (i.splitCoordinatesCLM
      (osiiPositiveRealTimeEmbed xi)).2.2 ∈
        openZeroConvexKernel (F.rightDomain i)
    rw [rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_rightDomain]
    simpa [xi] using hradial

theorem equation621CommonRadialRealSeed_mem_carrier
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (tau : Fin k -> Real)
    (htau : tau ∈
      (selectedEquation621CommonRadialRealSeedData P A R H).realRegion) :
    osiiPositiveRealTimeEmbed tau ∈
      equation621CommonRadialCarrier P A R H i := by
  let seed := selectedEquation621CommonRadialRealSeedData P A R H
  have hauto := seed.realRegion_automatic htau
  have hpos := seed.realRegion_positive htau
  exact ⟨
    positiveReal_mem_rootedReflectedGramRadialChronologicalDomain_of_commonRealAutomatic
      S depth P A R H i tau (hpos i.bridgeGlobalIndex) (hauto i),
    positiveReal_mem_localRootedRadial_of_commonAutomatic
      P A R H i tau hpos (hauto i)⟩

namespace Equation621StageMatchedCommonRadialRealSeedData

end Equation621StageMatchedCommonRadialRealSeedData

/-- On a common-radial chart, the two equation-`(6.21)` block parameters lie
simultaneously in the retained reflected-Gram and original rooted radial
kernels. -/
theorem equation621CommonRadialCarrier_targetParameters_mem_commonKernels
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ equation621CommonRadialCarrier P A R H i) :
    equation621TargetLeftParameter i z ∈
        openZeroConvexKernel
          ((rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
              S depth P A R H.toContinuousTranslationData).leftDomain i ∩
            (H.left i).domain) ∧
      equation621TargetRightParameter i z ∈
        openZeroConvexKernel
          ((rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
              S depth P A R H.toContinuousTranslationData).rightDomain i ∩
            (H.right i).domain) := by
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R H.toContinuousTranslationData
  let F := rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData A R H
  have hreflected := hz.1
  have hrooted := hz.2
  change generatorChronologicalParameterComplexCLE i z ∈
    E.radialNativeDomain i at hreflected
  change generatorChronologicalParameterComplexCLE i z ∈
    F.radialNativeDomain i at hrooted
  rw [openZeroConvexKernel_inter, openZeroConvexKernel_inter]
  constructor
  · refine ⟨?_, ?_⟩
    · simpa [E, equation621TargetLeftParameter] using hreflected.2.1
    · have hleftRoot : equation621TargetLeftParameter i z ∈
          (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            A R H).radialLeftDomain i := by
        simpa [F, equation621TargetLeftParameter] using hrooted.2.1
      change equation621TargetLeftParameter i z ∈
        openZeroConvexKernel
          ((rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            A R H).leftDomain i) at hleftRoot
      rw [rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_leftDomain]
        at hleftRoot
      exact hleftRoot
  · refine ⟨?_, ?_⟩
    · simpa [E, equation621TargetRightParameter] using hreflected.2.2
    · have hrightRoot : equation621TargetRightParameter i z ∈
          (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            A R H).radialRightDomain i := by
        simpa [F, equation621TargetRightParameter] using hrooted.2.2
      change equation621TargetRightParameter i z ∈
        openZeroConvexKernel
          ((rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            A R H).rightDomain i) at hrightRoot
      rw [rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_rightDomain]
        at hrightRoot
      exact hrightRoot

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
