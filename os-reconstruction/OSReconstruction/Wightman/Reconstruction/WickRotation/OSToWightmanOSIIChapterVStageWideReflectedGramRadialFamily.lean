/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramGeneratedBranch
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain













noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]

/-- The radial reflected-Gram chronological domain lies in its genuine
original-OS source-selected global packet branch. -/
theorem
    radialChronologicalDomain_subset_rootedReflectedGramTwoScaleDomainOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData
      ).radialChronologicalDomain i ⊆
      (rootedReflectedGramGeneratorTwoScaleApproximationFamilyOfOS
        S depth P A R H).domain i := by
  intro z hz
  let E :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let Q :=
    rootedReflectedGramGeneratorOpenFieldSourceAgreementData
      S depth P A R H
  let C :=
    rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
      S depth P A R H
  let w :=
    generatorChronologicalParameterComplexCLE i z
  have hw : w ∈ E.radialNativeDomain i := hz
  have hw_bridge : 0 < (w i.bridgeGlobalIndex).re := by
    change 0 < ((i.splitCoordinatesCLM w).1).re
    exact hw.1
  have htarget :
      JoinedIn (E.domain i)
        (i.nativeBridgePoint (w i.bridgeGlobalIndex)) w := by
    apply E.nativeBridgePoint_joinedIn_of_radial
      i w hw_bridge
    · intro t ht
      apply E.radialLeftDomain_subset i
      change
        star (t • (i.splitCoordinatesCLM w).2.1) ∈
          openZeroConvexKernel (E.leftDomain i)
      simpa using
        real_smul_mem_openZeroConvexKernel hw.2.1 ht.1 ht.2
    · intro t ht
      apply E.radialRightDomain_subset i
      exact
        real_smul_mem_openZeroConvexKernel hw.2.2 ht.1 ht.2
  have hseed :
      JoinedIn (E.domain i)
        (i.nativeBridgePoint (C.center i.bridgeGlobalIndex))
        (osiiPositiveRealTimeEmbed C.center) := by
    simpa [E, C, rootedReflectedGramRootSmearedGlobalFamilyOfOS,
      rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS,
      GeneratorOpenHilbertFieldScaleFamilyData.domain] using
      rootedReflectedGramSeedOfOS_joinedIn_nativeBridgePoint
        S depth P A R H i
  have hcenterPositive :
      0 < C.center i.bridgeGlobalIndex := by
    have hpositive :
        C.center ∈ section43TimeStrictPositiveRegion k :=
      Q.strictPositive_of_mem_commonPositiveRealOfOS
        C.center C.center_mem
    exact hpositive i.bridgeGlobalIndex
  have hbridge :
      JoinedIn (E.domain i)
        (i.nativeBridgePoint (C.center i.bridgeGlobalIndex))
        (i.nativeBridgePoint (w i.bridgeGlobalIndex)) :=
    E.nativeBridgePoints_joinedIn_domain i
      (C.center i.bridgeGlobalIndex)
      (w i.bridgeGlobalIndex)
      (by simpa using hcenterPositive)
      (by simpa using hw_bridge)
  have hjoin :
      JoinedIn (E.domain i)
        (osiiPositiveRealTimeEmbed C.center) w :=
    hseed.symm.trans (hbridge.trans htarget)
  change
    w ∈ rootedReflectedGramPacketScaleBranchOfOS
      S depth P A R H i
  have hmem := JoinedIn.target_mem_connectedComponentIn hjoin
  rw [← show SCV.realToComplex C.center =
    osiiPositiveRealTimeEmbed C.center by rfl] at hmem
  simpa [
    rootedReflectedGramPacketScaleBranchOfOS,
    rootedReflectedGramPacketScaleGermDataOfOS,
    GeneratorPacketScaleGermData.branch,
    C, E, rootedReflectedGramRootSmearedGlobalFamilyOfOS,
    rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS,
    GeneratorOpenHilbertFieldScaleFamilyData.domain] using hmem

/-- The radial chronological domain of the reflected-Gram field family lies
in the packet-scale branch selected by the common rooted germ. -/
theorem
    radialChronologicalDomain_subset_rootedReflectedGramTwoScaleDomain
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData
      ).radialChronologicalDomain i ⊆
      (rootedReflectedGramGeneratorTwoScaleApproximationFamily
        S depth P lgc A R H).domain i := by
  intro z hz
  let E :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let Q :=
    rootedReflectedGramGeneratorOpenFieldSourceAgreementData
      S depth P A R H
  let C :=
    rootedReflectedGramGeneratorCommonComplexModeGermData
      S depth P lgc A R H
  let w :=
    generatorChronologicalParameterComplexCLE i z
  have hw : w ∈ E.radialNativeDomain i := hz
  have hw_bridge : 0 < (w i.bridgeGlobalIndex).re := by
    change 0 < ((i.splitCoordinatesCLM w).1).re
    exact hw.1
  have htarget :
      JoinedIn (E.domain i)
        (i.nativeBridgePoint (w i.bridgeGlobalIndex)) w := by
    apply E.nativeBridgePoint_joinedIn_of_radial
      i w hw_bridge
    · intro t ht
      apply E.radialLeftDomain_subset i
      change
        star (t • (i.splitCoordinatesCLM w).2.1) ∈
          openZeroConvexKernel (E.leftDomain i)
      simpa using
        real_smul_mem_openZeroConvexKernel hw.2.1 ht.1 ht.2
    · intro t ht
      apply E.radialRightDomain_subset i
      exact
        real_smul_mem_openZeroConvexKernel hw.2.2 ht.1 ht.2
  have hseed :
      JoinedIn (E.domain i)
        (i.nativeBridgePoint (C.center i.bridgeGlobalIndex))
        (osiiPositiveRealTimeEmbed C.center) := by
    simpa [E, C, rootedReflectedGramRootSmearedGlobalFamily,
      rootedReflectedGramRootSmearedGlobalFamilyOfOS,
      rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS,
      GeneratorOpenHilbertFieldScaleFamilyData.domain] using
      rootedReflectedGramSeed_joinedIn_nativeBridgePoint
        S depth P lgc A R H i
  have hcenterPositive :
      0 < C.center i.bridgeGlobalIndex := by
    have hpositive :
        C.center ∈ section43TimeStrictPositiveRegion k :=
      Q.strictPositive_of_mem_commonPositiveReal
        lgc C.center C.center_mem
    exact hpositive i.bridgeGlobalIndex
  have hbridge :
      JoinedIn (E.domain i)
        (i.nativeBridgePoint (C.center i.bridgeGlobalIndex))
        (i.nativeBridgePoint (w i.bridgeGlobalIndex)) :=
    E.nativeBridgePoints_joinedIn_domain i
      (C.center i.bridgeGlobalIndex)
      (w i.bridgeGlobalIndex)
      (by simpa using hcenterPositive)
      (by simpa using hw_bridge)
  have hjoin :
      JoinedIn (E.domain i)
        (osiiPositiveRealTimeEmbed C.center) w :=
    hseed.symm.trans (hbridge.trans htarget)
  change
    w ∈ rootedReflectedGramPacketScaleBranch
      S depth P lgc A R H i
  have hmem := JoinedIn.target_mem_connectedComponentIn hjoin
  rw [← show SCV.realToComplex C.center =
    osiiPositiveRealTimeEmbed C.center by rfl] at hmem
  simpa [
    rootedReflectedGramPacketScaleBranch,
    rootedReflectedGramPacketScaleGermData,
    GeneratorPacketScaleGermData.branch,
    C, E, rootedReflectedGramRootSmearedGlobalFamily,
    rootedReflectedGramRootSmearedGlobalFamilyOfOS,
    rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS,
    GeneratorOpenHilbertFieldScaleFamilyData.domain] using hmem

/-- The genuine original-OS reflected-Gram two-scale family restricted to
the radial chronological domains used for source-compatible gluing. -/
noncomputable def
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorSpatialTwoScaleApproximationFamily d k := by
  let E :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let T :=
    rootedReflectedGramGeneratorTwoScaleApproximationFamilyOfOS
      S depth P A R H
  exact {
    domain := E.radialChronologicalDomain
    domain_open := E.radialChronologicalDomain_open
    approximation := T.approximation
    approximation_weaklyHolomorphic := by
      intro i timeScale shell χ
      exact
        (T.approximation_weaklyHolomorphic
          i timeScale shell χ).mono
            (radialChronologicalDomain_subset_rootedReflectedGramTwoScaleDomainOfOS
              S depth P A R H i)
    scalarLimit := T.scalarLimit
    locallyUniform := by
      intro i χ
      exact
        (T.locallyUniform i χ).mono
          (radialChronologicalDomain_subset_rootedReflectedGramTwoScaleDomainOfOS
            S depth P A R H i)
  }

@[simp]
theorem
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS_domain
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS
      S depth P A R H).domain i =
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData
      ).radialChronologicalDomain i :=
  rfl

/-- The reflected-Gram two-scale family restricted to radial chronological
generator domains. -/
noncomputable def
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorSpatialTwoScaleApproximationFamily d k := by
  let E :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let T :=
    rootedReflectedGramGeneratorTwoScaleApproximationFamily
      S depth P lgc A R H
  exact {
    domain := E.radialChronologicalDomain
    domain_open := E.radialChronologicalDomain_open
    approximation := T.approximation
    approximation_weaklyHolomorphic := by
      intro i timeScale shell χ
      exact
        (T.approximation_weaklyHolomorphic
          i timeScale shell χ).mono
            (radialChronologicalDomain_subset_rootedReflectedGramTwoScaleDomain
              S depth P lgc A R H i)
    scalarLimit := T.scalarLimit
    locallyUniform := by
      intro i χ
      exact
        (T.locallyUniform i χ).mono
          (radialChronologicalDomain_subset_rootedReflectedGramTwoScaleDomain
            S depth P lgc A R H i)
  }

@[simp]
theorem
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily_domain
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily
      S depth P lgc A R H).domain i =
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData
      ).radialChronologicalDomain i :=
  rfl

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
