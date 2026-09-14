/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedGenerator
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorPacketScaleGlobal











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

/-- The genuine original-OS common source germ inside the complete
stage-wide reflected-Gram rooted generator domain. -/
noncomputable def rootedReflectedGramPacketScaleGermDataOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    GeneratorPacketScaleGermData
      (rootedReflectedGramRootSmearedGlobalFamilyOfOS
        S depth P A R H) i := by
  let C :=
    rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
      S depth P A R H
  let G :=
    rootedReflectedGramGeneratorCommonPositiveRealModeAgreementDataOfOS
      S depth P A R H
  exact {
    germ := C.domain i
    germ_open := C.domain_open i
    germ_preconnected := (C.domain_convex i).isPreconnected
    center := C.center
    center_mem_germ := by
      rw [show SCV.realToComplex C.center =
          osiiPositiveRealTimeEmbed C.center by rfl]
      exact C.center_mem_domain i
    germ_subset_domain := by
      intro z hz
      change
        z ∈
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth P A R H.toContinuousTranslationData
            ).toGeneratorOpenHilbertFieldScaleFamilyData.domain i
      exact C.ball_subset_first i hz
    realRegion := G.realRegion
    realRegion_open := G.realRegion_open
    center_mem_realRegion := C.center_mem
  }

/-- The connected original-OS reflected-Gram global generator branch
selected by its actual source-compatible rooted germ. -/
noncomputable def rootedReflectedGramPacketScaleBranchOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  (rootedReflectedGramPacketScaleGermDataOfOS
    S depth P A R H i).branch

theorem rootedReflectedGramPacketScaleBranchOfOS_open
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    IsOpen
      (rootedReflectedGramPacketScaleBranchOfOS
        S depth P A R H i) :=
  (rootedReflectedGramPacketScaleGermDataOfOS
    S depth P A R H i).branch_open

theorem rootedReflectedGramPacketScaleBranchOfOS_subset_domain
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    rootedReflectedGramPacketScaleBranchOfOS
        S depth P A R H i ⊆
      (rootedReflectedGramRootSmearedGlobalFamilyOfOS
        S depth P A R H).domain i :=
  (rootedReflectedGramPacketScaleGermDataOfOS
    S depth P A R H i).branch_subset_domain

/-- The common connected complex germ embedded in the reflected-Gram global
root-smeared field domain. -/
noncomputable def rootedReflectedGramPacketScaleGermData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    GeneratorPacketScaleGermData
      (rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H) i := by
  let C :=
    rootedReflectedGramGeneratorCommonComplexModeGermData
      S depth P lgc A R H
  let G :=
    rootedReflectedGramGeneratorCommonPositiveRealModeAgreementData
      S depth P lgc A R H
  exact {
    germ := C.domain i
    germ_open := C.domain_open i
    germ_preconnected := (C.domain_convex i).isPreconnected
    center := C.center
    center_mem_germ := by
      rw [show SCV.realToComplex C.center =
          osiiPositiveRealTimeEmbed C.center by rfl]
      exact C.center_mem_domain i
    germ_subset_domain := by
      intro z hz
      change
        z ∈
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth P A R H.toContinuousTranslationData
            ).toGeneratorOpenHilbertFieldScaleFamilyData.domain i
      exact C.ball_subset_first i hz
    realRegion := G.realRegion
    realRegion_open := G.realRegion_open
    center_mem_realRegion := C.center_mem
  }

/-- The connected reflected-Gram global generator branch selected by the
common rooted germ. -/
noncomputable def rootedReflectedGramPacketScaleBranch
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  (rootedReflectedGramPacketScaleGermData
    S depth P lgc A R H i).branch

theorem rootedReflectedGramPacketScaleBranch_open
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    IsOpen
      (rootedReflectedGramPacketScaleBranch
        S depth P lgc A R H i) :=
  (rootedReflectedGramPacketScaleGermData
    S depth P lgc A R H i).branch_open

theorem rootedReflectedGramPacketScaleBranch_connected
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    IsConnected
      (rootedReflectedGramPacketScaleBranch
        S depth P lgc A R H i) :=
  (rootedReflectedGramPacketScaleGermData
    S depth P lgc A R H i).branch_connected

theorem rootedReflectedGramPacketScaleBranch_subset_domain
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    rootedReflectedGramPacketScaleBranch
        S depth P lgc A R H i ⊆
      (rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H).domain i :=
  (rootedReflectedGramPacketScaleGermData
    S depth P lgc A R H i).branch_subset_domain

/-- The genuine original-OS packet-scale seed for any continuous lift of
the complete reduced spatial source test. -/
noncomputable def rootedReflectedGramPacketScaleSeedDataOfOSOfLift
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    GeneratorPacketScaleSeedDataOfOS
      (rootedReflectedGramPacketScaleGermDataOfOS
        S depth P A R H i)
      ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
        (d := d) i).comp lift)
      χ := by
  let Q := rootedPacketScaleLimitDataOfOS H i (lift χ)
  refine {
    limit := Q.limit
    locallyUniform := ?_
  }
  have hseed :=
    rootedReflectedGramRootSmearedSpatialHermiteGeneratorSumOfOS_packetScale_seed
      S depth P A R H i (lift χ)
  apply hseed.congr
  intro timeScale z hz
  simpa [rootedReflectedGramRootSmearedGlobalFamilyOfOS] using
    (rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS_eq_spatialHermiteScalarSumOfOS_of_lift
      H.toContinuousTranslationData
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData
        ).toGeneratorOpenHilbertFieldScaleFamilyData
      i timeScale z lift χ)

/-- The locally uniform packet-scale seed for an arbitrary continuous lift of
the reduced spatial test. -/
noncomputable def rootedReflectedGramPacketScaleSeedDataOfLift
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    GeneratorPacketScaleSeedData
      (rootedReflectedGramPacketScaleGermData
        S depth P lgc A R H i)
      lgc
      ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
        (d := d) i).comp lift)
      χ := by
  let Q := rootedPacketScaleLimitData H lgc i (lift χ)
  refine {
    limit := Q.limit
    locallyUniform := ?_
  }
  have hseed :=
    rootedReflectedGramRootSmearedSpatialHermiteGeneratorSum_packetScale_seed
      S depth P lgc A R H i (lift χ)
  apply hseed.congr
  intro timeScale z hz
  simpa [rootedReflectedGramRootSmearedGlobalFamily] using
    (rootSmearedGeneratorOpenFieldSpatialHermiteSum_eq_spatialHermiteScalarSum_of_lift
      H.toContinuousTranslationData lgc
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData
        ).toGeneratorOpenHilbertFieldScaleFamilyData
      i timeScale z lift χ)

/-- A packet-scale branch limit for an arbitrary continuous spatial lift. -/
abbrev RootedReflectedGramPacketScaleBranchLimitDataOfLift
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :=
  (rootedReflectedGramPacketScaleSeedDataOfLift
    S depth P lgc A R H i lift χ).BranchLimitData

/-- The chosen packet-scale branch limit for an arbitrary continuous spatial
lift. -/
noncomputable def rootedReflectedGramPacketScaleBranchLimitDataOfLift
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    RootedReflectedGramPacketScaleBranchLimitDataOfLift
      S depth P lgc A R H i lift χ :=
  (rootedReflectedGramPacketScaleSeedDataOfLift
    S depth P lgc A R H i lift χ).branchLimitData

/-- The original-OS packet-scale seed in the scalar-sum coordinates
required by the genuine global two-scale assembly. -/
noncomputable def rootedReflectedGramPacketScaleSeedDataOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    GeneratorPacketScaleSeedDataOfOS
      (rootedReflectedGramPacketScaleGermDataOfOS
        S depth P A R H i)
      (rootedGeneratorSplitSpatialLiftCLM i) χ := by
  let lift :=
    section43SpatialBasepointLiftCLM d k
      (normalizedSpatialBasepointCutoff d).toSchwartz
  let Q := rootedPacketScaleLimitDataOfOS H i (lift χ)
  refine {
    limit := Q.limit
    locallyUniform := ?_
  }
  have hseed :=
    rootedReflectedGramRootSmearedSpatialHermiteGeneratorSumOfOS_packetScale_seed
      S depth P A R H i (lift χ)
  apply hseed.congr
  intro timeScale z hz
  simpa [rootedReflectedGramRootSmearedGlobalFamilyOfOS, lift] using
    (rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS_eq_spatialHermiteScalarSumOfOS
      H.toContinuousTranslationData
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData
        ).toGeneratorOpenHilbertFieldScaleFamilyData
      i timeScale z χ)

/-- The source-compatible original-OS holomorphic limit selected on the
entire connected stage-wide reflected-Gram generator branch. -/
abbrev RootedReflectedGramPacketScaleBranchLimitDataOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :=
  (rootedReflectedGramPacketScaleSeedDataOfOS
    S depth P A R H i χ).BranchLimitData

noncomputable def rootedReflectedGramPacketScaleBranchLimitDataOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    RootedReflectedGramPacketScaleBranchLimitDataOfOS
      S depth P A R H i χ :=
  (rootedReflectedGramPacketScaleSeedDataOfOS
    S depth P A R H i χ).branchLimitData

/-- The locally uniform packet-scale seed expressed in the scalar-sum
coordinates used by the global two-scale assembly. -/
noncomputable def rootedReflectedGramPacketScaleSeedData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    GeneratorPacketScaleSeedData
      (rootedReflectedGramPacketScaleGermData
        S depth P lgc A R H i)
      lgc (rootedGeneratorSplitSpatialLiftCLM i) χ := by
  let lift :=
    section43SpatialBasepointLiftCLM d k
      (normalizedSpatialBasepointCutoff d).toSchwartz
  let Q := rootedPacketScaleLimitData H lgc i (lift χ)
  refine {
    limit := Q.limit
    locallyUniform := ?_
  }
  have hseed :=
    rootedReflectedGramRootSmearedSpatialHermiteGeneratorSum_packetScale_seed
      S depth P lgc A R H i (lift χ)
  apply hseed.congr
  intro timeScale z hz
  simpa [rootedReflectedGramRootSmearedGlobalFamily, lift] using
    (rootSmearedGeneratorOpenFieldSpatialHermiteSum_eq_spatialHermiteScalarSum
      H.toContinuousTranslationData lgc
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData
        ).toGeneratorOpenHilbertFieldScaleFamilyData
      i timeScale z χ)

/-- A selected packet-scale holomorphic limit on the connected
reflected-Gram global branch. -/
abbrev RootedReflectedGramPacketScaleBranchLimitData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :=
  (rootedReflectedGramPacketScaleSeedData
    S depth P lgc A R H i χ).BranchLimitData

/-- The canonical chosen packet-scale limit on the connected reflected-Gram
global branch. -/
noncomputable def rootedReflectedGramPacketScaleBranchLimitData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    RootedReflectedGramPacketScaleBranchLimitData
      S depth P lgc A R H i χ :=
  (rootedReflectedGramPacketScaleSeedData
    S depth P lgc A R H i χ).branchLimitData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
