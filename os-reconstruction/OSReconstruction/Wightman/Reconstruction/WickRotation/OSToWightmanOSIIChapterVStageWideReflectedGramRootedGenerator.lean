/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedSources
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredSpatialSmearing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedTwoScaleFamily

















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

/-- The genuine original-OS all-split rooted family attached to the entire
same-depth reflected-Gram source atlas. -/
noncomputable def rootedReflectedGramRootSmearedGlobalFamilyOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorOpenHilbertFieldScaleFamilyData OS k :=
  rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS
    H.toContinuousTranslationData
    (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
      ).toGeneratorOpenHilbertFieldScaleFamilyData

/-- Compatibility presentation of the original-OS reflected-Gram all-split
rooted family. -/
noncomputable def rootedReflectedGramRootSmearedGlobalFamily
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (_lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorOpenHilbertFieldScaleFamilyData OS k :=
  rootedReflectedGramRootSmearedGlobalFamilyOfOS
    S depth P A R H

/-- The complete original-OS reflected-Gram global rooted Hermite series
agrees with the actual local rooted series on their common source germ. -/
theorem
    rootedReflectedGramRootSmearedSpatialHermiteGeneratorSumOfOS_eq
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (hz :
      z ∈
        (rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
          S depth P A R H).domain i)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        H.toContinuousTranslationData
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth P A R H.toContinuousTranslationData
          ).toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z F =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSumOfOS
        i timeScale z F := by
  calc
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        H.toContinuousTranslationData
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth P A R H.toContinuousTranslationData
          ).toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z F =
      rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        H.toContinuousTranslationData
        (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          A R H).toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z F := by
      exact
        rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS_eq_on_commonComplex
          (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
            S depth P A R H)
          H.toContinuousTranslationData
          (rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
            S depth P A R H)
          i timeScale z hz F
    _ =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSumOfOS
        i timeScale z F :=
      rootSmearedLocalGeneratorOpenFieldSpatialHermiteSumOfOS_eq
        H i timeScale z F

/-- The complete reflected-Gram global root-smeared Hermite series agrees
with the original local rooted series on the common complex germ. -/
theorem
    rootedReflectedGramRootSmearedSpatialHermiteGeneratorSum_eq
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (hz :
      z ∈
        (rootedReflectedGramGeneratorCommonComplexModeGermData
          S depth P lgc A R H).domain i)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSum
        H.toContinuousTranslationData lgc
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth P A R H.toContinuousTranslationData
          ).toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z F =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
        lgc i timeScale z F := by
  calc
    rootSmearedGeneratorOpenFieldSpatialHermiteSum
        H.toContinuousTranslationData lgc
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth P A R H.toContinuousTranslationData
          ).toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z F =
      rootSmearedGeneratorOpenFieldSpatialHermiteSum
        H.toContinuousTranslationData lgc
        (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          A R H).toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z F := by
      exact
        rootSmearedGeneratorOpenFieldSpatialHermiteSum_eq_on_commonComplex
          (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
            S depth P A R H)
          H.toContinuousTranslationData lgc
          (rootedReflectedGramGeneratorCommonComplexModeGermData
            S depth P lgc A R H)
          i timeScale z hz F
    _ =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
        lgc i timeScale z F :=
      rootSmearedLocalGeneratorOpenFieldSpatialHermiteSum_eq
        H lgc i timeScale z F

/-- The genuine original-OS reflected-Gram global rooted Hermite series
converges locally uniformly to the original packet-scale Vitali limit on
their actual common complex source germ. -/
theorem
    rootedReflectedGramRootSmearedSpatialHermiteGeneratorSumOfOS_packetScale_seed
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    TendstoLocallyUniformlyOn
      (fun timeScale z =>
        rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
          H.toContinuousTranslationData
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth P A R H.toContinuousTranslationData
            ).toGeneratorOpenHilbertFieldScaleFamilyData
          i timeScale z F)
      (rootedPacketScaleLimitDataOfOS H i F).limit
      atTop
      ((rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
        S depth P A R H).domain i) := by
  let C :=
    rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
      S depth P A R H
  let Q := rootedPacketScaleLimitDataOfOS H i F
  have hsub :
      C.domain i ⊆
        generatorSemigroupDomain i
          (H.toContinuousTranslationData.left i).domain
          (H.toContinuousTranslationData.right i).domain := by
    intro z hz
    simpa [C] using C.ball_subset_second i hz
  have hlocal :=
    Q.locallyUniform.mono hsub
  apply hlocal.congr
  intro timeScale z hz
  exact
    (rootedReflectedGramRootSmearedSpatialHermiteGeneratorSumOfOS_eq
      S depth P A R H i timeScale z hz F).symm

/-- The reflected-Gram global root-smeared Hermite series converges locally
uniformly on the common complex germ to the original rooted packet-scale
Vitali limit. -/
theorem
    rootedReflectedGramRootSmearedSpatialHermiteGeneratorSum_packetScale_seed
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    TendstoLocallyUniformlyOn
      (fun timeScale z =>
        rootSmearedGeneratorOpenFieldSpatialHermiteSum
          H.toContinuousTranslationData lgc
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth P A R H.toContinuousTranslationData
            ).toGeneratorOpenHilbertFieldScaleFamilyData
          i timeScale z F)
      (rootedPacketScaleLimitData H lgc i F).limit
      atTop
      ((rootedReflectedGramGeneratorCommonComplexModeGermData
        S depth P lgc A R H).domain i) := by
  let C :=
    rootedReflectedGramGeneratorCommonComplexModeGermData
      S depth P lgc A R H
  let Q := rootedPacketScaleLimitData H lgc i F
  have hsub :
      C.domain i ⊆
        generatorSemigroupDomain i
          (H.toContinuousTranslationData.left i).domain
          (H.toContinuousTranslationData.right i).domain := by
    intro z hz
    simpa [C] using C.ball_subset_second i hz
  have hlocal :=
    Q.locallyUniform.mono hsub
  apply hlocal.congr
  intro timeScale z hz
  exact
    (rootedReflectedGramRootSmearedSpatialHermiteGeneratorSum_eq
      S depth P lgc A R H i timeScale z hz F).symm

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
