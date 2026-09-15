/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedProductApproximationRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedGramPacketScaleUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedApproximationRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedGramProbeRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeneratorCommonRadialVitaliCover

/-!
# Reflected global rooted product rows for equation (6.21)

The selected ranked target is guaranteed to lie in the reflected global radial
domain, not in the original local rooted-field domains.  This file constructs
the source-native reflected left and right fields, identifies their finite
product row with the global Hermite packet by holomorphic uniqueness, proves
the diagonal Cauchy--Schwarz bound, and identifies the packet limit with the
ranked pointed extension.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k depth : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}
variable {I : Section43ProductTimeApproximateIdentity k}
variable {anchor : Fin k -> Real}

noncomputable def rootedReflectedGlobalProductLeftArbitraryField
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (test : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex) :
    (Fin (qLeft + 1) -> Complex) -> OSHilbertSpace OS :=
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let D := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qLeft) rfl
  fun z => D.reflectedGram.atlas.gram.anchoredAtlasField
    D.reflectedGram.atlas.sourceStage.stage
    D.reflectedGram.atlas.sourceStage.germ
    (D.sourceCLM (scale + H.commonTailStart i) test) z

noncomputable def rootedReflectedGlobalProductRightArbitraryField
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (test : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex) :
    (Fin (qRight + 1) -> Complex) -> OSHilbertSpace OS :=
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let D := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qRight) rfl
  fun z => D.reflectedGram.atlas.gram.anchoredAtlasField
    D.reflectedGram.atlas.sourceStage.stage
    D.reflectedGram.atlas.sourceStage.germ
    (D.sourceCLM (scale + H.commonTailStart i) test) z

noncomputable def rootedReflectedGlobalProductRootSmearedRightArbitraryField
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (test : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex) :
    (Fin (qRight + 1) -> Complex) -> OSHilbertSpace OS :=
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  fun z => H.semigroupBridgeRootOperator lgc i scale
    (rootedReflectedGlobalProductRightArbitraryField P A R H
      qLeft qRight hindex scale test z)

noncomputable def rootedReflectedGlobalProductArbitraryCandidate
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex) :
    OSIITimeGapSpace k -> Complex :=
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  generatorSemigroupCandidate OS lgc i
    (rootedReflectedGlobalProductLeftArbitraryField P A R H
      qLeft qRight hindex scale leftTest)
    (rootedReflectedGlobalProductRootSmearedRightArbitraryField P A R H lgc
      qLeft qRight hindex scale rightTest)

theorem rootedReflectedGlobalProductArbitraryCandidate_holomorphic
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex) :
    let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
    let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
    DifferentiableOn Complex
      (rootedReflectedGlobalProductArbitraryCandidate P A R H.toContinuousTranslationData
        lgc qLeft qRight hindex scale leftTest rightTest)
      (E.radialNativeDomain i) := by
  dsimp only
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let DLeft := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth P A R (equation621NontrivialGeneratorIndex qLeft qRight hindex)
      (q := qLeft) rfl
  let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R (equation621NontrivialGeneratorIndex qLeft qRight hindex)
      (q := qRight) rfl
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R H.toContinuousTranslationData
  have hleft : DifferentiableOn Complex
      (rootedReflectedGlobalProductLeftArbitraryField P A R H.toContinuousTranslationData
        qLeft qRight hindex scale leftTest)
      (E.radialLeftDomain i) := by
    apply (DLeft.reflectedGram.atlas.generatedSpatialField_holomorphic
      DLeft.sourceCLM (scale + H.toContinuousTranslationData.commonTailStart i)
      leftTest).mono
    intro z hz
    have hz' := E.radialLeftDomain_subset i hz
    simpa [E, DLeft, equation621NontrivialGeneratorIndex,
      rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData,
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.ofBlocks,
      rootedReflectedGramLeftGeneratorOpenFieldScaleBlockRealEdgeData,
      rootedLeftNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData,
      ReflectedGramSpatialSourceData.toOpenFieldScaleBlockRealEdgeData,
      rootedScaleShiftOpenFieldBlock] using hz'.1
  have hrightRaw : DifferentiableOn Complex
      (rootedReflectedGlobalProductRightArbitraryField P A R H.toContinuousTranslationData
        qLeft qRight hindex scale rightTest)
      (E.radialRightDomain i) := by
    apply (DRight.reflectedGram.atlas.generatedSpatialField_holomorphic
      DRight.sourceCLM (scale + H.toContinuousTranslationData.commonTailStart i)
      rightTest).mono
    intro z hz
    have hz' := E.radialRightDomain_subset i hz
    simpa [E, DRight, equation621NontrivialGeneratorIndex,
      rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData,
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.ofBlocks,
      rootedReflectedGramRightGeneratorOpenFieldScaleBlockRealEdgeData,
      rootedRightNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData,
      ReflectedGramSpatialSourceData.toOpenFieldScaleBlockRealEdgeData,
      rootedScaleShiftOpenFieldBlock] using hz'.1
  have hright : DifferentiableOn Complex
      (rootedReflectedGlobalProductRootSmearedRightArbitraryField P A R
        H.toContinuousTranslationData lgc qLeft qRight hindex scale rightTest)
      (E.radialRightDomain i) := by
    exact (differentiableOn_const
      (c := H.toContinuousTranslationData.semigroupBridgeRootOperator
        lgc i scale)).clm_apply hrightRaw
  simpa [rootedReflectedGlobalProductArbitraryCandidate, i, E,
    equation621NontrivialGeneratorIndex,
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.radialNativeDomain] using
    differentiableOn_generatorSemigroupCandidate OS lgc i
      (E.radialLeftDomain_open i) (E.radialRightDomain_open i)
      hleft hright

theorem rootedReflectedGlobalProductArbitraryCandidate_eq_local_on_commonRadial
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ equation621CommonRadialCarrier P A R H
      (equation621NontrivialGeneratorIndex qLeft qRight hindex)) :
    rootedReflectedGlobalProductArbitraryCandidate P A R H.toContinuousTranslationData
        lgc qLeft qRight hindex scale leftTest rightTest
        (generatorChronologicalParameterComplexCLE
          (equation621NontrivialGeneratorIndex qLeft qRight hindex) z) =
      H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc (equation621NontrivialGeneratorIndex qLeft qRight hindex)
        scale leftTest rightTest
        (generatorChronologicalParameterComplexCLE
          (equation621NontrivialGeneratorIndex qLeft qRight hindex) z) := by
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  have hkernels :=
    equation621CommonRadialCarrier_targetParameters_mem_commonKernels
      P A R H i z hz
  dsimp only [i] at hkernels
  have hkleft := hkernels.1
  change equation621TargetLeftParameter i z ∈ openZeroConvexKernel
    ((rootedLeftNontrivialReflectedGramSpatialSourceData S depth P A R i
      (q := qLeft) rfl).reflectedGram.atlas.spatialLinearDomain ∩
      (H.left i).domain) at hkleft
  have hkright := hkernels.2
  change equation621TargetRightParameter i z ∈ openZeroConvexKernel
    ((rootedRightNontrivialReflectedGramSpatialSourceData S depth P A R i
      (q := qRight) rfl).reflectedGram.atlas.spatialLinearDomain ∩
      (H.right i).domain) at hkright
  have hleft := rootedLeftArbitrarySpatialField_eq_reflectedGram
    P A R H qLeft (qRight + 2) (by omega) (by omega) hindex
    scale leftTest (equation621TargetLeftParameter i z) hkleft
  have hright := rootedRightArbitrarySpatialField_eq_reflectedGram
    P A R H (qLeft + 2) qRight (by omega) (by omega) hindex
    scale rightTest (equation621TargetRightParameter i z) hkright
  change @inner Complex (OSHilbertSpace OS) _
      (rootedReflectedGlobalProductLeftArbitraryField P A R H.toContinuousTranslationData
        qLeft qRight hindex scale leftTest
        (equation621TargetLeftParameter i z))
      (osTimeShiftHilbertComplex OS lgc
        ((generatorChronologicalParameterComplexCLE i z) i.bridgeGlobalIndex)
        (H.toContinuousTranslationData.semigroupBridgeRootOperator lgc i scale
          (rootedReflectedGlobalProductRightArbitraryField P A R
            H.toContinuousTranslationData qLeft qRight hindex scale rightTest
            (equation621TargetRightParameter i z)))) = _
  rw [show
      rootedReflectedGlobalProductLeftArbitraryField P A R H.toContinuousTranslationData
          qLeft qRight hindex scale leftTest
          (equation621TargetLeftParameter i z) =
        H.toContinuousTranslationData.leftArbitrarySpatialGeneratorField
          i scale leftTest (equation621TargetLeftParameter i z) by
        exact hleft,
    show
      rootedReflectedGlobalProductRightArbitraryField P A R H.toContinuousTranslationData
          qLeft qRight hindex scale rightTest
          (equation621TargetRightParameter i z) =
        H.toContinuousTranslationData.rightArbitrarySpatialGeneratorField
          i scale rightTest (equation621TargetRightParameter i z) by
        exact hright]
  rfl

noncomputable def rootedAbsoluteProductReflectedLift
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (N : Nat) :
    SchwartzMap (Section43SpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Section43SpatialSpace d (k + 1)) Complex :=
  (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
    (d := d) i).comp
      (section43SpatialBasepointLiftCLM d k
        (P.absoluteProductSpatialBasepointCutoff N).toSchwartz)

@[simp] theorem rootedAbsoluteProductReflectedLift_apply
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    rootedAbsoluteProductReflectedLift P i N
        (P.absoluteProductTargetSpatialApproxIdentity.section43Probe x N) =
      RootedA0BlockContinuousTranslationData.absoluteProductTargetHermiteSpatialTest
        P i x N := by
  rfl

/-- On the common positive-real seed, the reflected full-test packet is the
local arbitrary-spatial rooted candidate for every generator split. -/
theorem rootedAbsoluteProductReflectedScalarSum_eq_localCandidate_on_realSeed
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (N scale : Nat)
    (tau : Fin k -> Real)
    (htau : tau ∈
      (selectedEquation621CommonRadialRealSeedData P A R H).realRegion) :
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
    (rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H).spatialHermiteScalarSum
        lgc
        ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i).comp lift)
        i scale
        (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed tau)) chi =
      H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc i scale
        (RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
          (d := d) i.hn
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
            spatialApprox i x N))
        (RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
          (d := d) i.hm
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
            spatialApprox i x N))
        (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed tau)) := by
  dsimp only
  let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
  let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R H.toContinuousTranslationData
  let F := rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData A R H
  let seed := selectedEquation621CommonRadialRealSeedData P A R H
  have htauCommon : osiiPositiveRealTimeEmbed tau ∈
      equation621CommonRadialCarrier P A R H i := by
    simpa [seed] using
      equation621CommonRadialRealSeed_mem_carrier P A R H i tau htau
  have hnative : generatorChronologicalParameterComplexCLE i
      (osiiPositiveRealTimeEmbed tau) ∈
        generatorSemigroupDomain i (H.toContinuousTranslationData.left i).domain
          (H.toContinuousTranslationData.right i).domain := by
    have hfull := F.radialChronologicalDomain_subset i htauCommon.2
    simpa [F] using hfull
  have hbridge :
      0 < (generatorChronologicalParameter i tau) i.bridgeGlobalIndex := by
    rw [generatorChronologicalParameter_bridge]
    exact seed.realRegion_positive htau i.bridgeGlobalIndex
  have hautomatic : generatorChronologicalParameter i tau ∈
      (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
        S depth P A R H).commonRealAutomaticSet :=
    seed.realRegion_automatic htau i
  have hglobalLocal :
      rootSmearedGeneratorOpenFieldSpatialHermiteSum
          H.toContinuousTranslationData lgc
          E.toGeneratorOpenHilbertFieldScaleFamilyData
          i scale
          (generatorChronologicalParameterComplexCLE i
            (osiiPositiveRealTimeEmbed tau)) (lift chi) =
        H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
          lgc i scale
          (generatorChronologicalParameterComplexCLE i
            (osiiPositiveRealTimeEmbed tau)) (lift chi) := by
    rw [generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed]
    calc
      rootSmearedGeneratorOpenFieldSpatialHermiteSum
          H.toContinuousTranslationData lgc
          E.toGeneratorOpenHilbertFieldScaleFamilyData
          i scale (osiiPositiveRealTimeEmbed
            (generatorChronologicalParameter i tau)) (lift chi) =
        rootSmearedGeneratorOpenFieldSpatialHermiteSum
          H.toContinuousTranslationData lgc
          F.toGeneratorOpenHilbertFieldScaleFamilyData
          i scale (osiiPositiveRealTimeEmbed
            (generatorChronologicalParameter i tau)) (lift chi) := by
        apply tsum_congr
        intro mode
        rw [rootSmearedGeneratorModeOfOS_eq_of_commonRealAutomatic
          (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
            S depth P A R H)
          H.toContinuousTranslationData i scale mode
          (generatorChronologicalParameter i tau) hbridge hautomatic]
      _ = _ := rootSmearedLocalGeneratorOpenFieldSpatialHermiteSum_eq
        H lgc i scale
          (osiiPositiveRealTimeEmbed (generatorChronologicalParameter i tau))
          (lift chi)
  change
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyData
        H.toContinuousTranslationData lgc
        E.toGeneratorOpenHilbertFieldScaleFamilyData).spatialHermiteScalarSum
        lgc
        ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i).comp lift)
        i scale (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed tau)) chi = _
  rw [← rootSmearedGeneratorOpenFieldSpatialHermiteSum_eq_spatialHermiteScalarSum_of_lift
    H.toContinuousTranslationData lgc E.toGeneratorOpenHilbertFieldScaleFamilyData
    i scale (generatorChronologicalParameterComplexCLE i
      (osiiPositiveRealTimeEmbed tau)) lift chi]
  calc
    rootSmearedGeneratorOpenFieldSpatialHermiteSum
        H.toContinuousTranslationData lgc E.toGeneratorOpenHilbertFieldScaleFamilyData
        i scale (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed tau)) (lift chi) =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
        lgc i scale (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed tau)) (lift chi) := hglobalLocal
    _ = _ := by
      symm
      apply RootedA0BlockContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate_eq_hermiteSum_of_split
        H lgc i
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i x N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i x N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetFullSpatialTest
          spatialApprox x N)
        (RootedA0BlockContinuousTranslationData.generatorSplitSpatialPullback_absoluteProductTargetFullSpatialTest
          spatialApprox i x N)
        scale (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed tau)) hnative

theorem rootedAbsoluteProductReflectedScalarSum_eq_candidate_on_realSeed
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (N scale : Nat)
    (tau : Fin k -> Real)
    (htau : tau ∈
      (selectedEquation621CommonRadialRealSeedData P A R H).realRegion) :
    let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
    (rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H).spatialHermiteScalarSum
        lgc
        ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i).comp lift)
        i scale
        (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed tau)) chi =
      rootedReflectedGlobalProductArbitraryCandidate P A R H.toContinuousTranslationData
        lgc qLeft qRight hindex scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i x N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i x N)
        (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed tau)) := by
  dsimp only
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  have htauCommon : osiiPositiveRealTimeEmbed tau ∈
      equation621CommonRadialCarrier P A R H i := by
    exact equation621CommonRadialRealSeed_mem_carrier P A R H i tau htau
  have hlocal :=
    rootedAbsoluteProductReflectedScalarSum_eq_localCandidate_on_realSeed
      P A R H lgc i spatialApprox x N scale tau htau
  have hcandidate :=
    rootedReflectedGlobalProductArbitraryCandidate_eq_local_on_commonRadial
      P A R H lgc qLeft qRight hindex scale
      (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
        spatialApprox i x N)
      (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
        spatialApprox i x N)
      (osiiPositiveRealTimeEmbed tau) htauCommon
  apply hlocal.trans
  calc
    _ = H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc i scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i x N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i x N)
        (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed tau)) := by
      congr 2
    _ = _ := by simpa only [i] using hcandidate.symm

theorem rootedAbsoluteProductReflectedScalarSum_eq_candidate_on_radial
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (N scale : Nat)
    (z : OSIITimeGapSpace k)
    (hz : z ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData).radialChronologicalDomain
          (equation621NontrivialGeneratorIndex qLeft qRight hindex)) :
    let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
    (rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H).spatialHermiteScalarSum
        lgc
        ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i).comp lift)
        i scale (generatorChronologicalParameterComplexCLE i z) chi =
      rootedReflectedGlobalProductArbitraryCandidate P A R H.toContinuousTranslationData
        lgc qLeft qRight hindex scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i x N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i x N)
        (generatorChronologicalParameterComplexCLE i z) := by
  dsimp only
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
  let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R H.toContinuousTranslationData
  let B := rootedReflectedGramRootSmearedGlobalFamily S depth P lgc A R H
  let U := E.radialChronologicalDomain i
  let seed := selectedEquation621CommonRadialRealSeedData P A R H
  let f : OSIITimeGapSpace k -> Complex := fun w =>
    B.spatialHermiteScalarSum lgc
      ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
        (d := d) i).comp lift)
      i scale (generatorChronologicalParameterComplexCLE i w) chi
  let g : OSIITimeGapSpace k -> Complex := fun w =>
    rootedReflectedGlobalProductArbitraryCandidate P A R H.toContinuousTranslationData
      lgc qLeft qRight hindex scale
      (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
        spatialApprox i x N)
      (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
        spatialApprox i x N)
      (generatorChronologicalParameterComplexCLE i w)
  have hU_open : IsOpen U := E.radialChronologicalDomain_open i
  have hU_connected : IsConnected U := by
    obtain ⟨tau, htau⟩ := seed.realRegion_nonempty
    have hc : osiiPositiveRealTimeEmbed tau ∈ U := by
      have hcommon :=
        equation621CommonRadialRealSeed_mem_carrier P A R H i tau htau
      exact hcommon.1
    have hpath := E.radialChronologicalDomain_inter_isPathConnected
      E i i hc hc
    simpa [U] using hpath.isConnected
  have hf : DifferentiableOn Complex f U := by
    apply DifferentiableOn.comp
      (B.spatialHermiteScalarSum_differentiableOn lgc
        ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i).comp lift) i scale chi)
    · exact (generatorChronologicalParameterComplexCLE i).differentiable.differentiableOn
    · intro w hw
      have hdomain := E.radialChronologicalDomain_subset i hw
      change generatorChronologicalParameterComplexCLE i w ∈
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth P A R H.toContinuousTranslationData).domain i
      exact hdomain
  have hg : DifferentiableOn Complex g U := by
    apply DifferentiableOn.comp
      (rootedReflectedGlobalProductArbitraryCandidate_holomorphic
        P A R H lgc qLeft qRight hindex scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i x N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i x N))
    · exact (generatorChronologicalParameterComplexCLE i).differentiable.differentiableOn
    · intro w hw
      exact hw
  have hreal : forall tau, tau ∈ seed.realRegion ->
      f (SCV.realToComplex tau) = g (SCV.realToComplex tau) := by
    intro tau htau
    rw [show SCV.realToComplex tau = osiiPositiveRealTimeEmbed tau by rfl]
    exact rootedAbsoluteProductReflectedScalarSum_eq_candidate_on_realSeed
      P A R H lgc qLeft qRight hindex spatialApprox x N scale tau htau
  have hseed_mem : forall tau, tau ∈ seed.realRegion ->
      SCV.realToComplex tau ∈ U := by
    intro tau htau
    rw [show SCV.realToComplex tau = osiiPositiveRealTimeEmbed tau by rfl]
    exact (equation621CommonRadialRealSeed_mem_carrier
      P A R H i tau htau).1
  have hzero := SCV.identity_theorem_totally_real
    hU_open hU_connected (hf.sub hg)
    seed.realRegion_open seed.realRegion_nonempty hseed_mem
    (fun tau htau => sub_eq_zero.mpr (hreal tau htau))
    z hz
  exact sub_eq_zero.mp hzero

noncomputable def rootedReflectedGlobalProductLeftDiagonal
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (test : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex)
    (z : Fin (qLeft + 1) -> Complex) : Complex :=
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let D := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qLeft) rfl
  (D.reflectedGram.atlas.gram.cauchy
    (D.sourceCLM (scale + H.commonTailStart i) test)
    (D.sourceCLM (scale + H.commonTailStart i) test)).scalar
      (reflectedCauchyCenter z)

noncomputable def rootedReflectedGlobalProductRightDiagonal
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (test : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex)
    (z : Fin (qRight + 1) -> Complex) : Complex :=
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let D := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qRight) rfl
  (D.reflectedGram.atlas.gram.cauchy
    (D.sourceCLM (scale + H.commonTailStart i) test)
    (D.sourceCLM (scale + H.commonTailStart i) test)).scalar
      (reflectedCauchyCenter z)

/-- The actual finite rooted product row admits a sharp reflected estimate
after reserving any prescribed positive part of its bridge. The diagonal
vectors are damped by that same shift, not by a cutoff-dependent margin. -/
theorem norm_rootedReflectedGlobalProductArbitraryCandidate_le_sqrt_shifted_diagonals
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (z : OSIITimeGapSpace k)
    (hbridge : epsilon <
      (z (equation621NontrivialGeneratorIndex qLeft qRight hindex
        ).bridgeGlobalIndex).re) :
    let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
    let left := rootedReflectedGlobalProductLeftArbitraryField
      P A R H qLeft qRight hindex scale leftTest
      (equation621TargetLeftParameter i z)
    let right := rootedReflectedGlobalProductRightArbitraryField
      P A R H qLeft qRight hindex scale rightTest
      (equation621TargetRightParameter i z)
    ‖rootedReflectedGlobalProductArbitraryCandidate P A R H lgc
        qLeft qRight hindex scale leftTest rightTest
        (generatorChronologicalParameterComplexCLE i z)‖ <=
      Real.sqrt
        (‖@inner Complex (OSHilbertSpace OS) _ left
            (osiiOriginalOSHilbertComplex OS (epsilon : Complex) left)‖ *
          ‖@inner Complex (OSHilbertSpace OS) _ right
            (osiiOriginalOSHilbertComplex OS (epsilon : Complex) right)‖) := by
  dsimp only
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let left := rootedReflectedGlobalProductLeftArbitraryField
    P A R H qLeft qRight hindex scale leftTest
    (equation621TargetLeftParameter i z)
  let right := rootedReflectedGlobalProductRightArbitraryField
    P A R H qLeft qRight hindex scale rightTest
    (equation621TargetRightParameter i z)
  have hbridgeEq :
      (generatorChronologicalParameterComplexCLE i z) i.bridgeGlobalIndex =
        z i.bridgeGlobalIndex := generatorChronological_split_fst i z
  have hremaining : 0 < (z i.bridgeGlobalIndex - (epsilon : Complex)).re := by
    simpa using sub_pos.mpr hbridge
  change ‖@inner Complex (OSHilbertSpace OS) _ left
      (osiiOriginalOSHilbertComplex OS
        ((generatorChronologicalParameterComplexCLE i z) i.bridgeGlobalIndex)
        (H.semigroupBridgeRootOperatorOfOS i scale right))‖ <= _
  rw [hbridgeEq]
  simpa only [sub_add_cancel] using
    H.norm_inner_semigroupBridgeRootOperatorOfOS_shift_le
      i scale hepsilon hremaining left right

theorem norm_rootedReflectedGlobalProductArbitraryCandidate_le_sqrt_diagonals
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex)
    (z : OSIITimeGapSpace k)
    (hz : z ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H).radialChronologicalDomain
          (equation621NontrivialGeneratorIndex qLeft qRight hindex)) :
    ‖rootedReflectedGlobalProductArbitraryCandidate P A R H lgc
        qLeft qRight hindex scale leftTest rightTest
        (generatorChronologicalParameterComplexCLE
          (equation621NontrivialGeneratorIndex qLeft qRight hindex) z)‖ <=
      Real.sqrt
        (‖rootedReflectedGlobalProductLeftDiagonal P A R H qLeft qRight hindex
            scale leftTest (equation621TargetLeftParameter
              (equation621NontrivialGeneratorIndex qLeft qRight hindex) z)‖ *
          ‖rootedReflectedGlobalProductRightDiagonal P A R H qLeft qRight hindex
            scale rightTest (equation621TargetRightParameter
              (equation621NontrivialGeneratorIndex qLeft qRight hindex) z)‖) := by
  let i := equation621NontrivialGeneratorIndex qLeft qRight hindex
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R H
  let DLeft := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth P A R (equation621NontrivialGeneratorIndex qLeft qRight hindex)
      (q := qLeft) rfl
  let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R (equation621NontrivialGeneratorIndex qLeft qRight hindex)
      (q := qRight) rfl
  have hznative : generatorChronologicalParameterComplexCLE i z ∈
      E.radialNativeDomain i := hz
  have hzLeft : equation621TargetLeftParameter i z ∈
      DLeft.reflectedGram.atlas.spatialLinearDomain := by
    have hleft := hznative.2.1
    change equation621TargetLeftParameter i z ∈
      openZeroConvexKernel DLeft.reflectedGram.atlas.spatialLinearDomain at hleft
    rcases hleft with ⟨V, _hVOpen, _hVConvex, _hzero, hV, hzV⟩
    exact hV hzV
  have hzRight : equation621TargetRightParameter i z ∈
      DRight.reflectedGram.atlas.spatialLinearDomain := by
    have hright := hznative.2.2
    change equation621TargetRightParameter i z ∈
      openZeroConvexKernel DRight.reflectedGram.atlas.spatialLinearDomain at hright
    rcases hright with ⟨V, _hVOpen, _hVConvex, _hzero, hV, hzV⟩
    exact hV hzV
  have hleft :
      ‖rootedReflectedGlobalProductLeftArbitraryField P A R H qLeft qRight hindex
          scale leftTest (equation621TargetLeftParameter i z)‖ ^ 2 <=
        ‖rootedReflectedGlobalProductLeftDiagonal P A R H qLeft qRight hindex
          scale leftTest (equation621TargetLeftParameter i z)‖ := by
    convert DLeft.norm_spatialFieldCLM_sq_le_norm_diagonalScalar
      (scale + H.commonTailStart i) leftTest
      (equation621TargetLeftParameter i z) hzLeft using 1 <;>
      simp [rootedReflectedGlobalProductLeftArbitraryField,
        rootedReflectedGlobalProductLeftDiagonal, i, DLeft,
        equation621NontrivialGeneratorIndex,
        UniversalCompactCarrierAnchoredAtlasData.spatialFieldCLM_apply] <;> congr
  have hrightRaw :
      ‖rootedReflectedGlobalProductRightArbitraryField P A R H qLeft qRight hindex
          scale rightTest (equation621TargetRightParameter i z)‖ ^ 2 <=
        ‖rootedReflectedGlobalProductRightDiagonal P A R H qLeft qRight hindex
          scale rightTest (equation621TargetRightParameter i z)‖ := by
    convert DRight.norm_spatialFieldCLM_sq_le_norm_diagonalScalar
      (scale + H.commonTailStart i) rightTest
      (equation621TargetRightParameter i z) hzRight using 1 <;>
      simp [rootedReflectedGlobalProductRightArbitraryField,
        rootedReflectedGlobalProductRightDiagonal, i, DRight,
        equation621NontrivialGeneratorIndex,
        UniversalCompactCarrierAnchoredAtlasData.spatialFieldCLM_apply] <;> congr
  have hcontract :
      ‖rootedReflectedGlobalProductRootSmearedRightArbitraryField P A R H lgc
          qLeft qRight hindex scale rightTest
          (equation621TargetRightParameter i z)‖ <=
        ‖rootedReflectedGlobalProductRightArbitraryField P A R H
          qLeft qRight hindex scale rightTest
          (equation621TargetRightParameter i z)‖ := by
    calc
      _ <= ‖H.semigroupBridgeRootOperator lgc i scale‖ *
          ‖rootedReflectedGlobalProductRightArbitraryField P A R H
            qLeft qRight hindex scale rightTest
            (equation621TargetRightParameter i z)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ <= 1 * ‖rootedReflectedGlobalProductRightArbitraryField P A R H
            qLeft qRight hindex scale rightTest
            (equation621TargetRightParameter i z)‖ := by
        gcongr
        exact H.semigroupBridgeRootOperator_norm_le_one lgc i scale
      _ = _ := one_mul _
  have hright :
      ‖rootedReflectedGlobalProductRootSmearedRightArbitraryField P A R H lgc
          qLeft qRight hindex scale rightTest
          (equation621TargetRightParameter i z)‖ ^ 2 <=
        ‖rootedReflectedGlobalProductRightDiagonal P A R H qLeft qRight hindex
          scale rightTest (equation621TargetRightParameter i z)‖ :=
    (pow_le_pow_left₀ (norm_nonneg _) hcontract 2).trans hrightRaw
  apply norm_generatorSemigroupCandidate_le_sqrt_mul_of_norm_sq_le
    OS lgc i
    (rootedReflectedGlobalProductLeftArbitraryField P A R H
      qLeft qRight hindex scale leftTest)
    (rootedReflectedGlobalProductRootSmearedRightArbitraryField P A R H lgc
      qLeft qRight hindex scale rightTest)
    (generatorChronologicalParameterComplexCLE i z) hznative.1
    ‖rootedReflectedGlobalProductLeftDiagonal P A R H qLeft qRight hindex
      scale leftTest (equation621TargetLeftParameter i z)‖
    ‖rootedReflectedGlobalProductRightDiagonal P A R H qLeft qRight hindex
      scale rightTest (equation621TargetRightParameter i z)‖
    (norm_nonneg _) (norm_nonneg _)
  · exact hleft
  · exact hright

/-- The reflected packet target row converges to the selected honest
extension for every generator split, including the two one-particle endpoint
splits. -/
theorem current_reflectedAbsoluteProductTarget_row_tendsto_any
    {rank : Nat}
    {RankP : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k}
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
        Q.holomorphic.toContinuousTranslationData i hub z}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank RankP lgc i hub atlas z C0 Q D)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier)
    (x : Fin (k * d) -> Real) (N : Nat) :
    let y := equation621SplitTargetSpatialPoint i x
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe y N
    let point := generatorChronologicalParameterComplexCLE i
      (w - osiiPositiveRealTimeEmbed C0.anchor)
    Tendsto
      (fun scale =>
        (rootedReflectedGramRootSmearedGlobalFamily
          S depth D.adapted lgc Q.packet Q.roots Q.holomorphic
        ).spatialHermiteScalarSum lgc
          ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i).comp lift)
          i scale point chi)
      atTop
      (nhds (E.current.extension.toTimeContinuationStage.distribution w
        ((spatialApprox.equation621SplitTargetSpatialApproxIdentity i
          ).section43Probe x N))) := by
  dsimp only
  let y := equation621SplitTargetSpatialPoint i x
  let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
  let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe y N
  let targetChi :=
    (spatialApprox.equation621SplitTargetSpatialApproxIdentity i
      ).section43Probe x N
  let point := generatorChronologicalParameterComplexCLE i
    (w - osiiPositiveRealTimeEmbed C0.anchor)
  let BF := rootedReflectedGramPacketScaleBranchLimitDataOfLift
    S depth D.adapted lgc Q.packet Q.roots Q.holomorphic i lift chi
  have hradial :=
    RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain_any
      E w hw
  have hbranch : point ∈ rootedReflectedGramPacketScaleBranch
      S depth D.adapted lgc Q.packet Q.roots Q.holomorphic i := by
    have hchron : w - osiiPositiveRealTimeEmbed C0.anchor ∈
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth D.adapted Q.packet Q.roots
            Q.holomorphic.toContinuousTranslationData
        ).radialChronologicalDomain i := hradial
    exact radialChronologicalDomain_subset_rootedReflectedGramTwoScaleDomain
      S depth D.adapted lgc Q.packet Q.roots Q.holomorphic i hchron
  have hhead : section43SpatialHeadMarginal (lift chi) = targetChi := by
    rw [show lift chi =
      RootedA0BlockContinuousTranslationData.absoluteProductTargetHermiteSpatialTest
        spatialApprox i y N by
      exact rootedAbsoluteProductReflectedLift_apply spatialApprox i y N]
    rw [← RootedA0BlockContinuousTranslationData.absoluteProductTargetReducedSpatialTest]
    exact (spatialApprox.equation621SplitTargetSpatialApproxIdentity_section43Probe_adapted_eq
      i x N).symm
  have hlimit : BF.limit point =
      (rootedReflectedGramPacketScaleBranchLimitData
        S depth D.adapted lgc Q.packet Q.roots Q.holomorphic i targetChi
      ).limit point :=
    RootedA0BlockContinuousTranslationData.rootedReflectedGramPacketScaleBranchLimitDataOfLift_eq_canonical_of_headMarginal_eq
      S depth D.adapted lgc Q.packet Q.roots Q.holomorphic i lift chi targetChi
      hhead point hbranch
  have hcurrent : E.current.extension.toTimeContinuationStage.distribution
      w targetChi =
      (rootedReflectedGramPacketScaleBranchLimitData
        S depth D.adapted lgc Q.packet Q.roots Q.holomorphic i targetChi
      ).limit point := by
    rw [E.current.extension.newStage_eqOn_generatorDomain i
      (E.current.carrier_subset_extensionDomain hw)]
    simpa [targetChi, point] using
      E.current_packetScaleLimit_eq w hw targetChi
  have ht := BF.locallyUniform.tendsto_at hbranch
  rw [hlimit, ← hcurrent] at ht
  simpa [BF, lift, chi, point, targetChi] using ht

theorem current_reflectedAbsoluteProductTarget_row_tendsto
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
    let y := equation621SplitTargetSpatialPoint i x
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe y N
    let point := generatorChronologicalParameterComplexCLE i
      (w - osiiPositiveRealTimeEmbed C0.anchor)
    Tendsto
      (fun scale =>
        (rootedReflectedGramRootSmearedGlobalFamily
          S depth D.adapted lgc Q.packet Q.roots Q.holomorphic
        ).spatialHermiteScalarSum lgc
          ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i).comp lift)
          i scale point chi)
      atTop
      (nhds (E.current.extension.toTimeContinuationStage.distribution w
        ((spatialApprox.equation621SplitTargetSpatialApproxIdentity i
          ).section43Probe x N))) := by
  simpa using current_reflectedAbsoluteProductTarget_row_tendsto_any
    E spatialApprox w hw x N

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
