/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedApproximationRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621EndpointProbeRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedL1RankSuccessorFlatProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorAdaptiveShiftHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedPointedInduction











noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

open RootedTargetHubPointedDirectExtensionData

variable {d k depth rank : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}
variable {iota : Type*}

noncomputable def rootedReflectedGlobalLeftEndpointRightArbitraryField
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (qRight : Nat)
    (hindex : k = 1 + (qRight + 2) - 1)
    (scale : Nat)
    (test : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex) :
    (Fin (qRight + 1) -> Complex) -> OSHilbertSpace OS :=
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  let D := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qRight) rfl
  fun z => D.reflectedGram.atlas.gram.anchoredAtlasField
    D.reflectedGram.atlas.sourceStage.stage
    D.reflectedGram.atlas.sourceStage.germ
    (D.sourceCLM (scale + H.commonTailStart i) test) z

noncomputable def rootedReflectedGlobalLeftEndpointRootSmearedRightArbitraryField
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qRight : Nat)
    (hindex : k = 1 + (qRight + 2) - 1)
    (scale : Nat)
    (test : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex) :
    (Fin (qRight + 1) -> Complex) -> OSHilbertSpace OS :=
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  fun z => H.semigroupBridgeRootOperator lgc i scale
    (rootedReflectedGlobalLeftEndpointRightArbitraryField
      P A R H qRight hindex scale test z)

noncomputable def rootedReflectedGlobalLeftEndpointArbitraryCandidate
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qRight : Nat)
    (hindex : k = 1 + (qRight + 2) - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d 1) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex) :
    OSIITimeGapSpace k -> Complex :=
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  generatorSemigroupCandidate OS lgc i
    (H.leftArbitrarySpatialGeneratorField i scale leftTest)
    (rootedReflectedGlobalLeftEndpointRootSmearedRightArbitraryField
      P A R H lgc qRight hindex scale rightTest)

theorem rootedReflectedGlobalLeftEndpointArbitraryCandidate_holomorphic
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qRight : Nat)
    (hindex : k = 1 + (qRight + 2) - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d 1) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex) :
    let i := equation621LeftEndpointGeneratorIndex qRight hindex
    let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
    DifferentiableOn Complex
      (rootedReflectedGlobalLeftEndpointArbitraryCandidate
        P A R H.toContinuousTranslationData lgc qRight hindex scale
          leftTest rightTest)
      (E.radialNativeDomain i) := by
  dsimp only
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  let T := H.toContinuousTranslationData
  let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qRight) rfl
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R T
  have hleft : DifferentiableOn Complex
      (T.leftArbitrarySpatialGeneratorField i scale leftTest)
      (E.radialLeftDomain i) := by
    have hparam : ∀ z : Fin (i.n - 1) -> Complex, z = 0 := by
      intro z
      funext a
      have a0 : Fin 0 := by
        simpa [i, equation621LeftEndpointGeneratorIndex] using a
      exact Fin.elim0 a0
    have hconst : T.leftArbitrarySpatialGeneratorField i scale leftTest =
        fun _ => T.leftArbitrarySpatialGeneratorField i scale leftTest 0 := by
      funext z
      congr 1
      exact hparam z
    rw [hconst]
    exact differentiableOn_const
      (c := T.leftArbitrarySpatialGeneratorField i scale leftTest 0)
  have hrightRaw : DifferentiableOn Complex
      (rootedReflectedGlobalLeftEndpointRightArbitraryField
        P A R T qRight hindex scale rightTest)
      (E.radialRightDomain i) := by
    apply (DRight.reflectedGram.atlas.generatedSpatialField_holomorphic
      DRight.sourceCLM (scale + T.commonTailStart i) rightTest).mono
    intro z hz
    have hz' := E.radialRightDomain_subset i hz
    simpa [E, DRight, i,
      rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData,
      rootedReflectedGramRightGeneratorOpenFieldScaleBlockRealEdgeData,
      rootedRightNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData,
      ReflectedGramSpatialSourceData.toOpenFieldScaleBlockRealEdgeData,
      rootedScaleShiftOpenFieldBlock,
      rootedReflectedGlobalLeftEndpointRightArbitraryField] using hz'.1
  have hright : DifferentiableOn Complex
      (rootedReflectedGlobalLeftEndpointRootSmearedRightArbitraryField
        P A R T lgc qRight hindex scale rightTest)
      (E.radialRightDomain i) := by
    exact (differentiableOn_const
      (c := T.semigroupBridgeRootOperator lgc i scale)).clm_apply hrightRaw
  simpa [rootedReflectedGlobalLeftEndpointArbitraryCandidate, i, E] using
    differentiableOn_generatorSemigroupCandidate OS lgc i
      (E.radialLeftDomain_open i) (E.radialRightDomain_open i)
      hleft hright

theorem rootedReflectedGlobalLeftEndpointArbitraryCandidate_eq_local_on_commonRadial
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qRight : Nat)
    (hindex : k = 1 + (qRight + 2) - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d 1) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ equation621CommonRadialCarrier P A R H
      (equation621LeftEndpointGeneratorIndex qRight hindex)) :
    rootedReflectedGlobalLeftEndpointArbitraryCandidate
        P A R H.toContinuousTranslationData lgc qRight hindex scale
          leftTest rightTest
        (generatorChronologicalParameterComplexCLE
          (equation621LeftEndpointGeneratorIndex qRight hindex) z) =
      H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc (equation621LeftEndpointGeneratorIndex qRight hindex)
        scale leftTest rightTest
        (generatorChronologicalParameterComplexCLE
          (equation621LeftEndpointGeneratorIndex qRight hindex) z) := by
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  have hkernels :=
    equation621CommonRadialCarrier_targetParameters_mem_commonKernels
      P A R H i z hz
  have hright := rootedRightArbitrarySpatialField_eq_reflectedGram
    P A R H 1 qRight (by omega) (by omega) hindex
    scale rightTest (equation621TargetRightParameter i z) (by
      simpa [i, equation621LeftEndpointGeneratorIndex] using hkernels.2)
  rw [rootedReflectedGlobalLeftEndpointArbitraryCandidate,
    RootedA0BlockContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate,
    generatorSemigroupCandidate_apply, generatorSemigroupCandidate_apply]
  change @inner Complex (OSHilbertSpace OS) _
      (H.toContinuousTranslationData.leftArbitrarySpatialGeneratorField
        i scale leftTest (equation621TargetLeftParameter i z))
      (osTimeShiftHilbertComplex OS lgc
        ((generatorChronologicalParameterComplexCLE i z) i.bridgeGlobalIndex)
        (H.toContinuousTranslationData.semigroupBridgeRootOperator lgc i scale
          (rootedReflectedGlobalLeftEndpointRightArbitraryField
            P A R H.toContinuousTranslationData qRight hindex scale rightTest
            (equation621TargetRightParameter i z)))) = _
  rw [show
      rootedReflectedGlobalLeftEndpointRightArbitraryField
          P A R H.toContinuousTranslationData qRight hindex scale rightTest
          (equation621TargetRightParameter i z) =
        H.toContinuousTranslationData.rightArbitrarySpatialGeneratorField
          i scale rightTest (equation621TargetRightParameter i z) by
    simpa [i, rootedReflectedGlobalLeftEndpointRightArbitraryField,
      equation621LeftEndpointGeneratorIndex] using hright]
  simp only [RootedA0BlockContinuousTranslationData.rootSmearedRightArbitrarySpatialGeneratorField]
  rfl

theorem rootedAbsoluteProductReflectedScalarSum_eq_leftEndpointCandidate_on_radial
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qRight : Nat)
    (hindex : k = 1 + (qRight + 2) - 1)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (N scale : Nat)
    (z : OSIITimeGapSpace k)
    (hz : z ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData).radialChronologicalDomain
          (equation621LeftEndpointGeneratorIndex qRight hindex)) :
    let i := equation621LeftEndpointGeneratorIndex qRight hindex
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
    (rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H).spatialHermiteScalarSum
        lgc
        ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i).comp lift)
        i scale (generatorChronologicalParameterComplexCLE i z) chi =
      rootedReflectedGlobalLeftEndpointArbitraryCandidate
        P A R H.toContinuousTranslationData lgc qRight hindex scale
        (RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
          (d := d) i.hn
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
            spatialApprox i x N))
        (RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
          (d := d) i.hm
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
            spatialApprox i x N))
        (generatorChronologicalParameterComplexCLE i z) := by
  dsimp only
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
  let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R H.toContinuousTranslationData
  let B := rootedReflectedGramRootSmearedGlobalFamily S depth P lgc A R H
  let U := E.radialChronologicalDomain i
  let seed := selectedEquation621CommonRadialRealSeedData P A R H
  let leftTest := RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
    (d := d) i.hn
    (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
      spatialApprox i x N)
  let rightTest := RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
    (d := d) i.hm
    (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
      spatialApprox i x N)
  let f : OSIITimeGapSpace k -> Complex := fun w =>
    B.spatialHermiteScalarSum lgc
      ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
        (d := d) i).comp lift)
      i scale (generatorChronologicalParameterComplexCLE i w) chi
  let g : OSIITimeGapSpace k -> Complex := fun w =>
    rootedReflectedGlobalLeftEndpointArbitraryCandidate
      P A R H.toContinuousTranslationData lgc qRight hindex scale
        leftTest rightTest (generatorChronologicalParameterComplexCLE i w)
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
      simpa [B, E, rootedReflectedGramRootSmearedGlobalFamily,
        rootSmearedGeneratorOpenHilbertFieldScaleFamilyData] using hdomain
  have hg : DifferentiableOn Complex g U := by
    apply DifferentiableOn.comp
      (rootedReflectedGlobalLeftEndpointArbitraryCandidate_holomorphic
        P A R H lgc qRight hindex scale leftTest rightTest)
    · exact (generatorChronologicalParameterComplexCLE i).differentiable.differentiableOn
    · intro w hw
      exact hw
  have hreal : forall tau, tau ∈ seed.realRegion ->
      f (SCV.realToComplex tau) = g (SCV.realToComplex tau) := by
    intro tau htau
    rw [show SCV.realToComplex tau = osiiPositiveRealTimeEmbed tau by rfl]
    have hcommon :=
      equation621CommonRadialRealSeed_mem_carrier P A R H i tau htau
    have hlocal :=
      rootedAbsoluteProductReflectedScalarSum_eq_localCandidate_on_realSeed
        P A R H lgc i spatialApprox x N scale tau htau
    have hcandidate :=
      rootedReflectedGlobalLeftEndpointArbitraryCandidate_eq_local_on_commonRadial
        P A R H lgc qRight hindex scale leftTest rightTest
          (osiiPositiveRealTimeEmbed tau) hcommon
    exact hlocal.trans hcandidate.symm
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

noncomputable def rootedReflectedGlobalLeftEndpointRightDiagonal
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (qRight : Nat)
    (hindex : k = 1 + (qRight + 2) - 1)
    (scale : Nat)
    (test : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex)
    (z : Fin (qRight + 1) -> Complex) : Complex :=
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  let D := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qRight) rfl
  (D.reflectedGram.atlas.gram.cauchy
    (D.sourceCLM (scale + H.commonTailStart i) test)
    (D.sourceCLM (scale + H.commonTailStart i) test)).scalar
      (reflectedCauchyCenter z)

theorem norm_rootedReflectedGlobalLeftEndpointCandidate_le_sqrt_diagonals
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qRight : Nat)
    (hindex : k = 1 + (qRight + 2) - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d 1) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex)
    (z : OSIITimeGapSpace k)
    (hz : z ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H).radialChronologicalDomain
          (equation621LeftEndpointGeneratorIndex qRight hindex)) :
    let i := equation621LeftEndpointGeneratorIndex qRight hindex
    let leftDiagonal := @inner Complex (OSHilbertSpace OS) _
      (H.leftArbitrarySpatialGeneratorField i scale leftTest 0)
      (H.leftArbitrarySpatialGeneratorField i scale leftTest 0)
    ‖rootedReflectedGlobalLeftEndpointArbitraryCandidate
        P A R H lgc qRight hindex scale leftTest rightTest
        (generatorChronologicalParameterComplexCLE i z)‖ <=
      Real.sqrt
        (‖leftDiagonal‖ *
          ‖rootedReflectedGlobalLeftEndpointRightDiagonal
            P A R H qRight hindex scale rightTest
              (equation621TargetRightParameter i z)‖) := by
  dsimp only
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R H
  let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qRight) rfl
  let leftDiagonal := @inner Complex (OSHilbertSpace OS) _
    (H.leftArbitrarySpatialGeneratorField i scale leftTest 0)
    (H.leftArbitrarySpatialGeneratorField i scale leftTest 0)
  have hznative : generatorChronologicalParameterComplexCLE i z ∈
      E.radialNativeDomain i := hz
  have hzRight : equation621TargetRightParameter i z ∈
      DRight.reflectedGram.atlas.spatialLinearDomain := by
    have hright := hznative.2.2
    change equation621TargetRightParameter i z ∈
      openZeroConvexKernel DRight.reflectedGram.atlas.spatialLinearDomain at hright
    rcases hright with ⟨V, _hVOpen, _hVConvex, _hzero, hV, hzV⟩
    exact hV hzV
  have hzLeft : equation621TargetLeftParameter i z = 0 := by
    funext a
    have a0 : Fin 0 := by
      simpa [i, equation621LeftEndpointGeneratorIndex] using a
    exact Fin.elim0 a0
  have hleft :
      ‖H.leftArbitrarySpatialGeneratorField i scale leftTest
          (equation621TargetLeftParameter i z)‖ ^ 2 <= ‖leftDiagonal‖ := by
    rw [hzLeft]
    dsimp [leftDiagonal]
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hrightRaw :
      ‖rootedReflectedGlobalLeftEndpointRightArbitraryField
          P A R H qRight hindex scale rightTest
          (equation621TargetRightParameter i z)‖ ^ 2 <=
        ‖rootedReflectedGlobalLeftEndpointRightDiagonal
          P A R H qRight hindex scale rightTest
          (equation621TargetRightParameter i z)‖ := by
    simpa [rootedReflectedGlobalLeftEndpointRightArbitraryField,
      rootedReflectedGlobalLeftEndpointRightDiagonal, i, DRight,
      UniversalCompactCarrierAnchoredAtlasData.spatialFieldCLM_apply] using
      DRight.norm_spatialFieldCLM_sq_le_norm_diagonalScalar
        (scale + H.commonTailStart i) rightTest
        (equation621TargetRightParameter i z) hzRight
  have hcontract :
      ‖rootedReflectedGlobalLeftEndpointRootSmearedRightArbitraryField
          P A R H lgc qRight hindex scale rightTest
          (equation621TargetRightParameter i z)‖ <=
        ‖rootedReflectedGlobalLeftEndpointRightArbitraryField
          P A R H qRight hindex scale rightTest
          (equation621TargetRightParameter i z)‖ := by
    calc
      _ <= ‖H.semigroupBridgeRootOperator lgc i scale‖ *
          ‖rootedReflectedGlobalLeftEndpointRightArbitraryField
            P A R H qRight hindex scale rightTest
            (equation621TargetRightParameter i z)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ <= 1 * ‖rootedReflectedGlobalLeftEndpointRightArbitraryField
            P A R H qRight hindex scale rightTest
            (equation621TargetRightParameter i z)‖ := by
        gcongr
        exact H.semigroupBridgeRootOperator_norm_le_one lgc i scale
      _ = _ := one_mul _
  have hright :
      ‖rootedReflectedGlobalLeftEndpointRootSmearedRightArbitraryField
          P A R H lgc qRight hindex scale rightTest
          (equation621TargetRightParameter i z)‖ ^ 2 <=
        ‖rootedReflectedGlobalLeftEndpointRightDiagonal
          P A R H qRight hindex scale rightTest
          (equation621TargetRightParameter i z)‖ :=
    (pow_le_pow_left₀ (norm_nonneg _) hcontract 2).trans hrightRaw
  apply norm_generatorSemigroupCandidate_le_sqrt_mul_of_norm_sq_le
    OS lgc i
    (H.leftArbitrarySpatialGeneratorField i scale leftTest)
    (rootedReflectedGlobalLeftEndpointRootSmearedRightArbitraryField
      P A R H lgc qRight hindex scale rightTest)
    (generatorChronologicalParameterComplexCLE i z) hznative.1
    ‖leftDiagonal‖
    ‖rootedReflectedGlobalLeftEndpointRightDiagonal
      P A R H qRight hindex scale rightTest
      (equation621TargetRightParameter i z)‖
    (norm_nonneg _) (norm_nonneg _)
  · simpa [i, equation621TargetLeftParameter] using hleft
  · simpa [i, equation621TargetRightParameter] using hright

noncomputable def current_reflectedLeftEndpointApproximationRows
    {P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {qRight : Nat}
    {hindex : k = 1 + (qRight + 2) - 1}
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
        (equation621LeftEndpointGeneratorIndex qRight hindex) hub z}
    (E : RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank P lgc
        (equation621LeftEndpointGeneratorIndex qRight hindex)
        hub atlas z C0 Q D)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (w : OSIITimeGapSpace k) (hw : w ∈ E.current.carrier)
    (left_row_tendsto :
      let i := equation621LeftEndpointGeneratorIndex qRight hindex
      let v := w - osiiPositiveRealTimeEmbed C0.anchor
      let leftBlock := spatialApprox.generatorLeftBlockProductApproxIdentity i
      let leftProbe := leftBlock.reflectedSelfPairMarginalSpatialApproxIdentity
      let leftTest : (Fin (k * d) -> Real) -> Nat ->
          SchwartzMap (Section43SpatialSpace d 1) Complex := fun x N =>
        RootedA0BlockContinuousTranslationData.targetAdaptedLeftBlockSpatialTest
          spatialApprox i x N
      forall x N, Tendsto
        (fun scale => @inner Complex (OSHilbertSpace OS) _
          (Q.holomorphic.toContinuousTranslationData.leftArbitrarySpatialGeneratorField
            i scale (leftTest x N) 0)
          (Q.holomorphic.toContinuousTranslationData.leftArbitrarySpatialGeneratorField
            i scale (leftTest x N) 0))
        atTop
        (nhds ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) S 1).distribution
          (equation621TargetLeftTimePoint Q.packet i v)
          (leftProbe.section43Probe
            ((i.equation621TargetAdaptedSpatialSplitData d).leftPoint x) N)))) :
    let i := equation621LeftEndpointGeneratorIndex qRight hindex
    let v := w - osiiPositiveRealTimeEmbed C0.anchor
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
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) S 1).distribution
        (equation621TargetLeftTimePoint Q.packet i v))
      (DRight.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621TargetRightTimePoint Q.packet i v))
      leftProbe rightProbe (i.equation621TargetAdaptedSpatialSplitData d) := by
  dsimp only
  let i := equation621LeftEndpointGeneratorIndex qRight hindex
  let v := w - osiiPositiveRealTimeEmbed C0.anchor
  let T := Q.holomorphic.toContinuousTranslationData
  let DRight := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth D.adapted Q.packet Q.roots i (q := qRight) rfl
  let targetProbe := spatialApprox.equation621SplitTargetSpatialApproxIdentity i
  let leftProbe :=
    (spatialApprox.generatorLeftBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity
  let rightProbe :=
    (spatialApprox.generatorRightBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity
  let leftTest : (Fin (k * d) -> Real) -> Nat ->
      SchwartzMap (Section43SpatialSpace d 1) Complex := fun x N =>
    RootedA0BlockContinuousTranslationData.targetAdaptedLeftBlockSpatialTest
      spatialApprox i x N
  let rightTest : (Fin (k * d) -> Real) -> Nat ->
      SchwartzMap (Section43SpatialSpace d (qRight + 2)) Complex := fun x N =>
    RootedA0BlockContinuousTranslationData.targetAdaptedRightBlockSpatialTest
      spatialApprox i x N
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
    fun x N scale => @inner Complex (OSHilbertSpace OS) _
      (T.leftArbitrarySpatialGeneratorField i scale (leftTest x N) 0)
      (T.leftArbitrarySpatialGeneratorField i scale (leftTest x N) 0)
  let rightApprox : (Fin (k * d) -> Real) -> Nat -> Nat -> Complex :=
    fun x N scale =>
      rootedReflectedGlobalLeftEndpointRightDiagonal
        D.adapted Q.packet Q.roots T qRight hindex scale (rightTest x N)
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
      current_reflectedAbsoluteProductTarget_row_tendsto_any
        E spatialApprox w hw x N
  · intro x N
    simpa [leftApprox, leftProbe, leftTest, i, v] using
      left_row_tendsto x N
  · intro x N
    have hradial :=
      RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain_any
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
      simpa [i, DRight, equation621LeftEndpointGeneratorIndex] using
        rootedRightNontrivialReflectedGram_cutoff_eq_one
          D.adapted Q.packet Q.roots 1 qRight
            (by omega) (by omega) hindex
    have hrow :=
      tendsto_rootedRightNontrivialDiagonalScalar_to_distribution_generatorProbe_adapted
        D.adapted Q.packet Q.roots 1 qRight
          (by omega) (by omega) hindex spatialApprox x N
          (equation621TargetRightParameter i v)
          (by simpa [i, equation621LeftEndpointGeneratorIndex] using hzRight)
          (osiiMixedBlockGlobalReducedTime (qRight + 1)
            (Fin.append (Q.packet.rootedRightBlockAnchor i)
              (Q.packet.rootedRightBlockAnchor i))) rfl hcutoff
          (T.commonTailStart i) (T.commonTailStart i)
    dsimp only at hrow
    rw [RootedA0BlockContinuousTranslationData.generatorRightBlockProbe_eq_positiveTargetTest]
      at hrow
    simpa [rightApprox, rightProbe, rightTest, i, v, DRight,
      rootedReflectedGlobalLeftEndpointRightDiagonal,
      equation621LeftEndpointGeneratorIndex,
      equation621TargetRightTimePoint,
      RootedA0BlockContinuousTranslationData.generatorRightBlockProbe_eq_positiveTargetTest]
      using hrow
  · intro x N
    filter_upwards [] with scale
    let y := equation621SplitTargetSpatialPoint i x
    have hradial : v ∈
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth D.adapted Q.packet Q.roots T).radialChronologicalDomain i := by
      exact
        RootedTargetHubPointedDirectExtensionConstructionDataAtRank.current_parameter_mem_exact_radialNativeDomain_any
          E w hw
    have heq :=
      rootedAbsoluteProductReflectedScalarSum_eq_leftEndpointCandidate_on_radial
        D.adapted Q.packet Q.roots Q.holomorphic lgc qRight hindex
          spatialApprox y N scale v hradial
    have hbound :=
      norm_rootedReflectedGlobalLeftEndpointCandidate_le_sqrt_diagonals
        D.adapted Q.packet Q.roots T lgc qRight hindex scale
          (leftTest x N) (rightTest x N) v hradial
    rw [show targetApprox x N scale =
        rootedReflectedGlobalLeftEndpointArbitraryCandidate
          D.adapted Q.packet Q.roots T lgc qRight hindex scale
            (leftTest x N) (rightTest x N)
            (generatorChronologicalParameterComplexCLE i v) by
      simpa [targetApprox, leftTest, rightTest, i, v, y,
        RootedA0BlockContinuousTranslationData.targetAdaptedLeftBlockSpatialTest,
        RootedA0BlockContinuousTranslationData.targetAdaptedRightBlockSpatialTest]
        using heq]
    simpa [leftApprox, rightApprox, leftTest, rightTest, i, v, y]
      using hbound

noncomputable def rootedReflectedGlobalRightEndpointLeftArbitraryField
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (qLeft : Nat)
    (hindex : k = (qLeft + 2) + 1 - 1)
    (scale : Nat)
    (test : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex) :
    (Fin (qLeft + 1) -> Complex) -> OSHilbertSpace OS :=
  let i := equation621RightEndpointGeneratorIndex qLeft hindex
  let D := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qLeft) rfl
  fun z => D.reflectedGram.atlas.gram.anchoredAtlasField
    D.reflectedGram.atlas.sourceStage.stage
    D.reflectedGram.atlas.sourceStage.germ
    (D.sourceCLM (scale + H.commonTailStart i) test) z

noncomputable def rootedReflectedGlobalRightEndpointArbitraryCandidate
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft : Nat)
    (hindex : k = (qLeft + 2) + 1 - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d 1) Complex) :
    OSIITimeGapSpace k -> Complex :=
  let i := equation621RightEndpointGeneratorIndex qLeft hindex
  generatorSemigroupCandidate OS lgc i
    (rootedReflectedGlobalRightEndpointLeftArbitraryField
      P A R H qLeft hindex scale leftTest)
    (H.rootSmearedRightArbitrarySpatialGeneratorField
      lgc i scale rightTest)

theorem rootedReflectedGlobalRightEndpointArbitraryCandidate_holomorphic
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft : Nat)
    (hindex : k = (qLeft + 2) + 1 - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d 1) Complex) :
    let i := equation621RightEndpointGeneratorIndex qLeft hindex
    let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
    DifferentiableOn Complex
      (rootedReflectedGlobalRightEndpointArbitraryCandidate
        P A R H.toContinuousTranslationData lgc qLeft hindex scale
          leftTest rightTest)
      (E.radialNativeDomain i) := by
  dsimp only
  let i := equation621RightEndpointGeneratorIndex qLeft hindex
  let T := H.toContinuousTranslationData
  let DLeft := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := qLeft) rfl
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R T
  have hleft : DifferentiableOn Complex
      (rootedReflectedGlobalRightEndpointLeftArbitraryField
        P A R T qLeft hindex scale leftTest)
      (E.radialLeftDomain i) := by
    apply (DLeft.reflectedGram.atlas.generatedSpatialField_holomorphic
      DLeft.sourceCLM (scale + T.commonTailStart i) leftTest).mono
    intro z hz
    have hz' := E.radialLeftDomain_subset i hz
    simpa [E, DLeft, i,
      rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData,
      rootedReflectedGramLeftGeneratorOpenFieldScaleBlockRealEdgeData,
      rootedLeftNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData,
      ReflectedGramSpatialSourceData.toOpenFieldScaleBlockRealEdgeData,
      rootedScaleShiftOpenFieldBlock,
      rootedReflectedGlobalRightEndpointLeftArbitraryField] using hz'.1
  have hright : DifferentiableOn Complex
      (T.rootSmearedRightArbitrarySpatialGeneratorField lgc i scale rightTest)
      (E.radialRightDomain i) := by
    have hparam : ∀ z : Fin (i.m - 1) -> Complex, z = 0 := by
      intro z
      funext a
      exfalso
      have ha := a.isLt
      have hm : i.m = 1 := by
        rfl
      omega
    have hconst : T.rootSmearedRightArbitrarySpatialGeneratorField
        lgc i scale rightTest =
          fun _ => T.rootSmearedRightArbitrarySpatialGeneratorField
            lgc i scale rightTest 0 := by
      funext z
      congr 1
      exact hparam z
    rw [hconst]
    exact differentiableOn_const
      (c := T.rootSmearedRightArbitrarySpatialGeneratorField
        lgc i scale rightTest 0)
  simpa [rootedReflectedGlobalRightEndpointArbitraryCandidate, i, E] using
    differentiableOn_generatorSemigroupCandidate OS lgc i
      (E.radialLeftDomain_open i) (E.radialRightDomain_open i)
      hleft hright

theorem rootedReflectedGlobalRightEndpointArbitraryCandidate_eq_local_on_commonRadial
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft : Nat)
    (hindex : k = (qLeft + 2) + 1 - 1)
    (scale : Nat)
    (leftTest : SchwartzMap (Section43SpatialSpace d (qLeft + 2)) Complex)
    (rightTest : SchwartzMap (Section43SpatialSpace d 1) Complex)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ equation621CommonRadialCarrier P A R H
      (equation621RightEndpointGeneratorIndex qLeft hindex)) :
    rootedReflectedGlobalRightEndpointArbitraryCandidate
        P A R H.toContinuousTranslationData lgc qLeft hindex scale
          leftTest rightTest
        (generatorChronologicalParameterComplexCLE
          (equation621RightEndpointGeneratorIndex qLeft hindex) z) =
      H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc (equation621RightEndpointGeneratorIndex qLeft hindex)
        scale leftTest rightTest
        (generatorChronologicalParameterComplexCLE
          (equation621RightEndpointGeneratorIndex qLeft hindex) z) := by
  let i := equation621RightEndpointGeneratorIndex qLeft hindex
  have hkernels :=
    equation621CommonRadialCarrier_targetParameters_mem_commonKernels
      P A R H i z hz
  have hleft := rootedLeftArbitrarySpatialField_eq_reflectedGram
    P A R H qLeft 1 (by omega) (by omega) hindex
    scale leftTest (equation621TargetLeftParameter i z) (by
      simpa [i, equation621RightEndpointGeneratorIndex] using hkernels.1)
  rw [rootedReflectedGlobalRightEndpointArbitraryCandidate,
    RootedA0BlockContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate,
    generatorSemigroupCandidate_apply, generatorSemigroupCandidate_apply]
  change @inner Complex (OSHilbertSpace OS) _
      (rootedReflectedGlobalRightEndpointLeftArbitraryField
        P A R H.toContinuousTranslationData qLeft hindex scale leftTest
          (equation621TargetLeftParameter i z))
      (osTimeShiftHilbertComplex OS lgc
        ((generatorChronologicalParameterComplexCLE i z) i.bridgeGlobalIndex)
        (H.toContinuousTranslationData.rootSmearedRightArbitrarySpatialGeneratorField
          lgc i scale rightTest (equation621TargetRightParameter i z))) = _
  rw [show rootedReflectedGlobalRightEndpointLeftArbitraryField
        P A R H.toContinuousTranslationData qLeft hindex scale leftTest
          (equation621TargetLeftParameter i z) =
      H.toContinuousTranslationData.leftArbitrarySpatialGeneratorField
        i scale leftTest (equation621TargetLeftParameter i z) by
    simpa [i, rootedReflectedGlobalRightEndpointLeftArbitraryField,
      equation621RightEndpointGeneratorIndex] using hleft]
  rfl

theorem rootedAbsoluteProductReflectedScalarSum_eq_rightEndpointCandidate_on_radial
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (qLeft : Nat)
    (hindex : k = (qLeft + 2) + 1 - 1)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (N scale : Nat)
    (z : OSIITimeGapSpace k)
    (hz : z ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData).radialChronologicalDomain
          (equation621RightEndpointGeneratorIndex qLeft hindex)) :
    let i := equation621RightEndpointGeneratorIndex qLeft hindex
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
    (rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H).spatialHermiteScalarSum
        lgc
        ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i).comp lift)
        i scale (generatorChronologicalParameterComplexCLE i z) chi =
      rootedReflectedGlobalRightEndpointArbitraryCandidate
        P A R H.toContinuousTranslationData lgc qLeft hindex scale
        (RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
          (d := d) i.hn
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
            spatialApprox i x N))
        (RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
          (d := d) i.hm
          (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
            spatialApprox i x N))
        (generatorChronologicalParameterComplexCLE i z) := by
  dsimp only
  let i := equation621RightEndpointGeneratorIndex qLeft hindex
  let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
  let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
  let E := rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P A R H.toContinuousTranslationData
  let B := rootedReflectedGramRootSmearedGlobalFamily S depth P lgc A R H
  let U := E.radialChronologicalDomain i
  let seed := selectedEquation621CommonRadialRealSeedData P A R H
  let leftTest := RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
    (d := d) i.hn
    (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
      spatialApprox i x N)
  let rightTest := RootedA0BlockContinuousTranslationData.positiveBlockSpatialTest
    (d := d) i.hm
    (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
      spatialApprox i x N)
  let f : OSIITimeGapSpace k -> Complex := fun w =>
    B.spatialHermiteScalarSum lgc
      ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
        (d := d) i).comp lift)
      i scale (generatorChronologicalParameterComplexCLE i w) chi
  let g : OSIITimeGapSpace k -> Complex := fun w =>
    rootedReflectedGlobalRightEndpointArbitraryCandidate
      P A R H.toContinuousTranslationData lgc qLeft hindex scale
        leftTest rightTest (generatorChronologicalParameterComplexCLE i w)
  have hU_open : IsOpen U := E.radialChronologicalDomain_open i
  have hU_connected : IsConnected U := by
    obtain ⟨tau, htau⟩ := seed.realRegion_nonempty
    have hc : osiiPositiveRealTimeEmbed tau ∈ U :=
      (equation621CommonRadialRealSeed_mem_carrier P A R H i tau htau).1
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
      simpa [B, E, rootedReflectedGramRootSmearedGlobalFamily,
        rootSmearedGeneratorOpenHilbertFieldScaleFamilyData] using hdomain
  have hg : DifferentiableOn Complex g U := by
    apply DifferentiableOn.comp
      (rootedReflectedGlobalRightEndpointArbitraryCandidate_holomorphic
        P A R H lgc qLeft hindex scale leftTest rightTest)
    · exact (generatorChronologicalParameterComplexCLE i).differentiable.differentiableOn
    · intro w hw
      exact hw
  have hreal : forall tau, tau ∈ seed.realRegion ->
      f (SCV.realToComplex tau) = g (SCV.realToComplex tau) := by
    intro tau htau
    rw [show SCV.realToComplex tau = osiiPositiveRealTimeEmbed tau by rfl]
    have hcommon :=
      equation621CommonRadialRealSeed_mem_carrier P A R H i tau htau
    have hlocal :=
      rootedAbsoluteProductReflectedScalarSum_eq_localCandidate_on_realSeed
        P A R H lgc i spatialApprox x N scale tau htau
    have hcandidate :=
      rootedReflectedGlobalRightEndpointArbitraryCandidate_eq_local_on_commonRadial
        P A R H lgc qLeft hindex scale leftTest rightTest
          (osiiPositiveRealTimeEmbed tau) hcommon
    exact hlocal.trans hcandidate.symm
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

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
