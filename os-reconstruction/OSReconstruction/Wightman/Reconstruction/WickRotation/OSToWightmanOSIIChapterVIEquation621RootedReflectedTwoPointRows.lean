/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedEndpointRows

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedA0BlockContinuousTranslationData

open RootedTargetHubPointedDirectExtensionData

variable {d k : Nat} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}

theorem rootedAbsoluteProductReflectedScalarSum_eq_twoPointCandidate_on_radial
    {depth : Nat}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (hindex : k = 1 + 1 - 1)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (N scale : Nat)
    (z : OSIITimeGapSpace k)
    (hz : z ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData).radialChronologicalDomain
          (⟨1, 1, by omega, by omega, hindex⟩ : GeneratorIndex k)) :
    let i : GeneratorIndex k := ⟨1, 1, by omega, by omega, hindex⟩
    let lift := rootedAbsoluteProductReflectedLift spatialApprox i N
    let chi := spatialApprox.absoluteProductTargetSpatialApproxIdentity.section43Probe x N
    (rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H).spatialHermiteScalarSum
        lgc
        ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i).comp lift)
        i scale (generatorChronologicalParameterComplexCLE i z) chi =
      H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc i scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i x N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i x N)
        (generatorChronologicalParameterComplexCLE i z) := by
  dsimp only
  let i : GeneratorIndex k := ⟨1, 1, by omega, by omega, hindex⟩
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
    H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
      lgc i scale
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
  have hlocal : forall w, w ∈ U ->
      generatorChronologicalParameterComplexCLE i w ∈
        generatorSemigroupDomain i (H.left i).domain (H.right i).domain := by
    intro w hw
    have hdomain := E.radialChronologicalDomain_subset i hw
    change generatorChronologicalParameterComplexCLE i w ∈
      generatorSemigroupDomain i (E.leftDomain i) (E.rightDomain i)
      at hdomain
    rw [generatorSemigroupDomain, bridgedMixedHilbertPairingDomain,
      mixedHilbertPairingDomain] at hdomain ⊢
    rcases hdomain with ⟨hbridge, _hleft, _hright⟩
    refine ⟨hbridge, ?_, ?_⟩
    · have hleftEq :
          (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i w)).2.1 =
            (0 : Fin (i.n - 1) -> Complex) := by
        dsimp [i]
        funext a
        exact Fin.elim0 a
      rw [hleftEq]
      have hzero : (0 : Fin (i.n - 1) -> Complex) ∈
          (H.left i).domain :=
        (H.toContinuousTranslationData.left i).zero_mem_domain
      simpa [conjugateFieldDomain] using hzero
    · have hrightEq :
          (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i w)).2.2 =
            (0 : Fin (i.m - 1) -> Complex) := by
        dsimp [i]
        funext a
        exact Fin.elim0 a
      rw [hrightEq]
      have hzero : (0 : Fin (i.m - 1) -> Complex) ∈
          (H.right i).domain :=
        (H.toContinuousTranslationData.right i).zero_mem_domain
      exact hzero
  have hg : DifferentiableOn Complex g U := by
    apply DifferentiableOn.comp
      (differentiableOn_rootSmearedArbitrarySpatialGeneratorCandidate H
        lgc i scale
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetLeftSpatialTest
          spatialApprox i x N)
        (RootedA0BlockContinuousTranslationData.absoluteProductTargetRightSpatialTest
          spatialApprox i x N))
    · exact (generatorChronologicalParameterComplexCLE i).differentiable.differentiableOn
    · exact hlocal
  have hreal : forall tau, tau ∈ seed.realRegion ->
      f (SCV.realToComplex tau) = g (SCV.realToComplex tau) := by
    intro tau htau
    rw [show SCV.realToComplex tau = osiiPositiveRealTimeEmbed tau by rfl]
    exact rootedAbsoluteProductReflectedScalarSum_eq_localCandidate_on_realSeed
      P A R H lgc i spatialApprox x N scale tau htau
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

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
