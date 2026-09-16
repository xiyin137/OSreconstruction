/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRadialFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredOrderedTransport













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

/-- Chronological real parameters whose split reflections lie in the common
reflected-Gram/local source-agreement neighborhood for every split. -/
def rootedReflectedGramChronologicalCommonRealAutomaticSet
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    Set (Fin k → ℝ) :=
  {τ | ∀ i : GeneratorIndex k,
    generatorChronologicalParameter i τ ∈
      (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
        S depth P A R H).commonRealAutomaticSet}

/-- Finiteness of the generator splits gives one common chronological
neighborhood of the origin. -/
theorem rootedReflectedGramChronologicalCommonRealAutomaticSet_mem_nhds
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    rootedReflectedGramChronologicalCommonRealAutomaticSet
      S depth P A R H ∈ 𝓝 0 := by
  classical
  letI : Fintype (GeneratorIndex k) :=
    Fintype.ofEquiv (Fin k) (GeneratorIndex.equivGap k).symm
  let Q :=
    rootedReflectedGramGeneratorOpenFieldSourceAgreementData
      S depth P A R H
  change
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0,
      ∀ i : GeneratorIndex k,
        generatorChronologicalParameter i τ ∈
          Q.commonRealAutomaticSet
  rw [Filter.eventually_all]
  intro i
  have hreflection :
      Tendsto (generatorChronologicalParameter i)
        (𝓝 (0 : Fin k → ℝ)) (𝓝 0) := by
    have hfun :
        generatorChronologicalParameter i =
          (generatorChronologicalParameterCLE i :
            (Fin k → ℝ) → (Fin k → ℝ)) := by
      funext τ
      exact (generatorChronologicalParameterCLE_apply i τ).symm
    rw [hfun]
    exact
      (generatorChronologicalParameterCLE i).continuous.tendsto'
        0 0 (map_zero (generatorChronologicalParameterCLE i))
  exact hreflection.eventually Q.commonRealAutomaticSet_mem_nhds

/-- A chronological positive-real point in the common source-agreement
neighborhood belongs to the reflected-Gram radial restriction. -/
theorem
    positiveReal_mem_rootedReflectedGramRadialChronologicalDomain_of_commonRealAutomatic
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (hτ :
      generatorChronologicalParameter i τ ∈
        (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
          S depth P A R H).commonRealAutomaticSet) :
    osiiPositiveRealTimeEmbed τ ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData
      ).radialChronologicalDomain i := by
  let E :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let ξ :=
    generatorChronologicalParameter i τ
  change
    generatorChronologicalParameterComplexCLE i
        (osiiPositiveRealTimeEmbed τ) ∈
      E.radialNativeDomain i
  rw [generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed]
  refine ⟨?_, ?_, ?_⟩
  · change 0 < ξ i.bridgeGlobalIndex
    dsimp [ξ]
    rw [generatorChronologicalParameter_bridge]
    exact hbridge
  · change
      star
          (i.splitCoordinatesCLM
            (osiiPositiveRealTimeEmbed
              (generatorChronologicalParameter i τ))).2.1 ∈
        E.radialLeftDomain i
    have hleft_eq :
        star
            (i.splitCoordinatesCLM
              (osiiPositiveRealTimeEmbed
                (generatorChronologicalParameter i τ))).2.1 =
          SCV.realToComplex (i.leftRealCoordinates ξ) := by
      ext q
      change
        star
            ((i.splitCoordinatesCLM
              (osiiPositiveRealTimeEmbed
                (generatorChronologicalParameter i τ))).2.1 q) =
          (i.leftRealCoordinates ξ q : ℂ)
      dsimp [ξ]
      exact
        i.splitCoordinatesCLM_positiveReal_left
          (generatorChronologicalParameter i τ) q
    rw [hleft_eq]
    apply mem_openZeroConvexKernel_of_segment_subset
      (E.leftDomain_open i)
    rw [segment_subset_iff]
    intro a b ha hb hab
    have hb1 : b ≤ 1 := by
      linarith
    have hzero :
        a • (0 : Fin (i.n - 1) → ℂ) +
            b • SCV.realToComplex (i.leftRealCoordinates ξ) =
          b • SCV.realToComplex (i.leftRealCoordinates ξ) := by
      ext q
      simp
    have hmem :=
      rootedReflectedGramLeft_real_smul_mem
        S depth P A R H.toContinuousTranslationData
        i (i.leftRealCoordinates ξ) (hτ.1 i).1 b hb hb1
    exact hzero.symm ▸ hmem
  · have hright_eq :
        (i.splitCoordinatesCLM
            (osiiPositiveRealTimeEmbed
              (generatorChronologicalParameter i τ))).2.2 =
          SCV.realToComplex (i.rightRealCoordinates ξ) := by
      ext q
      change
        (i.splitCoordinatesCLM
            (osiiPositiveRealTimeEmbed
              (generatorChronologicalParameter i τ))).2.2 q =
          (i.rightRealCoordinates ξ q : ℂ)
      dsimp [ξ]
      exact
        i.splitCoordinatesCLM_positiveReal_right
          (generatorChronologicalParameter i τ) q
    rw [hright_eq]
    apply mem_openZeroConvexKernel_of_segment_subset
      (E.rightDomain_open i)
    rw [segment_subset_iff]
    intro a b ha hb hab
    have hb1 : b ≤ 1 := by
      linarith
    have hzero :
        a • (0 : Fin (i.m - 1) → ℂ) +
            b • SCV.realToComplex (i.rightRealCoordinates ξ) =
          b • SCV.realToComplex (i.rightRealCoordinates ξ) := by
      ext q
      simp
    have hmem :=
      rootedReflectedGramRight_real_smul_mem
        S depth P A R H.toContinuousTranslationData
        i (i.rightRealCoordinates ξ) (hτ.1 i).2 b hb hb1
    exact hzero.symm ▸ hmem

/-- On the actual common real source neighborhood, each original-OS global
reflected-Gram spatial sum equals the genuine local rooted sum. -/
theorem
    rootedReflectedGramSpatialHermiteScalarSumOfOS_eq_local_of_commonRealAutomatic
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hbridge : 0 < ξ i.bridgeGlobalIndex)
    (hξ :
      ξ ∈
        (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
          S depth P A R H).commonRealAutomaticSet)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (rootedReflectedGramRootSmearedGlobalFamilyOfOS
        S depth P A R H).spatialHermiteScalarSumOfOS
        (rootedGeneratorSplitSpatialLiftCLM i)
        i timeScale (osiiPositiveRealTimeEmbed ξ) χ =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSumOfOS
        i timeScale (osiiPositiveRealTimeEmbed ξ)
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ) := by
  let Q :=
    rootedReflectedGramGeneratorOpenFieldSourceAgreementData
      S depth P A R H
  let E :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let F :=
    rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      A R H
  change
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS
        H.toContinuousTranslationData
        E.toGeneratorOpenHilbertFieldScaleFamilyData
      ).spatialHermiteScalarSumOfOS
        (rootedGeneratorSplitSpatialLiftCLM i)
        i timeScale (osiiPositiveRealTimeEmbed ξ) χ =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSumOfOS
        i timeScale (osiiPositiveRealTimeEmbed ξ)
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ)
  rw [←
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS_eq_spatialHermiteScalarSumOfOS
      H.toContinuousTranslationData
      E.toGeneratorOpenHilbertFieldScaleFamilyData
      i timeScale (osiiPositiveRealTimeEmbed ξ) χ]
  calc
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        H.toContinuousTranslationData
        E.toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale (osiiPositiveRealTimeEmbed ξ)
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ) =
      rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        H.toContinuousTranslationData
        F.toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale (osiiPositiveRealTimeEmbed ξ)
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ) := by
      apply tsum_congr
      intro mode
      rw [rootSmearedGeneratorModeOfOS_eq_of_commonRealAutomatic
        Q H.toContinuousTranslationData
        i timeScale mode ξ hbridge hξ]
    _ =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSumOfOS
        i timeScale (osiiPositiveRealTimeEmbed ξ)
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ) :=
      rootSmearedLocalGeneratorOpenFieldSpatialHermiteSumOfOS_eq
        H i timeScale (osiiPositiveRealTimeEmbed ξ)
          (section43SpatialBasepointLiftCLM d k
            (normalizedSpatialBasepointCutoff d).toSchwartz χ)

/-- On the common chronological real neighborhood, every reflected-Gram
finite-scale spatial sum is the original local rooted sum. -/
theorem
    rootedReflectedGramSpatialHermiteScalarSum_eq_local_of_commonRealAutomatic
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hbridge : 0 < ξ i.bridgeGlobalIndex)
    (hξ :
      ξ ∈
        (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
          S depth P A R H).commonRealAutomaticSet)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H).spatialHermiteScalarSum
        lgc (rootedGeneratorSplitSpatialLiftCLM i)
        i timeScale (osiiPositiveRealTimeEmbed ξ) χ =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
        lgc i timeScale (osiiPositiveRealTimeEmbed ξ)
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ) :=
  rootedReflectedGramSpatialHermiteScalarSumOfOS_eq_local_of_commonRealAutomatic
    S depth P A R H i timeScale ξ hbridge hξ χ

/-- A genuine original-OS rooted source current gives the entire radial
reflected-Gram family one split-independent represented positive-real edge
on any prescribed neighborhood of the chronological origin. -/
theorem
    exists_rootedReflectedGramRadialCommonPositiveRealEdgeDataOfOS_of_currentData_on
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0) :
    ∃ E :
        (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS
          S depth P A R H).CommonPositiveRealEdgeData,
      E.realRegion ⊆ Q ∧
        IsPositiveRadial E.realRegion ∧
        E.realRegion ⊆ section43TimeStrictPositiveRegion k ∧
        OSIITimeSpatialRepresentsDistributionOn
          (anchoredOrderedTransportDistribution C.current anchor)
          E.orbit E.realRegion := by
  classical
  let D := H.toContinuousTranslationData
  let B :=
    rootedReflectedGramRootSmearedGlobalFamilyOfOS
      S depth P A R H
  let T :=
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS
      S depth P A R H
  let lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ :=
    section43SpatialBasepointLiftCLM d k
      (normalizedSpatialBasepointCutoff d).toSchwartz
  let Q' : Set (Fin k → ℝ) :=
    Q ∩ rootedReflectedGramChronologicalCommonRealAutomaticSet
      S depth P A R H
  have hQ' : Q' ∈ 𝓝 0 :=
    Filter.inter_mem hQ
      (rootedReflectedGramChronologicalCommonRealAutomaticSet_mem_nhds
        S depth P A R H)
  obtain
    ⟨V, hV_open, hV_ne, hVQ, hV_radial, hV_domain, hpacket⟩ :=
      D.exists_radial_tendsto_integral_rootSmearedSpatialHermiteGeneratorSumOfOS_commonChronological_mul_all_splits_of_currentData_on
        C Q' hQ'
  have hbridge :
      ∀ (i : GeneratorIndex k) τ, τ ∈ V →
        0 < τ i.bridgeGlobalIndex := by
    intro i τ hτ
    have hdomain := hV_domain i τ hτ
    have hpositive := hdomain.1
    rw [generatorChronological_split_fst] at hpositive
    simpa [osiiPositiveRealTimeEmbed] using hpositive
  have hmem :
      ∀ (i : GeneratorIndex k) τ, τ ∈ V →
        osiiPositiveRealTimeEmbed τ ∈ T.domain i := by
    intro i τ hτ
    exact
      positiveReal_mem_rootedReflectedGramRadialChronologicalDomain_of_commonRealAutomatic
        S depth P A R H i τ
        (hbridge i τ hτ) ((hVQ hτ).2 i)
  have hnative :
      ∀ (i : GeneratorIndex k) τ, τ ∈ V →
        osiiPositiveRealTimeEmbed
            (generatorChronologicalParameter i τ) ∈
          rootedReflectedGramPacketScaleBranchOfOS
            S depth P A R H i := by
    intro i τ hτ
    have hradial :
        osiiPositiveRealTimeEmbed τ ∈
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth P A R H.toContinuousTranslationData
          ).radialChronologicalDomain i :=
      hmem i τ hτ
    have hfull :=
      radialChronologicalDomain_subset_rootedReflectedGramTwoScaleDomainOfOS
        S depth P A R H i hradial
    change
      generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed τ) ∈
        rootedReflectedGramPacketScaleBranchOfOS
          S depth P A R H i at hfull
    rw [generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed]
      at hfull
    exact hfull
  have hV_positive :
      V ⊆ section43TimeStrictPositiveRegion k := by
    intro τ hτ q
    have hq :=
      hbridge (GeneratorIndex.ofGap q) τ hτ
    simpa [GeneratorIndex.bridgeGlobalIndex_eq_toGap] using hq
  let trace :
      SchwartzMap (Section43SpatialSpace d k) ℂ →
        SchwartzMap (Fin k → ℝ) ℂ → ℂ :=
    fun χ φ =>
      C.current (section43NPointTimeSpatialTensor d k
        (SCV.translateSchwartz (-anchor) φ)
        (section43SpatialHeadMarginal (lift χ)))
  have htrace :
      ∀ (i : GeneratorIndex k)
        (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
        (φ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.SupportsInOpen (φ : (Fin k → ℝ) → ℂ) V →
          ∫ τ : Fin k → ℝ,
              T.scalarLimit i (osiiPositiveRealTimeEmbed τ) χ * φ τ =
            trace χ φ := by
    intro i χ φ hφ
    let F := lift χ
    let G :=
      rootedReflectedGramPacketScaleBranchLimitDataOfOS
        S depth P A R H i χ
    let e : (Fin k → ℝ) → OSIITimeGapSpace k :=
      fun τ =>
        generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed τ)
    have he_cont : Continuous e :=
      (generatorChronologicalParameterComplexCLE i).continuous.comp
        continuous_osiiPositiveRealTimeEmbed
    have hlocal :
        TendstoLocallyUniformlyOn
          (fun timeScale τ =>
            B.spatialHermiteScalarSumOfOS
              (rootedGeneratorSplitSpatialLiftCLM i)
              i timeScale (e τ) χ)
          (fun τ => G.limit (e τ))
          atTop V := by
      exact
        G.locallyUniform.comp e
          (fun τ hτ => by
            simpa [e, rootedReflectedGramPacketScaleBranchOfOS] using
              hnative i τ hτ)
          he_cont.continuousOn
    have hcontinuous :
        ∀ timeScale,
          ContinuousOn
            (fun τ =>
              B.spatialHermiteScalarSumOfOS
                (rootedGeneratorSplitSpatialLiftCLM i)
                i timeScale (e τ) χ) V := by
      intro timeScale
      exact
        (B.spatialHermiteScalarSumOfOS_differentiableOn
          (rootedGeneratorSplitSpatialLiftCLM i)
          i timeScale χ).continuousOn.comp
            he_cont.continuousOn
            (fun τ hτ =>
              rootedReflectedGramPacketScaleBranchOfOS_subset_domain
                S depth P A R H i (by
                  simpa [e] using hnative i τ hτ))
    have hlimit :=
      SCV.tendsto_integral_mul_schwartz_of_tendstoLocallyUniformlyOn
        hV_open hcontinuous hlocal φ hφ
    have hsequence :
        (fun timeScale =>
          ∫ τ : Fin k → ℝ,
            B.spatialHermiteScalarSumOfOS
                (rootedGeneratorSplitSpatialLiftCLM i)
                i timeScale (e τ) χ *
              φ τ) =
        fun timeScale =>
          ∫ τ : Fin k → ℝ,
            D.rootSmearedSpatialHermiteGeneratorSumOfOS
                i timeScale (e τ) F *
              φ τ := by
      funext timeScale
      apply MeasureTheory.integral_congr_ae
      filter_upwards with τ
      by_cases hτ : τ ∈ tsupport (φ : (Fin k → ℝ) → ℂ)
      · have hτV := hφ.2 hτ
        have hsum :=
          rootedReflectedGramSpatialHermiteScalarSumOfOS_eq_local_of_commonRealAutomatic
            S depth P A R H i timeScale
            (generatorChronologicalParameter i τ)
            (by
              rw [generatorChronologicalParameter_bridge]
              exact hbridge i τ hτV)
            ((hVQ hτV).2 i) χ
        simpa [e, F,
          generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed]
          using congrArg (fun z : ℂ => z * φ τ) hsum
      · have hφ_zero : φ τ = 0 :=
          image_eq_zero_of_notMem_tsupport hτ
        simp [hφ_zero]
    rw [hsequence] at hlimit
    have hcommon := hpacket i F φ hφ
    have heq := tendsto_nhds_unique hlimit hcommon
    simpa [T,
      rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS,
      rootedReflectedGramGeneratorTwoScaleApproximationFamilyOfOS,
      rootedReflectedGramGeneratorNativeTwoScaleApproximationFamilyOfOS,
      GeneratorSpatialTwoScaleApproximationFamily.precomp,
      B, D, lift, F, G, e, trace] using heq
  let E :
      T.CommonPositiveRealEdgeData :=
    GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.ofCommonDistributionalTrace
      T V hV_open hV_ne hmem trace htrace
  let W : SchwartzNPoint d k →L[ℂ] ℂ :=
    anchoredOrderedTransportDistribution C.current anchor
  have hW :
      ∀ (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
        (φ : SchwartzMap (Fin k → ℝ) ℂ),
        W (section43OrderedPullbackTimeSpatialTensorCLM d k χ φ) =
          trace χ φ := by
    intro χ φ
    calc
      W (section43OrderedPullbackTimeSpatialTensorCLM d k χ φ) =
          C.current (section43NPointTimeSpatialTensor d k
            (SCV.translateSchwartz (-anchor) φ) χ) := by
        exact
          anchoredOrderedTransportDistribution_orderedPullbackTimeSpatialTensor
            C.current anchor χ φ
      _ = trace χ φ := by
        simp [trace, lift, section43SpatialHeadMarginal_basepointLift_eq]
  have hrep :
      OSIITimeSpatialRepresentsDistributionOn W E.orbit V := by
    intro χ φ hφ
    let i₀ : GeneratorIndex k := GeneratorIndex.ofGap (0 : Fin k)
    calc
      (W.comp (section43OrderedPullbackTimeSpatialTensorCLM d k χ)) φ =
          trace χ φ := by
        simpa only [ContinuousLinearMap.comp_apply] using hW χ φ
      _ = ∫ τ : Fin k → ℝ,
          T.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ * φ τ :=
        (htrace i₀ χ φ hφ).symm
      _ = ∫ τ : Fin k → ℝ, E.orbit τ χ * φ τ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with τ
        by_cases hτ :
            τ ∈ tsupport (φ : (Fin k → ℝ) → ℂ)
        · have hτV : τ ∈ V := hφ.2 hτ
          have heq :
              T.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ =
                E.orbit τ χ := by
            change
              T.diagonal.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ =
                E.toDiagonal.orbit τ χ
            exact (E.toDiagonal.scalarLimit_realEdge i₀ τ hτV).2 χ
          rw [heq]
        · have hφ_zero : φ τ = 0 :=
            image_eq_zero_of_notMem_tsupport hτ
          simp [hφ_zero]
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact (hVQ hτ).1
  · exact hV_radial
  · exact hV_positive
  · simpa [E, W,
      GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.ofCommonDistributionalTrace]
      using hrep

/-- A rooted current gives the reflected-Gram radial family one
split-independent represented positive-real edge.  The edge can be confined
to any prescribed neighborhood of the chronological origin. -/
theorem
    exists_rootedReflectedGramRadialCommonPositiveRealEdgeData_of_currentData_on
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0) :
    ∃ E :
        (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily
          S depth P lgc A R H).CommonPositiveRealEdgeData,
      E.realRegion ⊆ Q ∧
        IsPositiveRadial E.realRegion ∧
        E.realRegion ⊆ section43TimeStrictPositiveRegion k ∧
        OSIITimeSpatialRepresentsDistributionOn
          (anchoredOrderedTransportDistribution C.current anchor)
          E.orbit E.realRegion := by
  classical
  let D := H.toContinuousTranslationData
  let B :=
    rootedReflectedGramRootSmearedGlobalFamily
      S depth P lgc A R H
  let T :=
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily
      S depth P lgc A R H
  let lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ :=
    section43SpatialBasepointLiftCLM d k
      (normalizedSpatialBasepointCutoff d).toSchwartz
  let Q' : Set (Fin k → ℝ) :=
    Q ∩ rootedReflectedGramChronologicalCommonRealAutomaticSet
      S depth P A R H
  have hQ' : Q' ∈ 𝓝 0 :=
    Filter.inter_mem hQ
      (rootedReflectedGramChronologicalCommonRealAutomaticSet_mem_nhds
        S depth P A R H)
  obtain
    ⟨V, hV_open, hV_ne, hVQ, hV_radial, hV_domain, hpacket⟩ :=
      D.exists_radial_tendsto_integral_rootSmearedSpatialHermiteGeneratorSum_commonChronological_mul_all_splits_of_currentData_on
        lgc C Q' hQ'
  have hbridge :
      ∀ (i : GeneratorIndex k) τ, τ ∈ V →
        0 < τ i.bridgeGlobalIndex := by
    intro i τ hτ
    have hdomain := hV_domain i τ hτ
    have hpositive := hdomain.1
    rw [generatorChronological_split_fst] at hpositive
    simpa [osiiPositiveRealTimeEmbed] using hpositive
  have hmem :
      ∀ (i : GeneratorIndex k) τ, τ ∈ V →
        osiiPositiveRealTimeEmbed τ ∈ T.domain i := by
    intro i τ hτ
    exact
      positiveReal_mem_rootedReflectedGramRadialChronologicalDomain_of_commonRealAutomatic
        S depth P A R H i τ
        (hbridge i τ hτ) ((hVQ hτ).2 i)
  have hnative :
      ∀ (i : GeneratorIndex k) τ, τ ∈ V →
        osiiPositiveRealTimeEmbed
            (generatorChronologicalParameter i τ) ∈
          rootedReflectedGramPacketScaleBranch
            S depth P lgc A R H i := by
    intro i τ hτ
    have hradial :
        osiiPositiveRealTimeEmbed τ ∈
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth P A R H.toContinuousTranslationData
          ).radialChronologicalDomain i :=
      hmem i τ hτ
    have hfull :=
      radialChronologicalDomain_subset_rootedReflectedGramTwoScaleDomain
        S depth P lgc A R H i hradial
    change
      generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed τ) ∈
        rootedReflectedGramPacketScaleBranch
          S depth P lgc A R H i at hfull
    rw [generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed]
      at hfull
    exact hfull
  have hV_positive :
      V ⊆ section43TimeStrictPositiveRegion k := by
    intro τ hτ q
    have hq :=
      hbridge (GeneratorIndex.ofGap q) τ hτ
    simpa [GeneratorIndex.bridgeGlobalIndex_eq_toGap] using hq
  let trace :
      SchwartzMap (Section43SpatialSpace d k) ℂ →
        SchwartzMap (Fin k → ℝ) ℂ → ℂ :=
    fun χ φ =>
      C.current (section43NPointTimeSpatialTensor d k
        (SCV.translateSchwartz (-anchor) φ)
        (section43SpatialHeadMarginal (lift χ)))
  have htrace :
      ∀ (i : GeneratorIndex k)
        (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
        (φ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.SupportsInOpen (φ : (Fin k → ℝ) → ℂ) V →
          ∫ τ : Fin k → ℝ,
              T.scalarLimit i (osiiPositiveRealTimeEmbed τ) χ * φ τ =
            trace χ φ := by
    intro i χ φ hφ
    let F := lift χ
    let G :=
      rootedReflectedGramPacketScaleBranchLimitData
        S depth P lgc A R H i χ
    let e : (Fin k → ℝ) → OSIITimeGapSpace k :=
      fun τ =>
        generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed τ)
    have he_cont : Continuous e :=
      (generatorChronologicalParameterComplexCLE i).continuous.comp
        continuous_osiiPositiveRealTimeEmbed
    have hlocal :
        TendstoLocallyUniformlyOn
          (fun timeScale τ =>
            B.spatialHermiteScalarSum
              lgc (rootedGeneratorSplitSpatialLiftCLM i)
              i timeScale (e τ) χ)
          (fun τ => G.limit (e τ))
          atTop V := by
      exact
        G.locallyUniform.comp e
          (fun τ hτ => by
            simpa [e, rootedReflectedGramPacketScaleBranch] using
              hnative i τ hτ)
          he_cont.continuousOn
    have hcontinuous :
        ∀ timeScale,
          ContinuousOn
            (fun τ =>
              B.spatialHermiteScalarSum
                lgc (rootedGeneratorSplitSpatialLiftCLM i)
                i timeScale (e τ) χ) V := by
      intro timeScale
      exact
        (B.spatialHermiteScalarSum_differentiableOn
          lgc (rootedGeneratorSplitSpatialLiftCLM i)
          i timeScale χ).continuousOn.comp
            he_cont.continuousOn
            (fun τ hτ =>
              rootedReflectedGramPacketScaleBranch_subset_domain
                S depth P lgc A R H i (by
                  simpa [e] using hnative i τ hτ))
    have hlimit :=
      SCV.tendsto_integral_mul_schwartz_of_tendstoLocallyUniformlyOn
        hV_open hcontinuous hlocal φ hφ
    have hsequence :
        (fun timeScale =>
          ∫ τ : Fin k → ℝ,
            B.spatialHermiteScalarSum
                lgc (rootedGeneratorSplitSpatialLiftCLM i)
                i timeScale (e τ) χ *
              φ τ) =
        fun timeScale =>
          ∫ τ : Fin k → ℝ,
            D.rootSmearedSpatialHermiteGeneratorSum
                lgc i timeScale (e τ) F *
              φ τ := by
      funext timeScale
      apply MeasureTheory.integral_congr_ae
      filter_upwards with τ
      by_cases hτ : τ ∈ tsupport (φ : (Fin k → ℝ) → ℂ)
      · have hτV := hφ.2 hτ
        have hsum :=
          rootedReflectedGramSpatialHermiteScalarSum_eq_local_of_commonRealAutomatic
            S depth P lgc A R H i timeScale
            (generatorChronologicalParameter i τ)
            (by
              rw [generatorChronologicalParameter_bridge]
              exact hbridge i τ hτV)
            ((hVQ hτV).2 i) χ
        simpa [e, F,
          generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed]
          using congrArg (fun z : ℂ => z * φ τ) hsum
      · have hφ_zero : φ τ = 0 :=
          image_eq_zero_of_notMem_tsupport hτ
        simp [hφ_zero]
    rw [hsequence] at hlimit
    have hcommon := hpacket i F φ hφ
    have heq := tendsto_nhds_unique hlimit hcommon
    simpa [T,
      rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily,
      rootedReflectedGramGeneratorTwoScaleApproximationFamily,
      rootedReflectedGramGeneratorNativeTwoScaleApproximationFamily,
      GeneratorSpatialTwoScaleApproximationFamily.precomp,
      B, D, lift, F, G, e, trace] using heq
  let E :
      T.CommonPositiveRealEdgeData :=
    GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.ofCommonDistributionalTrace
      T V hV_open hV_ne hmem trace htrace
  let W : SchwartzNPoint d k →L[ℂ] ℂ :=
    anchoredOrderedTransportDistribution C.current anchor
  have hW :
      ∀ (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
        (φ : SchwartzMap (Fin k → ℝ) ℂ),
        W (section43OrderedPullbackTimeSpatialTensorCLM d k χ φ) =
          trace χ φ := by
    intro χ φ
    calc
      W (section43OrderedPullbackTimeSpatialTensorCLM d k χ φ) =
          C.current (section43NPointTimeSpatialTensor d k
            (SCV.translateSchwartz (-anchor) φ) χ) := by
        exact
          anchoredOrderedTransportDistribution_orderedPullbackTimeSpatialTensor
            C.current anchor χ φ
      _ = trace χ φ := by
        simp [trace, lift, section43SpatialHeadMarginal_basepointLift_eq]
  have hrep :
      OSIITimeSpatialRepresentsDistributionOn W E.orbit V := by
    intro χ φ hφ
    let i₀ : GeneratorIndex k := GeneratorIndex.ofGap (0 : Fin k)
    calc
      (W.comp (section43OrderedPullbackTimeSpatialTensorCLM d k χ)) φ =
          trace χ φ := by
        simpa only [ContinuousLinearMap.comp_apply] using hW χ φ
      _ = ∫ τ : Fin k → ℝ,
          T.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ * φ τ :=
        (htrace i₀ χ φ hφ).symm
      _ = ∫ τ : Fin k → ℝ, E.orbit τ χ * φ τ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with τ
        by_cases hτ :
            τ ∈ tsupport (φ : (Fin k → ℝ) → ℂ)
        · have hτV : τ ∈ V := hφ.2 hτ
          have heq :
              T.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ =
                E.orbit τ χ := by
            change
              T.diagonal.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ =
                E.toDiagonal.orbit τ χ
            exact (E.toDiagonal.scalarLimit_realEdge i₀ τ hτV).2 χ
          rw [heq]
        · have hφ_zero : φ τ = 0 :=
            image_eq_zero_of_notMem_tsupport hτ
          simp [hφ_zero]
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact (hVQ hτ).1
  · exact hV_radial
  · exact hV_positive
  · simpa [E, W,
      GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.ofCommonDistributionalTrace]
      using hrep

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
