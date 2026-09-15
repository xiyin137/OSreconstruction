/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedTwoScaleFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredOrderedTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapFullSourceRealEdge










noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace GeneratorSpatialTwoScaleApproximationFamily
namespace CommonPositiveRealEdgeData

variable
  (A : GeneratorSpatialTwoScaleApproximationFamily d k)
  (U : Set (Fin k → ℝ))
  (hU_open : IsOpen U)
  (hU_ne : U.Nonempty)
  (hmem :
    ∀ i τ, τ ∈ U →
      osiiPositiveRealTimeEmbed τ ∈ A.domain i)
  (trace :
    SchwartzMap (Section43SpatialSpace d k) ℂ →
      SchwartzMap (Fin k → ℝ) ℂ → ℂ)
  (htrace :
    ∀ (i : GeneratorIndex k)
      (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
      (φ : SchwartzMap (Fin k → ℝ) ℂ),
      SCV.SupportsInOpen (φ : (Fin k → ℝ) → ℂ) U →
        ∫ τ : Fin k → ℝ,
            A.scalarLimit i (osiiPositiveRealTimeEmbed τ) χ * φ τ =
          trace χ φ)

private noncomputable def selectedEdge :
    A.CommonPositiveRealEdgeData :=
  ofCommonDistributionalTrace A U hU_open hU_ne hmem trace htrace

/-- The orbit selected by distributional uniqueness represents any spacetime
distribution whose time-spatial tensor pairing is the supplied common trace. -/
theorem selectedEdge_represents
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (hW :
      ∀ (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
        (φ : SchwartzMap (Fin k → ℝ) ℂ),
        W (section43OrderedPullbackTimeSpatialTensorCLM d k χ φ) =
          trace χ φ) :
    OSIITimeSpatialRepresentsDistributionOn
      W (selectedEdge A U hU_open hU_ne hmem trace htrace).orbit U := by
  intro χ φ hφ
  let i₀ : GeneratorIndex k := GeneratorIndex.ofGap (0 : Fin k)
  calc
    (W.comp (section43OrderedPullbackTimeSpatialTensorCLM d k χ)) φ =
        trace χ φ := hW χ φ
    _ = ∫ τ : Fin k → ℝ,
          A.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ * φ τ :=
      (htrace i₀ χ φ hφ).symm
    _ = ∫ τ : Fin k → ℝ,
          (selectedEdge A U hU_open hU_ne hmem trace htrace).orbit τ χ *
            φ τ := by
      apply integral_congr_ae
      filter_upwards with τ
      by_cases hτ : τ ∈ tsupport (φ : (Fin k → ℝ) → ℂ)
      · have hτU : τ ∈ U := hφ.2 hτ
        have hτmem := hmem i₀ τ hτU
        rw [show
          (selectedEdge A U hU_open hU_ne hmem trace htrace).orbit τ χ =
            A.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ by
          exact
            A.diagonal.distribution_apply_of_mem
              i₀ (osiiPositiveRealTimeEmbed τ) hτmem χ]
      · have hφ_zero : φ τ = 0 :=
          image_eq_zero_of_notMem_tsupport hτ
        simp [hφ_zero]

omit [NeZero d] in
/-- Compact enclosure of the selected real edge gives the pointwise bound
required by the moving-slice stage package. -/
theorem selectedEdge_pointwiseBounded
    (K : Set (Fin k → ℝ))
    (hK_compact : IsCompact K)
    (hUK : U ⊆ K)
    (hKmem :
      ∀ τ ∈ K,
        osiiPositiveRealTimeEmbed τ ∈
          A.domain (GeneratorIndex.ofGap (0 : Fin k))) :
    OSIITimeSpatialPointwiseBoundedOn
      (selectedEdge A U hU_open hU_ne hmem trace htrace).orbit U := by
  intro χ
  let i₀ : GeneratorIndex k := GeneratorIndex.ofGap (0 : Fin k)
  have hhol :
      DifferentiableOn ℂ
        (fun z => A.scalarLimit i₀ z χ) (A.domain i₀) :=
    (A.locallyUniform i₀ χ).differentiableOn_finite
      (Filter.Eventually.of_forall fun p =>
        A.approximation_weaklyHolomorphic i₀ p.1 p.2 χ)
      (A.domain_open i₀)
  have hcontinuous :
      ContinuousOn
        (fun τ =>
          (selectedEdge A U hU_open hU_ne hmem trace htrace).orbit τ χ)
        K := by
    apply
      (hhol.continuousOn.comp
        continuous_osiiPositiveRealTimeEmbed.continuousOn hKmem).congr
    intro τ hτ
    change
      A.diagonal.distribution i₀ (osiiPositiveRealTimeEmbed τ) χ =
        A.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ
    exact
      A.diagonal.distribution_apply_of_mem
        i₀ (osiiPositiveRealTimeEmbed τ) (hKmem τ hτ) χ
  obtain ⟨B, hB⟩ :=
    hK_compact.exists_bound_of_continuousOn hcontinuous
  exact ⟨B, fun τ hτ => hB τ (hUK hτ)⟩

end CommonPositiveRealEdgeData
end GeneratorSpatialTwoScaleApproximationFamily

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

/-- A caller-supplied reduced Schwinger current gives a represented,
pointwise-bounded continuation stage. Its real edge can be confined to any
prescribed neighborhood using only the original OS axioms. -/
theorem exists_rootedRepresentedGeneratorStageOfOS_of_currentData_on
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0) :
    ∃
      (E :
        (rootedGeneratorDiagonalApproximationFamilyOfOS H
          ).CommonPositiveRealEdgeData)
      (P :
        ((rootedGeneratorDiagonalApproximationFamilyOfOS H
            ).toGeneratorFamilyOfConvex E
              (by
                simpa [rootedGeneratorDiagonalApproximationFamilyOfOS] using
                  rootedGeneratorTwoScaleApproximationFamilyOfOS_domain_convex H)
          ).toTimeContinuationStage.PositiveRealEdgeData
            (anchoredOrderedTransportDistribution C.current anchor)
            E.realRegion),
      E.realRegion ⊆ Q ∧
        P.orbit = E.orbit := by
  classical
  let D := H.toContinuousTranslationData
  let lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ :=
    section43SpatialBasepointLiftCLM d k
      (normalizedSpatialBasepointCutoff d).toSchwartz
  let T :=
    rootedGeneratorTwoScaleApproximationFamilyOfOS H
  obtain ⟨V, hV_open, hV_ne, hVQ, _hV_radial, hV_domain, hpacket⟩ :=
    D.exists_radial_tendsto_integral_rootSmearedSpatialHermiteGeneratorSumOfOS_commonChronological_mul_all_splits_of_currentData_on
      C Q hQ
  let center : Fin k → ℝ := hV_ne.some
  obtain ⟨radius, hradius, hclosed⟩ :=
    SCV.exists_pos_closedBall_subset_of_isOpen
      hV_open hV_ne.some_mem
  let U : Set (Fin k → ℝ) := Metric.ball center radius
  let K : Set (Fin k → ℝ) := Metric.closedBall center radius
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_ne : U.Nonempty :=
    ⟨center, Metric.mem_ball_self hradius⟩
  have hUK : U ⊆ K := Metric.ball_subset_closedBall
  have hKV : K ⊆ V := hclosed
  have hUV : U ⊆ V := hUK.trans hKV
  have hmem :
      ∀ i τ, τ ∈ U →
        osiiPositiveRealTimeEmbed τ ∈ T.domain i := by
    intro i τ hτ
    exact hV_domain i τ (hUV hτ)
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
        SCV.SupportsInOpen (φ : (Fin k → ℝ) → ℂ) U →
          ∫ τ : Fin k → ℝ,
              T.scalarLimit i (osiiPositiveRealTimeEmbed τ) χ * φ τ =
            trace χ φ := by
    intro i χ φ hφ
    let F := lift χ
    let P := rootedPacketScaleLimitDataOfOS H i F
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
            D.rootSmearedSpatialHermiteGeneratorSumOfOS
              i timeScale (e τ) F)
          (fun τ => P.limit (e τ))
          atTop U := by
      exact
        P.locallyUniform.comp e
          (fun τ hτ => hV_domain i τ (hUV hτ))
          he_cont.continuousOn
    have hcontinuous :
        ∀ timeScale,
          ContinuousOn
            (fun τ =>
              D.rootSmearedSpatialHermiteGeneratorSumOfOS
                i timeScale (e τ) F) U := by
      intro timeScale
      exact
        (H.differentiableOn_rootSmearedSpatialHermiteGeneratorSumOfOS
          i timeScale F).continuousOn.comp
            he_cont.continuousOn
            (fun τ hτ => hV_domain i τ (hUV hτ))
    have hlimit :=
      SCV.tendsto_integral_mul_schwartz_of_tendstoLocallyUniformlyOn
        hU_open hcontinuous hlocal φ hφ
    have hcommon :=
      hpacket i F φ
        ⟨hφ.1, hφ.2.trans hUV⟩
    have heq := tendsto_nhds_unique hlimit hcommon
    simpa [T, rootedGeneratorTwoScaleApproximationFamilyOfOS,
      rootedGeneratorNativeTwoScaleApproximationFamilyOfOS,
      GeneratorSpatialTwoScaleApproximationFamily.precomp,
      D, lift, F, P, e, trace] using heq
  let E₂ :
      T.CommonPositiveRealEdgeData :=
    GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.selectedEdge
      T U hU_open hU_ne hmem trace htrace
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
      OSIITimeSpatialRepresentsDistributionOn W E₂.orbit U := by
    exact
      GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.selectedEdge_represents
        T U hU_open hU_ne hmem trace htrace W hW
  have hbounded :
      OSIITimeSpatialPointwiseBoundedOn E₂.orbit U := by
    exact
      GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.selectedEdge_pointwiseBounded
        T U hU_open hU_ne hmem trace htrace K
        (isCompact_closedBall center radius) hUK
        (fun τ hτ =>
          hV_domain (GeneratorIndex.ofGap (0 : Fin k)) τ (hKV hτ))
  let E :
      (rootedGeneratorDiagonalApproximationFamilyOfOS H
        ).CommonPositiveRealEdgeData :=
    E₂.toDiagonal
  let P :
      ((rootedGeneratorDiagonalApproximationFamilyOfOS H
          ).toGeneratorFamilyOfConvex E
            (by
              simpa [rootedGeneratorDiagonalApproximationFamilyOfOS] using
                rootedGeneratorTwoScaleApproximationFamilyOfOS_domain_convex H)
        ).toTimeContinuationStage.PositiveRealEdgeData
          (anchoredOrderedTransportDistribution C.current anchor)
          E.realRegion :=
    (rootedGeneratorDiagonalApproximationFamilyOfOS H
      ).toTimeContinuationStagePositiveRealEdgeDataOfConvex
        E
        (by
          simpa [rootedGeneratorDiagonalApproximationFamilyOfOS] using
            rootedGeneratorTwoScaleApproximationFamilyOfOS_domain_convex H)
        W (GeneratorIndex.ofGap (0 : Fin k))
        (by
          simpa [E,
            E₂,
            GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.selectedEdge,
            GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.ofCommonDistributionalTrace,
            GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.toDiagonal,
            GeneratorSpatialApproximationFamily.CommonPositiveRealEdgeData.ofApproximationTendsto]
            using hrep)
        (by
          simpa [E,
            E₂,
            GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.selectedEdge,
            GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.ofCommonDistributionalTrace,
            GeneratorSpatialTwoScaleApproximationFamily.CommonPositiveRealEdgeData.toDiagonal,
            GeneratorSpatialApproximationFamily.CommonPositiveRealEdgeData.ofApproximationTendsto]
            using hbounded)
  refine ⟨E, P, ?_, ?_⟩
  · change U ⊆ Q
    exact hUV.trans hVQ
  rfl

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
