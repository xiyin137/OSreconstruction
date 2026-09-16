/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredGeneratedSpatialFields

















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d q : ℕ} [NeZero d]
variable
  {I : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) → ℝ}

theorem reflectedCauchyCenter_eq_reflectedCauchyIncrement
    (z : Fin (q + 1) → ℂ) :
    reflectedCauchyCenter z = reflectedCauchyIncrement z := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [reflectedCauchyCenter_left, reflectedCauchyIncrement_left]
  · rw [reflectedCauchyCenter_right, reflectedCauchyIncrement_right]

namespace PositiveHeadUniversalAnchoredAtlasData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {A :
    AnchoredPacketTimeShellFamilyData
      (d := d) I anchor}

/-- Restrict the global anchored spatial field to particlewise product tests
at one point of the open source-linear atlas domain. -/
noncomputable def spatialProductFieldCMM
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin ((q + 1) + 1) =>
        SchwartzMap (Fin d → ℝ) ℂ)
      (OSHilbertSpace OS) :=
  (D.spatialFieldCLM scale z hz).compContinuousMultilinearMap
    ((section43SpatialSchwartzParticleCLE d ((q + 1) + 1)
      ).symm.toContinuousLinearMap.compContinuousMultilinearMap
        (SchwartzMap.productTensorMLM ((q + 1) + 1)))

@[simp]
theorem spatialProductFieldCMM_apply
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain)
    (fs : Fin ((q + 1) + 1) →
      SchwartzMap (Fin d → ℝ) ℂ) :
    D.spatialProductFieldCMM scale z hz fs =
      D.gram.anchoredAtlasField
        D.sourceStage.stage D.sourceStage.germ
        (A.positiveHeadSpatialAnchoredSourceCLM scale
          ((section43SpatialSchwartzParticleCLE
            d ((q + 1) + 1)).symm
            (SchwartzMap.productTensor fs)))
        z :=
  rfl

/-- The complete packet-scale anchored field has the same compact-local
tensor-Gram representation on the global source-linear domain as on the
initial Gram ball. -/
noncomputable def
    toLocallyCompactTensorPairGramRepresentationData_anchoredSpatial
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    @LocallyCompactTensorPairGramRepresentationData
      (q + 1) (q + 1) (OSHilbertSpace OS) _ _
      (fun scale z =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (A.positiveHeadSpatialAnchoredSourceCLM scale χ) z)
      D.spatialLinearDomain := by
  let tail :=
    I.toSchwartzTimeApproximateIdentity.tail
      A.carrierData.tailStart
  let θ : SchwartzMap ℝ ℂ :=
    normalizedPositiveTimeBasepointCutoff.f
  refine
    { leftTest := tail.test
      rightTest := tail.test
      leftRadius := tail.radius
      rightRadius := tail.radius
      left_nonnegative := tail.nonnegative
      right_nonnegative := tail.nonnegative
      left_real := tail.real
      right_real := tail.real
      left_integral_one := tail.integral_one
      right_integral_one := tail.integral_one
      left_support := tail.support
      right_support := tail.support
      leftRadius_tendsto := tail.radius_tendsto
      rightRadius_tendsto := tail.radius_tendsto
      value :=
        positiveHeadSpatialMixedKernelCenterValue
          (anchor := anchor)
          D.sourceStage.stage D.sourceStage.germ.η χ
      localData := ?_ }
  intro z hz
  obtain ⟨K, hK_compact, hzK, hK_domain⟩ :=
    exists_compact_between
      (isCompact_singleton :
        IsCompact ({z} : Set (Fin (q + 1) → ℂ)))
      D.spatialLinearDomain_open
      (by simpa using hz)
  have hz_interior : z ∈ interior K :=
    hzK (by simp)
  have hK_nhds : K ∈ 𝓝[D.spatialLinearDomain] z := by
    apply mem_nhdsWithin_of_mem_nhds
    exact Filter.mem_of_superset
      (isOpen_interior.mem_nhds hz_interior) interior_subset
  refine
    ⟨K, hK_nhds, hK_compact,
      1, zero_lt_one,
      (fun w y =>
        osiiReflectedMixedProductBasepointKernel
          D.sourceStage.stage D.sourceStage.germ.η
          θ θ χ χ
          (reflectedCauchyIncrement w) y),
      (fun _ => Fin.append anchor anchor),
      ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hcenter :
        reflectedCauchyIncrement p.1 ∈
          reflectedMovingSliceCarrier
            D.sourceStage.stage D.sourceStage.germ.η := by
      rw [← reflectedCauchyCenter_eq_reflectedCauchyIncrement]
      exact (hK_domain hp.1).2.2
    exact
      (continuousAt_osiiReflectedMixedProductBasepointKernel_cauchyShift
        D.sourceStage.stage D.sourceStage.germ.η
        D.sourceStage.germ.η_compact
        θ θ
        normalizedPositiveTimeBasepointCutoff.compact
        normalizedPositiveTimeBasepointCutoff.compact
        χ χ hcenter (Fin.append anchor anchor) p.2).continuousWithinAt
  · intro pq w hw
    have hcenter :
        reflectedCauchyIncrement w ∈
          reflectedMovingSliceCarrier
            D.sourceStage.stage D.sourceStage.germ.η := by
      rw [← reflectedCauchyCenter_eq_reflectedCauchyIncrement]
      exact (hK_domain hw).2.2
    exact
      integrable_tensorProduct_mul_osiiReflectedMixedProductBasepointKernel
        D.sourceStage.stage D.sourceStage.germ.η
        θ θ
        normalizedPositiveTimeBasepointCutoff.compact
        normalizedPositiveTimeBasepointCutoff.compact
        χ χ
        (tail.test pq.1) (tail.test pq.2)
        (tail.compact pq.1) (tail.compact pq.2)
        hcenter (Fin.append anchor anchor)
  · intro pq w hw
    let a :=
      A.positiveHeadSpatialAnchoredSourceCLM pq.1 χ
    let b :=
      A.positiveHeadSpatialAnchoredSourceCLM pq.2 χ
    have hcenter :
        reflectedCauchyIncrement w ∈
          reflectedMovingSliceCarrier
            D.sourceStage.stage D.sourceStage.germ.η := by
      rw [← reflectedCauchyCenter_eq_reflectedCauchyIncrement]
      exact (hK_domain hw).2.2
    calc
      @inner ℂ (OSHilbertSpace OS) _
          (D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ a w)
          (D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ b w) =
          (D.gram.cauchy a b).scalar
            (reflectedCauchyCenter w) :=
        (D.gram.anchoredAtlas_scalar_reflectedCauchyCenter_eq_inner
          D.sourceStage.stage D.sourceStage.germ
          a b w (hK_domain hw).1).symm
      _ =
          reflectedMovingSliceScalar
            D.sourceStage.stage D.sourceStage.germ.η
            (diffVarReduction d ((q + 1) + ((q + 1) + 1))
              (mixedReflectedChronologicalSource
                (UniformCompactTimeSource.source a).1
                (UniformCompactTimeSource.source b).1))
            (reflectedCauchyIncrement w) := by
        rw [D.gram.cauchy_scalar a b,
          reflectedCauchyCenter_eq_reflectedCauchyIncrement]
      _ =
          ∫ y : Fin ((q + 1) + (q + 1)) → ℝ,
            ((tail.test pq.1).tensorProduct
              (tail.test pq.2)) y *
                osiiReflectedMixedProductBasepointKernel
                  D.sourceStage.stage D.sourceStage.germ.η
                  θ θ χ χ
                  (reflectedCauchyIncrement w)
                  (Fin.append anchor anchor + y) := by
        dsimp [a, b]
        simpa [tail, θ, headedTimeSpatialFullSource, timeTest,
          SchwartzTimeApproximateIdentity.tail,
          Section43ProductTimeApproximateIdentity.toSchwartzTimeApproximateIdentity] using
          (reflectedMovingSliceScalar_headedTimeSpatial_translatedApproximateIdentities
            D.sourceStage.stage D.sourceStage.germ.η
            θ θ tail tail anchor anchor χ χ
            normalizedPositiveTimeBasepointCutoff.compact
            normalizedPositiveTimeBasepointCutoff.compact
            pq.1 pq.2 w hcenter)
  · intro w hw
    rfl

/-- Pairwise reflected-Gram convergence for the packet-scale anchored fields
is locally uniform on the complete source-linear atlas domain. -/
noncomputable def toLocallyUniformPairwiseInnerLimitData_anchoredSpatial
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    LocallyUniformPairwiseInnerLimitData
      (fun scale z =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (A.positiveHeadSpatialAnchoredSourceCLM scale χ) z)
      D.spatialLinearDomain :=
  (D.toLocallyCompactTensorPairGramRepresentationData_anchoredSpatial χ
    ).toLocallyUniformPairwiseInnerLimitData

end PositiveHeadUniversalAnchoredAtlasData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
