import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniversalCompactCarrierAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTranslatedMixedDeltaProducer

/-!
# Translated spatial growth on the universal anchored atlas

Suppose a scale-indexed spatial source map into one universal compact-carrier
source space is exactly a translated product approximate identity.  The
complete reflected-Gram identity on the global anchored atlas then has the
same tensor-delta representation as the initial Gram chart.

This gives locally uniform pairwise Gram convergence and compact-uniform
Hermite bounds on the full source-linear atlas domain.  The statement is
independent of the origin of the translated product family, so it applies
directly to the rooted left and right Chapter V blocks.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

namespace OSIIChapterV
namespace UniversalCompactCarrierAnchoredAtlasData

variable {d q : ℕ} [NeZero d]
variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {K : Set (Fin ((q + 1) + 1) → ℝ)}

private theorem reflectedCauchyCenter_eq_increment
    (z : Fin (q + 1) → ℂ) :
    reflectedCauchyCenter z = reflectedCauchyIncrement z := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [reflectedCauchyCenter_left, reflectedCauchyIncrement_left]
  · rw [reflectedCauchyCenter_right, reflectedCauchyIncrement_right]

/-- Restrict a universal anchored spatial field to particlewise product
tests at one point of the source-linear atlas domain. -/
noncomputable def spatialProductFieldCMM
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin ((q + 1) + 1) =>
        SchwartzMap (Fin d → ℝ) ℂ)
      (OSHilbertSpace OS) :=
  (D.spatialFieldCLM sourceCLM scale z hz
    ).compContinuousMultilinearMap
      ((section43SpatialSchwartzParticleCLE d ((q + 1) + 1)
        ).symm.toContinuousLinearMap.compContinuousMultilinearMap
          (SchwartzMap.productTensorMLM ((q + 1) + 1)))

@[simp]
theorem spatialProductFieldCMM_apply
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain)
    (fs : Fin ((q + 1) + 1) →
      SchwartzMap (Fin d → ℝ) ℂ) :
    D.spatialProductFieldCMM sourceCLM scale z hz fs =
      D.gram.anchoredAtlasField
        D.sourceStage.stage D.sourceStage.germ
        (sourceCLM scale
          ((section43SpatialSchwartzParticleCLE
            d ((q + 1) + 1)).symm
            (SchwartzMap.productTensor fs)))
        z :=
  rfl

/-- A translated product source family has a compact-local tensor-Gram
representation on the complete source-linear anchored atlas domain. -/
noncomputable def
    toLocallyCompactTensorPairGramRepresentationData_translatedSpatial
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (hsource :
      ∀ scale χ,
        UniformCompactTimeSource.source (sourceCLM scale χ) =
          I.translatedPositiveTimeSpatialSource τ hτ χ scale)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    @LocallyCompactTensorPairGramRepresentationData
      (q + 1) ((q + 1) + 1) (OSHilbertSpace OS) _ _
      (fun scale z =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (sourceCLM scale χ) z)
      D.spatialLinearDomain := by
  refine
    { leftTest := I.test
      rightTest := I.test
      leftRadius := I.radius
      rightRadius := I.radius
      left_nonnegative := I.nonnegative
      right_nonnegative := I.nonnegative
      left_real := I.real
      right_real := I.real
      left_integral_one := I.integral_one
      right_integral_one := I.integral_one
      left_support := I.support
      right_support := I.support
      leftRadius_tendsto := I.radius_tendsto
      rightRadius_tendsto := I.radius_tendsto
      value :=
        Section43ProductTimeApproximateIdentity.mixedMovingKernelCenterValue
          τ D.sourceStage.stage D.sourceStage.germ.η χ
      localData := ?_ }
  intro z hz
  obtain ⟨Kz, hKz_compact, hzKz, hKz_domain⟩ :=
    exists_compact_between
      (isCompact_singleton :
        IsCompact ({z} : Set (Fin (q + 1) → ℂ)))
      D.spatialLinearDomain_open
      (by simpa using hz)
  have hz_interior : z ∈ interior Kz :=
    hzKz (by simp)
  have hKz_nhds : Kz ∈ 𝓝[D.spatialLinearDomain] z := by
    apply mem_nhdsWithin_of_mem_nhds
    exact Filter.mem_of_superset
      (isOpen_interior.mem_nhds hz_interior) interior_subset
  refine
    ⟨Kz, hKz_nhds, hKz_compact,
      1, zero_lt_one,
      (fun w y =>
        osiiReflectedMixedMovingKernel
          D.sourceStage.stage D.sourceStage.germ.η χ χ
          (reflectedCauchyIncrement w) y),
      (fun _ => osiiMixedTimeCenter τ τ),
      ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hcenter :
        reflectedCauchyIncrement p.1 ∈
          reflectedMovingSliceCarrier
            D.sourceStage.stage D.sourceStage.germ.η := by
      rw [← reflectedCauchyCenter_eq_increment]
      exact (hKz_domain hp.1).2.2
    exact
      (continuousAt_osiiReflectedMixedMovingKernel_cauchyShift
        D.sourceStage.stage D.sourceStage.germ.η χ χ hcenter
        (osiiMixedTimeCenter τ τ) p.2).continuousWithinAt
  · intro pq w hw
    have hcenter :
        reflectedCauchyIncrement w ∈
          reflectedMovingSliceCarrier
            D.sourceStage.stage D.sourceStage.germ.η := by
      rw [← reflectedCauchyCenter_eq_increment]
      exact (hKz_domain hw).2.2
    exact
      integrable_tensorProduct_mul_osiiReflectedMixedMovingKernel
        D.sourceStage.stage D.sourceStage.germ.η χ χ
        (I.test pq.1) (I.test pq.2)
        (I.test_compact pq.1) (I.test_compact pq.2)
        hcenter (osiiMixedTimeCenter τ τ)
  · intro pq w hw
    let a := sourceCLM pq.1 χ
    let b := sourceCLM pq.2 χ
    have hcenter :
        reflectedCauchyIncrement w ∈
          reflectedMovingSliceCarrier
            D.sourceStage.stage D.sourceStage.germ.η := by
      rw [← reflectedCauchyCenter_eq_increment]
      exact (hKz_domain hw).2.2
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
          a b w (hKz_domain hw).1).symm
      _ =
          reflectedMovingSliceScalar
            D.sourceStage.stage D.sourceStage.germ.η
            (diffVarReduction d ((q + 1) + ((q + 1) + 1))
              (mixedReflectedChronologicalSource
                (UniformCompactTimeSource.source a).1
                (UniformCompactTimeSource.source b).1))
            (reflectedCauchyIncrement w) := by
        rw [D.gram.cauchy_scalar a b,
          reflectedCauchyCenter_eq_increment]
      _ =
          ∫ y : Fin (((q + 1) + 1) + ((q + 1) + 1)) → ℝ,
            ((I.test pq.1).tensorProduct
              (I.test pq.2)) y *
                osiiReflectedMixedMovingKernel
                  D.sourceStage.stage D.sourceStage.germ.η
                  χ χ (reflectedCauchyIncrement w)
                  (osiiMixedTimeCenter τ τ + y) := by
        dsimp [a, b]
        rw [hsource pq.1 χ, hsource pq.2 χ]
        exact
          reflectedMovingSliceScalar_translatedApproximateIdentities
            D.sourceStage.stage D.sourceStage.germ.η
            I I τ τ hτ hτ χ χ pq.1 pq.2
            (reflectedCauchyIncrement w) hcenter
  · intro w hw
    rfl

/-- Pairwise reflected-Gram convergence for a translated spatial source
family is locally uniform on the complete source-linear atlas domain. -/
noncomputable def
    toLocallyUniformPairwiseInnerLimitData_translatedSpatial
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (hsource :
      ∀ scale χ,
        UniformCompactTimeSource.source (sourceCLM scale χ) =
          I.translatedPositiveTimeSpatialSource τ hτ χ scale)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    LocallyUniformPairwiseInnerLimitData
      (fun scale z =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (sourceCLM scale χ) z)
      D.spatialLinearDomain :=
  (D.toLocallyCompactTensorPairGramRepresentationData_translatedSpatial
    I τ hτ sourceCLM hsource χ).toLocallyUniformPairwiseInnerLimitData

/-- Every compact subset of the source-linear atlas domain has one
scale-uniform squared-norm bound for a fixed spatial Schwartz test. -/
theorem exists_translatedSpatialField_norm_sq_bound_on_compact
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (hsource :
      ∀ scale χ,
        UniformCompactTimeSource.source (sourceCLM scale χ) =
          I.translatedPositiveTimeSpatialSource τ hτ χ scale)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ)
    (C : Set (Fin (q + 1) → ℂ))
    (hC_compact : IsCompact C)
    (hC_domain : C ⊆ D.spatialLinearDomain) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ scale z, z ∈ C →
        ‖D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (sourceCLM scale χ) z‖ ^ 2 ≤ B := by
  exact
    (D.toLocallyUniformPairwiseInnerLimitData_translatedSpatial
      I τ hτ sourceCLM hsource χ).exists_norm_sq_bound_on_compact
        (fun scale =>
          (D.generatedSpatialField_holomorphic sourceCLM scale χ).mono
            (fun _ hz => hz.1))
        D.spatialLinearDomain_open C hC_compact hC_domain

set_option backward.isDefEq.respectTransparency false in
/-- Polynomially encoded particlewise Hermite tests have one Hilbert-vector
bound uniform in translated-source scale on every compact subset of the
source-linear anchored atlas domain. -/
theorem translatedSpatialField_encodedHermite_polyBounded_on_compact
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (hsource :
      ∀ scale χ,
        UniformCompactTimeSource.source (sourceCLM scale χ) =
          I.translatedPositiveTimeSpatialSource τ hτ χ scale)
    (C : Set (Fin (q + 1) → ℂ))
    (hC_compact : IsCompact C)
    (hC_domain : C ⊆ D.spatialLinearDomain)
    (βs : ℕ → Fin ((q + 1) + 1) → ℕ)
    (hβ : ∃ D_enc > 0, ∃ p : ℕ, ∀ r a,
      (βs r a : ℝ) ≤ D_enc * (1 + (r : ℝ)) ^ p) :
    ∃ B > 0, ∃ p : ℕ,
      ∀ (scale : ℕ) (z : Fin (q + 1) → ℂ), z ∈ C → ∀ r,
        ‖D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (sourceCLM scale
            ((section43SpatialSchwartzParticleCLE
              d ((q + 1) + 1)).symm
              (SchwartzMap.productTensor fun a =>
                complexifyRealSchwartz
                  (GaussianField.DyninMityaginSpace.basis
                    (E := SchwartzMap (Fin d → ℝ) ℝ)
                    (βs r a)))))
          z‖ ≤
            B * (1 + (r : ℝ)) ^ p := by
  let J := ℕ × C
  let T :
      J →
        ContinuousMultilinearMap ℂ
          (fun _ : Fin ((q + 1) + 1) =>
            SchwartzMap (Fin d → ℝ) ℂ)
          (OSHilbertSpace OS) :=
    fun j =>
      D.spatialProductFieldCMM sourceCLM
        j.1 j.2.1 (hC_domain j.2.2)
  have hT_pointwise :
      ∀ fs : Fin ((q + 1) + 1) →
          SchwartzMap (Fin d → ℝ) ℂ,
        ∃ B : ℝ, ∀ j : J, ‖T j fs‖ ≤ B := by
    intro fs
    let χ :
        SchwartzMap
          (Section43SpatialSpace d ((q + 1) + 1)) ℂ :=
      (section43SpatialSchwartzParticleCLE
        d ((q + 1) + 1)).symm
        (SchwartzMap.productTensor fs)
    obtain ⟨B, hB, hbound⟩ :=
      D.exists_translatedSpatialField_norm_sq_bound_on_compact
        I τ hτ sourceCLM hsource χ C hC_compact hC_domain
    refine ⟨Real.sqrt B, ?_⟩
    intro j
    have hj := hbound j.1 j.2.1 j.2.2
    have hfield :
        T j fs =
          D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ
            (sourceCLM j.1 χ) j.2.1 := by
      rfl
    rw [hfield]
    have hsqrt_sq : (Real.sqrt B) ^ 2 = B :=
      Real.sq_sqrt hB
    have hsqrt_nonneg : 0 ≤ Real.sqrt B :=
      Real.sqrt_nonneg B
    have hnorm_nonneg :
        0 ≤
          ‖D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ
            (sourceCLM j.1 χ) j.2.1‖ :=
      norm_nonneg _
    nlinarith
  obtain ⟨B, hB, p, hbound⟩ :=
    pointwiseBounded_cmm_encodedHermite_polyBounded
      (D := Fin d → ℝ) T βs hβ hT_pointwise
  refine ⟨B, hB, p, ?_⟩
  intro scale z hz r
  simpa [T, J] using hbound (scale, ⟨z, hz⟩) r

end UniversalCompactCarrierAnchoredAtlasData
end OSIIChapterV
end OSReconstruction
