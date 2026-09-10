import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformCompactTimeAnchoredAtlas

/-!
# Source linearity of the uniform compact-time anchored atlas

The maximal anchored atlas is constructed source by source, so its definition
does not itself remember the complex-module structure of the universal
fixed-carrier source family.  The fixed-anchor scalar identity recovers that
structure: the moving-slice scalar is linear in its right source, and vectors
in the closed anchor span are determined by all anchor pairings.
-/

noncomputable section

open Complex Filter Set Topology MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

theorem continuous_mixedReflectedChronologicalSource_diag :
    Continuous (fun f : SchwartzNPoint d (k + 1) =>
      mixedReflectedChronologicalSource f f) := by
  let R :
      SchwartzNPoint d ((k + 1) + (k + 1)) →L[ℂ]
        SchwartzNPoint d ((k + (k + 1)) + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (SpacetimeDim d)
        ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
          (finCongr (by omega)))).toContinuousLinearEquiv)
  change Continuous (fun f : SchwartzNPoint d (k + 1) =>
    R (f.osConjTensorProduct f))
  have hdiag :
      Continuous (fun f : SchwartzNPoint d (k + 1) =>
        f.osConjTensorProduct f) :=
    (SchwartzNPoint.osConjTensorProduct_continuous
      (d := d) (n := k + 1) (m := k + 1)).comp
        (continuous_id.prodMk continuous_id)
  exact R.continuous.comp hdiag

omit [NeZero d] in
/-- At every admissible reflected parameter, the moving-slice scalar is a
continuous complex-linear functional of the full reduced Schwartz source. -/
theorem exists_reflectedMovingSliceScalarCLM
    (stage : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (hη_compact :
      HasCompactSupport
        (η : (Fin (k + (k + 1)) → ℝ) → ℂ))
    (w : Fin (k + k) → ℂ)
    (hw : w ∈ reflectedMovingSliceCarrier stage η) :
    ∃ L : SchwartzNPoint d (k + (k + 1)) →L[ℂ] ℂ,
      ∀ F, L F = reflectedMovingSliceScalar stage η F w := by
  let z : Fin (k + (k + 1)) → ℂ :=
    -(reflectedReducedTimeDisplacementCLM k w)
  have hz : z ∈ osiiShiftedConvolutionCarrier stage η := hw
  let U : Set (Fin (k + (k + 1)) → ℝ) :=
    tsupport (η : (Fin (k + (k + 1)) → ℝ) → ℂ)
  let orbit : Set (OSIITimeGapSpace (k + (k + 1))) :=
    osiiShiftedConvolutionOrbit η z
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_schwartz_bound_osiiStage_on_compact
      stage orbit
      (isCompact_osiiShiftedConvolutionOrbit η hη_compact z)
      (osiiShiftedConvolutionOrbit_subset_carrier stage η ⟨z, hz⟩)
  have hbounded :
      OSIITimeSpatialPointwiseBoundedOn
        (osiiShiftedStageDistribution stage z) U := by
    intro χ
    refine
      ⟨C * s.sup
          (schwartzSeminormFamily ℂ
            (Section43SpatialSpace d (k + (k + 1))) ℂ) χ,
        ?_⟩
    intro τ hτ
    exact hbound
      (z + osiiPositiveRealTimeEmbed τ)
      ⟨τ, hτ, rfl⟩ χ
  obtain ⟨L, hL⟩ :=
    exists_osiiMovingSpatialSliceIntegralCLM
      η (osiiShiftedStageDistribution stage z) U
      hη_compact (fun _ h => h)
      (continuousOn_osiiShiftedStageDistribution_pairing
        stage η ⟨z, hz⟩)
      hbounded
  refine ⟨L, ?_⟩
  intro F
  rw [hL]
  rfl

theorem reflectedMovingSliceScalar_mixed_add_right
    (stage : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (hη_compact :
      HasCompactSupport
        (η : (Fin (k + (k + 1)) → ℝ) → ℂ))
    (f g h : SchwartzNPoint d (k + 1))
    (w : Fin (k + k) → ℂ)
    (hw : w ∈ reflectedMovingSliceCarrier stage η) :
    reflectedMovingSliceScalar stage η
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource f (g + h))) w =
      reflectedMovingSliceScalar stage η
          (diffVarReduction d (k + (k + 1))
            (mixedReflectedChronologicalSource f g)) w +
        reflectedMovingSliceScalar stage η
          (diffVarReduction d (k + (k + 1))
            (mixedReflectedChronologicalSource f h)) w := by
  let z : Fin (k + (k + 1)) → ℂ :=
    -(reflectedReducedTimeDisplacementCLM k w)
  let F : SchwartzNPoint d (k + (k + 1)) :=
    diffVarReduction d (k + (k + 1))
      (mixedReflectedChronologicalSource f g)
  let G : SchwartzNPoint d (k + (k + 1)) :=
    diffVarReduction d (k + (k + 1))
      (mixedReflectedChronologicalSource f h)
  have hz : z ∈ osiiShiftedConvolutionCarrier stage η := hw
  have hF :=
    integrable_osiiShiftedMovingSpatialSlicePairing
      stage η hη_compact F ⟨z, hz⟩
  have hG :=
    integrable_osiiShiftedMovingSpatialSlicePairing
      stage η hη_compact G ⟨z, hz⟩
  have hF' :
      Integrable (fun τ =>
        η τ *
          osiiShiftedStageDistribution stage z τ
            (osiiFullSourceSpatialSlice F τ)) := by
    simpa using hF
  have hG' :
      Integrable (fun τ =>
        η τ *
          osiiShiftedStageDistribution stage z τ
            (osiiFullSourceSpatialSlice G τ)) := by
    simpa using hG
  change
    osiiMovingSpatialSliceIntegral η
        (osiiShiftedStageDistribution stage z)
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource f (g + h))) =
      osiiMovingSpatialSliceIntegral η
          (osiiShiftedStageDistribution stage z) F +
        osiiMovingSpatialSliceIntegral η
          (osiiShiftedStageDistribution stage z) G
  have hsource :
      diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource f (g + h)) =
        F + G := by
    have hmixed :
        mixedReflectedChronologicalSource f (g + h) =
          mixedReflectedChronologicalSource f g +
            mixedReflectedChronologicalSource f h := by
      unfold mixedReflectedChronologicalSource
      rw [SchwartzNPoint.osConjTensorProduct_add_right]
      ext x
      rfl
    rw [hmixed, map_add]
  rw [hsource]
  change
    (∫ τ,
      η τ *
        osiiShiftedStageDistribution stage z τ
          (osiiFullSourceSpatialSlice (F + G) τ)) =
      (∫ τ,
        η τ *
          osiiShiftedStageDistribution stage z τ
            (osiiFullSourceSpatialSlice F τ)) +
        ∫ τ,
          η τ *
            osiiShiftedStageDistribution stage z τ
              (osiiFullSourceSpatialSlice G τ)
  rw [← integral_add hF' hG']
  apply integral_congr_ae
  filter_upwards [] with τ
  have hslice :
      osiiFullSourceSpatialSlice (F + G) τ =
        osiiFullSourceSpatialSlice F τ +
          osiiFullSourceSpatialSlice G τ := by
    ext x
    rfl
  rw [hslice, map_add, mul_add]

theorem reflectedMovingSliceScalar_mixed_smul_right
    (stage : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (f g : SchwartzNPoint d (k + 1))
    (c : ℂ)
    (w : Fin (k + k) → ℂ)
    (hw : w ∈ reflectedMovingSliceCarrier stage η) :
    reflectedMovingSliceScalar stage η
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource f (c • g))) w =
      c •
        reflectedMovingSliceScalar stage η
          (diffVarReduction d (k + (k + 1))
            (mixedReflectedChronologicalSource f g)) w := by
  let z : Fin (k + (k + 1)) → ℂ :=
    -(reflectedReducedTimeDisplacementCLM k w)
  let F : SchwartzNPoint d (k + (k + 1)) :=
    diffVarReduction d (k + (k + 1))
      (mixedReflectedChronologicalSource f g)
  have hz : z ∈ osiiShiftedConvolutionCarrier stage η := hw
  change
    osiiMovingSpatialSliceIntegral η
        (osiiShiftedStageDistribution stage z)
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource f (c • g))) =
      c •
        osiiMovingSpatialSliceIntegral η
          (osiiShiftedStageDistribution stage z) F
  have hsource :
      diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource f (c • g)) =
        c • F := by
    have hmixed :
        mixedReflectedChronologicalSource f (c • g) =
          c • mixedReflectedChronologicalSource f g := by
      unfold mixedReflectedChronologicalSource
      rw [SchwartzNPoint.osConjTensorProduct_smul_right]
      ext x
      rfl
    rw [hmixed, map_smul]
  rw [hsource]
  change
    (∫ τ,
      η τ *
        osiiShiftedStageDistribution stage z τ
          (osiiFullSourceSpatialSlice (c • F) τ)) =
      c •
        ∫ τ,
          η τ *
            osiiShiftedStageDistribution stage z τ
              (osiiFullSourceSpatialSlice F τ)
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with τ
  have hslice :
      osiiFullSourceSpatialSlice (c • F) τ =
        c • osiiFullSourceSpatialSlice F τ := by
    ext x
    rfl
  rw [hslice, map_smul]
  simp only [smul_eq_mul]
  ring

namespace UniformCompactTimeMixedHilbertGramFamilyData

variable {q : ℕ}
variable {OS : OsterwalderSchraderAxioms d}
variable {K : Set (Fin ((q + 1) + 1) → ℝ)}

theorem anchoredAtlasField_add
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (b c : AnchoredSourceIndex d q K)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ)
    (hreflected :
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z ∈
        reflectedMovingSliceCarrier stage germ.η) :
    G.anchoredAtlasField stage germ (b + c) z =
      G.anchoredAtlasField stage germ b z +
        G.anchoredAtlasField stage germ c z := by
  apply
    eq_of_mem_sourceAnchorSpan_of_inner_eq
      (fun a => G.hilbert.field a 0)
      (G.anchoredAtlasField_mem_sourceAnchorSpan
        stage germ (b + c) z hz)
      ((sourceAnchorSpan (fun a => G.hilbert.field a 0)).add_mem
        (G.anchoredAtlasField_mem_sourceAnchorSpan
          stage germ b z hz)
        (G.anchoredAtlasField_mem_sourceAnchorSpan
          stage germ c z hz))
  intro a
  rw [inner_add_right]
  rw [← G.anchoredAtlas_scalar_eq_inner_anchor
    stage germ a (b + c) z hz]
  rw [← G.anchoredAtlas_scalar_eq_inner_anchor
    stage germ a b z hz]
  rw [← G.anchoredAtlas_scalar_eq_inner_anchor
    stage germ a c z hz]
  rw [G.cauchy_scalar a (b + c),
    G.cauchy_scalar a b, G.cauchy_scalar a c]
  apply reflectedMovingSliceScalar_mixed_add_right
  exact germ.η_compact
  exact hreflected

theorem anchoredAtlasField_smul
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (c : ℂ)
    (b : AnchoredSourceIndex d q K)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ)
    (hreflected :
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z ∈
        reflectedMovingSliceCarrier stage germ.η) :
    G.anchoredAtlasField stage germ (c • b) z =
      c • G.anchoredAtlasField stage germ b z := by
  apply
    eq_of_mem_sourceAnchorSpan_of_inner_eq
      (fun a => G.hilbert.field a 0)
      (G.anchoredAtlasField_mem_sourceAnchorSpan
        stage germ (c • b) z hz)
      ((sourceAnchorSpan (fun a => G.hilbert.field a 0)).smul_mem c
        (G.anchoredAtlasField_mem_sourceAnchorSpan
          stage germ b z hz))
  intro a
  rw [inner_smul_right]
  rw [← G.anchoredAtlas_scalar_eq_inner_anchor
    stage germ a (c • b) z hz]
  rw [← G.anchoredAtlas_scalar_eq_inner_anchor
    stage germ a b z hz]
  rw [G.cauchy_scalar a (c • b), G.cauchy_scalar a b]
  apply reflectedMovingSliceScalar_mixed_smul_right
  exact hreflected

/-- The complete local reflected-Gram identity of the maximal atlas,
specialized to the reflected center of one field point. -/
theorem anchoredAtlas_scalar_reflectedCauchyCenter_eq_inner
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a b : AnchoredSourceIndex d q K)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ) :
    (G.cauchy a b).scalar (reflectedCauchyCenter z) =
      @inner ℂ (OSHilbertSpace OS) _
        (G.anchoredAtlasField stage germ a z)
        (G.anchoredAtlasField stage germ b z) := by
  rcases Set.mem_iUnion.mp hz with ⟨C, hzC⟩
  have hleft :
      star (fun i =>
        reflectedCauchyCenter z
          (Fin.castAdd (q + 1) i)) = z := by
    funext i
    simp
  have hright :
      (fun i =>
        reflectedCauchyCenter z
          (Fin.natAdd (q + 1) i)) = z := by
    funext i
    exact reflectedCauchyCenter_right z i
  have hw :
      reflectedCauchyCenter z ∈
        reflectedHilbertPairKernelDomain
          C.gram.domain C.gram.domain := by
    constructor
    · simpa only [hleft] using hzC
    · simpa only [hright] using hzC
  have h :=
    SourceIndexedAnchoredReflectedGramChart.scalar_eq_gluedKernel_on_chart
      C a b hw
  unfold reflectedHilbertPairKernel at h
  rw [hleft, hright] at h
  exact h

/-- The diagonal prescribed scalar controls the squared norm of the globally
glued source field at every covered point. -/
theorem anchoredAtlasField_norm_sq_eq_scalar_re
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (b : AnchoredSourceIndex d q K)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ) :
    ‖G.anchoredAtlasField stage germ b z‖ ^ 2 =
      ((G.cauchy b b).scalar (reflectedCauchyCenter z)).re := by
  rw [G.anchoredAtlas_scalar_reflectedCauchyCenter_eq_inner
    stage germ b b z hz]
  exact
    (inner_self_eq_norm_sq (𝕜 := ℂ)
      (G.anchoredAtlasField stage germ b z)).symm

/-- At every point of the global anchored domain, the continued Hilbert
field is complex-linear in the universal fixed-carrier source. -/
noncomputable def anchoredAtlasFieldLinearMap
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ)
    (hreflected :
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z ∈
        reflectedMovingSliceCarrier stage germ.η) :
    AnchoredSourceIndex d q K →ₗ[ℂ] OSHilbertSpace OS where
  toFun a := G.anchoredAtlasField stage germ a z
  map_add' b c :=
    G.anchoredAtlasField_add stage germ b c z hz hreflected
  map_smul' c b :=
    G.anchoredAtlasField_smul stage germ c b z hz hreflected

@[simp] theorem anchoredAtlasFieldLinearMap_apply
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ)
    (hreflected :
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z ∈
        reflectedMovingSliceCarrier stage germ.η)
    (a : AnchoredSourceIndex d q K) :
    G.anchoredAtlasFieldLinearMap stage germ z hz hreflected a =
      G.anchoredAtlasField stage germ a z :=
  rfl

/-- On the concrete scalar moving-slice carrier, the globally glued
source-linear field is continuous in the universal fixed-carrier source. -/
theorem anchoredAtlasFieldLinearMap_continuous
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ)
    (hreflected :
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z ∈
        reflectedMovingSliceCarrier stage germ.η)
    (hcenter :
      reflectedCauchyCenter z ∈
        reflectedMovingSliceCarrier stage germ.η) :
    Continuous
      (G.anchoredAtlasFieldLinearMap
        stage germ z hz hreflected) := by
  let T :=
    G.anchoredAtlasFieldLinearMap
      stage germ z hz hreflected
  obtain ⟨L, hL⟩ :=
    exists_reflectedMovingSliceScalarCLM
      stage germ.η germ.η_compact
      (reflectedCauchyCenter z) hcenter
  let J :
      AnchoredSourceIndex d q K →L[ℂ]
        SchwartzNPoint d ((q + 1) + 1) :=
    (euclideanPositiveTimeSubmodule
        (d := d) ((q + 1) + 1)).subtypeL.comp
      (uniformCompactTimeSourceSubmodule
        d ((q + 1) + 1) K).subtypeL
  let Q : AnchoredSourceIndex d q K → ℝ :=
    fun b =>
      (L
        (diffVarReduction d ((q + 1) + ((q + 1) + 1))
          (mixedReflectedChronologicalSource (J b) (J b)))).re
  have hmixed :
      Continuous (fun b : AnchoredSourceIndex d q K =>
        mixedReflectedChronologicalSource (J b) (J b)) :=
    (continuous_mixedReflectedChronologicalSource_diag
      (d := d) (k := q + 1)).comp J.continuous
  have hQ : Continuous Q := by
    exact Complex.continuous_re.comp
      (L.continuous.comp
        ((diffVarReduction d ((q + 1) + ((q + 1) + 1))).continuous.comp
          hmixed))
  have hnorm_sq (b : AnchoredSourceIndex d q K) :
      ‖T b‖ ^ 2 = Q b := by
    change
      ‖G.anchoredAtlasField stage germ b z‖ ^ 2 =
        Q b
    calc
      ‖G.anchoredAtlasField stage germ b z‖ ^ 2 =
          ((G.cauchy b b).scalar
            (reflectedCauchyCenter z)).re :=
        G.anchoredAtlasField_norm_sq_eq_scalar_re
          stage germ b z hz
      _ =
          (reflectedMovingSliceScalar stage germ.η
            (diffVarReduction d ((q + 1) + ((q + 1) + 1))
              (mixedReflectedChronologicalSource
                (UniformCompactTimeSource.source (K := K) b).1
                (UniformCompactTimeSource.source (K := K) b).1))
            (reflectedCauchyCenter z)).re := by
        rw [G.cauchy_scalar b b]
      _ = Q b := by
        rw [← hL]
        rfl
  have hQ_zero : Q 0 = 0 := by
    calc
      Q 0 = ‖T 0‖ ^ 2 := (hnorm_sq 0).symm
      _ = 0 := by rw [map_zero]; norm_num
  have hQ_tendsto :
      Tendsto Q (𝓝 0) (𝓝 0) := by
    have hQ_at : ContinuousAt Q 0 := hQ.continuousAt
    simpa only [ContinuousAt, hQ_zero] using hQ_at
  have hnorm_sq_tendsto :
      Tendsto (fun b : AnchoredSourceIndex d q K => ‖T b‖ ^ 2)
        (𝓝 0) (𝓝 0) :=
    hQ_tendsto.congr'
      (Filter.Eventually.of_forall fun b => (hnorm_sq b).symm)
  have hnorm_tendsto :
      Tendsto (fun b : AnchoredSourceIndex d q K => ‖T b‖)
        (𝓝 0) (𝓝 0) := by
    have hsqrt :=
      Real.continuous_sqrt.continuousAt.tendsto.comp
        hnorm_sq_tendsto
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm,
      Real.sqrt_zero] using hsqrt
  apply continuous_of_tendsto_nhds_zero T
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto

/-- The global anchored source field, bundled as a continuous complex-linear
map at every concrete reflected moving-slice point. -/
noncomputable def anchoredAtlasFieldContinuousLinearMap
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ)
    (hreflected :
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z ∈
        reflectedMovingSliceCarrier stage germ.η)
    (hcenter :
      reflectedCauchyCenter z ∈
        reflectedMovingSliceCarrier stage germ.η) :
    AnchoredSourceIndex d q K →L[ℂ] OSHilbertSpace OS where
  toLinearMap :=
    G.anchoredAtlasFieldLinearMap
      stage germ z hz hreflected
  cont :=
    G.anchoredAtlasFieldLinearMap_continuous
      stage germ z hz hreflected hcenter

@[simp] theorem anchoredAtlasFieldContinuousLinearMap_apply
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ)
    (hreflected :
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z ∈
        reflectedMovingSliceCarrier stage germ.η)
    (hcenter :
      reflectedCauchyCenter z ∈
        reflectedMovingSliceCarrier stage germ.η)
    (a : AnchoredSourceIndex d q K) :
    G.anchoredAtlasFieldContinuousLinearMap
        stage germ z hz hreflected hcenter a =
      G.anchoredAtlasField stage germ a z :=
  rfl

/-- On the complete generated mixed carrier, the globally continued anchored
field is complex-linear in the universal fixed-carrier source. -/
noncomputable def anchoredAtlasGeneratedFieldLinearMap
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((q + 1) + ((q + 1) + 1)) N) ⊆
        stage.carrier)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase ((q + 1) + 1) N)) :
    AnchoredSourceIndex d q K →ₗ[ℂ] OSHilbertSpace OS :=
  G.anchoredAtlasFieldLinearMap stage germ z
    (G.generatedMixedCarrier_subset_anchoredAtlasCoveredDomain
      stage germ hgenerated hz)
    (zeroAnchorPair_mem_reflectedMovingSliceCarrier_of_generated
      stage germ.η germ.η_support hgenerated hz)

@[simp] theorem anchoredAtlasGeneratedFieldLinearMap_apply
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((q + 1) + ((q + 1) + 1)) N) ⊆
        stage.carrier)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase ((q + 1) + 1) N))
    (a : AnchoredSourceIndex d q K) :
    G.anchoredAtlasGeneratedFieldLinearMap
        stage germ hgenerated z hz a =
      G.anchoredAtlasField stage germ a z :=
  rfl

/-- On the complete generated mixed carrier, the globally continued anchored
field is a continuous complex-linear map of the universal fixed-carrier
source. -/
noncomputable def anchoredAtlasGeneratedFieldContinuousLinearMap
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((q + 1) + ((q + 1) + 1)) N) ⊆
        stage.carrier)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase ((q + 1) + 1) N)) :
    AnchoredSourceIndex d q K →L[ℂ] OSHilbertSpace OS :=
  G.anchoredAtlasFieldContinuousLinearMap stage germ z
    (G.generatedMixedCarrier_subset_anchoredAtlasCoveredDomain
      stage germ hgenerated hz)
    (zeroAnchorPair_mem_reflectedMovingSliceCarrier_of_generated
      stage germ.η germ.η_support hgenerated hz)
    (reflectedCauchyCenter_mem_reflectedMovingSliceCarrier_of_generated
      stage germ.η germ.η_support hgenerated hz)

@[simp] theorem anchoredAtlasGeneratedFieldContinuousLinearMap_apply
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((q + 1) + ((q + 1) + 1)) N) ⊆
        stage.carrier)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase ((q + 1) + 1) N))
    (a : AnchoredSourceIndex d q K) :
    G.anchoredAtlasGeneratedFieldContinuousLinearMap
        stage germ hgenerated z hz a =
      G.anchoredAtlasField stage germ a z :=
  rfl

end UniformCompactTimeMixedHilbertGramFamilyData
end OSIIChapterV
end OSReconstruction
