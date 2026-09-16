/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedSchwingerGerm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedTransport













open Complex MeasureTheory Topology Filter

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d m : ℕ} [NeZero d]

theorem timeCutoff_translateConfiguration
    (s : Fin m → ℝ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (F : SchwartzNPoint d m) :
    SchwartzMap.smulLeftCLM ℂ
        (section43NPointTimeCutoffWeight d m
          (SCV.translateSchwartz s η))
        (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) s) F) =
      translateSchwartzConfiguration
        (osiiDifferenceTimeTranslation (d := d) s)
        (SchwartzMap.smulLeftCLM ℂ
          (section43NPointTimeCutoffWeight d m η) F) := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (section43NPointTimeCutoffWeight_hasTemperateGrowth d m
      (SCV.translateSchwartz s η))]
  rw [translateSchwartzConfiguration_apply]
  rw [translateSchwartzConfiguration_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (section43NPointTimeCutoffWeight_hasTemperateGrowth d m η)]
  simp only [section43NPointTimeCutoffWeight, SCV.translateSchwartz_apply]
  rw [section43QTime_add_osiiDifferenceTimeTranslation]

theorem exists_mem_nhds_tsupport_translateSchwartz_subset
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : HasCompactSupport (η : (Fin m → ℝ) → ℂ))
    (U : Set (Fin m → ℝ))
    (hU_open : IsOpen U)
    (hU : tsupport (η : (Fin m → ℝ) → ℂ) ⊆ U) :
    ∃ V ∈ 𝓝 (0 : Fin m → ℝ), ∀ s ∈ V,
      tsupport
          ((SCV.translateSchwartz s η :
            SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ) ⊆ U := by
  let K := tsupport (η : (Fin m → ℝ) → ℂ)
  let N : Set ((Fin m → ℝ) × (Fin m → ℝ)) :=
    {p | p.1 - p.2 ∈ U}
  have hN_open : IsOpen N := by
    exact hU_open.preimage (continuous_fst.sub continuous_snd)
  have hKN : K ×ˢ ({0} : Set (Fin m → ℝ)) ⊆ N := by
    rintro ⟨y, s⟩ ⟨hy, rfl⟩
    change y - 0 ∈ U
    simpa [K] using hU hy
  obtain ⟨W, V, hW_open, hV_open, hKW, h0V, hWV⟩ :=
    generalized_tube_lemma hη
      (isCompact_singleton : IsCompact ({0} : Set (Fin m → ℝ)))
      hN_open hKN
  refine ⟨V, hV_open.mem_nhds (h0V rfl), ?_⟩
  intro s hs x hx
  have hxsK : x + s ∈ K := by
    rw [tsupport_translateSchwartz_eq_preimage] at hx
    exact hx
  have hpair : (x + s, s) ∈ W ×ˢ V :=
    ⟨hKW hxsK, hs⟩
  have hsub := hWV hpair
  simpa [N] using hsub

def reflectedMovingSliceScalar
    {k : ℕ}
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (F : SchwartzNPoint d (k + (k + 1)))
    (w : Fin (k + k) → ℂ) : ℂ :=
  osiiStageMovingSliceScalar A η F
    (-(reflectedReducedTimeDisplacementCLM k w))

def reflectedMovingSliceCarrier
    {k : ℕ}
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ) :
    Set (Fin (k + k) → ℂ) :=
  (fun w => -(reflectedReducedTimeDisplacementCLM k w)) ⁻¹'
    osiiStageMovingSliceCarrier A η

omit [NeZero d] in
theorem isOpen_reflectedMovingSliceCarrier
    {k : ℕ}
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (hη : HasCompactSupport
      (η : (Fin (k + (k + 1)) → ℝ) → ℂ)) :
    IsOpen (reflectedMovingSliceCarrier A η) := by
  exact (isOpen_osiiStageMovingSliceCarrier A η hη).preimage
    (continuous_neg.comp
      (reflectedReducedTimeDisplacementCLM k).continuous)

omit [NeZero d] in
/-- If the positive real-time image of a represented region lies in the
continuation carrier and contains the cutoff support, then the reflected
moving-slice chart contains its Taylor basepoint. -/
theorem zero_mem_reflectedMovingSliceCarrier
    {k : ℕ}
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (U : Set (Fin (k + (k + 1)) → ℝ))
    (hη_support :
      tsupport (η : (Fin (k + (k + 1)) → ℝ) → ℂ) ⊆ U)
    (hU_carrier :
      ∀ τ ∈ U, osiiPositiveRealTimeEmbed τ ∈ A.carrier) :
    (0 : Fin (k + k) → ℂ) ∈ reflectedMovingSliceCarrier A η := by
  intro τ hτ
  change
    -(reflectedReducedTimeDisplacementCLM k
        (0 : Fin (k + k) → ℂ)) +
        osiiPositiveRealTimeEmbed τ ∈ A.carrier
  rw [map_zero, neg_zero, zero_add]
  exact hU_carrier τ (hη_support hτ)

omit [NeZero d] in
/-- Openness of the reflected moving-slice carrier supplies the uniform
closed internal polydisc required by the Cauchy/Taylor endpoint. -/
theorem exists_reflectedMovingSlice_closedPolydisc
    {k : ℕ}
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (hη_comp :
      HasCompactSupport
        (η : (Fin (k + (k + 1)) → ℝ) → ℂ))
    (U : Set (Fin (k + (k + 1)) → ℝ))
    (hη_support :
      tsupport (η : (Fin (k + (k + 1)) → ℝ) → ℂ) ⊆ U)
    (hU_carrier :
      ∀ τ ∈ U, osiiPositiveRealTimeEmbed τ ∈ A.carrier) :
    ∃ R > 0,
      SCV.closedPolydisc (0 : Fin (k + k) → ℂ) (fun _ => R) ⊆
        reflectedMovingSliceCarrier A η := by
  have h0 :
      (0 : Fin (k + k) → ℂ) ∈ reflectedMovingSliceCarrier A η :=
    zero_mem_reflectedMovingSliceCarrier A η U hη_support hU_carrier
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.mp
      (isOpen_reflectedMovingSliceCarrier A η hη_comp) 0 h0
  refine ⟨ε / 2, by linarith, ?_⟩
  intro w hw
  apply hεsub
  rw [Metric.mem_ball]
  have hdist : dist w 0 ≤ ε / 2 := by
    apply (dist_pi_le_iff (by linarith)).2
    intro i
    exact (SCV.mem_closedPolydisc_iff.mp hw) i
  linarith

omit [NeZero d] in
theorem differentiableOn_reflectedMovingSliceScalar
    {k : ℕ}
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (F : SchwartzNPoint d (k + (k + 1)))
    (hη : HasCompactSupport
      (η : (Fin (k + (k + 1)) → ℝ) → ℂ)) :
    DifferentiableOn ℂ
      (reflectedMovingSliceScalar A η F)
      (reflectedMovingSliceCarrier A η) := by
  apply DifferentiableOn.comp
    (differentiableOn_osiiStageMovingSliceScalar A η F hη)
  · fun_prop
  · intro w hw
    exact hw

theorem neg_reflectedReducedTimeDisplacementCLM_realEmbedding
    {k : ℕ}
    (u : Fin (k + k) → ℝ) :
    -(reflectedReducedTimeDisplacementCLM k
        (realCoordinateEmbeddingCLM (k + k) u)) =
      osiiPositiveRealTimeEmbed
        (-reflectedReducedTimeDisplacement u) := by
  ext j
  rw [reflectedReducedTimeDisplacementCLM_apply]
  simp only [Pi.neg_apply, osiiPositiveRealTimeEmbed]
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r <;> simp

theorem continuous_reflectedReducedTimeDisplacement
    {k : ℕ} :
    Continuous
      (reflectedReducedTimeDisplacement :
        (Fin (k + k) → ℝ) → Fin (k + (k + 1)) → ℝ) := by
  apply continuous_pi
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [reflectedReducedTimeDisplacement_left]
    have h : Continuous
        (fun u : Fin (k + k) → ℝ => u (Fin.castAdd k (Fin.rev i))) :=
      continuous_apply _
    exact h.neg
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · simpa only [reflectedReducedTimeDisplacement_bridge] using
        (continuous_const :
          Continuous (fun _ : Fin (k + k) → ℝ => (0 : ℝ)))
    · simp only [reflectedReducedTimeDisplacement_right]
      have h : Continuous
          (fun u : Fin (k + k) → ℝ => u (Fin.natAdd k i)) :=
        continuous_apply _
      exact h.neg

/-- A source-specific equality for the translated convolution of the stage's
own positive-real orbit is already the complete reflected scalar real edge.
No auxiliary spacetime distribution or representation theorem is involved. -/
theorem
    reflectedMovingSliceScalar_family_realEdge_eventually_of_stageOrbitIntegral
    {k : ℕ}
    {ι : Type*}
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (F : ι → SchwartzNPoint d (k + (k + 1)))
    (g : ι → (Fin (k + k) → ℝ) → ℂ)
    (hedge :
      ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
        ∀ a,
          osiiMovingSpatialSliceIntegral
              (SCV.translateSchwartz
                (reflectedReducedTimeDisplacement u) η)
              (fun τ =>
                A.distribution (osiiPositiveRealTimeEmbed τ))
              (translateSchwartzConfiguration
                (osiiDifferenceTimeTranslation (d := d)
                  (reflectedReducedTimeDisplacement u)) (F a)) =
            g a u) :
    ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
      ∀ a,
        realAffineSlice
          (reflectedMovingSliceScalar A η (F a)) 0 u =
            g a u := by
  filter_upwards [hedge] with u hu
  intro a
  let t : Fin (k + (k + 1)) → ℝ :=
    reflectedReducedTimeDisplacement u
  calc
    realAffineSlice
        (reflectedMovingSliceScalar A η (F a)) 0 u =
        osiiStageMovingSliceScalar A η (F a)
          (osiiPositiveRealTimeEmbed (-t)) := by
      simp only [realAffineSlice, zero_add,
        reflectedMovingSliceScalar]
      rw [neg_reflectedReducedTimeDisplacementCLM_realEmbedding]
    _ =
        osiiMovingSpatialSliceIntegral
          (SCV.translateSchwartz t η)
          (fun τ =>
            A.distribution (osiiPositiveRealTimeEmbed τ))
          (translateSchwartzConfiguration
            (osiiDifferenceTimeTranslation (d := d) t) (F a)) := by
      simpa using
        osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_movingSpatialSliceIntegral
          A η (F a) (-t)
    _ = g a u := by
      simpa [t] using hu a

/-- A represented stage needs to agree with the intended real edge only on
the concrete translated cutoff currents used by the moving-slice family.
No representation theorem for an auxiliary reduced functional away from
those currents is required. -/
theorem
    reflectedMovingSliceScalar_family_realEdge_eventually_of_orderedSourceEdge
    {k : ℕ}
    {ι : Type*}
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (hη_comp : HasCompactSupport
      (η : (Fin (k + (k + 1)) → ℝ) → ℂ))
    (W : SchwartzNPoint d (k + (k + 1)) →L[ℂ] ℂ)
    (U : Set (Fin (k + (k + 1)) → ℝ))
    (hU_open : IsOpen U)
    (hη_support :
      tsupport (η : (Fin (k + (k + 1)) → ℝ) → ℂ) ⊆ U)
    (hscalar :
      ∀ χ : SchwartzMap
          (Section43SpatialSpace d (k + (k + 1))) ℂ,
        ContinuousOn
          (fun τ => A.distribution
            (osiiPositiveRealTimeEmbed τ) χ) U)
    (hbounded :
      OSIITimeSpatialPointwiseBoundedOn
        (fun τ => A.distribution
          (osiiPositiveRealTimeEmbed τ)) U)
    (hrep :
      OSIITimeSpatialRepresentsDistributionOn
        W
        (fun τ => A.distribution
          (osiiPositiveRealTimeEmbed τ)) U)
    (F : ι → SchwartzNPoint d (k + (k + 1)))
    (g : ι → (Fin (k + k) → ℝ) → ℂ)
    (horderedEdge :
      ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
        ∀ a,
          W
              (section43OrderedPullbackFullCutoffCLM d (k + (k + 1))
                (SCV.translateSchwartz
                  (reflectedReducedTimeDisplacement u) η)
                (translateSchwartzConfiguration
                  (osiiDifferenceTimeTranslation (d := d)
                    (reflectedReducedTimeDisplacement u)) (F a))) =
            g a u) :
    ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
      ∀ a,
        realAffineSlice
          (reflectedMovingSliceScalar A η (F a)) 0 u =
            g a u := by
  obtain ⟨V, hV, htranslate⟩ :=
    exists_mem_nhds_tsupport_translateSchwartz_subset
      η hη_comp U hU_open hη_support
  have hdisp_zero :
      reflectedReducedTimeDisplacement
          (0 : Fin (k + k) → ℝ) =
        0 := by
    ext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp
    · intro r
      refine Fin.cases ?_ (fun i => ?_) r <;> simp
  have hpreV :
      reflectedReducedTimeDisplacement ⁻¹' V ∈
        𝓝 (0 : Fin (k + k) → ℝ) := by
    have hV0 :
        V ∈ 𝓝
          (reflectedReducedTimeDisplacement
            (0 : Fin (k + k) → ℝ)) := by
      rw [hdisp_zero]
      exact hV
    exact
      continuous_reflectedReducedTimeDisplacement.continuousAt hV0
  filter_upwards [hpreV, horderedEdge] with u hu hedgeu
  intro a
  let t : Fin (k + (k + 1)) → ℝ :=
    reflectedReducedTimeDisplacement u
  have hsupport :
      tsupport
          ((SCV.translateSchwartz (-(-t)) η :
            SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ) :
            (Fin (k + (k + 1)) → ℝ) → ℂ) ⊆ U := by
    simpa [t] using htranslate t hu
  have hmove :=
    osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_orderedPullbackFullCutoff
      A W η U hη_comp
      hscalar hbounded hrep (F a) (-t) hsupport
  calc
    realAffineSlice
        (reflectedMovingSliceScalar A η (F a)) 0 u =
        osiiStageMovingSliceScalar A η (F a)
          (osiiPositiveRealTimeEmbed (-t)) := by
      simp only [realAffineSlice, zero_add,
        reflectedMovingSliceScalar]
      rw [neg_reflectedReducedTimeDisplacementCLM_realEmbedding]
    _ =
        W
          (section43OrderedPullbackFullCutoffCLM d (k + (k + 1))
            (SCV.translateSchwartz t η)
            (translateSchwartzConfiguration
              (osiiDifferenceTimeTranslation (d := d) t) (F a))) := by
      simpa using hmove
    _ = g a u := by
      simpa [t] using hedgeu a

/-- Cutoff invariance converts a raw translated edge for `W` into the exact
ordered-current edge needed by the represented moving-slice chart. -/
theorem orderedTransportDistribution_family_orderedSourceEdge_eventually
    {k : ℕ}
    {ι : Type*}
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (W : SchwartzNPoint d (k + (k + 1)) →L[ℂ] ℂ)
    (F : ι → SchwartzNPoint d (k + (k + 1)))
    (hcutoff :
      ∀ a,
        SchwartzMap.smulLeftCLM ℂ
            (section43NPointTimeCutoffWeight d (k + (k + 1)) η) (F a) =
          F a)
    (g : ι → (Fin (k + k) → ℝ) → ℂ)
    (hedge :
      ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
        ∀ a,
          W (translateSchwartzConfiguration
            (osiiDifferenceTimeTranslation (d := d)
              (reflectedReducedTimeDisplacement u)) (F a)) =
            g a u) :
    ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
      ∀ a,
        orderedTransportDistribution W
            (section43OrderedPullbackFullCutoffCLM d (k + (k + 1))
              (SCV.translateSchwartz
                (reflectedReducedTimeDisplacement u) η)
              (translateSchwartzConfiguration
                (osiiDifferenceTimeTranslation (d := d)
                  (reflectedReducedTimeDisplacement u)) (F a))) =
          g a u := by
  filter_upwards [hedge] with u hu
  intro a
  let t : Fin (k + (k + 1)) → ℝ :=
    reflectedReducedTimeDisplacement u
  calc
    orderedTransportDistribution W
        (section43OrderedPullbackFullCutoffCLM d (k + (k + 1))
          (SCV.translateSchwartz t η)
          (translateSchwartzConfiguration
            (osiiDifferenceTimeTranslation (d := d) t) (F a))) =
        W (SchwartzMap.smulLeftCLM ℂ
          (section43NPointTimeCutoffWeight d (k + (k + 1))
            (SCV.translateSchwartz t η))
          (translateSchwartzConfiguration
            (osiiDifferenceTimeTranslation (d := d) t) (F a))) := by
      exact orderedTransportDistribution_cutoff W
        (SCV.translateSchwartz t η)
        (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) t) (F a))
    _ =
        W (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) t)
          (SchwartzMap.smulLeftCLM ℂ
            (section43NPointTimeCutoffWeight d (k + (k + 1)) η)
            (F a))) := by
      rw [timeCutoff_translateConfiguration]
    _ =
        W (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) t) (F a)) := by
      rw [hcutoff a]
    _ = g a u := by
      simpa [t] using hu a

/-- A common reduced Schwinger real-edge neighborhood remains common after
passing every source in the family through the same represented moving-slice
chart. -/
theorem reflectedMovingSliceScalar_family_realEdge_eventually
    {k : ℕ}
    {ι : Type*}
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (hη_comp : HasCompactSupport
      (η : (Fin (k + (k + 1)) → ℝ) → ℂ))
    (W : SchwartzNPoint d (k + (k + 1)) →L[ℂ] ℂ)
    (U : Set (Fin (k + (k + 1)) → ℝ))
    (hU_open : IsOpen U)
    (hη_support :
      tsupport (η : (Fin (k + (k + 1)) → ℝ) → ℂ) ⊆ U)
    (hscalar :
      ∀ χ : SchwartzMap
          (Section43SpatialSpace d (k + (k + 1))) ℂ,
        ContinuousOn
          (fun τ => A.distribution
            (osiiPositiveRealTimeEmbed τ) χ) U)
    (hbounded :
      OSIITimeSpatialPointwiseBoundedOn
        (fun τ => A.distribution
          (osiiPositiveRealTimeEmbed τ)) U)
    (hrep :
      OSIITimeSpatialRepresentsDistributionOn
        (orderedTransportDistribution W)
        (fun τ => A.distribution
          (osiiPositiveRealTimeEmbed τ)) U)
    (F : ι → SchwartzNPoint d (k + (k + 1)))
    (hcutoff :
      ∀ a,
        SchwartzMap.smulLeftCLM ℂ
            (section43NPointTimeCutoffWeight d (k + (k + 1)) η) (F a) =
          F a)
    (g : ι → (Fin (k + k) → ℝ) → ℂ)
    (hedge :
      ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
        ∀ a,
          W (translateSchwartzConfiguration
            (osiiDifferenceTimeTranslation (d := d)
              (reflectedReducedTimeDisplacement u)) (F a)) =
            g a u) :
    ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
      ∀ a,
        realAffineSlice
          (reflectedMovingSliceScalar A η (F a)) 0 u =
            g a u := by
  have horderedEdge :
      ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
        ∀ a,
          orderedTransportDistribution W
              (section43OrderedPullbackFullCutoffCLM d (k + (k + 1))
                (SCV.translateSchwartz
                  (reflectedReducedTimeDisplacement u) η)
              (translateSchwartzConfiguration
                  (osiiDifferenceTimeTranslation (d := d)
                    (reflectedReducedTimeDisplacement u)) (F a))) =
            g a u := by
    exact
      orderedTransportDistribution_family_orderedSourceEdge_eventually
        η W F hcutoff g hedge
  exact
    reflectedMovingSliceScalar_family_realEdge_eventually_of_orderedSourceEdge
      A η hη_comp (orderedTransportDistribution W)
      U hU_open hη_support hscalar hbounded hrep F g horderedEdge

end OSIIChapterV
end OSReconstruction
