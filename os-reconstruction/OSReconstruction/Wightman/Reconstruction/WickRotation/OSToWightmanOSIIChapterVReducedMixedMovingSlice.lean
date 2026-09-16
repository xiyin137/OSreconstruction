/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedMixedSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTensorMovingSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTimeSmearingRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDoubleDeltaSmearing









noncomputable section

open Complex MeasureTheory Topology Filter
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

/-- Original two-block time coordinates transported to the exact full arity
used by the Chapter V continuation stage. -/
def osiiMixedBlockGlobalTimeTuple
    (k : ℕ)
    (δ : Fin ((k + 1) + (k + 1)) → ℝ) :
    Fin ((k + (k + 1)) + 1) → ℝ :=
  section43TimeTupleTransport (by omega)
    (osiiAxisPairBlockGlobalTimeAffine
      (k + 1) (k + 1) 0 0 δ)

/-- The reduced-time tail of the mixed block-global tuple. -/
def osiiMixedBlockGlobalReducedTime
    (k : ℕ)
    (δ : Fin ((k + 1) + (k + 1)) → ℝ) :
    Fin (k + (k + 1)) → ℝ :=
  Fin.tail (osiiMixedBlockGlobalTimeTuple k δ)

theorem continuous_osiiMixedBlockGlobalReducedTime
    (k : ℕ) :
    Continuous (osiiMixedBlockGlobalReducedTime k) := by
  exact
    (tailCLM (k + (k + 1))).continuous.comp
      ((continuous_section43TimeTupleTransport (by omega)).comp
        ((osiiAxisPairBlockGlobalTimeCLE
          (k + 1) (k + 1)).continuous.add continuous_const))

/-- Center of the independent left/right time delta variables. -/
def osiiMixedTimeCenter
    (τ₁ τ₂ : Fin (k + 1) → ℝ) :
    Fin ((k + 1) + (k + 1)) → ℝ :=
  Fin.append τ₁ τ₂

/-- Fixed spatial marginal of a chronologically reordered mixed
time/spatial source. -/
noncomputable def osiiMixedSpatialHeadMarginal
    (χ₁ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    SchwartzMap
      (Section43SpatialSpace d (k + (k + 1))) ℂ :=
  section43SpatialHeadMarginal
    (section43SpatialSchwartzTransport d (by omega)
      (GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalSpatialPullbackCLM
        (d := d) (k + 1) (k + 1)
        (section43TwoBlockSpatialProduct χ₁ χ₂)))

/-- Scale-independent mixed moving-slice kernel in the original independent
left/right time coordinates. -/
def osiiReflectedMixedMovingKernel
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (w : Fin (k + k) → ℂ)
    (δ : Fin ((k + 1) + (k + 1)) → ℝ) : ℂ :=
  osiiStageFixedSpatialCutoffIntegrand A ρ
    (osiiMixedSpatialHeadMarginal χ₁ χ₂)
    (-(reflectedReducedTimeDisplacementCLM k w))
    (osiiMixedBlockGlobalReducedTime k δ)

set_option maxHeartbeats 800000 in
/-- The mixed kernel is jointly continuous at every point whose reflected
moving parameter lies in the moving-slice carrier. -/
theorem continuousAt_osiiReflectedMixedMovingKernel
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    {w : Fin (k + k) → ℂ}
    (hw : w ∈ reflectedMovingSliceCarrier A ρ)
    (δ : Fin ((k + 1) + (k + 1)) → ℝ) :
    ContinuousAt
      (Function.uncurry
        (osiiReflectedMixedMovingKernel A ρ χ₁ χ₂))
      (w, δ) := by
  let τ := osiiMixedBlockGlobalReducedTime k δ
  let z := -(reflectedReducedTimeDisplacementCLM k w)
  have hτ_cont :
      Continuous (osiiMixedBlockGlobalReducedTime k) :=
    continuous_osiiMixedBlockGlobalReducedTime k
  by_cases hτ : τ ∈ tsupport
      (ρ : (Fin (k + (k + 1)) → ℝ) → ℂ)
  · have hshift :
        z + osiiPositiveRealTimeEmbed τ ∈ A.carrier :=
      hw hτ
    have heval :
        ContinuousAt
          (fun p :
            OSIITimeGapSpace (k + (k + 1)) ×
              SchwartzMap
                (Section43SpatialSpace d (k + (k + 1))) ℂ =>
            A.distribution p.1 p.2)
          (z + osiiPositiveRealTimeEmbed τ,
            osiiMixedSpatialHeadMarginal χ₁ χ₂) := by
      have hmem :
          (z + osiiPositiveRealTimeEmbed τ,
              osiiMixedSpatialHeadMarginal χ₁ χ₂) ∈
            A.carrier ×ˢ Set.univ :=
        ⟨hshift, Set.mem_univ _⟩
      exact
        ((continuousOn_osiiWeaklyHolomorphicEvaluation A)
          _ hmem).continuousAt
          ((A.carrier_open.prod isOpen_univ).mem_nhds hmem)
    have htime :
        Continuous
          (fun p :
            (Fin (k + k) → ℂ) ×
              (Fin ((k + 1) + (k + 1)) → ℝ) =>
            -(reflectedReducedTimeDisplacementCLM k p.1) +
              osiiPositiveRealTimeEmbed
                (osiiMixedBlockGlobalReducedTime k p.2)) := by
      exact
        (continuous_neg.comp
            ((reflectedReducedTimeDisplacementCLM k).continuous.comp
              continuous_fst)).add
          (continuous_osiiPositiveRealTimeEmbed.comp
            (hτ_cont.comp continuous_snd))
    have hinner :
        ContinuousAt
          (fun p :
            (Fin (k + k) → ℂ) ×
              (Fin ((k + 1) + (k + 1)) → ℝ) =>
            (-(reflectedReducedTimeDisplacementCLM k p.1) +
                osiiPositiveRealTimeEmbed
                  (osiiMixedBlockGlobalReducedTime k p.2),
              osiiMixedSpatialHeadMarginal χ₁ χ₂))
          (w, δ) :=
      (htime.prodMk continuous_const).continuousAt
    have hdistribution :
        ContinuousAt
          (fun p :
            (Fin (k + k) → ℂ) ×
              (Fin ((k + 1) + (k + 1)) → ℝ) =>
            A.distribution
              (-(reflectedReducedTimeDisplacementCLM k p.1) +
                osiiPositiveRealTimeEmbed
                  (osiiMixedBlockGlobalReducedTime k p.2))
              (osiiMixedSpatialHeadMarginal χ₁ χ₂))
          (w, δ) :=
      ContinuousAt.comp'
        (f := fun p :
          (Fin (k + k) → ℂ) ×
            (Fin ((k + 1) + (k + 1)) → ℝ) =>
          (-(reflectedReducedTimeDisplacementCLM k p.1) +
              osiiPositiveRealTimeEmbed
                (osiiMixedBlockGlobalReducedTime k p.2),
            osiiMixedSpatialHeadMarginal χ₁ χ₂))
        (g := fun p :
          OSIITimeGapSpace (k + (k + 1)) ×
            SchwartzMap
              (Section43SpatialSpace d (k + (k + 1))) ℂ =>
          A.distribution p.1 p.2)
        heval hinner
    have hcutoff :
        ContinuousAt
          (fun p :
            (Fin (k + k) → ℂ) ×
              (Fin ((k + 1) + (k + 1)) → ℝ) =>
            ρ (osiiMixedBlockGlobalReducedTime k p.2))
          (w, δ) :=
      (ρ.continuous.comp (hτ_cont.comp continuous_snd)).continuousAt
    change
      ContinuousAt
        (fun p :
          (Fin (k + k) → ℂ) ×
            (Fin ((k + 1) + (k + 1)) → ℝ) =>
          ρ (osiiMixedBlockGlobalReducedTime k p.2) *
            A.distribution
              (-(reflectedReducedTimeDisplacementCLM k p.1) +
                osiiPositiveRealTimeEmbed
                  (osiiMixedBlockGlobalReducedTime k p.2))
              (osiiMixedSpatialHeadMarginal χ₁ χ₂))
        (w, δ)
    have hproduct :
        ContinuousAt
          (fun p :
            (Fin (k + k) → ℂ) ×
              (Fin ((k + 1) + (k + 1)) → ℝ) =>
            ρ (osiiMixedBlockGlobalReducedTime k p.2) *
              A.distribution
                (-(reflectedReducedTimeDisplacementCLM k p.1) +
                  osiiPositiveRealTimeEmbed
                    (osiiMixedBlockGlobalReducedTime k p.2))
                (osiiMixedSpatialHeadMarginal χ₁ χ₂))
          (w, δ) :=
      hcutoff.mul hdistribution
    simpa only [reflectedReducedTimeDisplacementCLM_apply] using hproduct
  · have hnot :
        {σ : Fin (k + (k + 1)) → ℝ |
          σ ∉ tsupport
            (ρ : (Fin (k + (k + 1)) → ℝ) → ℂ)} ∈ 𝓝 τ :=
      (isClosed_tsupport
        (ρ : (Fin (k + (k + 1)) → ℝ) → ℂ)
        ).isOpen_compl.mem_nhds hτ
    have hmap :
        ContinuousAt
          (fun p :
            (Fin (k + k) → ℂ) ×
              (Fin ((k + 1) + (k + 1)) → ℝ) =>
            osiiMixedBlockGlobalReducedTime k p.2)
          (w, δ) :=
      (hτ_cont.comp continuous_snd).continuousAt
    have hpnot :
        {p :
          (Fin (k + k) → ℂ) ×
            (Fin ((k + 1) + (k + 1)) → ℝ) |
          osiiMixedBlockGlobalReducedTime k p.2 ∉
            tsupport
              (ρ : (Fin (k + (k + 1)) → ℝ) → ℂ)} ∈
          𝓝 (w, δ) :=
      hmap hnot
    have hzero :
        Function.uncurry
            (osiiReflectedMixedMovingKernel A ρ χ₁ χ₂) =ᶠ[𝓝 (w, δ)]
          fun _ => 0 := by
      filter_upwards [hpnot] with p hp
      have hρ : ρ (osiiMixedBlockGlobalReducedTime k p.2) = 0 :=
        image_eq_zero_of_notMem_tsupport hp
      change
        ρ (osiiMixedBlockGlobalReducedTime k p.2) *
            A.distribution
              (-(reflectedReducedTimeDisplacementCLM k p.1) +
                osiiPositiveRealTimeEmbed
                  (osiiMixedBlockGlobalReducedTime k p.2))
              (osiiMixedSpatialHeadMarginal χ₁ χ₂) =
          0
      rw [hρ, zero_mul]
    exact (continuousAt_congr hzero).2 continuousAt_const

theorem continuous_reflectedCauchyIncrement_map
    (k : ℕ) :
    Continuous
      (reflectedCauchyIncrement :
        (Fin k → ℂ) → (Fin (k + k) → ℂ)) := by
  apply continuous_pi
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [reflectedCauchyIncrement, Fin.addCases_left,
      Function.comp_apply, starRingEnd_apply] using!
      (continuous_star.comp
        (continuous_apply i :
          Continuous (fun z : Fin k → ℂ => z i)))
  · simpa only [reflectedCauchyIncrement, Fin.addCases_right] using
      (continuous_apply i :
        Continuous (fun z : Fin k → ℂ => z i))

/-- Joint continuity after inserting the Cauchy-reflected parameter and an
arbitrary fixed time center. -/
theorem continuousAt_osiiReflectedMixedMovingKernel_cauchyShift
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    {w : Fin k → ℂ}
    (hw :
      reflectedCauchyIncrement w ∈
        reflectedMovingSliceCarrier A ρ)
    (center y : Fin ((k + 1) + (k + 1)) → ℝ) :
    ContinuousAt
      (Function.uncurry fun z x =>
        osiiReflectedMixedMovingKernel A ρ χ₁ χ₂
          (reflectedCauchyIncrement z) (center + x))
      (w, y) := by
  have hkernel :=
    continuousAt_osiiReflectedMixedMovingKernel
      A ρ χ₁ χ₂ hw (center + y)
  have hinner :
      ContinuousAt
        (fun p :
          (Fin k → ℂ) ×
            (Fin ((k + 1) + (k + 1)) → ℝ) =>
          (reflectedCauchyIncrement p.1, center + p.2))
        (w, y) :=
    (((continuous_reflectedCauchyIncrement_map k).comp
        continuous_fst).prodMk
      (continuous_const.add continuous_snd)).continuousAt
  exact
    ContinuousAt.comp'
      (f := fun p :
        (Fin k → ℂ) ×
          (Fin ((k + 1) + (k + 1)) → ℝ) =>
        (reflectedCauchyIncrement p.1, center + p.2))
      (g := Function.uncurry
        (osiiReflectedMixedMovingKernel A ρ χ₁ χ₂))
      hkernel hinner

/-- Compact tensor tests times the centered mixed kernel are integrable at
every represented reflected parameter. -/
theorem integrable_tensorProduct_mul_osiiReflectedMixedMovingKernel_of_mem
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (left right : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (hleft : HasCompactSupport
      (left : (Fin (k + 1) → ℝ) → ℂ))
    (hright : HasCompactSupport
      (right : (Fin (k + 1) → ℝ) → ℂ))
    {w : Fin (k + k) → ℂ}
    (hw : w ∈ reflectedMovingSliceCarrier A ρ)
    (center : Fin ((k + 1) + (k + 1)) → ℝ) :
    Integrable
      (fun y : Fin ((k + 1) + (k + 1)) → ℝ =>
        (left.tensorProduct right) y *
          osiiReflectedMixedMovingKernel A ρ χ₁ χ₂
            w (center + y)) := by
  have hkernel :
      Continuous
        (fun y : Fin ((k + 1) + (k + 1)) → ℝ =>
          osiiReflectedMixedMovingKernel A ρ χ₁ χ₂
            w (center + y)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hjoint :=
      continuousAt_osiiReflectedMixedMovingKernel
        A ρ χ₁ χ₂ hw (center + y)
    exact
      ContinuousAt.comp'
        (f := fun x : Fin ((k + 1) + (k + 1)) → ℝ =>
          (w, center + x))
        (g := Function.uncurry
          (osiiReflectedMixedMovingKernel A ρ χ₁ χ₂))
        hjoint
        (continuous_const.prodMk
          (continuous_const.add continuous_id)).continuousAt
  have hcompact :
      HasCompactSupport
        (left.tensorProduct right :
          (Fin ((k + 1) + (k + 1)) → ℝ) → ℂ) :=
    SchwartzMap.tensorProduct_hasCompactSupport
      (k + 1) (k + 1) left right hleft hright
  exact
    ((left.tensorProduct right).continuous.mul hkernel
      ).integrable_of_hasCompactSupport hcompact.mul_right

/-- Compatibility specialization of mixed-kernel integrability to a
reflected Cauchy increment. -/
theorem integrable_tensorProduct_mul_osiiReflectedMixedMovingKernel
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (left right : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (hleft : HasCompactSupport
      (left : (Fin (k + 1) → ℝ) → ℂ))
    (hright : HasCompactSupport
      (right : (Fin (k + 1) → ℝ) → ℂ))
    {w : Fin k → ℂ}
    (hw :
      reflectedCauchyIncrement w ∈
        reflectedMovingSliceCarrier A ρ)
    (center : Fin ((k + 1) + (k + 1)) → ℝ) :
    Integrable
      (fun y : Fin ((k + 1) + (k + 1)) → ℝ =>
        (left.tensorProduct right) y *
          osiiReflectedMixedMovingKernel A ρ χ₁ χ₂
            (reflectedCauchyIncrement w) (center + y)) := by
  exact
    integrable_tensorProduct_mul_osiiReflectedMixedMovingKernel_of_mem
      A ρ χ₁ χ₂ left right hleft hright hw center

/-- Exact two-block product-smearing formula for the reflected moving-slice
scalar. -/
theorem reflectedMovingSliceScalar_mixed_timeSpatial_eq_blockGlobalIntegral
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (η₁ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (η₂ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (hη₁ : HasCompactSupport
      (η₁ : (Fin (k + 1) → ℝ) → ℂ))
    (hη₂ : HasCompactSupport
      (η₂ : (Fin (k + 1) → ℝ) → ℂ))
    (w : Fin (k + k) → ℂ)
    (hw : w ∈ reflectedMovingSliceCarrier A ρ) :
    reflectedMovingSliceScalar A ρ
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource
            (section43OrderedPullbackTimeSpatialTensorCLM
              d (k + 1) χ₁ η₁)
            (section43OrderedPullbackTimeSpatialTensorCLM
              d (k + 1) χ₂ η₂)))
        w =
      ∫ δ : Fin ((k + 1) + (k + 1)) → ℝ,
        (η₁.conj (splitFirst (k + 1) (k + 1) δ) *
            η₂ (splitLast (k + 1) (k + 1) δ)) *
          osiiReflectedMixedMovingKernel A ρ χ₁ χ₂ w δ := by
  let h :
      (k + 1) + (k + 1) =
        (k + (k + 1)) + 1 := by omega
  let χ :=
    section43SpatialSchwartzTransport d h
      (GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalSpatialPullbackCLM
        (d := d) (k + 1) (k + 1)
        (section43TwoBlockSpatialProduct χ₁ χ₂))
  let φ :=
    section43TimeSchwartzTransport h
      (osiiAxisPairGlobalTimeCutoff
        (k + 1) (k + 1) η₁.conj η₂ 0 0)
  have hφ_compact : HasCompactSupport
      (φ : (Fin ((k + (k + 1)) + 1) → ℝ) → ℂ) := by
    apply section43TimeSchwartzTransport_hasCompactSupport
    exact
      osiiAxisPairGlobalTimeCutoff_hasCompactSupport
        (k + 1) (k + 1) η₁.conj η₂
        (hasCompactSupport_schwartzMap_conj η₁ hη₁) hη₂ 0 0
  unfold reflectedMovingSliceScalar
  rw [mixedReflectedChronologicalSource_timeSpatial_normalForm]
  rw [
    osiiStageMovingSliceScalar_diffVarReduction_orderedPullback_timeSpatialTensor_eq_globalIntegral
      A ρ φ hφ_compact χ
      (-(reflectedReducedTimeDisplacementCLM k w)) hw]
  rw [← integral_comp_section43TimeTupleTransport h]
  dsimp only [φ]
  simp only [section43TimeSchwartzTransport_apply]
  rw [integral_osiiAxisPairGlobalTimeCutoff_mul]
  rfl

/-- For translated real approximate identities, the mixed moving scalar is
the tensor smearing of the common kernel about the left/right time center. -/
theorem reflectedMovingSliceScalar_translatedApproximateIdentities
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (I J : Section43ProductTimeApproximateIdentity (k + 1))
    (τ₁ τ₂ : Fin (k + 1) → ℝ)
    (hτ₁ : τ₁ ∈ section43TimeStrictPositiveRegion (k + 1))
    (hτ₂ : τ₂ ∈ section43TimeStrictPositiveRegion (k + 1))
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (p q : ℕ)
    (w : Fin (k + k) → ℂ)
    (hw : w ∈ reflectedMovingSliceCarrier A ρ) :
    reflectedMovingSliceScalar A ρ
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource
            (I.translatedPositiveTimeSpatialSource
              τ₁ hτ₁ χ₁ p).1
            (J.translatedPositiveTimeSpatialSource
              τ₂ hτ₂ χ₂ q).1))
        w =
      ∫ y : Fin ((k + 1) + (k + 1)) → ℝ,
        ((I.test p).tensorProduct (J.test q)) y *
          osiiReflectedMixedMovingKernel A ρ χ₁ χ₂ w
            (osiiMixedTimeCenter τ₁ τ₂ + y) := by
  let η₁ := SCV.translateSchwartz (-τ₁) (I.test p)
  let η₂ := SCV.translateSchwartz (-τ₂) (J.test q)
  rw [Section43ProductTimeApproximateIdentity.translatedPositiveTimeSpatialSource_coe]
  rw [Section43ProductTimeApproximateIdentity.translatedPositiveTimeSpatialSource_coe]
  rw [
    reflectedMovingSliceScalar_mixed_timeSpatial_eq_blockGlobalIntegral
      A ρ η₁ χ₁ η₂ χ₂
      (I.translatedSource τ₁ hτ₁ p).compact
      (J.translatedSource τ₂ hτ₂ q).compact w hw]
  let F : (Fin ((k + 1) + (k + 1)) → ℝ) → ℂ :=
    fun δ =>
      (η₁.conj (splitFirst (k + 1) (k + 1) δ) *
          η₂ (splitLast (k + 1) (k + 1) δ)) *
        osiiReflectedMixedMovingKernel A ρ χ₁ χ₂ w δ
  calc
    (∫ δ : Fin ((k + 1) + (k + 1)) → ℝ, F δ) =
      ∫ y : Fin ((k + 1) + (k + 1)) → ℝ,
        F (y + osiiMixedTimeCenter τ₁ τ₂) := by
          exact
            (MeasureTheory.integral_add_right_eq_self
              F (osiiMixedTimeCenter τ₁ τ₂)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      have hreal :
          starRingEnd ℂ
              (I.test p (splitFirst (k + 1) (k + 1) y)) =
            I.test p (splitFirst (k + 1) (k + 1) y) :=
        Complex.conj_eq_iff_im.mpr
          (I.real p (splitFirst (k + 1) (k + 1) y))
      have heta₁ :
          η₁.conj
              (splitFirst (k + 1) (k + 1)
                (y + osiiMixedTimeCenter τ₁ τ₂)) =
            I.test p (splitFirst (k + 1) (k + 1) y) := by
        simpa [η₁, osiiMixedTimeCenter,
          SCV.translateSchwartz_apply, SchwartzMap.conj_apply,
          add_assoc] using hreal
      have heta₂ :
          η₂
              (splitLast (k + 1) (k + 1)
                (y + osiiMixedTimeCenter τ₁ τ₂)) =
            J.test q (splitLast (k + 1) (k + 1) y) := by
        simp [η₂, osiiMixedTimeCenter,
          SCV.translateSchwartz_apply, add_assoc]
      simp only [F]
      rw [heta₁, heta₂, SchwartzMap.tensorProduct_apply]
      rw [add_comm y (osiiMixedTimeCenter τ₁ τ₂)]

/-- Independently shrinking left and right time sources recover the raw mixed
kernel at their common translated center. -/
theorem tendsto_reflectedMovingSliceScalar_translatedApproximateIdentities
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (I J : Section43ProductTimeApproximateIdentity (k + 1))
    (τ₁ τ₂ : Fin (k + 1) → ℝ)
    (hτ₁ : τ₁ ∈ section43TimeStrictPositiveRegion (k + 1))
    (hτ₂ : τ₂ ∈ section43TimeStrictPositiveRegion (k + 1))
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (w : Fin (k + k) → ℂ)
    (hw : w ∈ reflectedMovingSliceCarrier A ρ) :
    Tendsto
      (fun pq : ℕ × ℕ =>
        reflectedMovingSliceScalar A ρ
          (diffVarReduction d (k + (k + 1))
            (mixedReflectedChronologicalSource
              (I.translatedPositiveTimeSpatialSource
                τ₁ hτ₁ χ₁ pq.1).1
              (J.translatedPositiveTimeSpatialSource
                τ₂ hτ₂ χ₂ pq.2).1))
          w)
      atTop
      (𝓝 (osiiReflectedMixedMovingKernel A ρ χ₁ χ₂ w
        (osiiMixedTimeCenter τ₁ τ₂))) := by
  have hkernel :
      ContinuousAt
        (fun delta : Fin ((k + 1) + (k + 1)) → ℝ =>
          osiiReflectedMixedMovingKernel A ρ χ₁ χ₂ w delta)
        (osiiMixedTimeCenter τ₁ τ₂) := by
    exact
      ContinuousAt.comp'
        (f := fun delta : Fin ((k + 1) + (k + 1)) → ℝ =>
          (w, delta))
        (g := Function.uncurry
          (osiiReflectedMixedMovingKernel A ρ χ₁ χ₂))
        (continuousAt_osiiReflectedMixedMovingKernel
          A ρ χ₁ χ₂ hw (osiiMixedTimeCenter τ₁ τ₂))
        (continuous_const.prodMk continuous_id).continuousAt
  have hlimit :=
    tendsto_integral_tensorPair_shrinking_schwartz_approx_identities
      I.test J.test I.radius J.radius
      (fun delta => osiiReflectedMixedMovingKernel A ρ χ₁ χ₂ w delta)
      (osiiMixedTimeCenter τ₁ τ₂)
      I.nonnegative J.nonnegative I.real J.real
      I.integral_one J.integral_one I.support J.support
      I.radius_tendsto J.radius_tendsto hkernel
      (fun pq =>
        integrable_tensorProduct_mul_osiiReflectedMixedMovingKernel_of_mem
          A ρ χ₁ χ₂ (I.test pq.1) (J.test pq.2)
          (I.test_compact pq.1) (J.test_compact pq.2) hw
          (osiiMixedTimeCenter τ₁ τ₂))
  apply (tendsto_congr' ?_).2 hlimit
  exact
    Filter.Eventually.of_forall fun pq =>
      reflectedMovingSliceScalar_translatedApproximateIdentities
        A ρ I J τ₁ τ₂ hτ₁ hτ₂ χ₁ χ₂ pq.1 pq.2 w hw

end OSIIChapterV
end OSReconstruction
