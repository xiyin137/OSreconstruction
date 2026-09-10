/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSimultaneousStageLevel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialFactorExhaustion














noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- The exact predecessor-stage data for shrinking one-particle sources.

The only genuinely inductive field is `edge`; the uniform support and mixed
reduced-Schwinger germ are constructive outputs of the compact-time source
machinery. -/
structure OneParticleTranslatedMixedDeltaPredecessorData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity 1)
    (τ : Fin 1 → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion 1) where
  tailStart : ℕ
  uniformSupport :
    HasUniformCompactStrictPositiveDifferenceTimeSupport
      (fun p :
          ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ =>
        (I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + tailStart)).1)
  germ :
    UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun p :
          ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + tailStart))
  stageCutoff : SchwartzMap (Fin 1 → ℝ) ℂ
  stageCutoff_support :
    tsupport (stageCutoff : (Fin 1 → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion 1
  realRegion : Set (Fin 1 → ℝ)
  realRegion_open : IsOpen realRegion
  cutoff_support :
    tsupport (germ.η : (Fin 1 → ℝ) → ℂ) ⊆ realRegion
  edge :
    (L.stage 1).PositiveRealEdgeData
      (orderedTransportDistribution
        (canonicalReducedTimeCutoffSchwingerCLM
          OS stageCutoff stageCutoff_support))
      realRegion
  stageCutoff_one_on :
    ∀ᶠ u : Fin 0 → ℝ in 𝓝 0,
      ∀ ab :
        (ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ) ×
          (ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ),
        ∀ x ∈ tsupport
            (translateSchwartzConfiguration
              (reflectedReducedAbsoluteDisplacement (d := d) u)
              (mixedReflectedChronologicalSource
                (I.translatedPositiveTimeSpatialSource
                  τ hτ ab.1.2 (ab.1.1 + tailStart)).1
                (I.translatedPositiveTimeSpatialSource
                  τ hτ ab.2.2 (ab.2.1 + tailStart)).1) :
              NPointDomain d 2 → ℂ),
          reducedTimeCutoffWeight (d := d) stageCutoff x = 1

namespace SimultaneousTimeContinuationStageLevel

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity 1}
  {τ : Fin 1 → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion 1}

/-- The simultaneous canonical-cutoff invariant also supplies the
one-particle reflected predecessor at reduced arity one. -/
theorem exists_oneParticleTranslatedMixedDeltaPredecessorData
    (H : L.HasCanonicalReducedCompactEdges OS) :
    Nonempty
      (OneParticleTranslatedMixedDeltaPredecessorData
        L OS I τ hτ) := by
  obtain ⟨tailStart, uniformSupport⟩ :=
    I.exists_tail_translatedPositiveTimeSpatialSource_uniformCompactSupport
      (d := d) τ hτ
  let f :
      (ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ) →
        euclideanPositiveTimeSubmodule (d := d) 1 :=
    fun p =>
      I.translatedPositiveTimeSpatialSource
        τ hτ p.2 (p.1 + tailStart)
  obtain ⟨germ⟩ :=
    exists_uniformCompactTimeMixedReflectedSourceFamilyData
      OS f uniformSupport
  obtain ⟨edge⟩ :=
    H 1
      (tsupport (germ.η : (Fin 1 → ℝ) → ℂ))
      germ.η_compact germ.η_support
  exact ⟨{
    tailStart := tailStart
    uniformSupport := uniformSupport
    germ := germ
    stageCutoff := edge.cutoff
    stageCutoff_support := edge.cutoff_support
    realRegion := edge.realRegion
    realRegion_open := edge.realRegion_open
    cutoff_support := edge.compactCarrier_subset
    edge := edge.edge
    stageCutoff_one_on := by
      filter_upwards [germ.cutoff_one_on] with u hu
      intro ab x hx
      exact
        edge.reducedTimeCutoffWeight_eq_one_of_auxiliary
          germ.η Set.Subset.rfl x (hu ab x hx) }⟩

end SimultaneousTimeContinuationStageLevel

namespace OneParticleTranslatedMixedDeltaPredecessorData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity 1}
  {τ : Fin 1 → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion 1}

/-- The scale-indexed one-particle field is constant in the empty
chronological parameter. -/
noncomputable def field
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ)
    (χ : SchwartzMap (Section43SpatialSpace d 1) ℂ)
    (N : ℕ) (_ : Fin 0 → ℂ) :
    OSHilbertSpace OS :=
  osiiPositiveTimeSingleVectorCLM OS 1
    (I.translatedPositiveTimeSpatialSource
      τ hτ χ (N + D.tailStart))

/-- The common moving kernel evaluated at the one-particle delta center. -/
def centerValue
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ)
    (χ : SchwartzMap (Section43SpatialSpace d 1) ℂ)
    (w : Fin 0 → ℂ) : ℂ :=
  osiiReflectedMixedMovingKernel
    (L.stage 1) D.germ.η χ χ
    (reflectedCauchyIncrement w)
    (osiiMixedTimeCenter τ τ)

/-- The cutoff-weighted represented A0 value selected at the one-particle
delta center. -/
def centerA0Value
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ)
    (χ : SchwartzMap (Section43SpatialSpace d 1) ℂ) : ℂ :=
  let σ :=
    osiiMixedBlockGlobalReducedTime 0
      (osiiMixedTimeCenter τ τ)
  D.germ.η σ *
    D.edge.orbit σ (osiiMixedSpatialHeadMarginal χ χ)

/-- The stage edge puts the zero reflected displacement in the moving-slice
carrier. -/
theorem zero_mem_movingSliceCarrier
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ) :
    (0 : Fin 0 → ℂ) ∈
      reflectedMovingSliceCarrier (L.stage 1) D.germ.η := by
  exact
    zero_mem_reflectedMovingSliceCarrier
      (L.stage 1) D.germ.η D.realRegion D.cutoff_support
      (fun σ hσ => (D.edge.stageEdge σ hσ).1)

/-- At the empty complex increment, the common kernel center is exactly the
cutoff-weighted represented A0 real-edge value. -/
theorem centerValue_eq_centerA0Value
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ)
    (χ : SchwartzMap (Section43SpatialSpace d 1) ℂ) :
    D.centerValue χ 0 = D.centerA0Value χ := by
  let σ :=
    osiiMixedBlockGlobalReducedTime 0
      (osiiMixedTimeCenter τ τ)
  by_cases hη : D.germ.η σ = 0
  · simp [centerValue, centerA0Value,
      osiiReflectedMixedMovingKernel,
      osiiStageFixedSpatialCutoffIntegrand, σ, hη]
  · have hσ_support :
        σ ∈ tsupport (D.germ.η : (Fin 1 → ℝ) → ℂ) :=
      (subset_tsupport (D.germ.η : (Fin 1 → ℝ) → ℂ))
        (show σ ∈ Function.support
            (D.germ.η : (Fin 1 → ℝ) → ℂ) by
          exact hη)
    have hσ_region : σ ∈ D.realRegion :=
      D.cutoff_support hσ_support
    have hedge := (D.edge.stageEdge σ hσ_region).2
    simp only [centerValue, centerA0Value,
      osiiReflectedMixedMovingKernel,
      osiiStageFixedSpatialCutoffIntegrand,
      reflectedCauchyIncrement_zero, map_zero, neg_zero, zero_add]
    change
      D.germ.η σ *
          (L.stage 1).distribution
            (osiiPositiveRealTimeEmbed σ)
            (osiiMixedSpatialHeadMarginal χ χ) =
        D.germ.η σ *
          D.edge.orbit σ
            (osiiMixedSpatialHeadMarginal χ χ)
    rw [hedge]

/-- The represented moving slice at zero is the mixed Schwinger pairing for
every pair of one-particle sources in the tail family. -/
theorem reflectedMovingSliceScalar_zero_eq_schwinger
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ)
    (a b :
      ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ) :
    reflectedMovingSliceScalar
        (L.stage 1) D.germ.η
        (diffVarReduction d 1
          (mixedReflectedChronologicalSource
            (I.translatedPositiveTimeSpatialSource
              τ hτ a.2 (a.1 + D.tailStart)).1
            (I.translatedPositiveTimeSpatialSource
              τ hτ b.2 (b.1 + D.tailStart)).1))
        0 =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          ((I.translatedPositiveTimeSpatialSource
              τ hτ a.2 (a.1 + D.tailStart)).1.osConjTensorProduct
            (I.translatedPositiveTimeSpatialSource
              τ hτ b.2 (b.1 + D.tailStart)).1)) := by
  let f :=
    fun p :
        ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ =>
      I.translatedPositiveTimeSpatialSource
        τ hτ p.2 (p.1 + D.tailStart)
  let F :=
    fun ab :
        (ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ) ×
          (ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ) =>
      diffVarReduction d 1
        (mixedReflectedChronologicalSource
          (f ab.1).1 (f ab.2).1)
  let g :=
    fun ab :
        (ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ) ×
          (ℕ × SchwartzMap (Section43SpatialSpace d 1) ℂ) =>
      fun u : Fin 0 → ℝ =>
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (translateSchwartzConfiguration
              (reflectedSourceParameterDisplacementCLM
                (fun r : Fin 0 =>
                  chronologicalTimeSourceDirection (d := d) r) u)
              ((f ab.1).1.osConjTensorProduct (f ab.2).1)))
  have hedge :
      ∀ᶠ u : Fin 0 → ℝ in 𝓝 0,
        ∀ ab,
          realAffineSlice
              (reflectedMovingSliceScalar
                (L.stage 1) D.germ.η (F ab)) 0 u =
            g ab u := by
    have hstageEdge :
        ∀ᶠ u : Fin 0 → ℝ in 𝓝 0,
          ∀ ab,
            canonicalReducedTimeCutoffSchwingerCLM
                OS D.stageCutoff D.stageCutoff_support
                (translateSchwartzConfiguration
                  (osiiDifferenceTimeTranslation (d := d)
                    (reflectedReducedTimeDisplacement (k := 0) u))
                  (F ab)) =
              g ab u := by
      filter_upwards [
        eventually_mixedReflectedRawTranslation_vanishes_of_uniformCompactTimeSupport
          f D.uniformSupport,
        D.stageCutoff_one_on] with
        u hraw hone
      intro ab
      let ψ : SchwartzNPoint d 2 :=
        translateSchwartzConfiguration
          (reflectedReducedAbsoluteDisplacement (d := d) (k := 0) u)
          (mixedReflectedChronologicalSource
            (f ab.1).1 (f ab.2).1)
      have hψ :
          VanishesToInfiniteOrderOnCoincidence ψ := by
        exact
          translate_mixedReflectedChronologicalSource_vanishes_of_raw
            u (f ab.1).1 (f ab.2).1 (hraw ab)
      calc
        canonicalReducedTimeCutoffSchwingerCLM
            OS D.stageCutoff D.stageCutoff_support
            (translateSchwartzConfiguration
              (osiiDifferenceTimeTranslation (d := d)
                (reflectedReducedTimeDisplacement (k := 0) u))
              (F ab)) =
          canonicalReducedTimeCutoffSchwingerCLM
            OS D.stageCutoff D.stageCutoff_support
            (diffVarReduction d 1 ψ) := by
              rw [
                translate_diffVarReduction_reflectedReducedTimeDisplacement]
        _ = OS.S 2 ⟨ψ, hψ⟩ := by
          exact
            canonicalReducedTimeCutoffSchwingerCLM_apply_diffVarReduction_eq_of_cutoff
              OS D.stageCutoff D.stageCutoff_support ψ hψ
                (reducedTimeCutoff_smul_eq_of_one_on_tsupport
                  D.stageCutoff ψ (by simpa [ψ] using hone ab))
        _ = g ab u := by
          rw [← ZeroDiagonalSchwartz.ofClassical_of_vanishes ψ hψ]
          simpa [ψ, g] using
            mixedReflectedChronologicalSource_schwinger_eq_raw
              OS u (f ab.1).1 (f ab.2).1 (hraw ab)
    exact
      reflectedMovingSliceScalar_family_realEdge_eventually
        (L.stage 1) D.germ.η D.germ.η_compact
        (canonicalReducedTimeCutoffSchwingerCLM
          OS D.stageCutoff D.stageCutoff_support)
        D.realRegion D.realRegion_open D.cutoff_support
        D.edge.stage_continuousOn D.edge.stage_pointwiseBounded
        D.edge.stage_represents F
        (by
          intro ab
          simpa [F, f] using D.germ.cutoff ab.1 ab.2)
        g
        hstageEdge
  have hzero := (mem_of_mem_nhds hedge) (a, b)
  dsimp [F, f, g, realAffineSlice] at hzero
  have htranslate_zero
      (φ : SchwartzNPoint d 2) :
      translateSchwartzConfiguration (0 : NPointDomain d 2) φ = φ := by
    ext x
    simp
  simpa only [map_zero, zero_add, htranslate_zero] using hzero

/-- Every pairwise Gram value of the one-particle tail fields is the exact
tensor smearing of one common moving kernel. -/
theorem inner_field_eq_kernelIntegral
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ)
    (χ : SchwartzMap (Section43SpatialSpace d 1) ℂ)
    (p q : ℕ)
    (w : Fin 0 → ℂ) :
    @inner ℂ (OSHilbertSpace OS) _
        (D.field χ p w) (D.field χ q w) =
      ∫ y : Fin (1 + 1) → ℝ,
        ((I.test (p + D.tailStart)).tensorProduct
          (I.test (q + D.tailStart))) y *
          osiiReflectedMixedMovingKernel
            (L.stage 1) D.germ.η χ χ
            (reflectedCauchyIncrement w)
            (osiiMixedTimeCenter τ τ + y) := by
  have hw : w = 0 := Subsingleton.elim _ _
  subst w
  simp only [field]
  rw [osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger]
  rw [← D.reflectedMovingSliceScalar_zero_eq_schwinger
    (p, χ) (q, χ)]
  simpa only [zero_add, reflectedCauchyIncrement_zero] using
    reflectedMovingSliceScalar_translatedApproximateIdentities
      (k := 0)
      (L.stage 1) D.germ.η I I τ τ hτ hτ χ χ
      (p + D.tailStart) (q + D.tailStart) 0
      D.zero_mem_movingSliceCarrier

set_option maxHeartbeats 1200000 in
/-- The one-particle translated source fields satisfy the complete local
pairwise Gram representation contract on the unique empty-parameter domain. -/
noncomputable def toLocallyCompactTensorPairGramRepresentationData
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ)
    (χ : SchwartzMap (Section43SpatialSpace d 1) ℂ) :
    @LocallyCompactTensorPairGramRepresentationData
      0 1 (OSHilbertSpace OS) _ _
      (D.field χ) Set.univ := by
  let tail := I.toSchwartzTimeApproximateIdentity.tail D.tailStart
  exact
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
      value := D.centerValue χ
      localData := by
        intro z _
        refine
          ⟨Set.univ, univ_mem, isCompact_univ,
            1, zero_lt_one, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact fun w y =>
            osiiReflectedMixedMovingKernel
              (L.stage 1) D.germ.η χ χ
              (reflectedCauchyIncrement w) y
        · exact fun _ => osiiMixedTimeCenter τ τ
        · intro p hp
          have hp0 : p.1 = 0 := Subsingleton.elim _ _
          have hp_eq : p = (0, p.2) := Prod.ext hp0 rfl
          rw [hp_eq]
          exact
            (continuousAt_osiiReflectedMixedMovingKernel_cauchyShift
              (k := 0)
              (w := (0 : Fin 0 → ℂ))
              (L.stage 1) D.germ.η χ χ
              (by
                simpa only [reflectedCauchyIncrement_zero] using
                  D.zero_mem_movingSliceCarrier)
              (osiiMixedTimeCenter τ τ) p.2).continuousWithinAt
        · intro pq w _
          have hw : w = 0 := Subsingleton.elim _ _
          subst w
          exact
            integrable_tensorProduct_mul_osiiReflectedMixedMovingKernel
              (k := 0)
              (w := (0 : Fin 0 → ℂ))
              (L.stage 1) D.germ.η χ χ
              (I.test (pq.1 + D.tailStart))
              (I.test (pq.2 + D.tailStart))
              (I.test_compact (pq.1 + D.tailStart))
              (I.test_compact (pq.2 + D.tailStart))
              (by
                simpa only [reflectedCauchyIncrement_zero] using
                  D.zero_mem_movingSliceCarrier)
              (osiiMixedTimeCenter τ τ)
        · intro pq w _
          exact D.inner_field_eq_kernelIntegral χ pq.1 pq.2 w
        · intro w _
          rfl }

/-- At each shrinking scale, the one-particle source construction is a
continuous linear map in the spatial Schwartz profile. -/
noncomputable def fieldVectorCLM
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ)
    (N : ℕ) :
    SchwartzMap (Section43SpatialSpace d 1) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (osiiPositiveTimeSingleVectorCLM OS 1).comp
    (section43PositiveTimeSpatialSourceCLM d 1
      (I.translatedSource τ hτ (N + D.tailStart)))

@[simp]
theorem fieldVectorCLM_apply
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d 1) ℂ) :
    D.fieldVectorCLM N χ =
      osiiPositiveTimeSingleVectorCLM OS 1
        (I.translatedPositiveTimeSpatialSource
          τ hτ χ (N + D.tailStart)) :=
  rfl

end OneParticleTranslatedMixedDeltaPredecessorData

end OSIIChapterV
end OSReconstruction
