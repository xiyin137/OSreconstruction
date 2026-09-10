/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedCarrierCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedAnchoredCoherence
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformCompactTimeAnchoredSeed

noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The scalar-stage point obtained by pairing the zero Hilbert anchor with
one variable mixed point and translating by the cutoff parameter. -/
def zeroAnchorShiftedStagePoint
    {m : ℕ}
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ) :
    Fin (m + (m + 1)) → ℂ :=
  -(reflectedReducedTimeDisplacementCLM m
      (reflectedAnchorPair (0 : Fin m → ℂ) z)) +
    osiiPositiveRealTimeEmbed τ

@[simp]
theorem zeroAnchorShiftedStagePoint_left
    {m : ℕ}
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ)
    (i : Fin m) :
    zeroAnchorShiftedStagePoint τ z
        (Fin.castAdd (m + 1) i) =
      τ (Fin.castAdd (m + 1) i) := by
  simp [zeroAnchorShiftedStagePoint,
    reflectedReducedTimeDisplacementCLM_apply,
    reflectedReducedTimeDisplacement_left,
    reflectedAnchorPair, osiiPositiveRealTimeEmbed]

@[simp]
theorem zeroAnchorShiftedStagePoint_bridge
    {m : ℕ}
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ) :
    zeroAnchorShiftedStagePoint τ z
        (Fin.natAdd m (0 : Fin (m + 1))) =
      τ (Fin.natAdd m (0 : Fin (m + 1))) := by
  simp [zeroAnchorShiftedStagePoint,
    reflectedReducedTimeDisplacementCLM_apply,
    reflectedReducedTimeDisplacement_bridge,
    osiiPositiveRealTimeEmbed]

@[simp]
theorem zeroAnchorShiftedStagePoint_right
    {m : ℕ}
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ)
    (i : Fin m) :
    zeroAnchorShiftedStagePoint τ z
        (Fin.natAdd m i.succ) =
      z i + τ (Fin.natAdd m i.succ) := by
  rw [zeroAnchorShiftedStagePoint]
  simp only [Pi.add_apply, Pi.neg_apply,
    reflectedReducedTimeDisplacementCLM_apply,
    reflectedReducedTimeDisplacement_right, neg_neg,
    osiiPositiveRealTimeEmbed]
  rw [reflectedAnchorPair, Fin.append_right]

theorem zeroAnchorShiftedStagePoint_mem_rightHalfPlane
    {m : ℕ}
    {τ : Fin (m + (m + 1)) → ℝ}
    {z : Fin m → ℂ}
    (hτ :
      τ ∈ section43TimeStrictPositiveRegion (m + (m + 1)))
    (hz : z ∈ osiiTimeRightHalfPlane m) :
    zeroAnchorShiftedStagePoint τ z ∈
      osiiTimeRightHalfPlane (m + (m + 1)) := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [zeroAnchorShiftedStagePoint_left]
    simpa using hτ (Fin.castAdd (m + 1) i)
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · rw [zeroAnchorShiftedStagePoint_bridge]
      simpa using hτ (Fin.natAdd m (0 : Fin (m + 1)))
    · rw [zeroAnchorShiftedStagePoint_right]
      simpa using add_pos (hz i) (hτ (Fin.natAdd m i.succ))

theorem abs_argumentVector_zeroAnchorShiftedStagePoint_le
    {m : ℕ}
    {τ : Fin (m + (m + 1)) → ℝ}
    {z : Fin m → ℂ}
    (hτ :
      τ ∈ section43TimeStrictPositiveRegion (m + (m + 1)))
    (hz : z ∈ osiiTimeRightHalfPlane m) :
    ∀ j,
      |osiiTimeArgumentVector
          (zeroAnchorShiftedStagePoint τ z) j| ≤
        |reflectedMixedDiagonal z j| := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedMixedDiagonal_left]
    simp only [osiiTimeArgumentVector,
      zeroAnchorShiftedStagePoint_left, abs_neg]
    rw [Complex.arg_ofReal_of_nonneg
      (hτ (Fin.castAdd (m + 1) i)).le]
    simp
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · rw [reflectedMixedDiagonal_bridge]
      simp only [osiiTimeArgumentVector,
        zeroAnchorShiftedStagePoint_bridge, abs_zero]
      rw [Complex.arg_ofReal_of_nonneg
        (hτ (Fin.natAdd m (0 : Fin (m + 1)))).le]
      simp
    · rw [reflectedMixedDiagonal_right]
      simp only [osiiTimeArgumentVector,
        zeroAnchorShiftedStagePoint_right]
      exact
        abs_arg_add_ofReal_le
          (hz i) (hτ (Fin.natAdd m i.succ)).le

/-- Every generated mixed point keeps its zero-anchor pairing inside the
same reflected moving-slice scalar carrier. -/
theorem zeroAnchorPair_mem_reflectedMovingSliceCarrier_of_generated
    {d m N : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (η : SchwartzMap (Fin (m + (m + 1)) → ℝ) ℂ)
    (hη_support :
      tsupport
          (η : (Fin (m + (m + 1)) → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase (m + (m + 1)) N) ⊆
        A.carrier)
    {z : Fin m → ℂ}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase (m + 1) N)) :
    reflectedAnchorPair (0 : Fin m → ℂ) z ∈
      reflectedMovingSliceCarrier A η := by
  intro τ hτ
  change zeroAnchorShiftedStagePoint τ z ∈ A.carrier
  apply hgenerated
  have hτpos := hη_support hτ
  refine
    ⟨zeroAnchorShiftedStagePoint_mem_rightHalfPlane
        hτpos hz.1,
      ?_⟩
  apply
    OSIIGeneratedLogarithmicArgument.scalar_hyperrectangle
      (reflectedMixedDiagonal_generated
        (by simpa [reflectedMixedArgument] using hz.2))
  exact
    abs_argumentVector_zeroAnchorShiftedStagePoint_le
      hτpos hz.1

/-- Generated-base realization propagates zero-anchor scalar-domain
membership over the full radial continuation segment. -/
theorem zeroAnchorPair_segment_subset_reflectedMovingSliceCarrier_of_generated
    {d m N : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (η : SchwartzMap (Fin (m + (m + 1)) → ℝ) ℂ)
    (hη_support :
      tsupport
          (η : (Fin (m + (m + 1)) → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase (m + (m + 1)) N) ⊆
        A.carrier)
    {z : Fin m → ℂ}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase (m + 1) N)) :
    ∀ center ∈ segment ℝ (0 : Fin m → ℂ) z,
      reflectedAnchorPair (0 : Fin m → ℂ) center ∈
        reflectedMovingSliceCarrier A η := by
  intro center hcenter
  rw [segment_eq_image_lineMap] at hcenter
  obtain ⟨t, ht, rfl⟩ := hcenter
  by_cases ht0 : t = 0
  · subst t
    have hzero :
        reflectedAnchorPair
            (0 : Fin m → ℂ) (0 : Fin m → ℂ) =
          (0 : Fin (m + m) → ℂ) := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [reflectedAnchorPair]
      · rw [reflectedAnchorPair, Fin.append_right]
        rfl
    rw [AffineMap.lineMap_apply_zero, hzero]
    exact
      zero_mem_reflectedMovingSliceCarrier_of_generated
        A η hη_support hgenerated
  · apply
      zeroAnchorPair_mem_reflectedMovingSliceCarrier_of_generated
        A η hη_support hgenerated
    simpa [AffineMap.lineMap_apply_module] using
      real_smul_mem_osiiMixedTailArgumentCarrier_of_pos
        hz (lt_of_le_of_ne ht.1 (Ne.symm ht0))

namespace SourceIndexedAnchoredReflectedGramContinuationChain

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {ι : Type*} {k : ℕ}
  {scalar :
    ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ}
  {anchorPoint : Fin (k + 1) → ℂ}
  {anchorField : ι → H}
  {P : SourceIndexedReflectedGramHilbertFieldData
    H ι (k + 1) scalar}

/-- A variable point in an open Hilbert polydisc maps into the corresponding
closed scalar polydisc around its fixed-anchor pairing. -/
theorem reflectedAnchorPair_mem_closedPolydisc
    {center z : Fin (k + 1) → ℂ}
    {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hz : z ∈ SCV.Polydisc center (fun _ => radius)) :
    reflectedAnchorPair anchorPoint z ∈
      SCV.closedPolydisc
        (reflectedAnchorPair anchorPoint center)
        (fun _ => radius) := by
  rw [SCV.mem_closedPolydisc_iff]
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp [reflectedAnchorPair, hradius]
  · intro i
    rw [reflectedAnchorPair, reflectedAnchorPair,
      Fin.append_right, Fin.append_right]
    exact le_of_lt ((SCV.mem_polydisc_iff.mp hz) i)

omit [CompleteSpace H] in
/-- The fixed-anchor pairing of a compact Hilbert segment has a uniform
closed-polydisc neighborhood inside the retained scalar domain. -/
theorem exists_uniform_anchorPair_closedPolydisc_along_segment
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar)
    (anchorPoint : Fin (k + 1) → ℂ)
    {start target : Fin (k + 1) → ℂ}
    (hanchor :
      ∀ center ∈ segment ℝ start target,
        reflectedAnchorPair anchorPoint center ∈ P.scalarDomain) :
    ∃ radius > 0,
      ∀ center ∈ segment ℝ start target,
        SCV.closedPolydisc
            (reflectedAnchorPair anchorPoint center)
            (fun _ => radius) ⊆
          P.scalarDomain := by
  have hsegment :
      IsCompact (segment ℝ start target) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hanchor_continuous :
      Continuous
        (fun z : Fin (k + 1) → ℂ =>
          reflectedAnchorPair anchorPoint z) := by
    apply continuous_pi
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [reflectedAnchorPair, Fin.append_left]
      fun_prop
    · intro i
      simp only [reflectedAnchorPair, Fin.append_right]
      fun_prop
  let K : Set (Fin ((k + 1) + (k + 1)) → ℂ) :=
    (fun z => reflectedAnchorPair anchorPoint z) ''
      segment ℝ start target
  have hK_compact : IsCompact K :=
    hsegment.image hanchor_continuous
  have hK_subset : K ⊆ P.scalarDomain := by
    rintro _ ⟨center, hcenter, rfl⟩
    exact hanchor center hcenter
  obtain ⟨radius, hradius, huniform⟩ :=
    SourceIndexedComplexCenteredHilbertCauchyData.exists_uniform_closedPolydisc_subset_open
      hK_compact P.scalarDomain_open hK_subset
  refine ⟨radius, hradius, ?_⟩
  intro center hcenter
  exact huniform _ ⟨center, hcenter, rfl⟩

/-- A waypoint chain can be continued while retaining the fixed-anchor
coherence contract at every stage. -/
theorem exists_chain_of_waypoints
    (A₀ : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar anchorPoint anchorField P)
    (radius : ℝ)
    (hradius : 0 < radius)
    (points : List (Fin (k + 1) → ℂ))
    (hne : points ≠ [])
    (hfirst : points.head hne ∈ P.domain)
    (hreflected :
      ∀ center ∈ points,
        SCV.closedPolydisc
            (reflectedCauchyCenter center)
            (fun _ => radius) ⊆
          P.scalarDomain)
    (hanchor :
      ∀ center ∈ points,
        SCV.closedPolydisc
            (reflectedAnchorPair anchorPoint center)
            (fun _ => radius) ⊆
          P.scalarDomain)
    (hchain :
      points.IsChain (fun center next =>
        next ∈ SCV.Polydisc center (fun _ => radius))) :
    ∃ C : SourceIndexedReflectedGramContinuationChain
        H ι k scalar P points.length.pred,
      ∃ _Aterminal :
          SourceIndexedAnchoredReflectedGramHilbertFieldData
            scalar anchorPoint anchorField C.terminal,
        points.getLast hne ∈ C.terminal.domain := by
  induction points generalizing P with
  | nil =>
      exact (hne rfl).elim
  | cons first rest ih =>
      cases rest with
      | nil =>
          refine
            ⟨SourceIndexedReflectedGramContinuationChain.nil P,
              A₀, ?_⟩
          simpa using hfirst
      | cons next tail =>
          have hnext :
              next ∈
                SCV.Polydisc first (fun _ => radius) :=
            (List.isChain_cons_cons.mp hchain).1
          have htail :
              (next :: tail).IsChain (fun center next =>
                next ∈ SCV.Polydisc center (fun _ => radius)) :=
            (List.isChain_cons_cons.mp hchain).2
          have hfirst_mem : first ∈ P.domain := by
            simpa using hfirst
          have hfirst_reflected :
              SCV.closedPolydisc
                  (reflectedCauchyCenter first)
                  (fun _ => radius) ⊆
                P.scalarDomain :=
            hreflected first (by simp)
          have hfirst_anchor :
              SCV.closedPolydisc
                  (reflectedAnchorPair anchorPoint first)
                  (fun _ => radius) ⊆
                P.scalarDomain :=
            hanchor first (by simp)
          obtain ⟨stepData, hstepCenter, hstepRadius⟩ :=
            SourceIndexedComplexCenteredHilbertCauchyData.exists_at_with_scalarRadius
              P first hfirst_mem radius hradius hfirst_reflected
          have hnext_mem : next ∈ stepData.toSuccessor.domain := by
            simpa [
              SourceIndexedComplexCenteredHilbertCauchyData.successorDomain,
              hstepCenter, hstepRadius]
              using hnext
          have hstep_anchor :
              ∀ z ∈ stepData.successorDomain,
                reflectedAnchorPair anchorPoint z ∈
                  P.scalarDomain := by
            intro z hz
            apply hfirst_anchor
            apply reflectedAnchorPair_mem_closedPolydisc hradius.le
            simpa [
              SourceIndexedComplexCenteredHilbertCauchyData.successorDomain,
              hstepCenter, hstepRadius] using hz
          let A₁ := A₀.toSuccessor stepData hstep_anchor
          have hreflected_tail :
              ∀ center ∈ next :: tail,
                SCV.closedPolydisc
                    (reflectedCauchyCenter center)
                    (fun _ => radius) ⊆
                  stepData.toSuccessor.scalarDomain := by
            intro center hcenter
            rw [stepData.toSuccessor_scalarDomain]
            exact hreflected center (by simp [hcenter])
          have hanchor_tail :
              ∀ center ∈ next :: tail,
                SCV.closedPolydisc
                    (reflectedAnchorPair anchorPoint center)
                    (fun _ => radius) ⊆
                  stepData.toSuccessor.scalarDomain := by
            intro center hcenter
            rw [stepData.toSuccessor_scalarDomain]
            exact hanchor center (by simp [hcenter])
          obtain ⟨C, Aterminal, hlast⟩ :=
            ih A₁
              (by simp)
              (by simpa using hnext_mem)
              hreflected_tail hanchor_tail htail
          refine
            ⟨SourceIndexedReflectedGramContinuationChain.cons
                stepData C,
              Aterminal,
              ?_⟩
          simpa using hlast

/-- Finite straight-segment continuation for one already selected common
scalar radius.

Keeping the radius selection outside this lemma lets later quantitative
callers intersect the scalar-domain radius with chart and boundary-margin
radii before constructing the chain. -/
theorem exists_chain_reaching_of_segment_with_radius
    (A₀ : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar anchorPoint anchorField P)
    {start target : Fin (k + 1) → ℂ}
    (radius : ℝ)
    (hradius : 0 < radius)
    (hstart : start ∈ P.domain)
    (hreflected :
      ∀ center ∈ segment ℝ start target,
        SCV.closedPolydisc
            (reflectedCauchyCenter center)
            (fun _ => radius) ⊆
          P.scalarDomain)
    (hanchor :
      ∀ center ∈ segment ℝ start target,
        SCV.closedPolydisc
            (reflectedAnchorPair anchorPoint center)
            (fun _ => radius) ⊆
          P.scalarDomain) :
    ∃ n : ℕ,
      ∃ C : SourceIndexedReflectedGramContinuationChain
          H ι k scalar P n,
        ∃ _Aterminal :
            SourceIndexedAnchoredReflectedGramHilbertFieldData
              scalar anchorPoint anchorField C.terminal,
          target ∈ C.terminal.domain := by
  obtain ⟨steps, hsteps, hmesh⟩ :=
    SourceIndexedReflectedGramContinuationChain.exists_segmentSubdivision_mesh_lt
      start target radius hradius
  let points :=
    SourceIndexedReflectedGramContinuationChain.segmentSubdivision
      start target steps
  have hpoints_ne : points ≠ [] := by
    exact
      SourceIndexedReflectedGramContinuationChain.segmentSubdivision_ne_nil
        start target steps
  have hpoints_first : points.head hpoints_ne ∈ P.domain := by
    simpa [points] using hstart
  have hpoints_reflected :
      ∀ center ∈ points,
        SCV.closedPolydisc
            (reflectedCauchyCenter center)
            (fun _ => radius) ⊆
          P.scalarDomain := by
    intro center hcenter
    exact
      hreflected center
        (SourceIndexedReflectedGramContinuationChain.mem_segment_of_mem_segmentSubdivision
          start target steps hsteps hcenter)
  have hpoints_anchor :
      ∀ center ∈ points,
        SCV.closedPolydisc
            (reflectedAnchorPair anchorPoint center)
            (fun _ => radius) ⊆
          P.scalarDomain := by
    intro center hcenter
    exact
      hanchor center
        (SourceIndexedReflectedGramContinuationChain.mem_segment_of_mem_segmentSubdivision
          start target steps hsteps hcenter)
  have hpoints_chain :
      points.IsChain (fun center next =>
        next ∈ SCV.Polydisc center (fun _ => radius)) := by
    exact
      SourceIndexedReflectedGramContinuationChain.segmentSubdivision_isChain
        start target steps hsteps radius hmesh
  obtain ⟨C, Aterminal, hlast⟩ :=
    exists_chain_of_waypoints A₀ radius hradius points
      hpoints_ne hpoints_first hpoints_reflected
      hpoints_anchor hpoints_chain
  refine ⟨points.length.pred, C, Aterminal, ?_⟩
  have hlast_eq :
      points.getLast hpoints_ne = target := by
    simpa [points] using
      SourceIndexedReflectedGramContinuationChain.segmentSubdivision_getLast
        start target steps hsteps
  rwa [hlast_eq] at hlast

/-- Finite straight-segment continuation with simultaneous reflected-center
and fixed-anchor scalar-domain control. -/
theorem exists_chain_reaching_of_segment_subsets_scalarDomain
    (A₀ : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar anchorPoint anchorField P)
    {start target : Fin (k + 1) → ℂ}
    (hstart : start ∈ P.domain)
    (hreflected :
      ∀ center ∈ segment ℝ start target,
        reflectedCauchyCenter center ∈ P.scalarDomain)
    (hanchor :
      ∀ center ∈ segment ℝ start target,
        reflectedAnchorPair anchorPoint center ∈ P.scalarDomain) :
    ∃ n : ℕ,
      ∃ C : SourceIndexedReflectedGramContinuationChain
          H ι k scalar P n,
        ∃ _Aterminal :
            SourceIndexedAnchoredReflectedGramHilbertFieldData
              scalar anchorPoint anchorField C.terminal,
          target ∈ C.terminal.domain := by
  obtain ⟨reflectedRadius, hreflectedRadius, hreflectedUniform⟩ :=
    SourceIndexedComplexCenteredHilbertCauchyData.exists_uniform_reflected_closedPolydisc_along_segment
      P hreflected
  obtain ⟨anchorRadius, hanchorRadius, hanchorUniform⟩ :=
    exists_uniform_anchorPair_closedPolydisc_along_segment
      P anchorPoint hanchor
  let radius := min reflectedRadius anchorRadius
  have hradius : 0 < radius := by
    exact lt_min hreflectedRadius hanchorRadius
  apply exists_chain_reaching_of_segment_with_radius
    A₀ radius hradius hstart
  · intro center hcenter w hw
    apply hreflectedUniform center hcenter
    exact
      SCV.closedPolydisc_mono
        (fun _ => min_le_left reflectedRadius anchorRadius) hw
  · intro center hcenter w hw
    apply hanchorUniform center hcenter
    exact
      SCV.closedPolydisc_mono
        (fun _ => min_le_right reflectedRadius anchorRadius) hw

end SourceIndexedAnchoredReflectedGramContinuationChain

/-- An anchored reflected-Gram field whose scalar domain is the moving-slice
carrier reaches every generated mixed point through an anchored chain. -/
theorem exists_anchored_chain_reaching_generatedMixedCarrier
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {ι : Type*} {k N : ℕ}
    {scalar :
      ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ}
    {anchorField : ι → H}
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar)
    (A₀ : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar (0 : Fin (k + 1) → ℂ) anchorField P)
    {d : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d
      ((k + 1) + ((k + 1) + 1)))
    (η : SchwartzMap
      (Fin ((k + 1) + ((k + 1) + 1)) → ℝ) ℂ)
    (hη_support :
      tsupport
          (η :
            (Fin ((k + 1) + ((k + 1) + 1)) → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion
          ((k + 1) + ((k + 1) + 1)))
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((k + 1) + ((k + 1) + 1)) N) ⊆
        A.carrier)
    (hscalarDomain :
      P.scalarDomain = reflectedMovingSliceCarrier A η)
    (hzero : (0 : Fin (k + 1) → ℂ) ∈ P.domain)
    {z : Fin (k + 1) → ℂ}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase ((k + 1) + 1) N)) :
    ∃ n : ℕ,
      ∃ C : SourceIndexedReflectedGramContinuationChain
          H ι k scalar P n,
        ∃ _Aterminal :
            SourceIndexedAnchoredReflectedGramHilbertFieldData
              scalar (0 : Fin (k + 1) → ℂ)
              anchorField C.terminal,
          z ∈ C.terminal.domain := by
  apply
    SourceIndexedAnchoredReflectedGramContinuationChain.exists_chain_reaching_of_segment_subsets_scalarDomain
      A₀ hzero
  · intro center hcenter
    rw [hscalarDomain]
    exact
      reflected_segment_subset_reflectedMovingSliceCarrier_of_generated
        A η hη_support hgenerated hz center hcenter
  · intro center hcenter
    rw [hscalarDomain]
    exact
      zeroAnchorPair_segment_subset_reflectedMovingSliceCarrier_of_generated
        A η hη_support hgenerated hz center hcenter

namespace UniformCompactTimeMixedHilbertGramFamilyData

variable {d q N : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {K : Set (Fin ((q + 1) + 1) → ℝ)}

end UniformCompactTimeMixedHilbertGramFamilyData

end OSIIChapterV
end OSReconstruction
