/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedOpenBase
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVPointedStageLevel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumTailTargetHubPointedExtension












noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Every reflected Cauchy point over the compact target-and-hub box stays
in the same ranked scalar argument carrier as the original mixed target. -/
theorem
    reflectedCauchyShiftedStagePoint_targetHubBox_mem_argumentCarrier_of_strictGeneratedAtRank
    {m N rank : Nat}
    {anchor hub : Fin (m + 1) -> Real}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hhub : forall i, anchor i <= hub i)
    {tau : Fin (m + (m + 1)) -> Real}
    (htau : ReflectedTimeDominatesTailAnchor anchor tau)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank))
    {u v : Real}
    (hu : u ∈ Set.Icc (0 : Real) 1)
    (hv : v ∈ Set.Icc (0 : Real) 1) :
    reflectedCauchyShiftedStagePoint tau
        (tailAnchorTargetHubBoxPoint anchor hub z u v) ∈
      osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          (m + (m + 1)) N rank) := by
  refine
    ⟨reflectedCauchyShiftedStagePoint_targetHubBox_mem_rightHalfPlane
        hanchor hhub htau hz.1 hu hv,
      ?_⟩
  apply
    OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_hyperrectangle
      (reflectedMixedDiagonal_strictGeneratedAtRank
        (by simpa [reflectedMixedArgument] using hz.2))
  exact
    abs_argumentVector_reflectedCauchyShiftedStagePoint_targetHubBox_le
      hanchor hhub htau hz.1 hu hv

/-- Every zero-anchor point over the same target-and-hub box stays in the
same ranked scalar argument carrier. -/
theorem
    zeroAnchorShiftedStagePoint_targetHubBox_mem_argumentCarrier_of_strictGeneratedAtRank
    {m N rank : Nat}
    {anchor hub : Fin (m + 1) -> Real}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hhub : forall i, anchor i <= hub i)
    {tau : Fin (m + (m + 1)) -> Real}
    (htau : ReflectedTimeDominatesTailAnchor anchor tau)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank))
    {u v : Real}
    (hu : u ∈ Set.Icc (0 : Real) 1)
    (hv : v ∈ Set.Icc (0 : Real) 1) :
    zeroAnchorShiftedStagePoint tau
        (tailAnchorTargetHubBoxPoint anchor hub z u v) ∈
      osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          (m + (m + 1)) N rank) := by
  refine
    ⟨zeroAnchorShiftedStagePoint_targetHubBox_mem_rightHalfPlane
        hanchor hhub htau hz.1 hu hv,
      ?_⟩
  apply
    OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_hyperrectangle
      (reflectedMixedDiagonal_strictGeneratedAtRank
        (by simpa [reflectedMixedArgument] using hz.2))
  exact
    abs_argumentVector_zeroAnchorShiftedStagePoint_targetHubBox_le
      hanchor hhub htau hz.1 hu hv

/-- An open cutoff-time neighborhood whose complete reflected target-hub box
stays inside one argument carrier.

Unlike the stage-region witness, this remembers the actual argument carrier
rather than only a surrounding continuation stage.  That distinction is what
later makes a compact unshifted orbit stable under a small normalization
shift. -/
structure TailAnchorTargetHubBoxReflectedArgumentRegionData
    {m : Nat}
    (base : Set (Fin (m + (m + 1)) -> Real))
    (anchor hub : Fin (m + 1) -> Real)
    (z : Fin m -> Complex)
    (J : Set (Fin (m + (m + 1)) -> Real)) where
  region : Set (Fin (m + (m + 1)) -> Real)
  region_open : IsOpen region
  compactCarrier_subset : J ⊆ region
  region_positive :
    region ⊆ section43TimeStrictPositiveRegion (m + (m + 1))
  reflectedCauchy_box_mem :
    forall tau, tau ∈ region ->
      forall u, u ∈ Set.Icc (0 : Real) 1 ->
        forall v, v ∈ Set.Icc (0 : Real) 1 ->
          reflectedCauchyShiftedStagePoint tau
              (tailAnchorTargetHubBoxPoint anchor hub z u v) ∈
            osiiTimeArgumentCarrier base
  zeroAnchor_box_mem :
    forall tau, tau ∈ region ->
      forall u, u ∈ Set.Icc (0 : Real) 1 ->
        forall v, v ∈ Set.Icc (0 : Real) 1 ->
          zeroAnchorShiftedStagePoint tau
              (tailAnchorTargetHubBoxPoint anchor hub z u v) ∈
            osiiTimeArgumentCarrier base

set_option maxHeartbeats 800000 in
/-- A next-depth, next-rank mixed target has a compactly uniform open
reflected target-hub neighborhood inside the matching open scalar carrier.

The source compact carrier only needs weak anchor domination.  The selected
open neighborhood may extend below that anchor; its point is instead that
the whole reflected box remains in the genuine successor argument carrier. -/
theorem
    nonempty_tailAnchorTargetHubBoxReflectedArgumentRegionData_of_rankSuccessor
    {m depth rank : Nat}
    {anchor hub : Fin (m + 1) -> Real}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hhub : forall i, anchor i <= hub i)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) (depth + 1) (rank + 1)))
    (J : Set (Fin (m + (m + 1)) -> Real))
    (hJ_compact : IsCompact J)
    (hJ_dominates :
      forall tau, tau ∈ J ->
        ReflectedTimeDominatesTailAnchor anchor tau) :
    Nonempty
      (TailAnchorTargetHubBoxReflectedArgumentRegionData
        (osiiStrictGeneratedLogarithmicBaseAtRank
          (m + (m + 1)) (depth + 1) (rank + 1))
        anchor hub z J) := by
  let good :
      Set (((Fin (m + (m + 1)) -> Real) × (Real × Real))) :=
    {p |
      reflectedCauchyTailAnchorTargetHubBoxStageMap anchor hub z p ∈
        osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) (depth + 1) (rank + 1)) ∧
      zeroAnchorTailAnchorTargetHubBoxStageMap anchor hub z p ∈
        osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) (depth + 1) (rank + 1))}
  have hgood_open : IsOpen good := by
    exact
      ((isOpen_rankSuccessorTimeArgumentCarrier
          rank (m + (m + 1)) depth).preimage
        (continuous_reflectedCauchyTailAnchorTargetHubBoxStageMap
          anchor hub z)).inter
      ((isOpen_rankSuccessorTimeArgumentCarrier
          rank (m + (m + 1)) depth).preimage
        (continuous_zeroAnchorTailAnchorTargetHubBoxStageMap
          anchor hub z))
  have hproduct :
      J ×ˢ
          (Set.Icc (0 : Real) 1 ×ˢ Set.Icc (0 : Real) 1) ⊆
        good := by
    rintro ⟨tau, u, v⟩ ⟨htauJ, hu, hv⟩
    exact
      ⟨reflectedCauchyShiftedStagePoint_targetHubBox_mem_argumentCarrier_of_strictGeneratedAtRank
          hanchor hhub (hJ_dominates tau htauJ) hz hu hv,
        zeroAnchorShiftedStagePoint_targetHubBox_mem_argumentCarrier_of_strictGeneratedAtRank
          hanchor hhub (hJ_dominates tau htauJ) hz hu hv⟩
  obtain ⟨W, V, hW_open, _hV_open, hJW, hboxV, hWV⟩ :=
    generalized_tube_lemma
      (X := Fin (m + (m + 1)) -> Real) (Y := Real × Real)
      hJ_compact
      ((isCompact_Icc : IsCompact (Set.Icc (0 : Real) 1)).prod
        (isCompact_Icc : IsCompact (Set.Icc (0 : Real) 1)))
      hgood_open hproduct
  let U :=
    W ∩ section43TimeStrictPositiveRegion (m + (m + 1))
  refine ⟨{
    region := U
    region_open :=
      hW_open.inter
        (isOpen_section43TimeStrictPositiveRegion
          (m + (m + 1)))
    compactCarrier_subset := ?_
    region_positive := ?_
    reflectedCauchy_box_mem := ?_
    zeroAnchor_box_mem := ?_ }⟩
  · intro tau htau
    exact
      ⟨hJW htau,
        (hJ_dominates tau htau).strictPositive hanchor⟩
  · exact inter_subset_right
  · intro tau htau u hu v hv
    have hpair :
        (tau, (u, v)) ∈ W ×ˢ V :=
      ⟨htau.1, hboxV ⟨hu, hv⟩⟩
    have hgood : (tau, (u, v)) ∈ good := hWV hpair
    exact hgood.1
  · intro tau htau u hu v hv
    have hpair :
        (tau, (u, v)) ∈ W ×ˢ V :=
      ⟨htau.1, hboxV ⟨hu, hv⟩⟩
    have hgood : (tau, (u, v)) ∈ good := hWV hpair
    exact hgood.2

/-- Radial points over the centered hub-to-target segment stay in the same
ranked scalar argument carrier.

The centered tail itself need not lie in the original mixed carrier:
subtracting the positive anchor can enlarge its principal arguments.  What
the reflected Gram estimate actually uses is weaker and true: after radial
contraction, every point on that segment is a point of the target-and-hub
box, so the ranked box estimate applies directly. -/
theorem
    reflectedCauchyShiftedStagePoint_targetHubSegment_mem_argumentCarrier_of_strictGeneratedAtRank
    {m N rank : Nat}
    {anchor hub : Fin (m + 1) -> Real}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hhub : forall i, anchor i <= hub i)
    {tau : Fin (m + (m + 1)) -> Real}
    (htau : ReflectedTimeDominatesTailAnchor anchor tau)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank))
    {w : Fin m -> Complex}
    (hw :
      w ∈ segment Real
        (tailAnchorCenteredHubPoint anchor hub)
        (tailAnchorCenteredPoint anchor z))
    {r : Real}
    (hr : r ∈ Set.Icc (0 : Real) 1) :
    reflectedCauchyShiftedStagePoint tau (r • w) ∈
      osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          (m + (m + 1)) N rank) := by
  rw [segment_eq_image_lineMap] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  let u : Real := r * (1 - s)
  let v : Real := r * s
  have hu : u ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · exact mul_nonneg hr.1 (sub_nonneg.mpr hs.2)
    · calc
        u = r * (1 - s) := rfl
        _ <= r * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [hs.1]) hr.1
        _ = r := mul_one r
        _ <= 1 := hr.2
  have hv : v ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · exact mul_nonneg hr.1 hs.1
    · calc
        v = r * s := rfl
        _ <= r * 1 := mul_le_mul_of_nonneg_left hs.2 hr.1
        _ = r := mul_one r
        _ <= 1 := hr.2
  have hbox :
      r • AffineMap.lineMap (k := Real)
          (tailAnchorCenteredHubPoint anchor hub)
          (tailAnchorCenteredPoint anchor z) s =
        tailAnchorTargetHubBoxPoint anchor hub z u v := by
    ext j
    simp [AffineMap.lineMap_apply_module,
      tailAnchorTargetHubBoxPoint, u, v]
    ring
  rw [hbox]
  exact
    reflectedCauchyShiftedStagePoint_targetHubBox_mem_argumentCarrier_of_strictGeneratedAtRank
      hanchor hhub htau hz hu hv

/-- Rank-`rank` scalar realization contains every reflected Cauchy point
over the compact target-and-hub box of a rank-`rank` mixed target. -/
theorem
    reflectedCauchyShiftedStagePoint_targetHubBox_mem_of_strictGeneratedAtRank
    {d m N rank : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) N rank) ⊆
        A.carrier)
    {anchor hub : Fin (m + 1) -> Real}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hhub : forall i, anchor i <= hub i)
    {tau : Fin (m + (m + 1)) -> Real}
    (htau : ReflectedTimeDominatesTailAnchor anchor tau)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank))
    {u v : Real}
    (hu : u ∈ Set.Icc (0 : Real) 1)
    (hv : v ∈ Set.Icc (0 : Real) 1) :
    reflectedCauchyShiftedStagePoint tau
        (tailAnchorTargetHubBoxPoint anchor hub z u v) ∈
      A.carrier := by
  exact
    hscalar
      (reflectedCauchyShiftedStagePoint_targetHubBox_mem_argumentCarrier_of_strictGeneratedAtRank
        hanchor hhub htau hz hu hv)

/-- Rank-`rank` scalar realization also contains every zero-anchor point over
the complete target-and-hub box. -/
theorem
    zeroAnchorShiftedStagePoint_targetHubBox_mem_of_strictGeneratedAtRank
    {d m N rank : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) N rank) ⊆
        A.carrier)
    {anchor hub : Fin (m + 1) -> Real}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hhub : forall i, anchor i <= hub i)
    {tau : Fin (m + (m + 1)) -> Real}
    (htau : ReflectedTimeDominatesTailAnchor anchor tau)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank))
    {u v : Real}
    (hu : u ∈ Set.Icc (0 : Real) 1)
    (hv : v ∈ Set.Icc (0 : Real) 1) :
    zeroAnchorShiftedStagePoint tau
        (tailAnchorTargetHubBoxPoint anchor hub z u v) ∈
      A.carrier := by
  exact
    hscalar
      (zeroAnchorShiftedStagePoint_targetHubBox_mem_argumentCarrier_of_strictGeneratedAtRank
        hanchor hhub htau hz hu hv)

set_option maxHeartbeats 800000 in
/-- Compactness upgrades rank-`rank` target-and-hub box coverage to one open
strict-positive cutoff-support region. -/
theorem
    nonempty_tailAnchorTargetHubBoxTimeRegionData_of_strictGeneratedAtRank
    {d m N rank : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) N rank) ⊆
        A.carrier)
    {anchor hub : Fin (m + 1) -> Real}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hhub : forall i, anchor i <= hub i)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank))
    (J : Set (Fin (m + (m + 1)) -> Real))
    (hJ_compact : IsCompact J)
    (hJ_dominates :
      ∀ tau ∈ J, ReflectedTimeDominatesTailAnchor anchor tau) :
    Nonempty
      (TailAnchorTargetHubBoxTimeRegionData
        A anchor hub z J) := by
  let good :
      Set (((Fin (m + (m + 1)) -> Real) × (Real × Real))) :=
    {p |
      reflectedCauchyTailAnchorTargetHubBoxStageMap anchor hub z p ∈
          A.carrier ∧
        zeroAnchorTailAnchorTargetHubBoxStageMap anchor hub z p ∈
          A.carrier}
  have hgood_open : IsOpen good := by
    exact
      (A.carrier_open.preimage
          (continuous_reflectedCauchyTailAnchorTargetHubBoxStageMap
            anchor hub z)
        ).inter
        (A.carrier_open.preimage
          (continuous_zeroAnchorTailAnchorTargetHubBoxStageMap
            anchor hub z))
  have hproduct :
      J ×ˢ
          (Set.Icc (0 : Real) 1 ×ˢ Set.Icc (0 : Real) 1) ⊆
        good := by
    rintro ⟨tau, u, v⟩ ⟨htauJ, hu, hv⟩
    exact
      ⟨reflectedCauchyShiftedStagePoint_targetHubBox_mem_of_strictGeneratedAtRank
          A hscalar hanchor hhub (hJ_dominates tau htauJ) hz hu hv,
        zeroAnchorShiftedStagePoint_targetHubBox_mem_of_strictGeneratedAtRank
          A hscalar hanchor hhub (hJ_dominates tau htauJ) hz hu hv⟩
  obtain ⟨W, V, hW_open, _hV_open, hJW, hboxV, hWV⟩ :=
    generalized_tube_lemma
      (X := Fin (m + (m + 1)) -> Real) (Y := Real × Real)
      hJ_compact
      ((isCompact_Icc : IsCompact (Set.Icc (0 : Real) 1)).prod
        (isCompact_Icc : IsCompact (Set.Icc (0 : Real) 1)))
      hgood_open hproduct
  let U :=
    W ∩ section43TimeStrictPositiveRegion (m + (m + 1))
  refine ⟨{
    region := U
    region_open :=
      hW_open.inter
        (isOpen_section43TimeStrictPositiveRegion
          (m + (m + 1)))
    compactCarrier_subset := ?_
    region_positive := ?_
    reflectedCauchy_box_mem := ?_
    zeroAnchor_box_mem := ?_ }⟩
  · intro tau htau
    exact
      ⟨hJW htau,
        (hJ_dominates tau htau).strictPositive hanchor⟩
  · exact inter_subset_right
  · intro tau htau u hu v hv
    have hpair :
        (tau, (u, v)) ∈
          W ×ˢ V :=
      ⟨htau.1, hboxV ⟨hu, hv⟩⟩
    exact (hWV hpair).1
  · intro tau htau u hu v hv
    have hpair :
        (tau, (u, v)) ∈
          W ×ˢ V :=
      ⟨htau.1, hboxV ⟨hu, hv⟩⟩
    exact (hWV hpair).2

/-- Source-carrier form of the rank-`rank` target-and-hub cutoff-support
region. -/
theorem
    nonempty_tailAnchorTargetHubBoxTimeRegionData_of_sourceCarrier_strictGeneratedAtRank
    {d m N rank : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) N rank) ⊆
        A.carrier)
    {anchor hub : Fin (m + 1) -> Real}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hhub : forall i, anchor i <= hub i)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank))
    (K : Set (Fin (m + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_lower : ∀ tau ∈ K, forall i, anchor i <= tau i) :
    Nonempty
      (TailAnchorTargetHubBoxTimeRegionData
        A anchor hub z
          (reflectedChronologicalGapCarrier m K)) := by
  exact
    nonempty_tailAnchorTargetHubBoxTimeRegionData_of_strictGeneratedAtRank
      A hscalar hanchor hhub hz
      (reflectedChronologicalGapCarrier m K)
      (isCompact_reflectedChronologicalGapCarrier hK_compact)
      (reflectedChronologicalGapCarrier_dominatesTailAnchor
        hanchor hK_lower)

set_option maxHeartbeats 800000 in
/-- A compact source carrier admits a target-and-hub adapted universal atlas
for one rank-`rank` strict generated mixed target. -/
theorem
    nonempty_targetHubAdaptedUniversalCompactCarrierAnchoredAtlasData_of_strictGeneratedAtRank
    {d q N rank : Nat} [NeZero d]
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower :
      ∀ tau ∈ K, forall i, anchor i <= tau i)
    (hub : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) N rank))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) N rank) ⊆
        (L.reflectedPairStage (q := q)).carrier) :
    Nonempty
      (TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor hub z) := by
  obtain ⟨R⟩ :=
    nonempty_tailAnchorTargetHubBoxTimeRegionData_of_sourceCarrier_strictGeneratedAtRank
      (L.reflectedPairStage (q := q)) hscalar hanchor
      hanchor_hub hz K hK_compact hK_lower
  let f :
      UniformCompactTimeSource d ((q + 1) + 1) K ->
        euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1) :=
    fun a => UniformCompactTimeSource.source a
  have hfK :
      forall a x, x ∈ tsupport
          ((f a).1 :
            NPointDomain d ((q + 1) + 1) -> Complex) ->
        section43QTime (d := d) (n := (q + 1) + 1)
            (section43DiffCoordRealCLE d ((q + 1) + 1) x) ∈ K := by
    intro a x hx
    exact a.2 x hx
  obtain ⟨germ, hgerm_region⟩ :=
    exists_uniformCompactTimeMixedReflectedSourceFamilyData_of_sourceCarrier_subset_open
      OS f K hK_compact hK_positive hfK
      R.region R.region_open R.region_positive R.compactCarrier_subset
  obtain ⟨D, hD_germ⟩ :=
    exists_universalCompactCarrierAnchoredAtlasData_of_germ
      L OS H K hK_compact hK_positive germ
  refine ⟨{
    atlas := D
    boxRegion := R
    cutoff_support_region := ?_ }⟩
  rw [hD_germ]
  exact hgerm_region

namespace TailAnchorTargetHubBoxReflectedArgumentRegionData

/-- Forget an exact argument-carrier region to the stage-valued target-hub
region used by the qualitative vacuum-tail construction.  Both reflected and
zero-anchor boxes are transported through the same carrier inclusion. -/
def toTimeRegionData
    {d m : Nat} [NeZero d]
    {A : OSIITimeContinuationStage d (m + (m + 1))}
    {base : Set (Fin (m + (m + 1)) -> Real)}
    {anchor hub : Fin (m + 1) -> Real}
    {z : Fin m -> Complex}
    {J : Set (Fin (m + (m + 1)) -> Real)}
    (R : TailAnchorTargetHubBoxReflectedArgumentRegionData
      base anchor hub z J)
    (hbase : osiiTimeArgumentCarrier base ⊆ A.carrier) :
    TailAnchorTargetHubBoxTimeRegionData A anchor hub z J where
  region := R.region
  region_open := R.region_open
  compactCarrier_subset := R.compactCarrier_subset
  region_positive := R.region_positive
  reflectedCauchy_box_mem := by
    intro tau htau u hu v hv
    exact hbase (R.reflectedCauchy_box_mem tau htau u hu v hv)
  zeroAnchor_box_mem := by
    intro tau htau u hu v hv
    exact hbase (R.zeroAnchor_box_mem tau htau u hu v hv)

end TailAnchorTargetHubBoxReflectedArgumentRegionData

/-- A target-hub atlas selected directly inside one positive analytic-rank
source carrier.  Unlike the two-rank compatibility package below, the target
is required only at the named successor rank; no false lower-rank membership
is introduced. -/
structure PositiveRankTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
    {d q depth rank : Nat} [NeZero d]
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (anchor hub : Fin ((q + 1) + 1) -> Real)
    (z : Fin (q + 1) -> Complex) where
  current :
    TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      L OS K anchor hub z
  rankRegion :
    TailAnchorTargetHubBoxReflectedArgumentRegionData
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1))
      anchor hub z (reflectedChronologicalGapCarrier (q + 1) K)
  cutoff_support_rank :
    tsupport
        (current.atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
      rankRegion.region

set_option maxHeartbeats 1000000 in
/-- Select a target-hub atlas whose one concrete cutoff is supported inside
the exact positive-rank argument carrier containing the target. -/
theorem
    nonempty_positiveRankTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
    {d q depth rank : Nat} [NeZero d]
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower :
      forall tau, tau ∈ K -> forall i, anchor i <= tau i)
    (hub : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1)) ⊆
        (L.reflectedPairStage (q := q)).carrier) :
    Nonempty
      (PositiveRankTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        (depth := depth) (rank := rank) L OS K anchor hub z) := by
  obtain ⟨Q⟩ :=
    nonempty_tailAnchorTargetHubBoxReflectedArgumentRegionData_of_rankSuccessor
      hanchor hanchor_hub hz
      (reflectedChronologicalGapCarrier (q + 1) K)
      (isCompact_reflectedChronologicalGapCarrier hK_compact)
      (reflectedChronologicalGapCarrier_dominatesTailAnchor
        hanchor hK_lower)
  let R : TailAnchorTargetHubBoxTimeRegionData
      (L.reflectedPairStage (q := q)) anchor hub z
      (reflectedChronologicalGapCarrier (q + 1) K) :=
    Q.toTimeRegionData hscalar
  let f :
      UniformCompactTimeSource d ((q + 1) + 1) K ->
        euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1) :=
    fun a => UniformCompactTimeSource.source a
  have hfK :
      forall a x, x ∈ tsupport
          ((f a).1 :
            NPointDomain d ((q + 1) + 1) -> Complex) ->
        section43QTime (d := d) (n := (q + 1) + 1)
            (section43DiffCoordRealCLE d ((q + 1) + 1) x) ∈ K := by
    intro a x hx
    exact a.2 x hx
  obtain ⟨germ, hgerm_region⟩ :=
    exists_uniformCompactTimeMixedReflectedSourceFamilyData_of_sourceCarrier_subset_open
      OS f K hK_compact hK_positive hfK
      Q.region Q.region_open Q.region_positive Q.compactCarrier_subset
  obtain ⟨D, hD_germ⟩ :=
    exists_universalCompactCarrierAnchoredAtlasData_of_germ
      L OS H K hK_compact hK_positive germ
  let current :
      TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor hub z := {
    atlas := D
    boxRegion := R
    cutoff_support_region := by
      rw [hD_germ]
      exact hgerm_region }
  exact ⟨{
    current := current
    rankRegion := Q
    cutoff_support_rank := by
      change
        tsupport
            (D.sourceStage.germ.η :
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
          Q.region
      rw [hD_germ]
      exact hgerm_region }⟩

/-- The canonical exact-carrier atlas selected for one strictly positive
depth and analytic rank.  Naming this choice lets the qualitative tail
constructor and the quantitative source certificate use the same germ. -/
noncomputable def
    selectedPositiveRankTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
    {d q depth rank : Nat} [NeZero d]
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower :
      forall tau, tau ∈ K -> forall i, anchor i <= tau i)
    (hub : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1)) ⊆
        (L.reflectedPairStage (q := q)).carrier) :
    PositiveRankTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      (depth := depth) (rank := rank) L OS K anchor hub z :=
  Classical.choice
    (nonempty_positiveRankTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      L OS H K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz hscalar)

/-- Select the ordinary target-hub atlas, using the exact argument-carrier
choice whenever both the depth and analytic rank are successors. -/
noncomputable def
    selectedTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData_of_strictGeneratedAtRank
    {d q : Nat} [NeZero d]
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower :
      forall tau, tau ∈ K -> forall i, anchor i <= tau i)
    (hub : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (depth rank : Nat)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (L.reflectedPairStage (q := q)).carrier) :
    TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      L OS K anchor hub z := by
  rcases depth with (_ | depth)
  · exact Classical.choice
      (nonempty_targetHubAdaptedUniversalCompactCarrierAnchoredAtlasData_of_strictGeneratedAtRank
        L OS H K hK_compact hK_positive anchor hanchor hK_lower
        hub hanchor_hub z hz hscalar)
  rcases rank with (_ | rank)
  · exact Classical.choice
      (nonempty_targetHubAdaptedUniversalCompactCarrierAnchoredAtlasData_of_strictGeneratedAtRank
        L OS H K hK_compact hK_positive anchor hanchor hK_lower
        hub hanchor_hub z hz hscalar)
  exact
    (selectedPositiveRankTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      L OS H K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz hscalar).current

/-- A ranked target-hub atlas whose selected cutoff also stays in the open
next-depth, next-rank scalar argument carrier.

The ordinary target-hub package remembers only the surrounding continuation
stage.  Normalized-envelope shifts need this stronger route-owned witness so
the same concrete cutoff carries a compact safe-shift window. -/
structure RankSuccessorTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
    {d q depth rank : Nat} [NeZero d]
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (anchor hub : Fin ((q + 1) + 1) -> Real)
    (z : Fin (q + 1) -> Complex) where
  current :
    TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      L OS K anchor hub z
  successorRegion :
    TailAnchorTargetHubBoxReflectedArgumentRegionData
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1))
      anchor hub z (reflectedChronologicalGapCarrier (q + 1) K)
  cutoff_support_successor :
    tsupport
        (current.atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
      successorRegion.region

set_option maxHeartbeats 1000000 in
/-- Select one target-hub atlas whose cutoff simultaneously supports the
current ranked stage and the open rank-successor argument carrier. -/
theorem
    nonempty_rankSuccessorTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
    {d q depth rank : Nat} [NeZero d]
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower :
      forall tau, tau ∈ K -> forall i, anchor i <= tau i)
    (hub : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (hz_current :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (hz_successor :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (L.reflectedPairStage (q := q)).carrier) :
    Nonempty
      (RankSuccessorTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        (depth := depth) (rank := rank)
        L OS K anchor hub z) := by
  obtain ⟨R⟩ :=
    nonempty_tailAnchorTargetHubBoxTimeRegionData_of_sourceCarrier_strictGeneratedAtRank
      (L.reflectedPairStage (q := q)) hscalar hanchor
      hanchor_hub hz_current K hK_compact hK_lower
  obtain ⟨Q⟩ :=
    nonempty_tailAnchorTargetHubBoxReflectedArgumentRegionData_of_rankSuccessor
      hanchor hanchor_hub hz_successor
      (reflectedChronologicalGapCarrier (q + 1) K)
      (isCompact_reflectedChronologicalGapCarrier hK_compact)
      (reflectedChronologicalGapCarrier_dominatesTailAnchor
        hanchor hK_lower)
  let f :
      UniformCompactTimeSource d ((q + 1) + 1) K ->
        euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1) :=
    fun a => UniformCompactTimeSource.source a
  have hfK :
      forall a x, x ∈ tsupport
          ((f a).1 :
            NPointDomain d ((q + 1) + 1) -> Complex) ->
        section43QTime (d := d) (n := (q + 1) + 1)
            (section43DiffCoordRealCLE d ((q + 1) + 1) x) ∈ K := by
    intro a x hx
    exact a.2 x hx
  let U := R.region ∩ Q.region
  have hU_open : IsOpen U :=
    R.region_open.inter Q.region_open
  have hU_positive :
      U ⊆ section43TimeStrictPositiveRegion
        ((q + 1) + ((q + 1) + 1)) :=
    inter_subset_left.trans R.region_positive
  have hcarrier_U :
      reflectedChronologicalGapCarrier (q + 1) K ⊆ U := by
    intro tau htau
    exact
      ⟨R.compactCarrier_subset htau,
        Q.compactCarrier_subset htau⟩
  obtain ⟨germ, hgerm_region⟩ :=
    exists_uniformCompactTimeMixedReflectedSourceFamilyData_of_sourceCarrier_subset_open
      OS f K hK_compact hK_positive hfK
      U hU_open hU_positive hcarrier_U
  obtain ⟨D, hD_germ⟩ :=
    exists_universalCompactCarrierAnchoredAtlasData_of_germ
      L OS H K hK_compact hK_positive germ
  let current :
      TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor hub z := {
      atlas := D
      boxRegion := R
      cutoff_support_region := by
        rw [hD_germ]
        exact hgerm_region.trans inter_subset_left }
  exact ⟨{
    current := current
    successorRegion := Q
    cutoff_support_successor := by
      change
        tsupport
            (D.sourceStage.germ.η :
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
          Q.region
      rw [hD_germ]
      exact hgerm_region.trans inter_subset_right }⟩

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d q : Nat} [NeZero d]
variable
  {OS : OsterwalderSchraderAxioms d}
  {L : SimultaneousTimeContinuationStageLevel d}
  {iota : Type*}

/-- Concrete packet and positive-head Gram provenance retained by one
vacuum-tail direct extension.  The qualitative extension interface keeps its
Gram source type abstract; this route-owned record remembers the concrete
source family needed for quantitative normalized-envelope estimates. -/
structure VacuumTailTargetHubPointedDirectExtensionConstructionData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (hub : Fin (q + 1) -> Real)
    (z : OSIITimeGapSpace (q + 1))
    (atlas : GeneratorStagePointedConvexAtlas
      (L.stage (q + 1)) (osiiPositiveRealTimeEmbed hub) iota) where
  approximateIdentity : Section43ProductTimeApproximateIdentity (q + 1)
  anchor : Fin (q + 1) -> Real
  packet : AnchoredPacketTimeShellFamilyData
    (d := d) approximateIdentity anchor
  atlasData : PositiveHeadUniversalAnchoredAtlasData L OS packet
  directExtension : VacuumTailTargetHubPointedDirectExtensionData
    L OS hub z atlas
  diagonalCenterDomain_eq :
    directExtension.diagonalCenterDomain =
      atlasData.gram.reachableAnchoredAtlasCoveredDomain
        atlasData.sourceStage.stage atlasData.sourceStage.germ
  diagonalCenter_mem_spatialLinearDomain : forall w,
    w ∈ directExtension.carrier ->
      directExtension.diagonalCenter w ∈ atlasData.spatialLinearDomain
  approximation_eq_packet : forall scale w test,
    directExtension.approximation scale w test =
      atlasData.vacuumTailPacketSpatialDistribution scale
        (directExtension.diagonalCenter w) test
  diagonalScalar_eq : forall scale test,
    directExtension.diagonalScalar scale test =
      (atlasData.gram.cauchy
        (packet.positiveHeadSpatialAnchoredSourceCLM scale
          (PositiveHeadUniversalAnchoredAtlasData.vacuumTailSpatialLiftCLM
            test))
        (packet.positiveHeadSpatialAnchoredSourceCLM scale
          (PositiveHeadUniversalAnchoredAtlasData.vacuumTailSpatialLiftCLM
            test))).scalar

set_option maxHeartbeats 1000000 in
/-- Build the vacuum-tail extension after choosing the target-adapted source
atlas.  Keeping the choice as an argument lets quantitative callers retain
extra cutoff geometry without duplicating the analytic extension body. -/
noncomputable def
    vacuumTailTargetHubPointedDirectExtensionConstructionData_of_atlasSelector
    (L : SimultaneousTimeContinuationStageLevel d)
    (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
    (depth rank : Nat)
    (hub : Fin (q + 1) -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion (q + 1))
    (atlas :
      GeneratorStagePointedConvexAtlas
        (L.stage (q + 1))
        (osiiPositiveRealTimeEmbed hub) iota)
    (z : OSIITimeGapSpace (q + 1))
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (atlasSelector : forall
      (C : TargetHubHalfAnchorData hub z)
      (I0 : Section43ProductTimeApproximateIdentity (q + 1))
      (lower : LowerAnchoredPacketTimeShellFamilyData
        (d := d) I0 C.anchor),
      TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS
        lower.packet.positiveHeadSpatialSourceCarrier
        lower.packet.positiveHeadSpatialSourceLowerAnchor
        (Fin.cons normalizedPositiveTimeBasepointLower hub) z) :
    VacuumTailTargetHubPointedDirectExtensionConstructionData
      L OS hub z atlas := by
  let C := targetHubHalfAnchorData hub hhub z hz.1
  let I0 : Section43ProductTimeApproximateIdentity (q + 1) :=
    Classical.choice
      (Section43ProductTimeApproximateIdentity.nonempty (q + 1))
  let lower := Classical.choice
    (nonempty_lowerAnchoredPacketTimeShellFamilyData
      (d := d) I0 C.anchor C.anchor_positive)
  let A := lower.packet
  let sourceHub : Fin ((q + 1) + 1) -> Real :=
    Fin.cons normalizedPositiveTimeBasepointLower hub
  let adapted := atlasSelector C I0 lower
  let D : PositiveHeadUniversalAnchoredAtlasData
      L OS A :=
    adapted.atlas.toPositiveHead
  let centered :=
    selectedVacuumTailTargetHubCenteredConvexChartData adapted
  let carrier : Set (OSIITimeGapSpace (q + 1)) :=
    {w |
      w + osiiPositiveRealTimeEmbed (-C.anchor) ∈ centered.domain}
  have hcarrier_open : IsOpen carrier :=
    centered.domain_open.preimage
      (continuous_id.add continuous_const)
  have hcarrier_convex : Convex Real carrier :=
    centered.domain_convex.translate_preimage_left
      (osiiPositiveRealTimeEmbed (-C.anchor))
  have hcenteredHub :
      tailAnchorCenteredHubPoint
          A.positiveHeadSpatialSourceLowerAnchor sourceHub =
        osiiPositiveRealTimeEmbed hub -
          osiiPositiveRealTimeEmbed C.anchor := by
    ext j
    simp [tailAnchorCenteredHubPoint_apply, sourceHub,
      positiveHeadSpatialSourceLowerAnchor,
      osiiPositiveRealTimeEmbed]
  have hcenteredTarget :
      tailAnchorCenteredPoint
          A.positiveHeadSpatialSourceLowerAnchor z =
        z - osiiPositiveRealTimeEmbed C.anchor := by
    ext j
    simp [tailAnchorCenteredPoint,
      positiveHeadSpatialSourceLowerAnchor,
      osiiPositiveRealTimeEmbed]
  have hembed_neg :
      osiiPositiveRealTimeEmbed (-C.anchor) =
        -osiiPositiveRealTimeEmbed C.anchor := by
    ext j
    simp [osiiPositiveRealTimeEmbed]
  have hcarrier_subset :
      carrier ⊆ D.vacuumTailAbsoluteStage.carrier := by
    intro w hw
    change
      w + osiiPositiveRealTimeEmbed (-C.anchor) ∈
        D.spatialLinearDomain
    exact centered.domain_subset hw
  have hanchor_carrier :
      osiiPositiveRealTimeEmbed C.anchor ∈ carrier := by
    change
      osiiPositiveRealTimeEmbed C.anchor +
          osiiPositiveRealTimeEmbed (-C.anchor) ∈
        centered.domain
    convert centered.zero_mem using 1 <;>
      ext j <;> simp [osiiPositiveRealTimeEmbed]
  have hhub_carrier :
      osiiPositiveRealTimeEmbed hub ∈ carrier := by
    change
      osiiPositiveRealTimeEmbed hub +
          osiiPositiveRealTimeEmbed (-C.anchor) ∈
        centered.domain
    rw [hembed_neg]
    rw [← sub_eq_add_neg, ← hcenteredHub]
    exact centered.hub_mem
  have htarget_carrier : z ∈ carrier := by
    change
      z + osiiPositiveRealTimeEmbed (-C.anchor) ∈
        centered.domain
    rw [hembed_neg]
    rw [← sub_eq_add_neg, ← hcenteredTarget]
    exact centered.target_mem
  let M := Classical.choice
    (nonempty_stageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      (A := A) (Hcanonical (q + 1)))
  have hanchor_predecessor :
      osiiPositiveRealTimeEmbed C.anchor ∈
        (L.stage (q + 1)).carrier :=
    (Hcanonical (q + 1)).positiveReal_mem_carrier
      C.anchor C.anchor_positive
  have hseedExists := Set.mem_iUnion.mp
    (atlas.carrier_subset_iUnion hanchor_predecessor)
  let seedChart := Classical.choose hseedExists
  have hseed := Classical.choose_spec hseedExists
  let extension :
      GeneratorStageExtensionData (L.stage (q + 1)) :=
    D.vacuumTailTargetHubPointedStageExtensionData
      M atlas seedChart hseed
      carrier hcarrier_open hcarrier_convex hcarrier_subset
      hanchor_carrier hhub_carrier
  have hextension_domain :
      extension.domain (firstBridgeGeneratorIndex q) = carrier := by
    change firstBridgeOnlyDomain q carrier
        (firstBridgeGeneratorIndex q) = carrier
    exact firstBridgeOnlyDomain_first q carrier
  let directExtension :
      VacuumTailTargetHubPointedDirectExtensionData
        L OS hub z atlas :=
    {
      extension := extension
      carrier := carrier
      carrier_open := hcarrier_open
      carrier_convex := hcarrier_convex
      carrier_subset_extensionDomain := by
        rw [hextension_domain]
      hub_mem_carrier := hhub_carrier
      target_mem_carrier := htarget_carrier
      approximation := fun scale w =>
        D.vacuumTailPacketSpatialDistribution scale
          (w + osiiPositiveRealTimeEmbed (-C.anchor))
      approximation_tendsto := by
        intro w hw chi
        have hcentered :
            w + osiiPositiveRealTimeEmbed (-C.anchor) ∈
              D.spatialLinearDomain :=
          centered.domain_subset hw
        have ht :=
          (D.vacuumTailSpatialDistribution_locallyUniform chi).tendsto_at
            hcentered
        have heval :
            extension.distribution
                (firstBridgeGeneratorIndex q) w chi =
              D.vacuumTailLimitSpatialDistribution
                (w + osiiPositiveRealTimeEmbed (-C.anchor)) chi := by
          change D.vacuumTailAbsoluteStage.distribution w chi = _
          rfl
        rw [heval]
        exact ht
      diagonalCenterDomain :=
        D.gram.reachableAnchoredAtlasCoveredDomain
          D.sourceStage.stage D.sourceStage.germ
      diagonalCenter := fun w =>
        w + osiiPositiveRealTimeEmbed (-C.anchor)
      diagonalCenter_mem := by
        intro w hw
        exact centered.domain_subset_reachableAtlas hw
      diagonalScalar := fun scale test =>
        (D.gram.cauchy
          (A.positiveHeadSpatialAnchoredSourceCLM scale
            (PositiveHeadUniversalAnchoredAtlasData.vacuumTailSpatialLiftCLM
              test))
          (A.positiveHeadSpatialAnchoredSourceCLM scale
            (PositiveHeadUniversalAnchoredAtlasData.vacuumTailSpatialLiftCLM
              test))).scalar
      gramSourceIndex :=
        UniformCompactTimeSource d ((q + 1) + 1)
          A.positiveHeadSpatialSourceCarrier
      gramScalar := fun a b => (D.gram.cauchy a b).scalar
      gramAnchorField := fun a => D.gram.hilbert.field a 0
      gramSeed :=
        D.gram.toInitialSourceIndexedReflectedGramHilbertFieldData
          OS
          (fun a : UniformCompactTimeSource d ((q + 1) + 1)
              A.positiveHeadSpatialSourceCarrier =>
            UniformCompactTimeSource.source a)
          D.sourceStage.stage D.sourceStage.germ
      diagonalSource := fun scale test =>
        A.positiveHeadSpatialAnchoredSourceCLM scale
          (PositiveHeadUniversalAnchoredAtlasData.vacuumTailSpatialLiftCLM
            test)
      diagonalScalar_eq_gram := by
        intro scale test
        rfl
      diagonalCenterDomain_eq_reachableAtlas := rfl
      diagonalPoint := fun w =>
        reflectedCauchyCenter
          (w + osiiPositiveRealTimeEmbed (-C.anchor))
      diagonalPoint_eq_reflectedCenter := fun _w => rfl
      norm_approximation_le_of_diagonal := by
        intro lgc scale w hw test B hB hdiagonal
        have hcentered :
            w + osiiPositiveRealTimeEmbed (-C.anchor) ∈
              D.spatialLinearDomain :=
          centered.domain_subset hw
        exact
          D.norm_vacuumTailPacket_le_of_scalar_diagonal_bound
            lgc scale
            (w + osiiPositiveRealTimeEmbed (-C.anchor))
            hcentered test B hB hdiagonal
      norm_approximation_le_sqrt_of_diagonal := by
        intro lgc scale w hw test B hdiagonal
        have hcentered :
            w + osiiPositiveRealTimeEmbed (-C.anchor) ∈
              D.spatialLinearDomain :=
          centered.domain_subset hw
        exact
          D.norm_vacuumTailPacket_le_sqrt_of_scalar_diagonal_bound
            lgc scale
            (w + osiiPositiveRealTimeEmbed (-C.anchor))
            hcentered test B hdiagonal }
  exact
    {
      approximateIdentity := I0
      anchor := C.anchor
      packet := A
      atlasData := D
      directExtension := directExtension
      diagonalCenterDomain_eq := rfl
      diagonalCenter_mem_spatialLinearDomain := by
        intro w hw
        exact centered.domain_subset hw
      approximation_eq_packet := by
        intro scale w test
        rfl
      diagonalScalar_eq := by
        intro scale test
        rfl }

set_option maxHeartbeats 1000000 in
/-- Every rank-`rank` strict generated mixed-tail point admits a genuine
scalar-stage extension whose convex chart contains the exact target and the
fixed predecessor hub, retaining its concrete packet and Gram atlas. -/
noncomputable def
    vacuumTailTargetHubPointedDirectExtensionConstructionData_of_strictGeneratedAtRank
    (L : SimultaneousTimeContinuationStageLevel d)
    (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
    (depth rank : Nat)
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (L.stage
          ((q + 1) + ((q + 1) + 1))).carrier)
    (hub : Fin (q + 1) -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion (q + 1))
    (atlas :
      GeneratorStagePointedConvexAtlas
        (L.stage (q + 1))
        (osiiPositiveRealTimeEmbed hub) iota)
    (z : OSIITimeGapSpace (q + 1))
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank)) :
    VacuumTailTargetHubPointedDirectExtensionConstructionData
      L OS hub z atlas :=
  vacuumTailTargetHubPointedDirectExtensionConstructionData_of_atlasSelector
    L Hcanonical depth rank hub hhub atlas z hz
      (fun C I0 lower =>
        let A := lower.packet
        let sourceHub : Fin ((q + 1) + 1) -> Real :=
          Fin.cons normalizedPositiveTimeBasepointLower hub
        let hsourceAnchorHub : forall j,
            A.positiveHeadSpatialSourceLowerAnchor j <= sourceHub j := by
          intro j
          refine Fin.cases ?_ ?_ j
          · simp [sourceHub, positiveHeadSpatialSourceLowerAnchor]
          · intro r
            simpa [sourceHub, positiveHeadSpatialSourceLowerAnchor] using
              C.anchor_le_hub r
        selectedTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData_of_strictGeneratedAtRank
          L OS Hcanonical
          A.positiveHeadSpatialSourceCarrier
          A.positiveHeadSpatialSourceCarrier_compact
          A.positiveHeadSpatialSourceCarrier_positive
          A.positiveHeadSpatialSourceLowerAnchor
          A.positiveHeadSpatialSourceLowerAnchor_positive
          (A.positiveHeadSpatialSourceLowerAnchor_le_carrier
            lower.anchor_le_carrier)
          sourceHub hsourceAnchorHub z depth rank hz hscalar)

namespace PositiveRankVacuumTailTargetHubPointedDirectExtensionSourceData

end PositiveRankVacuumTailTargetHubPointedDirectExtensionSourceData

/-- One target index for the complete rank-`rank` strict generated
mixed-tail carrier at positive scalar arity `q + 1`. -/
structure VacuumTailStrictGeneratedMixedTargetAtRank
    (q depth rank : Nat) where
  target : OSIITimeGapSpace (q + 1)
  target_mem :
    target ∈ osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank
        ((q + 1) + 1) depth rank)

/-- Select the provenance-carrying vacuum-tail construction assigned to one
ranked mixed target. -/
noncomputable def
    selectedVacuumTailStrictGeneratedTargetHubPointedConstructionAtRank
    (L : SimultaneousTimeContinuationStageLevel d)
    (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
    (depth rank : Nat)
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (L.stage
          ((q + 1) + ((q + 1) + 1))).carrier)
    (hub : Fin (q + 1) -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion (q + 1))
    (atlas :
      GeneratorStagePointedConvexAtlas
        (L.stage (q + 1))
        (osiiPositiveRealTimeEmbed hub) iota)
    (a : VacuumTailStrictGeneratedMixedTargetAtRank q depth rank) :
    VacuumTailTargetHubPointedDirectExtensionConstructionData
      L OS hub a.target atlas :=
  vacuumTailTargetHubPointedDirectExtensionConstructionData_of_strictGeneratedAtRank
    L Hcanonical depth rank hscalar
    hub hhub atlas a.target a.target_mem

/-- Select the pointed vacuum-tail extension assigned to one ranked mixed
target. -/
noncomputable def
    selectedVacuumTailStrictGeneratedTargetHubPointedDirectExtensionAtRank
    (L : SimultaneousTimeContinuationStageLevel d)
    (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
    (depth rank : Nat)
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (L.stage
          ((q + 1) + ((q + 1) + 1))).carrier)
    (hub : Fin (q + 1) -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion (q + 1))
    (atlas :
      GeneratorStagePointedConvexAtlas
        (L.stage (q + 1))
        (osiiPositiveRealTimeEmbed hub) iota)
    (a : VacuumTailStrictGeneratedMixedTargetAtRank q depth rank) :
    VacuumTailTargetHubPointedDirectExtensionData
      L OS hub a.target atlas :=
  (selectedVacuumTailStrictGeneratedTargetHubPointedConstructionAtRank
    L Hcanonical depth rank hscalar hub hhub atlas a).directExtension

/-- The target-indexed pointed convex-core atlas for rank-`rank`
mixed-tail projection at one positive scalar arity. -/
noncomputable def
    vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
    (L : SimultaneousTimeContinuationStageLevel d)
    (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
    (depth rank : Nat)
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (L.stage
          ((q + 1) + ((q + 1) + 1))).carrier)
    (hub : Fin (q + 1) -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion (q + 1))
    (atlas :
      GeneratorStagePointedConvexAtlas
        (L.stage (q + 1))
        (osiiPositiveRealTimeEmbed hub) iota) :
    GeneratorStageExtensionConvexCoreAtlasData
      (L.stage (q + 1)) where
  chart := VacuumTailStrictGeneratedMixedTargetAtRank q depth rank
  chartGenerator := fun _ => firstBridgeGeneratorIndex q
  carrier := fun a =>
    (selectedVacuumTailStrictGeneratedTargetHubPointedDirectExtensionAtRank
      L Hcanonical depth rank hscalar hub hhub atlas a).carrier
  carrier_open := fun a =>
    (selectedVacuumTailStrictGeneratedTargetHubPointedDirectExtensionAtRank
      L Hcanonical depth rank hscalar hub hhub atlas a).carrier_open
  carrier_convex := fun a =>
    (selectedVacuumTailStrictGeneratedTargetHubPointedDirectExtensionAtRank
      L Hcanonical depth rank hscalar hub hhub atlas a).carrier_convex
  extension := fun a =>
    (selectedVacuumTailStrictGeneratedTargetHubPointedDirectExtensionAtRank
      L Hcanonical depth rank hscalar hub hhub atlas a).extension
  carrier_subset_extensionDomain := fun a =>
    (selectedVacuumTailStrictGeneratedTargetHubPointedDirectExtensionAtRank
      L Hcanonical depth rank hscalar hub hhub atlas a
        ).carrier_subset_extensionDomain
  commonPoint := osiiPositiveRealTimeEmbed hub
  commonPoint_mem_predecessor :=
    (Hcanonical (q + 1)).positiveReal_mem_carrier hub hhub
  commonPoint_mem_carrier := fun a =>
    (selectedVacuumTailStrictGeneratedTargetHubPointedDirectExtensionAtRank
      L Hcanonical depth rank hscalar hub hhub atlas a).hub_mem_carrier

namespace VacuumTailStrictGeneratedTargetHubPointedProjectionAtRank

variable
  (L : SimultaneousTimeContinuationStageLevel d)
  (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
  (depth rank : Nat)
  (hscalar :
    osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
      (L.stage
        ((q + 1) + ((q + 1) + 1))).carrier)
  (hub : Fin (q + 1) -> Real)
  (hhub : hub ∈ section43TimeStrictPositiveRegion (q + 1))
  (atlas :
    GeneratorStagePointedConvexAtlas
      (L.stage (q + 1))
      (osiiPositiveRealTimeEmbed hub) iota)

/-- The selected target charts cover the complete rank-`rank` strict
generated mixed-tail carrier. -/
theorem mixedTailArgumentCarrier_subset_iUnion_carrier :
    osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank) ⊆
      ⋃ a : VacuumTailStrictGeneratedMixedTargetAtRank q depth rank,
        (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
          L Hcanonical depth rank hscalar hub hhub atlas).carrier a := by
  intro z hz
  let a : VacuumTailStrictGeneratedMixedTargetAtRank q depth rank :=
    { target := z
      target_mem := hz }
  exact
    Set.mem_iUnion_of_mem a
      (selectedVacuumTailStrictGeneratedTargetHubPointedDirectExtensionAtRank
        L Hcanonical depth rank hscalar hub hhub atlas a
        ).target_mem_carrier

/-- One glued scalar successor contains the complete rank-`rank` strict
generated mixed-tail carrier. -/
theorem mixedTailArgumentCarrier_subset_successorCarrier :
    osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank) ⊆
      (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
        L Hcanonical depth rank hscalar
          hub hhub atlas).successorStage.carrier :=
  (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
      L Hcanonical depth rank hscalar hub hhub atlas
    ).subset_successorCarrier_of_subset_iUnion_carrier
      _
      (mixedTailArgumentCarrier_subset_iUnion_carrier
        L Hcanonical depth rank hscalar hub hhub atlas)

/-- The ranked projection successor preserves the pointed convex-atlas
invariant through the same positive-real hub. -/
noncomputable def successorPointedConvexAtlas :
    GeneratorStagePointedConvexAtlas
      (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
        L Hcanonical depth rank hscalar
          hub hhub atlas).successorStage
      (osiiPositiveRealTimeEmbed hub)
      (Sum iota
        (VacuumTailStrictGeneratedMixedTargetAtRank q depth rank)) :=
  (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
    L Hcanonical depth rank hscalar
      hub hhub atlas).successorPointedConvexAtlas atlas

end VacuumTailStrictGeneratedTargetHubPointedProjectionAtRank

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

/-- The exact rank-`rank` reflected scalar inputs consumed by the ranked
vacuum-tail projection. -/
structure StageWideStrictGeneratedReflectedScalarRankInputData
    {d : Nat}
    (L : SimultaneousTimeContinuationStageLevel d)
    (depth rank : Nat) where
  reflectedScalarStrictGeneratedAtRank :
    forall q,
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (L.stage
          ((q + 1) + ((q + 1) + 1))).carrier

namespace StageWideStrictGeneratedReflectedScalarRankInputData

/-- A simultaneous rank-`rank` scalar realization supplies the smaller
reflected-arity input interface. -/
def ofScalarAtRank
    {d : Nat}
    (L : SimultaneousTimeContinuationStageLevel d)
    (depth rank : Nat)
    (hscalar :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBaseAtRank
              arity depth rank) ⊆
          (L.stage arity).carrier) :
    StageWideStrictGeneratedReflectedScalarRankInputData
      L depth rank where
  reflectedScalarStrictGeneratedAtRank q :=
    hscalar ((q + 1) + ((q + 1) + 1))

end StageWideStrictGeneratedReflectedScalarRankInputData

namespace CanonicalGeneratorPointedConvexAtlasStageLevelData

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

variable {d depth rank : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

variable
  (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
  (R :
    StageWideStrictGeneratedReflectedScalarRankInputData
      D.stageLevel depth rank)

/-- The target-indexed convex-core atlas for rank-`rank` mixed-tail
projection at one positive scalar arity. -/
noncomputable def vacuumTailProjectionRankConvexCoreAtlas
    (q : Nat) :
    GeneratorStageExtensionConvexCoreAtlasData
      (D.stageLevel.stage (q + 1)) :=
  vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
    D.stageLevel D.canonicalEdges depth rank
    (R.reflectedScalarStrictGeneratedAtRank q)
    (D.hub q) (D.hub_positive q) (D.pointedAtlas q)

/-- Retain the zero-gap predecessor and project every positive-arity
rank-`rank` mixed tail into one scalar successor. -/
noncomputable def vacuumTailProjectionRankStageLevel :
    SimultaneousTimeContinuationStageLevel d where
  stage
    | 0 => D.stageLevel.stage 0
    | q + 1 => (D.vacuumTailProjectionRankConvexCoreAtlas R q).successorStage

@[simp]
theorem vacuumTailProjectionRankStageLevel_stage_zero :
    (D.vacuumTailProjectionRankStageLevel R).stage 0 =
      D.stageLevel.stage 0 :=
  rfl

@[simp]
theorem vacuumTailProjectionRankStageLevel_stage_succ
    (q : Nat) :
    (D.vacuumTailProjectionRankStageLevel R).stage (q + 1) =
      (D.vacuumTailProjectionRankConvexCoreAtlas R q).successorStage :=
  rfl

/-- The ranked projection successor retains every predecessor carrier. -/
theorem oldCarrier_subset_vacuumTailProjectionRankStageLevel
    (k : Nat) :
    (D.stageLevel.stage k).carrier ⊆
      ((D.vacuumTailProjectionRankStageLevel R).stage k).carrier := by
  cases k with
  | zero =>
      exact Set.Subset.rfl
  | succ q =>
      exact
        (D.vacuumTailProjectionRankConvexCoreAtlas R q
          ).oldCarrier_subset_successorCarrier

/-- The ranked projection successor agrees with its predecessor on the
complete old carrier. -/
theorem vacuumTailProjectionRankStageLevel_extends
    (k : Nat) :
    Set.EqOn
      ((D.vacuumTailProjectionRankStageLevel R).stage k).distribution
      (D.stageLevel.stage k).distribution
      (D.stageLevel.stage k).carrier := by
  cases k with
  | zero =>
      exact Set.eqOn_refl _ _
  | succ q =>
      exact
        (D.vacuumTailProjectionRankConvexCoreAtlas R q
          ).successorStage_extends_predecessor

/-- Canonical compact positive-real edges survive ranked projection. -/
theorem vacuumTailProjectionRankStageLevel_hasCanonicalEdges :
    (D.vacuumTailProjectionRankStageLevel R
      ).HasCanonicalReducedCompactEdges OS := by
  intro k
  cases k with
  | zero =>
      exact D.canonicalEdges 0
  | succ q =>
      exact
        (D.vacuumTailProjectionRankConvexCoreAtlas R q).stageExtensionData
          |>.preservesCanonicalReducedCompactStageEdges
            OS (D.canonicalEdges (q + 1))

/-- The rank projection successor is again a simultaneous fixed-hub pointed
convex-atlas stage level. -/
noncomputable def vacuumTailProjectionRankNext :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS where
  stageLevel := D.vacuumTailProjectionRankStageLevel R
  canonicalEdges :=
    D.vacuumTailProjectionRankStageLevel_hasCanonicalEdges R
  chart := fun q =>
    Sum (D.chart q)
      (VacuumTailStrictGeneratedMixedTargetAtRank q depth rank)
  hub := D.hub
  hub_positive := D.hub_positive
  pointedAtlas := fun q =>
    VacuumTailStrictGeneratedTargetHubPointedProjectionAtRank.successorPointedConvexAtlas
      D.stageLevel D.canonicalEdges depth rank
      (R.reflectedScalarStrictGeneratedAtRank q)
      (D.hub q) (D.hub_positive q) (D.pointedAtlas q)

/-- At every positive scalar arity, the successor contains the complete
rank-`rank` strict generated mixed-tail carrier. -/
theorem strictGeneratedMixedTailCarrierAtRank_subset_vacuumTailProjectionRankNext
    (q : Nat) :
    osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank) ⊆
      ((D.vacuumTailProjectionRankNext R).stageLevel.stage
        (q + 1)).carrier := by
  exact
    VacuumTailStrictGeneratedTargetHubPointedProjectionAtRank.mixedTailArgumentCarrier_subset_successorCarrier
      D.stageLevel D.canonicalEdges depth rank
      (R.reflectedScalarStrictGeneratedAtRank q)
      (D.hub q) (D.hub_positive q) (D.pointedAtlas q)

/-- Every exact rank-`rank` mixed argument projects to its scalar tail in
the successor. -/
theorem mixedTailMemScalar_vacuumTailProjectionRankNext
    (k : Nat)
    (x : Fin (k + 1) -> Real)
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed (k + 1) depth x) :
    osiiTimeArgumentCarrier
        ({Fin.tail x} : Set (Fin k -> Real)) ⊆
      ((D.vacuumTailProjectionRankNext R).stageLevel.stage k).carrier := by
  cases k with
  | zero =>
      intro z _hz
      have hpositive :
          (0 : Fin 0 -> Real) ∈
            section43TimeStrictPositiveRegion 0 := by
        intro i
        exact Fin.elim0 i
      have hzero :
          osiiPositiveRealTimeEmbed (0 : Fin 0 -> Real) ∈
            (D.stageLevel.stage 0).carrier :=
        (D.canonicalEdges 0).positiveReal_mem_carrier
          (0 : Fin 0 -> Real) hpositive
      have hz_eq :
          z = osiiPositiveRealTimeEmbed (0 : Fin 0 -> Real) :=
        Subsingleton.elim _ _
      rw [hz_eq]
      simpa only [
        vacuumTailProjectionRankNext,
        vacuumTailProjectionRankStageLevel_stage_zero
      ] using hzero
  | succ q =>
      intro z hz
      apply
        D.strictGeneratedMixedTailCarrierAtRank_subset_vacuumTailProjectionRankNext
          R q
      refine ⟨hz.1, ?_⟩
      have harg :
          osiiTimeArgumentVector z = Fin.tail x :=
        Set.mem_singleton_iff.mp hz.2
      have hhead : x 0 = 0 :=
        OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
          (by omega) hx
      have hcons : Fin.cons 0 (Fin.tail x) = x := by
        simpa [hhead] using Fin.cons_self_tail x
      rw [harg, hcons]
      exact hx

end CanonicalGeneratorPointedConvexAtlasStageLevelData

end OSIIChapterV
end OSReconstruction
