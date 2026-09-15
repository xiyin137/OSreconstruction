/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRadialFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedVacuumTail
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedOpenBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubDirectExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubPointedDirectExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRadialStageExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVanishingAnchorStageExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOpenFieldScales
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

set_option maxHeartbeats 800000 in
/-- Two rank-`rank` target-and-hub requests on one compact carrier admit one
common universal atlas. -/
theorem
    nonempty_pairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData_of_strictGeneratedAtRank
    {q depth rank : Nat}
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor₁ :
      anchor₁ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₁ :
      ∀ tau ∈ K, ∀ i, anchor₁ i <= tau i)
    (hub₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₁ : forall i, anchor₁ i <= hub₁ i)
    (z₁ : Fin (q + 1) -> Complex)
    (hz₁ :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (anchor₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor₂ :
      anchor₂ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₂ :
      ∀ tau ∈ K, ∀ i, anchor₂ i <= tau i)
    (hub₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₂ : forall i, anchor₂ i <= hub₂ i)
    (z₂ : Fin (q + 1) -> Complex)
    (hz₂ :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (L.reflectedPairStage (q := q)).carrier) :
    Nonempty
      (PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor₁ hub₁ z₁ anchor₂ hub₂ z₂) := by
  obtain ⟨R₁⟩ :=
    nonempty_tailAnchorTargetHubBoxTimeRegionData_of_sourceCarrier_strictGeneratedAtRank
      (L.reflectedPairStage (q := q)) hscalar hanchor₁
      hanchor_hub₁ hz₁ K hK_compact hK_lower₁
  obtain ⟨R₂⟩ :=
    nonempty_tailAnchorTargetHubBoxTimeRegionData_of_sourceCarrier_strictGeneratedAtRank
      (L.reflectedPairStage (q := q)) hscalar hanchor₂
      hanchor_hub₂ hz₂ K hK_compact hK_lower₂
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
  let U := R₁.region ∩ R₂.region
  have hU_open : IsOpen U :=
    R₁.region_open.inter R₂.region_open
  have hU_positive :
      U ⊆ section43TimeStrictPositiveRegion
        ((q + 1) + ((q + 1) + 1)) :=
    inter_subset_left.trans R₁.region_positive
  have hcarrier_U :
      reflectedChronologicalGapCarrier (q + 1) K ⊆ U := by
    intro tau htau
    exact
      ⟨R₁.compactCarrier_subset htau,
        R₂.compactCarrier_subset htau⟩
  obtain ⟨germ, hgerm_region⟩ :=
    exists_uniformCompactTimeMixedReflectedSourceFamilyData_of_sourceCarrier_subset_open
      OS f K hK_compact hK_positive hfK
      U hU_open hU_positive hcarrier_U
  obtain ⟨D, hD_germ⟩ :=
    exists_universalCompactCarrierAnchoredAtlasData_of_germ
      L OS H K hK_compact hK_positive germ
  refine ⟨{
    atlas := D
    firstRegion := R₁
    secondRegion := R₂
    cutoff_support_first := ?_
    cutoff_support_second := ?_ }⟩
  · rw [hD_germ]
    exact hgerm_region.trans inter_subset_left
  · rw [hD_germ]
    exact hgerm_region.trans inter_subset_right

/-- One common ranked target-hub atlas for two requests, with the selected
cutoff retained inside both open rank-successor argument carriers.

This is the equal-source-carrier form needed by rooted generator charts:
choosing two separate cutoffs would overwrite one block when the carrier
entries coincide. -/
structure PairRankSuccessorTargetHubAdaptedAtlasData
    {q depth rank : Nat}
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (anchor₁ hub₁ : Fin ((q + 1) + 1) -> Real)
    (z₁ : Fin (q + 1) -> Complex)
    (anchor₂ hub₂ : Fin ((q + 1) + 1) -> Real)
    (z₂ : Fin (q + 1) -> Complex) where
  current :
    PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      L OS K anchor₁ hub₁ z₁ anchor₂ hub₂ z₂
  firstSuccessorRegion :
    TailAnchorTargetHubBoxReflectedArgumentRegionData
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1))
      anchor₁ hub₁ z₁ (reflectedChronologicalGapCarrier (q + 1) K)
  secondSuccessorRegion :
    TailAnchorTargetHubBoxReflectedArgumentRegionData
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1))
      anchor₂ hub₂ z₂ (reflectedChronologicalGapCarrier (q + 1) K)
  cutoff_support_first_successor :
    tsupport
        (current.atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
      firstSuccessorRegion.region
  cutoff_support_second_successor :
    tsupport
        (current.atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
      secondSuccessorRegion.region

set_option maxHeartbeats 1200000 in
/-- Two current-rank target-hub requests with next-rank membership admit one
common cutoff supported in both successor argument rooms. -/
theorem
    nonempty_pairRankSuccessorTargetHubAdaptedAtlasData_of_strictGeneratedAtRank
    {q depth rank : Nat}
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor₁ :
      anchor₁ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₁ :
      forall tau, tau ∈ K -> forall i, anchor₁ i <= tau i)
    (hub₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₁ : forall i, anchor₁ i <= hub₁ i)
    (z₁ : Fin (q + 1) -> Complex)
    (hz₁_current :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (hz₁_successor :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1)))
    (anchor₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor₂ :
      anchor₂ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₂ :
      forall tau, tau ∈ K -> forall i, anchor₂ i <= tau i)
    (hub₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₂ : forall i, anchor₂ i <= hub₂ i)
    (z₂ : Fin (q + 1) -> Complex)
    (hz₂_current :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (hz₂_successor :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (L.reflectedPairStage (q := q)).carrier) :
    Nonempty
      (PairRankSuccessorTargetHubAdaptedAtlasData
        (q := q) (depth := depth) (rank := rank)
        L OS K anchor₁ hub₁ z₁ anchor₂ hub₂ z₂) := by
  obtain ⟨R₁⟩ :=
    nonempty_tailAnchorTargetHubBoxTimeRegionData_of_sourceCarrier_strictGeneratedAtRank
      (L.reflectedPairStage (q := q)) hscalar hanchor₁
      hanchor_hub₁ hz₁_current K hK_compact hK_lower₁
  obtain ⟨R₂⟩ :=
    nonempty_tailAnchorTargetHubBoxTimeRegionData_of_sourceCarrier_strictGeneratedAtRank
      (L.reflectedPairStage (q := q)) hscalar hanchor₂
      hanchor_hub₂ hz₂_current K hK_compact hK_lower₂
  obtain ⟨Q₁⟩ :=
    nonempty_tailAnchorTargetHubBoxReflectedArgumentRegionData_of_rankSuccessor
      hanchor₁ hanchor_hub₁ hz₁_successor
      (reflectedChronologicalGapCarrier (q + 1) K)
      (isCompact_reflectedChronologicalGapCarrier hK_compact)
      (reflectedChronologicalGapCarrier_dominatesTailAnchor
        hanchor₁ hK_lower₁)
  obtain ⟨Q₂⟩ :=
    nonempty_tailAnchorTargetHubBoxReflectedArgumentRegionData_of_rankSuccessor
      hanchor₂ hanchor_hub₂ hz₂_successor
      (reflectedChronologicalGapCarrier (q + 1) K)
      (isCompact_reflectedChronologicalGapCarrier hK_compact)
      (reflectedChronologicalGapCarrier_dominatesTailAnchor
        hanchor₂ hK_lower₂)
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
  let U :=
    (R₁.region ∩ R₂.region) ∩ (Q₁.region ∩ Q₂.region)
  have hU_open : IsOpen U :=
    (R₁.region_open.inter R₂.region_open).inter
      (Q₁.region_open.inter Q₂.region_open)
  have hU_positive :
      U ⊆ section43TimeStrictPositiveRegion
        ((q + 1) + ((q + 1) + 1)) :=
    inter_subset_left.trans
      (inter_subset_left.trans R₁.region_positive)
  have hcarrier_U :
      reflectedChronologicalGapCarrier (q + 1) K ⊆ U := by
    intro tau htau
    exact
      ⟨⟨R₁.compactCarrier_subset htau,
          R₂.compactCarrier_subset htau⟩,
        ⟨Q₁.compactCarrier_subset htau,
          Q₂.compactCarrier_subset htau⟩⟩
  obtain ⟨germ, hgerm_region⟩ :=
    exists_uniformCompactTimeMixedReflectedSourceFamilyData_of_sourceCarrier_subset_open
      OS f K hK_compact hK_positive hfK
      U hU_open hU_positive hcarrier_U
  obtain ⟨D, hD_germ⟩ :=
    exists_universalCompactCarrierAnchoredAtlasData_of_germ
      L OS H K hK_compact hK_positive germ
  let current :
      PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor₁ hub₁ z₁ anchor₂ hub₂ z₂ := {
      atlas := D
      firstRegion := R₁
      secondRegion := R₂
      cutoff_support_first := by
        rw [hD_germ]
        exact
          hgerm_region.trans
            (inter_subset_left.trans inter_subset_left)
      cutoff_support_second := by
        rw [hD_germ]
        exact
          hgerm_region.trans
            (inter_subset_left.trans inter_subset_right) }
  exact ⟨{
    current := current
    firstSuccessorRegion := Q₁
    secondSuccessorRegion := Q₂
    cutoff_support_first_successor := by
      change
        tsupport
            (D.sourceStage.germ.η :
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
          Q₁.region
      rw [hD_germ]
      exact
        hgerm_region.trans
          (inter_subset_right.trans inter_subset_left)
    cutoff_support_second_successor := by
      change
        tsupport
            (D.sourceStage.germ.η :
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
          Q₂.region
      rw [hD_germ]
      exact
        hgerm_region.trans
          (inter_subset_right.trans inter_subset_right) }⟩

namespace StageWideStrictGeneratedMixedReflectedGramRankData

variable
  {C : Type*}
  [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {depth rank : Nat}

/-- Select one target-and-hub adapted atlas using only the current strict
rank scalar realization. -/
noncomputable def selectedTargetHubAdaptedAtlasAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower : ∀ tau ∈ K, ∀ i, anchor i <= tau i)
    (hub : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank)) :
    TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S) OS K anchor hub z :=
  Classical.choice
    (nonempty_targetHubAdaptedUniversalCompactCarrierAnchoredAtlasData_of_strictGeneratedAtRank
      (q := q) (N := depth) (rank := rank)
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S) OS
      (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
        (OS := OS) S)
      K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz
      (P.scalarStrictGeneratedAtRank
        ((q + 1) + ((q + 1) + 1))))

/-- Select one target-hub atlas while retaining the cutoff's open
rank-successor argument region. -/
noncomputable def selectedRankSuccessorTargetHubAdaptedAtlasAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower : forall tau, tau ∈ K -> forall i, anchor i <= tau i)
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
          ((q + 1) + 1) (depth + 1) (rank + 1))) :
    RankSuccessorTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      (q := q) (depth := depth) (rank := rank)
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S) OS K anchor hub z :=
  Classical.choice
    (nonempty_rankSuccessorTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      (q := q) (depth := depth) (rank := rank)
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S) OS
      (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
        (OS := OS) S)
      K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz_current hz_successor
      (P.scalarStrictGeneratedAtRank
        ((q + 1) + ((q + 1) + 1))))

/-- Forget only the retained successor-room witness while keeping the
corresponding concrete reflected-Gram atlas. -/
noncomputable def rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower : forall tau, tau ∈ K -> forall i, anchor i <= tau i)
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
          ((q + 1) + 1) (depth + 1) (rank + 1))) :
    ReflectedGramAtlasData (OS := OS) S q K where
  atlas :=
    (P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
      q K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz_current hz_successor).current.atlas

/-- Replace one analytic atlas entry by the rank-successor-safe selected
target-hub atlas. -/
noncomputable def rankSuccessorTargetHubAdaptedAtCarrierAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (B : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower : forall tau, tau ∈ K -> forall i, anchor i <= tau i)
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
          ((q + 1) + 1) (depth + 1) (rank + 1))) :
    StageWideReflectedGramAtlasFamilyData (OS := OS) S depth :=
  B.replaceCarrier q K
    (P.rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
      q K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz_current hz_successor)

/-- The rank-successor-safe replacement retains the same centered
hub-to-target segment in its radial zero-convex kernel. -/
theorem
    rankSuccessorTargetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (B : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower : forall tau, tau ∈ K -> forall i, anchor i <= tau i)
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
          ((q + 1) + 1) (depth + 1) (rank + 1))) :
    segment Real
        (tailAnchorCenteredHubPoint anchor hub)
        (tailAnchorCenteredPoint anchor z) ⊆
      openZeroConvexKernel
        ((((P.rankSuccessorTargetHubAdaptedAtCarrierAtRank B
            q K hK_compact hK_positive anchor hanchor hK_lower
            hub hanchor_hub z hz_current hz_successor).forCarrier
          q K hK_compact hK_positive).atlas).spatialLinearDomain) := by
  change
    segment Real
        (tailAnchorCenteredHubPoint anchor hub)
        (tailAnchorCenteredPoint anchor z) ⊆
      openZeroConvexKernel
        ((((B.replaceCarrier q K
          (P.rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
            q K hK_compact hK_positive anchor hanchor hK_lower
            hub hanchor_hub z hz_current hz_successor)).forCarrier
          q K hK_compact hK_positive).atlas).spatialLinearDomain)
  rw [StageWideReflectedGramAtlasFamilyData.replaceCarrier_forCarrier_same]
  simpa [rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank] using
    (P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
      q K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz_current hz_successor
    ).current.centeredHub_target_segment_subset_openZeroConvexKernel

/-- The selected successor argument room remains attached to the concrete
cutoff after replacing one stage-wide atlas entry. -/
theorem
    rankSuccessorTargetHubAdaptedAtCarrierAtRank_cutoff_support_successor
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (B : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower : forall tau, tau ∈ K -> forall i, anchor i <= tau i)
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
          ((q + 1) + 1) (depth + 1) (rank + 1))) :
    tsupport
        (((P.rankSuccessorTargetHubAdaptedAtCarrierAtRank B
            q K hK_compact hK_positive anchor hanchor hK_lower
            hub hanchor_hub z hz_current hz_successor).forCarrier
          q K hK_compact hK_positive).atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
      (P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
        q K hK_compact hK_positive anchor hanchor hK_lower
        hub hanchor_hub z hz_current hz_successor).successorRegion.region := by
  change
    tsupport
        (((B.replaceCarrier q K
          (P.rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
            q K hK_compact hK_positive anchor hanchor hK_lower
            hub hanchor_hub z hz_current hz_successor)).forCarrier
          q K hK_compact hK_positive).atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
      (P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
        q K hK_compact hK_positive anchor hanchor hK_lower
        hub hanchor_hub z hz_current hz_successor).successorRegion.region
  rw [StageWideReflectedGramAtlasFamilyData.replaceCarrier_forCarrier_same]
  simpa [rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank] using
    (P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
      q K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz_current hz_successor
    ).cutoff_support_successor

/-- Forget the geometric witness while retaining the target-adapted analytic
atlas. -/
noncomputable def targetHubAdaptedReflectedGramAtlasAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower : ∀ tau ∈ K, ∀ i, anchor i <= tau i)
    (hub : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank)) :
    ReflectedGramAtlasData (OS := OS) S q K where
  atlas :=
    (P.selectedTargetHubAdaptedAtlasAtRank
      q K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz).atlas

/-- Replace one entry of an arbitrary analytic atlas family by a ranked
target-adapted atlas. -/
noncomputable def targetHubAdaptedAtCarrierAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (B : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower : ∀ tau ∈ K, ∀ i, anchor i <= tau i)
    (hub : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank)) :
    StageWideReflectedGramAtlasFamilyData (OS := OS) S depth :=
  B.replaceCarrier q K
    (P.targetHubAdaptedReflectedGramAtlasAtRank
      q K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz)

/-- The replaced entry contains the complete centered hub-to-target segment
in its radial zero-convex kernel. -/
theorem
    targetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (B : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower : ∀ tau ∈ K, ∀ i, anchor i <= tau i)
    (hub : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank)) :
    segment Real
        (tailAnchorCenteredHubPoint anchor hub)
        (tailAnchorCenteredPoint anchor z) ⊆
      openZeroConvexKernel
        ((((P.targetHubAdaptedAtCarrierAtRank B
            q K hK_compact hK_positive anchor hanchor hK_lower
            hub hanchor_hub z hz).forCarrier
          q K hK_compact hK_positive).atlas).spatialLinearDomain) := by
  change
    segment Real
        (tailAnchorCenteredHubPoint anchor hub)
        (tailAnchorCenteredPoint anchor z) ⊆
      openZeroConvexKernel
        ((((B.replaceCarrier q K
          (P.targetHubAdaptedReflectedGramAtlasAtRank
            q K hK_compact hK_positive anchor hanchor hK_lower
            hub hanchor_hub z hz)).forCarrier
          q K hK_compact hK_positive).atlas).spatialLinearDomain)
  rw [StageWideReflectedGramAtlasFamilyData.replaceCarrier_forCarrier_same]
  simpa [targetHubAdaptedReflectedGramAtlasAtRank] using
    (P.selectedTargetHubAdaptedAtlasAtRank
      q K hK_compact hK_positive anchor hanchor hK_lower
      hub hanchor_hub z hz
    ).centeredHub_target_segment_subset_openZeroConvexKernel

/-- Select one common atlas for two ranked target-and-hub requests on the
same source carrier. -/
noncomputable def selectedPairTargetHubAdaptedAtlasAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor₁ :
      anchor₁ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₁ :
      ∀ tau ∈ K, ∀ i, anchor₁ i <= tau i)
    (hub₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₁ : forall i, anchor₁ i <= hub₁ i)
    (z₁ : Fin (q + 1) -> Complex)
    (hz₁ :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (anchor₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor₂ :
      anchor₂ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₂ :
      ∀ tau ∈ K, ∀ i, anchor₂ i <= tau i)
    (hub₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₂ : forall i, anchor₂ i <= hub₂ i)
    (z₂ : Fin (q + 1) -> Complex)
    (hz₂ :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank)) :
    PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S) OS K
      anchor₁ hub₁ z₁ anchor₂ hub₂ z₂ :=
  Classical.choice
    (nonempty_pairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData_of_strictGeneratedAtRank
      (q := q) (depth := depth) (rank := rank)
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S) OS
      (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
        (OS := OS) S)
      K hK_compact hK_positive
      anchor₁ hanchor₁ hK_lower₁ hub₁ hanchor_hub₁ z₁ hz₁
      anchor₂ hanchor₂ hK_lower₂ hub₂ hanchor_hub₂ z₂ hz₂
      (P.scalarStrictGeneratedAtRank
        ((q + 1) + ((q + 1) + 1))))

/-- Select one common pair atlas while retaining both cutoff successor
argument regions. -/
noncomputable def selectedPairRankSuccessorTargetHubAdaptedAtlasAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor₁ :
      anchor₁ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₁ :
      forall tau, tau ∈ K -> forall i, anchor₁ i <= tau i)
    (hub₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₁ : forall i, anchor₁ i <= hub₁ i)
    (z₁ : Fin (q + 1) -> Complex)
    (hz₁_current :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (hz₁_successor :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1)))
    (anchor₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor₂ :
      anchor₂ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₂ :
      forall tau, tau ∈ K -> forall i, anchor₂ i <= tau i)
    (hub₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₂ : forall i, anchor₂ i <= hub₂ i)
    (z₂ : Fin (q + 1) -> Complex)
    (hz₂_current :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (hz₂_successor :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1))) :
    PairRankSuccessorTargetHubAdaptedAtlasData
      (q := q) (depth := depth) (rank := rank)
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S) OS K
      anchor₁ hub₁ z₁ anchor₂ hub₂ z₂ :=
  Classical.choice
    (nonempty_pairRankSuccessorTargetHubAdaptedAtlasData_of_strictGeneratedAtRank
      (q := q) (depth := depth) (rank := rank)
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S) OS
      (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
        (OS := OS) S)
      K hK_compact hK_positive
      anchor₁ hanchor₁ hK_lower₁ hub₁ hanchor_hub₁
      z₁ hz₁_current hz₁_successor
      anchor₂ hanchor₂ hK_lower₂ hub₂ hanchor_hub₂
      z₂ hz₂_current hz₂_successor
      (P.scalarStrictGeneratedAtRank
        ((q + 1) + ((q + 1) + 1))))

/-- Forget only the pair successor-room witnesses while keeping their shared
concrete reflected-Gram atlas. -/
noncomputable def pairRankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor₁ :
      anchor₁ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₁ :
      forall tau, tau ∈ K -> forall i, anchor₁ i <= tau i)
    (hub₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₁ : forall i, anchor₁ i <= hub₁ i)
    (z₁ : Fin (q + 1) -> Complex)
    (hz₁_current :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (hz₁_successor :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1)))
    (anchor₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor₂ :
      anchor₂ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₂ :
      forall tau, tau ∈ K -> forall i, anchor₂ i <= tau i)
    (hub₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₂ : forall i, anchor₂ i <= hub₂ i)
    (z₂ : Fin (q + 1) -> Complex)
    (hz₂_current :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (hz₂_successor :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1))) :
    ReflectedGramAtlasData (OS := OS) S q K where
  atlas :=
    (P.selectedPairRankSuccessorTargetHubAdaptedAtlasAtRank
      q K hK_compact hK_positive
      anchor₁ hanchor₁ hK_lower₁ hub₁ hanchor_hub₁
      z₁ hz₁_current hz₁_successor
      anchor₂ hanchor₂ hK_lower₂ hub₂ hanchor_hub₂
      z₂ hz₂_current hz₂_successor).current.atlas

/-- Forget a common pair witness while retaining its analytic atlas. -/
noncomputable def pairTargetHubAdaptedReflectedGramAtlasAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (anchor₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor₁ :
      anchor₁ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₁ :
      ∀ tau ∈ K, ∀ i, anchor₁ i <= tau i)
    (hub₁ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₁ : forall i, anchor₁ i <= hub₁ i)
    (z₁ : Fin (q + 1) -> Complex)
    (hz₁ :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank))
    (anchor₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor₂ :
      anchor₂ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK_lower₂ :
      ∀ tau ∈ K, ∀ i, anchor₂ i <= tau i)
    (hub₂ : Fin ((q + 1) + 1) -> Real)
    (hanchor_hub₂ : forall i, anchor₂ i <= hub₂ i)
    (z₂ : Fin (q + 1) -> Complex)
    (hz₂ :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank)) :
    ReflectedGramAtlasData (OS := OS) S q K where
  atlas :=
    (P.selectedPairTargetHubAdaptedAtlasAtRank
      q K hK_compact hK_positive
      anchor₁ hanchor₁ hK_lower₁ hub₁ hanchor_hub₁ z₁ hz₁
      anchor₂ hanchor₂ hK_lower₂ hub₂ hanchor_hub₂ z₂ hz₂).atlas

/-- The payload needed after adapting two ranked rooted carrier entries. -/
structure TwoTargetHubAdaptedAtlasFamilyDataAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q₁ : Nat)
    (K₁ : Set (Fin ((q₁ + 1) + 1) -> Real))
    (hK₁_compact : IsCompact K₁)
    (hK₁_positive :
      K₁ ⊆ section43TimeStrictPositiveRegion ((q₁ + 1) + 1))
    (anchor₁ hub₁ : Fin ((q₁ + 1) + 1) -> Real)
    (z₁ : Fin (q₁ + 1) -> Complex)
    (q₂ : Nat)
    (K₂ : Set (Fin ((q₂ + 1) + 1) -> Real))
    (hK₂_compact : IsCompact K₂)
    (hK₂_positive :
      K₂ ⊆ section43TimeStrictPositiveRegion ((q₂ + 1) + 1))
    (anchor₂ hub₂ : Fin ((q₂ + 1) + 1) -> Real)
    (z₂ : Fin (q₂ + 1) -> Complex) where
  adapted : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth
  first_segment :
    segment Real
        (tailAnchorCenteredHubPoint anchor₁ hub₁)
        (tailAnchorCenteredPoint anchor₁ z₁) ⊆
      openZeroConvexKernel
        (((adapted.forCarrier
          q₁ K₁ hK₁_compact hK₁_positive).atlas).spatialLinearDomain)
  second_segment :
    segment Real
        (tailAnchorCenteredHubPoint anchor₂ hub₂)
        (tailAnchorCenteredPoint anchor₂ z₂) ⊆
      openZeroConvexKernel
        (((adapted.forCarrier
          q₂ K₂ hK₂_compact hK₂_positive).atlas).spatialLinearDomain)

set_option maxHeartbeats 800000 in
/-- Adapt two ranked carrier entries simultaneously, using one common cutoff
when the two requests share the same carrier. -/
theorem nonempty_twoTargetHubAdaptedAtlasFamilyDataAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q₁ : Nat)
    (K₁ : Set (Fin ((q₁ + 1) + 1) -> Real))
    (hK₁_compact : IsCompact K₁)
    (hK₁_positive :
      K₁ ⊆ section43TimeStrictPositiveRegion ((q₁ + 1) + 1))
    (anchor₁ : Fin ((q₁ + 1) + 1) -> Real)
    (hanchor₁ :
      anchor₁ ∈ section43TimeStrictPositiveRegion ((q₁ + 1) + 1))
    (hK₁_lower :
      ∀ tau ∈ K₁, ∀ i, anchor₁ i <= tau i)
    (hub₁ : Fin ((q₁ + 1) + 1) -> Real)
    (hanchor_hub₁ : forall i, anchor₁ i <= hub₁ i)
    (z₁ : Fin (q₁ + 1) -> Complex)
    (hz₁ :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q₁ + 1) + 1) depth rank))
    (q₂ : Nat)
    (K₂ : Set (Fin ((q₂ + 1) + 1) -> Real))
    (hK₂_compact : IsCompact K₂)
    (hK₂_positive :
      K₂ ⊆ section43TimeStrictPositiveRegion ((q₂ + 1) + 1))
    (anchor₂ : Fin ((q₂ + 1) + 1) -> Real)
    (hanchor₂ :
      anchor₂ ∈ section43TimeStrictPositiveRegion ((q₂ + 1) + 1))
    (hK₂_lower :
      ∀ tau ∈ K₂, ∀ i, anchor₂ i <= tau i)
    (hub₂ : Fin ((q₂ + 1) + 1) -> Real)
    (hanchor_hub₂ : forall i, anchor₂ i <= hub₂ i)
    (z₂ : Fin (q₂ + 1) -> Complex)
    (hz₂ :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q₂ + 1) + 1) depth rank)) :
    Nonempty
      (TwoTargetHubAdaptedAtlasFamilyDataAtRank
        P
        q₁ K₁ hK₁_compact hK₁_positive anchor₁ hub₁ z₁
        q₂ K₂ hK₂_compact hK₂_positive anchor₂ hub₂ z₂) := by
  classical
  by_cases hq : q₂ = q₁
  · subst q₂
    by_cases hK : K₂ = K₁
    · subst K₂
      let D :=
        P.selectedPairTargetHubAdaptedAtlasAtRank
          q₁ K₁ hK₁_compact hK₁_positive
          anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁ z₁ hz₁
          anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂ z₂ hz₂
      let G :=
        P.pairTargetHubAdaptedReflectedGramAtlasAtRank
          q₁ K₁ hK₁_compact hK₁_positive
          anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁ z₁ hz₁
          anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂ z₂ hz₂
      let B :=
        P.toAtlasFamily.replaceCarrier q₁ K₁ G
      refine ⟨{
        adapted := B
        first_segment := ?_
        second_segment := ?_ }⟩
      · rw [show
          B.forCarrier q₁ K₁ hK₁_compact hK₁_positive = G by
            simp [B]]
        simpa [G, D,
          pairTargetHubAdaptedReflectedGramAtlasAtRank,
          selectedPairTargetHubAdaptedAtlasAtRank,
          PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData.first] using
          D.first.centeredHub_target_segment_subset_openZeroConvexKernel
      · rw [show
          B.forCarrier q₁ K₁ hK₁_compact hK₁_positive = G by
            simp [B]]
        simpa [G, D,
          pairTargetHubAdaptedReflectedGramAtlasAtRank,
          selectedPairTargetHubAdaptedAtlasAtRank,
          PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData.second] using
          D.second.centeredHub_target_segment_subset_openZeroConvexKernel
    · let B₁ :=
        P.targetHubAdaptedAtCarrierAtRank P.toAtlasFamily
          q₁ K₁ hK₁_compact hK₁_positive
          anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁ z₁ hz₁
      let B₂ :=
        P.targetHubAdaptedAtCarrierAtRank B₁
          q₁ K₂ hK₂_compact hK₂_positive
          anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂ z₂ hz₂
      refine ⟨{
        adapted := B₂
        first_segment := ?_
        second_segment := ?_ }⟩
      · rw [show
          B₂.forCarrier q₁ K₁ hK₁_compact hK₁_positive =
            B₁.forCarrier q₁ K₁ hK₁_compact hK₁_positive by
              simpa [B₂, targetHubAdaptedAtCarrierAtRank] using
                (B₁.replaceCarrier_forCarrier_same_arity_carrier_ne
                  q₁ K₂ K₁
                  (P.targetHubAdaptedReflectedGramAtlasAtRank
                    q₁ K₂ hK₂_compact hK₂_positive
                    anchor₂ hanchor₂ hK₂_lower
                    hub₂ hanchor_hub₂ z₂ hz₂)
                  hK₁_compact hK₁_positive (Ne.symm hK))]
        exact
          P.targetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
            P.toAtlasFamily
            q₁ K₁ hK₁_compact hK₁_positive
            anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁ z₁ hz₁
      · exact
          P.targetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
            B₁ q₁ K₂ hK₂_compact hK₂_positive
            anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂ z₂ hz₂
  · let B₁ :=
      P.targetHubAdaptedAtCarrierAtRank P.toAtlasFamily
        q₁ K₁ hK₁_compact hK₁_positive
        anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁ z₁ hz₁
    let B₂ :=
      P.targetHubAdaptedAtCarrierAtRank B₁
        q₂ K₂ hK₂_compact hK₂_positive
        anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂ z₂ hz₂
    refine ⟨{
      adapted := B₂
      first_segment := ?_
      second_segment := ?_ }⟩
    · rw [show
        B₂.forCarrier q₁ K₁ hK₁_compact hK₁_positive =
          B₁.forCarrier q₁ K₁ hK₁_compact hK₁_positive by
            simpa [B₂, targetHubAdaptedAtCarrierAtRank] using
              (B₁.replaceCarrier_forCarrier_arity_ne
                q₂ K₂
                (P.targetHubAdaptedReflectedGramAtlasAtRank
                  q₂ K₂ hK₂_compact hK₂_positive
                  anchor₂ hanchor₂ hK₂_lower
                  hub₂ hanchor_hub₂ z₂ hz₂)
                q₁ K₁ hK₁_compact hK₁_positive (Ne.symm hq))]
      exact
        P.targetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
          P.toAtlasFamily
          q₁ K₁ hK₁_compact hK₁_positive
          anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁ z₁ hz₁
    · exact
        P.targetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
          B₁ q₂ K₂ hK₂_compact hK₂_positive
          anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂ z₂ hz₂

/-- Two ranked carrier replacements together with the concrete successor
argument rooms retained by their selected cutoffs.

The older two-carrier payload remains useful for pure stage geometry.  This
stronger route-owned package is what normalized envelopes consume: it keeps
the same adapted family while remembering why each nontrivial block has a
compact safe-shift window. -/
structure TwoRankSuccessorTargetHubAdaptedAtlasFamilyDataAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q₁ : Nat)
    (K₁ : Set (Fin ((q₁ + 1) + 1) -> Real))
    (hK₁_compact : IsCompact K₁)
    (hK₁_positive :
      K₁ ⊆ section43TimeStrictPositiveRegion ((q₁ + 1) + 1))
    (anchor₁ hub₁ : Fin ((q₁ + 1) + 1) -> Real)
    (z₁ : Fin (q₁ + 1) -> Complex)
    (q₂ : Nat)
    (K₂ : Set (Fin ((q₂ + 1) + 1) -> Real))
    (hK₂_compact : IsCompact K₂)
    (hK₂_positive :
      K₂ ⊆ section43TimeStrictPositiveRegion ((q₂ + 1) + 1))
    (anchor₂ hub₂ : Fin ((q₂ + 1) + 1) -> Real)
    (z₂ : Fin (q₂ + 1) -> Complex) where
  current :
    TwoTargetHubAdaptedAtlasFamilyDataAtRank
      P
      q₁ K₁ hK₁_compact hK₁_positive anchor₁ hub₁ z₁
      q₂ K₂ hK₂_compact hK₂_positive anchor₂ hub₂ z₂
  firstSuccessorRegion :
    TailAnchorTargetHubBoxReflectedArgumentRegionData
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q₁ + 1) + ((q₁ + 1) + 1)) (depth + 1) (rank + 1))
      anchor₁ hub₁ z₁ (reflectedChronologicalGapCarrier (q₁ + 1) K₁)
  secondSuccessorRegion :
    TailAnchorTargetHubBoxReflectedArgumentRegionData
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q₂ + 1) + ((q₂ + 1) + 1)) (depth + 1) (rank + 1))
      anchor₂ hub₂ z₂ (reflectedChronologicalGapCarrier (q₂ + 1) K₂)
  first_cutoff_support_successor :
    tsupport
        (((current.adapted.forCarrier
          q₁ K₁ hK₁_compact hK₁_positive).atlas.sourceStage.germ.η :
          (Fin ((q₁ + 1) + ((q₁ + 1) + 1)) -> Real) -> Complex)) ⊆
      firstSuccessorRegion.region
  second_cutoff_support_successor :
    tsupport
        (((current.adapted.forCarrier
          q₂ K₂ hK₂_compact hK₂_positive).atlas.sourceStage.germ.η :
          (Fin ((q₂ + 1) + ((q₂ + 1) + 1)) -> Real) -> Complex)) ⊆
      secondSuccessorRegion.region

set_option maxHeartbeats 1400000 in
/-- Adapt two ranked entries with one successor-safe cutoff per surviving
carrier entry, sharing that cutoff when the requests coincide. -/
theorem nonempty_twoRankSuccessorTargetHubAdaptedAtlasFamilyDataAtRank
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (q₁ : Nat)
    (K₁ : Set (Fin ((q₁ + 1) + 1) -> Real))
    (hK₁_compact : IsCompact K₁)
    (hK₁_positive :
      K₁ ⊆ section43TimeStrictPositiveRegion ((q₁ + 1) + 1))
    (anchor₁ : Fin ((q₁ + 1) + 1) -> Real)
    (hanchor₁ :
      anchor₁ ∈ section43TimeStrictPositiveRegion ((q₁ + 1) + 1))
    (hK₁_lower :
      forall tau, tau ∈ K₁ -> forall i, anchor₁ i <= tau i)
    (hub₁ : Fin ((q₁ + 1) + 1) -> Real)
    (hanchor_hub₁ : forall i, anchor₁ i <= hub₁ i)
    (z₁ : Fin (q₁ + 1) -> Complex)
    (hz₁_current :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q₁ + 1) + 1) depth rank))
    (hz₁_successor :
      z₁ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q₁ + 1) + 1) (depth + 1) (rank + 1)))
    (q₂ : Nat)
    (K₂ : Set (Fin ((q₂ + 1) + 1) -> Real))
    (hK₂_compact : IsCompact K₂)
    (hK₂_positive :
      K₂ ⊆ section43TimeStrictPositiveRegion ((q₂ + 1) + 1))
    (anchor₂ : Fin ((q₂ + 1) + 1) -> Real)
    (hanchor₂ :
      anchor₂ ∈ section43TimeStrictPositiveRegion ((q₂ + 1) + 1))
    (hK₂_lower :
      forall tau, tau ∈ K₂ -> forall i, anchor₂ i <= tau i)
    (hub₂ : Fin ((q₂ + 1) + 1) -> Real)
    (hanchor_hub₂ : forall i, anchor₂ i <= hub₂ i)
    (z₂ : Fin (q₂ + 1) -> Complex)
    (hz₂_current :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q₂ + 1) + 1) depth rank))
    (hz₂_successor :
      z₂ ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q₂ + 1) + 1) (depth + 1) (rank + 1))) :
    Nonempty
      (TwoRankSuccessorTargetHubAdaptedAtlasFamilyDataAtRank
        P
        q₁ K₁ hK₁_compact hK₁_positive anchor₁ hub₁ z₁
        q₂ K₂ hK₂_compact hK₂_positive anchor₂ hub₂ z₂) := by
  classical
  by_cases hq : q₂ = q₁
  · subst q₂
    by_cases hK : K₂ = K₁
    · subst K₂
      let D :=
        P.selectedPairRankSuccessorTargetHubAdaptedAtlasAtRank
          q₁ K₁ hK₁_compact hK₁_positive
          anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
          z₁ hz₁_current hz₁_successor
          anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
          z₂ hz₂_current hz₂_successor
      let G :=
        P.pairRankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
          q₁ K₁ hK₁_compact hK₁_positive
          anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
          z₁ hz₁_current hz₁_successor
          anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
          z₂ hz₂_current hz₂_successor
      let B := P.toAtlasFamily.replaceCarrier q₁ K₁ G
      let current :
          TwoTargetHubAdaptedAtlasFamilyDataAtRank
            P
            q₁ K₁ hK₁_compact hK₁_positive anchor₁ hub₁ z₁
            q₁ K₁ hK₂_compact hK₂_positive anchor₂ hub₂ z₂ := {
        adapted := B
        first_segment := by
          rw [show
              B.forCarrier q₁ K₁ hK₁_compact hK₁_positive = G by
                simp [B]]
          simpa [G, D,
            pairRankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank,
            selectedPairRankSuccessorTargetHubAdaptedAtlasAtRank,
            PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData.first] using
            D.current.first.centeredHub_target_segment_subset_openZeroConvexKernel
        second_segment := by
          rw [show
              B.forCarrier q₁ K₁ hK₂_compact hK₂_positive = G by
                simp [B]]
          simpa [G, D,
            pairRankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank,
            selectedPairRankSuccessorTargetHubAdaptedAtlasAtRank,
            PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData.second] using
            D.current.second.centeredHub_target_segment_subset_openZeroConvexKernel }
      exact ⟨{
        current := current
        firstSuccessorRegion := D.firstSuccessorRegion
        secondSuccessorRegion := D.secondSuccessorRegion
        first_cutoff_support_successor := by
          rw [show
              current.adapted.forCarrier
                  q₁ K₁ hK₁_compact hK₁_positive = G by
                simp [current, B]]
          simpa [G, D,
            pairRankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank,
            selectedPairRankSuccessorTargetHubAdaptedAtlasAtRank] using
            D.cutoff_support_first_successor
        second_cutoff_support_successor := by
          rw [show
              current.adapted.forCarrier
                  q₁ K₁ hK₂_compact hK₂_positive = G by
                simp [current, B]]
          simpa [G, D,
            pairRankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank,
            selectedPairRankSuccessorTargetHubAdaptedAtlasAtRank] using
            D.cutoff_support_second_successor }⟩
    · let D1 :=
        P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
          q₁ K₁ hK₁_compact hK₁_positive
          anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
          z₁ hz₁_current hz₁_successor
      let B1 :=
        P.rankSuccessorTargetHubAdaptedAtCarrierAtRank P.toAtlasFamily
          q₁ K₁ hK₁_compact hK₁_positive
          anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
          z₁ hz₁_current hz₁_successor
      let D2 :=
        P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
          q₁ K₂ hK₂_compact hK₂_positive
          anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
          z₂ hz₂_current hz₂_successor
      let B2 :=
        P.rankSuccessorTargetHubAdaptedAtCarrierAtRank B1
          q₁ K₂ hK₂_compact hK₂_positive
          anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
          z₂ hz₂_current hz₂_successor
      let current :
          TwoTargetHubAdaptedAtlasFamilyDataAtRank
            P
            q₁ K₁ hK₁_compact hK₁_positive anchor₁ hub₁ z₁
            q₁ K₂ hK₂_compact hK₂_positive anchor₂ hub₂ z₂ := {
        adapted := B2
        first_segment := by
          rw [show
              B2.forCarrier q₁ K₁ hK₁_compact hK₁_positive =
                B1.forCarrier q₁ K₁ hK₁_compact hK₁_positive by
              simpa [B2, rankSuccessorTargetHubAdaptedAtCarrierAtRank] using
                (B1.replaceCarrier_forCarrier_same_arity_carrier_ne
                  q₁ K₂ K₁
                  (P.rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
                    q₁ K₂ hK₂_compact hK₂_positive
                    anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
                    z₂ hz₂_current hz₂_successor)
                  hK₁_compact hK₁_positive (Ne.symm hK))]
          simpa [B1] using
            P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
              P.toAtlasFamily
              q₁ K₁ hK₁_compact hK₁_positive
              anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
              z₁ hz₁_current hz₁_successor
        second_segment := by
          simpa [B2] using
            P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
              B1 q₁ K₂ hK₂_compact hK₂_positive
              anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
              z₂ hz₂_current hz₂_successor }
      exact ⟨{
        current := current
        firstSuccessorRegion := D1.successorRegion
        secondSuccessorRegion := D2.successorRegion
        first_cutoff_support_successor := by
          rw [show
              current.adapted.forCarrier
                  q₁ K₁ hK₁_compact hK₁_positive =
                B1.forCarrier q₁ K₁ hK₁_compact hK₁_positive by
              simpa [current, B2,
                rankSuccessorTargetHubAdaptedAtCarrierAtRank] using
                (B1.replaceCarrier_forCarrier_same_arity_carrier_ne
                  q₁ K₂ K₁
                  (P.rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
                    q₁ K₂ hK₂_compact hK₂_positive
                    anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
                    z₂ hz₂_current hz₂_successor)
                  hK₁_compact hK₁_positive (Ne.symm hK))]
          simpa [B1, D1] using
            P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_cutoff_support_successor
              P.toAtlasFamily
              q₁ K₁ hK₁_compact hK₁_positive
              anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
              z₁ hz₁_current hz₁_successor
        second_cutoff_support_successor := by
          simpa [current, B2, D2] using
            P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_cutoff_support_successor
              B1 q₁ K₂ hK₂_compact hK₂_positive
              anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
              z₂ hz₂_current hz₂_successor }⟩
  · let D1 :=
      P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
        q₁ K₁ hK₁_compact hK₁_positive
        anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
        z₁ hz₁_current hz₁_successor
    let B1 :=
      P.rankSuccessorTargetHubAdaptedAtCarrierAtRank P.toAtlasFamily
        q₁ K₁ hK₁_compact hK₁_positive
        anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
        z₁ hz₁_current hz₁_successor
    let D2 :=
      P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
        q₂ K₂ hK₂_compact hK₂_positive
        anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
        z₂ hz₂_current hz₂_successor
    let B2 :=
      P.rankSuccessorTargetHubAdaptedAtCarrierAtRank B1
        q₂ K₂ hK₂_compact hK₂_positive
        anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
        z₂ hz₂_current hz₂_successor
    let current :
        TwoTargetHubAdaptedAtlasFamilyDataAtRank
          P
          q₁ K₁ hK₁_compact hK₁_positive anchor₁ hub₁ z₁
          q₂ K₂ hK₂_compact hK₂_positive anchor₂ hub₂ z₂ := {
      adapted := B2
      first_segment := by
        rw [show
            B2.forCarrier q₁ K₁ hK₁_compact hK₁_positive =
              B1.forCarrier q₁ K₁ hK₁_compact hK₁_positive by
            simpa [B2, rankSuccessorTargetHubAdaptedAtCarrierAtRank] using
              (B1.replaceCarrier_forCarrier_arity_ne
                q₂ K₂
                (P.rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
                  q₂ K₂ hK₂_compact hK₂_positive
                  anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
                  z₂ hz₂_current hz₂_successor)
                q₁ K₁ hK₁_compact hK₁_positive (Ne.symm hq))]
        simpa [B1] using
          P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
            P.toAtlasFamily
            q₁ K₁ hK₁_compact hK₁_positive
            anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
            z₁ hz₁_current hz₁_successor
      second_segment := by
        simpa [B2] using
          P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
            B1 q₂ K₂ hK₂_compact hK₂_positive
            anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
            z₂ hz₂_current hz₂_successor }
    exact ⟨{
      current := current
      firstSuccessorRegion := D1.successorRegion
      secondSuccessorRegion := D2.successorRegion
      first_cutoff_support_successor := by
        rw [show
            current.adapted.forCarrier
                q₁ K₁ hK₁_compact hK₁_positive =
              B1.forCarrier q₁ K₁ hK₁_compact hK₁_positive by
            simpa [current, B2,
              rankSuccessorTargetHubAdaptedAtCarrierAtRank] using
              (B1.replaceCarrier_forCarrier_arity_ne
                q₂ K₂
                (P.rankSuccessorTargetHubAdaptedReflectedGramAtlasAtRank
                  q₂ K₂ hK₂_compact hK₂_positive
                  anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
                  z₂ hz₂_current hz₂_successor)
                q₁ K₁ hK₁_compact hK₁_positive (Ne.symm hq))]
        simpa [B1, D1] using
          P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_cutoff_support_successor
            P.toAtlasFamily
            q₁ K₁ hK₁_compact hK₁_positive
            anchor₁ hanchor₁ hK₁_lower hub₁ hanchor_hub₁
            z₁ hz₁_current hz₁_successor
      second_cutoff_support_successor := by
        simpa [current, B2, D2] using
          P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_cutoff_support_successor
            B1 q₂ K₂ hK₂_compact hK₂_positive
            anchor₂ hanchor₂ hK₂_lower hub₂ hanchor_hub₂
            z₂ hz₂_current hz₂_successor }⟩

end StageWideStrictGeneratedMixedReflectedGramRankData

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

/-- The reflected-left block target of one ranked generator chart remains in
the corresponding mixed-tail rank.

The singleton generator carrier fixes the target's principal arguments
exactly.  Removing the mixed head then recovers the left ranked argument
without any additional geometric hypothesis. -/
theorem rootedLeftBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
    {k q m depth rank : Nat}
    (hn : 1 <= q + 2)
    (hm : 1 <= m)
    (hnm : k = q + 2 + m - 1)
    (z : OSIITimeGapSpace k)
    (left : Fin (q + 2) -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed (q + 2) depth left)
    (right : Fin m -> Real)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint
            (⟨q + 2, m, hn, hm, hnm⟩ : GeneratorIndex k)
            left theta right} :
          Set (Fin k -> Real))) :
    rootedLeftBlockTarget
        (⟨q + 2, m, hn, hm, hnm⟩ : GeneratorIndex k) z ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank) := by
  let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let zleft := rootedLeftBlockTarget i z
  have hzleft_exact :
      zleft ∈
        osiiTimeArgumentCarrier
          ({osiiMixedArgumentTail left} :
            Set (Fin (q + 1) -> Real)) := by
    simpa [i, zleft, rootedLeftBlockTarget] using
      star_generatorChronological_split_left_mem_argumentCarrier
        i left theta right hz
  refine ⟨hzleft_exact.1, ?_⟩
  have harg :
      osiiTimeArgumentVector zleft =
        osiiMixedArgumentTail left :=
    Set.mem_singleton_iff.mp hzleft_exact.2
  have hhead : left 0 = 0 :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
      (by omega) hleft
  have hcons :
      Fin.cons 0 (osiiMixedArgumentTail left) = left := by
    simpa [osiiMixedArgumentTail, hhead] using
      Fin.cons_self_tail left
  have hconsarg :
      @Fin.cons (q + 1) (fun _ => Real) 0
          (osiiTimeArgumentVector zleft) =
        @Fin.cons (q + 1) (fun _ => Real) 0
          (osiiMixedArgumentTail left) :=
    congrArg
      (fun v : Fin (q + 1) -> Real =>
        @Fin.cons (q + 1) (fun _ => Real) 0 v) harg
  rw [hconsarg, hcons]
  simpa [i, osiiStrictGeneratedMixedLogarithmicBaseAtRank] using hleft

/-- The right block target of one ranked generator chart remains in the
corresponding mixed-tail rank. -/
theorem rootedRightBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
    {k n q depth rank : Nat}
    (hn : 1 <= n)
    (hm : 1 <= q + 2)
    (hnm : k = n + (q + 2) - 1)
    (z : OSIITimeGapSpace k)
    (left : Fin n -> Real)
    (right : Fin (q + 2) -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed (q + 2) depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint
            (⟨n, q + 2, hn, hm, hnm⟩ : GeneratorIndex k)
            left theta right} :
          Set (Fin k -> Real))) :
    rootedRightBlockTarget
        (⟨n, q + 2, hn, hm, hnm⟩ : GeneratorIndex k) z ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank) := by
  let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
  let zright := rootedRightBlockTarget i z
  have hzright_exact :
      zright ∈
        osiiTimeArgumentCarrier
          ({osiiMixedArgumentTail right} :
            Set (Fin (q + 1) -> Real)) := by
    simpa [i, zright, rootedRightBlockTarget] using
      generatorChronological_split_right_mem_argumentCarrier
        i left theta right hz
  refine ⟨hzright_exact.1, ?_⟩
  have harg :
      osiiTimeArgumentVector zright =
        osiiMixedArgumentTail right :=
    Set.mem_singleton_iff.mp hzright_exact.2
  have hhead : right 0 = 0 :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
      (by omega) hright
  have hcons :
      Fin.cons 0 (osiiMixedArgumentTail right) = right := by
    simpa [osiiMixedArgumentTail, hhead] using
      Fin.cons_self_tail right
  have hconsarg :
      @Fin.cons (q + 1) (fun _ => Real) 0
          (osiiTimeArgumentVector zright) =
        @Fin.cons (q + 1) (fun _ => Real) 0
          (osiiMixedArgumentTail right) :=
    congrArg
      (fun v : Fin (q + 1) -> Real =>
        @Fin.cons (q + 1) (fun _ => Real) 0 v) harg
  rw [hconsarg, hcons]
  simpa [i, osiiStrictGeneratedMixedLogarithmicBaseAtRank] using hright

variable {k : Nat} [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {C : Type*}
  [CanonicalGeneratorStageLevelProvider OS C]
  {ι : Type*}

/-- A rooted target-hub replacement together with the concrete
rank-successor argument rooms retained by every nontrivial block cutoff.

The ordinary rooted replacement is still the analytic payload consumed by
the stage-extension construction.  The extra fields are route-owned
provenance: they remember that the very same selected cutoff lies in an open
next-depth, next-rank argument carrier, which is the input needed for a
compact normalization-shift window.  One-particle blocks contribute no field
because there is no reflected nontrivial source at that side. -/
structure RootedRankSuccessorTargetHubAdaptedReflectedGramData
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k) where
  current :
    RootedTargetHubAdaptedReflectedGramData
      S depth P.toAtlasFamily A R H i hub z
  leftSuccessorRegion : forall
      (q m : Nat) (hn : 1 <= q + 2) (hm : 1 <= m)
      (hnm : k = q + 2 + m - 1)
      (_hi : i = ⟨q + 2, m, hn, hm, hnm⟩),
    let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    TailAnchorTargetHubBoxReflectedArgumentRegionData
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1))
      (A.rootedLeftBlockAnchor j)
      (rootedLeftBlockHub j hub)
      (rootedLeftBlockTarget j z)
      (reflectedChronologicalGapCarrier (q + 1)
        (A.rootedLeftBlockSpatialSourceCarrier R j))
  left_cutoff_support_successor : forall
      (q m : Nat) (hn : 1 <= q + 2) (hm : 1 <= m)
      (hnm : k = q + 2 + m - 1)
      (_hi : i = ⟨q + 2, m, hn, hm, hnm⟩),
    let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    tsupport
        (((current.adapted.forCarrier
          q
          (A.rootedLeftBlockSpatialSourceCarrier R j)
          (A.rootedLeftBlockSpatialSourceCarrier_compact R j)
          (A.rootedLeftBlockSpatialSourceCarrier_positive R j)
        ).atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex)) ⊆
      (leftSuccessorRegion q m hn hm hnm _hi).region
  rightSuccessorRegion : forall
      (n q : Nat) (hn : 1 <= n) (hm : 1 <= q + 2)
      (hnm : k = n + (q + 2) - 1)
      (_hi : i = ⟨n, q + 2, hn, hm, hnm⟩),
    let j : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
    TailAnchorTargetHubBoxReflectedArgumentRegionData
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1))
      (A.rootedRightBlockAnchor j)
      (rootedRightBlockHub j hub)
      (rootedRightBlockTarget j z)
      (reflectedChronologicalGapCarrier (q + 1)
        (A.rootedRightBlockSpatialSourceCarrier R j))
  right_cutoff_support_successor : forall
      (n q : Nat) (hn : 1 <= n) (hm : 1 <= q + 2)
      (hnm : k = n + (q + 2) - 1)
      (_hi : i = ⟨n, q + 2, hn, hm, hnm⟩),
    let j : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
    tsupport
        (((current.adapted.forCarrier
          q
          (A.rootedRightBlockSpatialSourceCarrier R j)
          (A.rootedRightBlockSpatialSourceCarrier_compact R j)
          (A.rootedRightBlockSpatialSourceCarrier_positive R j)
        ).atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex)) ⊆
      (rightSuccessorRegion n q hn hm hnm _hi).region

set_option maxHeartbeats 1200000 in
/-- The successor-safe two-carrier replacement specializes to two nontrivial
rooted blocks of one physical generator split. -/
theorem
    nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_of_nontrivial_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (qleft qright : Nat)
    (hileft : i.n = qleft + 2)
    (hiright : i.m = qright + 2)
    (hub : Fin k -> Real)
    (hanchor_hub : forall j, anchor j <= hub j)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedRankSuccessorTargetHubAdaptedReflectedGramData
        S depth rank P A R H i hub z) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hileft hiright
  subst n
  subst m
  let i : GeneratorIndex k :=
    ⟨qleft + 2, qright + 2, hn, hm, hnm⟩
  let Kleft := A.rootedLeftBlockSpatialSourceCarrier R i
  let Kright := A.rootedRightBlockSpatialSourceCarrier R i
  let zleft := rootedLeftBlockTarget i z
  let zright := rootedRightBlockTarget i z
  have hzleft :
      zleft ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qleft + 1) + 1) depth rank) := by
    simpa [i, zleft] using
      rootedLeftBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
        hn hm hnm z left hleft right theta hz
  have hzleft_successor :
      zleft ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qleft + 1) + 1) (depth + 1) (rank + 1)) := by
    refine ⟨hzleft.1, ?_⟩
    exact
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_depth_succ
        (by omega) hzleft.2).mono (Nat.le_succ rank)
  have hzright :
      zright ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qright + 1) + 1) depth rank) := by
    simpa [i, zright] using
      rootedRightBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
        hn hm hnm z left right hright theta hz
  have hzright_successor :
      zright ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qright + 1) + 1) (depth + 1) (rank + 1)) := by
    refine ⟨hzright.1, ?_⟩
    exact
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_depth_succ
        (by omega) hzright.2).mono (Nat.le_succ rank)
  obtain ⟨D⟩ :=
    P.nonempty_twoRankSuccessorTargetHubAdaptedAtlasFamilyDataAtRank
      qleft Kleft
      (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
      (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i)
      (A.rootedLeftBlockSpatialSourceCarrier_lower R i)
      (rootedLeftBlockHub i hub)
      (A.rootedLeftBlockAnchor_le_hub i hub hanchor_hub)
      zleft hzleft hzleft_successor
      qright Kright
      (A.rootedRightBlockSpatialSourceCarrier_compact R i)
      (A.rootedRightBlockSpatialSourceCarrier_positive R i)
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i)
      (A.rootedRightBlockSpatialSourceCarrier_lower R i)
      (rootedRightBlockHub i hub)
      (A.rootedRightBlockAnchor_le_hub i hub hanchor_hub)
      zright hzright hzright_successor
  let current :
      RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily A R H i hub z := {
    adapted := D.current.adapted
    left_segment := by
      change
        segment Real
            (rootedLeftBlockTarget i
              (osiiPositiveRealTimeEmbed hub -
                osiiPositiveRealTimeEmbed anchor))
            (rootedLeftBlockTarget i
              (z - osiiPositiveRealTimeEmbed anchor)) ⊆
          openZeroConvexKernel
            (((D.current.adapted.forCarrier
              qleft Kleft
              (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
              (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
            ).atlas).spatialLinearDomain)
      simp only [rootedLeftBlockTarget]
      rw [A.rootedLeftBlockHub_centered i hub,
        A.rootedLeftBlockTarget_centered i z]
      simpa [Kleft, zleft] using D.current.first_segment
    right_segment := by
      change
        segment Real
            (rootedRightBlockTarget i
              (osiiPositiveRealTimeEmbed hub -
                osiiPositiveRealTimeEmbed anchor))
            (rootedRightBlockTarget i
              (z - osiiPositiveRealTimeEmbed anchor)) ⊆
          openZeroConvexKernel
            (((D.current.adapted.forCarrier
              qright Kright
              (A.rootedRightBlockSpatialSourceCarrier_compact R i)
              (A.rootedRightBlockSpatialSourceCarrier_positive R i)
            ).atlas).spatialLinearDomain)
      simp only [rootedRightBlockTarget]
      rw [A.rootedRightBlockHub_centered i hub,
        A.rootedRightBlockTarget_centered i z]
      simpa [Kright, zright] using D.current.second_segment }
  refine ⟨{
    current := current
    leftSuccessorRegion := ?_
    left_cutoff_support_successor := ?_
    rightSuccessorRegion := ?_
    right_cutoff_support_successor := ?_ }⟩
  · intro q m hn' hm' hnm' hi
    have hq : q = qleft := by
      have hq' : qleft + 2 = q + 2 :=
        congrArg (fun j : GeneratorIndex k => j.n) hi
      omega
    have hm_eq : m = qright + 2 := by
      have hm' : qright + 2 = m :=
        congrArg (fun j : GeneratorIndex k => j.m) hi
      exact hm'.symm
    subst q
    subst m
    simpa [i, Kleft, zleft] using D.firstSuccessorRegion
  · intro q m hn' hm' hnm' hi
    have hq : q = qleft := by
      have hq' : qleft + 2 = q + 2 :=
        congrArg (fun j : GeneratorIndex k => j.n) hi
      omega
    have hm_eq : m = qright + 2 := by
      have hm' : qright + 2 = m :=
        congrArg (fun j : GeneratorIndex k => j.m) hi
      exact hm'.symm
    subst q
    subst m
    simpa [current, i, Kleft, zleft] using
      D.first_cutoff_support_successor
  · intro n q hn' hm' hnm' hi
    have hn_eq : n = qleft + 2 := by
      have hn' : qleft + 2 = n :=
        congrArg (fun j : GeneratorIndex k => j.n) hi
      exact hn'.symm
    have hq : q = qright := by
      have hq' : qright + 2 = q + 2 :=
        congrArg (fun j : GeneratorIndex k => j.m) hi
      omega
    subst n
    subst q
    simpa [i, Kright, zright] using D.secondSuccessorRegion
  · intro n q hn' hm' hnm' hi
    have hn_eq : n = qleft + 2 := by
      have hn' : qleft + 2 = n :=
        congrArg (fun j : GeneratorIndex k => j.n) hi
      exact hn'.symm
    have hq : q = qright := by
      have hq' : qright + 2 = q + 2 :=
        congrArg (fun j : GeneratorIndex k => j.m) hi
      omega
    subst n
    subst q
    simpa [current, i, Kright, zright] using
      D.second_cutoff_support_successor

set_option maxHeartbeats 1200000 in
/-- If the left block has one particle, retain the successor-safe cutoff only
for the nontrivial right block. -/
theorem
    nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_of_left_one_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hileft : i.n = 1)
    (qright : Nat)
    (hiright : i.m = qright + 2)
    (hub : Fin k -> Real)
    (hanchor_hub : forall j, anchor j <= hub j)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedRankSuccessorTargetHubAdaptedReflectedGramData
        S depth rank P A R H i hub z) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hileft hiright
  subst n
  subst m
  let i : GeneratorIndex k :=
    ⟨1, qright + 2, hn, hm, hnm⟩
  let Kright := A.rootedRightBlockSpatialSourceCarrier R i
  let zright := rootedRightBlockTarget i z
  have hzright :
      zright ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qright + 1) + 1) depth rank) := by
    simpa [i, zright] using
      rootedRightBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
        hn hm hnm z left right hright theta hz
  have hzright_successor :
      zright ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qright + 1) + 1) (depth + 1) (rank + 1)) := by
    refine ⟨hzright.1, ?_⟩
    exact
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_depth_succ
        (by omega) hzright.2).mono (Nat.le_succ rank)
  let E :=
    P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
      qright Kright
      (A.rootedRightBlockSpatialSourceCarrier_compact R i)
      (A.rootedRightBlockSpatialSourceCarrier_positive R i)
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i)
      (A.rootedRightBlockSpatialSourceCarrier_lower R i)
      (rootedRightBlockHub i hub)
      (A.rootedRightBlockAnchor_le_hub i hub hanchor_hub)
      zright hzright hzright_successor
  let adapted :=
    P.rankSuccessorTargetHubAdaptedAtCarrierAtRank P.toAtlasFamily
      qright Kright
      (A.rootedRightBlockSpatialSourceCarrier_compact R i)
      (A.rootedRightBlockSpatialSourceCarrier_positive R i)
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i)
      (A.rootedRightBlockSpatialSourceCarrier_lower R i)
      (rootedRightBlockHub i hub)
      (A.rootedRightBlockAnchor_le_hub i hub hanchor_hub)
      zright hzright hzright_successor
  let current :
      RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily A R H i hub z := {
    adapted := adapted
    left_segment := by
      exact
        subset_radialLeftDomain_of_arity_one
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth adapted A R H)
          i rfl _
    right_segment := by
      change
        segment Real
            (rootedRightBlockTarget i
              (osiiPositiveRealTimeEmbed hub -
                osiiPositiveRealTimeEmbed anchor))
            (rootedRightBlockTarget i
              (z - osiiPositiveRealTimeEmbed anchor)) ⊆
          openZeroConvexKernel
            (((adapted.forCarrier
              qright Kright
              (A.rootedRightBlockSpatialSourceCarrier_compact R i)
              (A.rootedRightBlockSpatialSourceCarrier_positive R i)
            ).atlas).spatialLinearDomain)
      simp only [rootedRightBlockTarget]
      rw [A.rootedRightBlockHub_centered i hub,
        A.rootedRightBlockTarget_centered i z]
      simpa [adapted, Kright, zright] using
        P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
          P.toAtlasFamily
          qright Kright
          (A.rootedRightBlockSpatialSourceCarrier_compact R i)
          (A.rootedRightBlockSpatialSourceCarrier_positive R i)
          (A.rootedRightBlockAnchor i)
          (A.rootedRightBlockAnchor_positive i)
          (A.rootedRightBlockSpatialSourceCarrier_lower R i)
          (rootedRightBlockHub i hub)
          (A.rootedRightBlockAnchor_le_hub i hub hanchor_hub)
          zright hzright hzright_successor }
  refine ⟨{
    current := current
    leftSuccessorRegion := ?_
    left_cutoff_support_successor := ?_
    rightSuccessorRegion := ?_
    right_cutoff_support_successor := ?_ }⟩
  · intro q m hn' hm' hnm' hi
    have hbad : (1 : Nat) = q + 2 := by
      simpa [i] using
        congrArg (fun j : GeneratorIndex k => j.n) hi
    omega
  · intro q m hn' hm' hnm' hi
    have hbad : (1 : Nat) = q + 2 := by
      simpa [i] using
        congrArg (fun j : GeneratorIndex k => j.n) hi
    omega
  · intro n q hn' hm' hnm' hi
    have hn_eq : n = 1 := by
      have hn' : (1 : Nat) = n := by
        simpa [i] using
          congrArg (fun j : GeneratorIndex k => j.n) hi
      exact hn'.symm
    have hq : q = qright := by
      have hq' : qright + 2 = q + 2 := by
        simpa [i] using
          congrArg (fun j : GeneratorIndex k => j.m) hi
      omega
    subst n
    subst q
    simpa [E, i, Kright, zright] using E.successorRegion
  · intro n q hn' hm' hnm' hi
    have hn_eq : n = 1 := by
      have hn' : (1 : Nat) = n := by
        simpa [i] using
          congrArg (fun j : GeneratorIndex k => j.n) hi
      exact hn'.symm
    have hq : q = qright := by
      have hq' : qright + 2 = q + 2 := by
        simpa [i] using
          congrArg (fun j : GeneratorIndex k => j.m) hi
      omega
    subst n
    subst q
    simpa [current, adapted, E, i, Kright, zright] using
      P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_cutoff_support_successor
        P.toAtlasFamily
        qright Kright
        (A.rootedRightBlockSpatialSourceCarrier_compact R i)
        (A.rootedRightBlockSpatialSourceCarrier_positive R i)
        (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor_positive i)
        (A.rootedRightBlockSpatialSourceCarrier_lower R i)
        (rootedRightBlockHub i hub)
        (A.rootedRightBlockAnchor_le_hub i hub hanchor_hub)
        zright hzright hzright_successor

set_option maxHeartbeats 1200000 in
/-- If the right block has one particle, retain the successor-safe cutoff only
for the nontrivial left block. -/
theorem
    nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_of_right_one_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (qleft : Nat)
    (hileft : i.n = qleft + 2)
    (hiright : i.m = 1)
    (hub : Fin k -> Real)
    (hanchor_hub : forall j, anchor j <= hub j)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (right : Fin i.m -> Real)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedRankSuccessorTargetHubAdaptedReflectedGramData
        S depth rank P A R H i hub z) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hileft hiright
  subst n
  subst m
  let i : GeneratorIndex k :=
    ⟨qleft + 2, 1, hn, hm, hnm⟩
  let Kleft := A.rootedLeftBlockSpatialSourceCarrier R i
  let zleft := rootedLeftBlockTarget i z
  have hzleft :
      zleft ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qleft + 1) + 1) depth rank) := by
    simpa [i, zleft] using
      rootedLeftBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
        hn hm hnm z left hleft right theta hz
  have hzleft_successor :
      zleft ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qleft + 1) + 1) (depth + 1) (rank + 1)) := by
    refine ⟨hzleft.1, ?_⟩
    exact
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_depth_succ
        (by omega) hzleft.2).mono (Nat.le_succ rank)
  let E :=
    P.selectedRankSuccessorTargetHubAdaptedAtlasAtRank
      qleft Kleft
      (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
      (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i)
      (A.rootedLeftBlockSpatialSourceCarrier_lower R i)
      (rootedLeftBlockHub i hub)
      (A.rootedLeftBlockAnchor_le_hub i hub hanchor_hub)
      zleft hzleft hzleft_successor
  let adapted :=
    P.rankSuccessorTargetHubAdaptedAtCarrierAtRank P.toAtlasFamily
      qleft Kleft
      (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
      (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i)
      (A.rootedLeftBlockSpatialSourceCarrier_lower R i)
      (rootedLeftBlockHub i hub)
      (A.rootedLeftBlockAnchor_le_hub i hub hanchor_hub)
      zleft hzleft hzleft_successor
  let current :
      RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily A R H i hub z := {
    adapted := adapted
    left_segment := by
      change
        segment Real
            (rootedLeftBlockTarget i
              (osiiPositiveRealTimeEmbed hub -
                osiiPositiveRealTimeEmbed anchor))
            (rootedLeftBlockTarget i
              (z - osiiPositiveRealTimeEmbed anchor)) ⊆
          openZeroConvexKernel
            (((adapted.forCarrier
              qleft Kleft
              (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
              (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
            ).atlas).spatialLinearDomain)
      simp only [rootedLeftBlockTarget]
      rw [A.rootedLeftBlockHub_centered i hub,
        A.rootedLeftBlockTarget_centered i z]
      simpa [adapted, Kleft, zleft] using
        P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
          P.toAtlasFamily
          qleft Kleft
          (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
          (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
          (A.rootedLeftBlockAnchor i)
          (A.rootedLeftBlockAnchor_positive i)
          (A.rootedLeftBlockSpatialSourceCarrier_lower R i)
          (rootedLeftBlockHub i hub)
          (A.rootedLeftBlockAnchor_le_hub i hub hanchor_hub)
          zleft hzleft hzleft_successor
    right_segment := by
      exact
        subset_radialRightDomain_of_arity_one
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth adapted A R H)
          i rfl _ }
  refine ⟨{
    current := current
    leftSuccessorRegion := ?_
    left_cutoff_support_successor := ?_
    rightSuccessorRegion := ?_
    right_cutoff_support_successor := ?_ }⟩
  · intro q m hn' hm' hnm' hi
    have hq : q = qleft := by
      have hq' : qleft + 2 = q + 2 := by
        simpa [i] using
          congrArg (fun j : GeneratorIndex k => j.n) hi
      omega
    have hm_eq : m = 1 := by
      have hm' : (1 : Nat) = m := by
        simpa [i] using
          congrArg (fun j : GeneratorIndex k => j.m) hi
      exact hm'.symm
    subst q
    subst m
    simpa [E, i, Kleft, zleft] using E.successorRegion
  · intro q m hn' hm' hnm' hi
    have hq : q = qleft := by
      have hq' : qleft + 2 = q + 2 := by
        simpa [i] using
          congrArg (fun j : GeneratorIndex k => j.n) hi
      omega
    have hm_eq : m = 1 := by
      have hm' : (1 : Nat) = m := by
        simpa [i] using
          congrArg (fun j : GeneratorIndex k => j.m) hi
      exact hm'.symm
    subst q
    subst m
    simpa [current, adapted, E, i, Kleft, zleft] using
      P.rankSuccessorTargetHubAdaptedAtCarrierAtRank_cutoff_support_successor
        P.toAtlasFamily
        qleft Kleft
        (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
        (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
        (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor_positive i)
        (A.rootedLeftBlockSpatialSourceCarrier_lower R i)
        (rootedLeftBlockHub i hub)
        (A.rootedLeftBlockAnchor_le_hub i hub hanchor_hub)
        zleft hzleft hzleft_successor
  · intro n q hn' hm' hnm' hi
    have hbad : (1 : Nat) = q + 2 := by
      simpa [i] using
        congrArg (fun j : GeneratorIndex k => j.m) hi
    omega
  · intro n q hn' hm' hnm' hi
    have hbad : (1 : Nat) = q + 2 := by
      simpa [i] using
        congrArg (fun j : GeneratorIndex k => j.m) hi
    omega

/-- If both rooted blocks have one particle, there are no nontrivial
reflected sources and hence no successor-shift windows to retain. -/
theorem
    nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_of_both_one_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hileft : i.n = 1)
    (hiright : i.m = 1)
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k) :
    Nonempty
      (RootedRankSuccessorTargetHubAdaptedReflectedGramData
        S depth rank P A R H i hub z) := by
  let current :
      RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily A R H i hub z := {
    adapted := P.toAtlasFamily
    left_segment := by
      exact
        subset_radialLeftDomain_of_arity_one
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth P.toAtlasFamily A R H)
          i hileft _
    right_segment := by
      exact
        subset_radialRightDomain_of_arity_one
          (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
            S depth P.toAtlasFamily A R H)
          i hiright _ }
  refine ⟨{
    current := current
    leftSuccessorRegion := ?_
    left_cutoff_support_successor := ?_
    rightSuccessorRegion := ?_
    right_cutoff_support_successor := ?_ }⟩
  · intro q m hn hm hnm hi
    have hbad : (1 : Nat) = q + 2 := by
      rw [← hileft]
      exact congrArg (fun j : GeneratorIndex k => j.n) hi
    omega
  · intro q m hn hm hnm hi
    have hbad : (1 : Nat) = q + 2 := by
      rw [← hileft]
      exact congrArg (fun j : GeneratorIndex k => j.n) hi
    omega
  · intro n q hn hm hnm hi
    have hbad : (1 : Nat) = q + 2 := by
      rw [← hiright]
      exact congrArg (fun j : GeneratorIndex k => j.m) hi
    omega
  · intro n q hn hm hnm hi
    have hbad : (1 : Nat) = q + 2 := by
      rw [← hiright]
      exact congrArg (fun j : GeneratorIndex k => j.m) hi
    omega

set_option maxHeartbeats 1200000 in
/-- Every strict rank physical generator split admits one rooted replacement
whose nontrivial cutoffs retain their next-rank argument rooms. -/
theorem nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (hanchor_hub : forall j, anchor j <= hub j)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedRankSuccessorTargetHubAdaptedReflectedGramData
        S depth rank P A R H i hub z) := by
  by_cases hleft_one : i.n = 1
  · by_cases hright_one : i.m = 1
    · exact
        nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_of_both_one_atRank
          S depth rank P A R H i hleft_one hright_one hub z
    · obtain ⟨qright, hqright⟩ :
          ∃ qright, i.m = qright + 2 := by
        have hm : 1 <= i.m := i.hm
        refine ⟨i.m - 2, ?_⟩
        omega
      exact
        nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_of_left_one_atRank
          S depth rank P A R H i hleft_one qright hqright
          hub hanchor_hub z left right hright theta hz
  · obtain ⟨qleft, hqleft⟩ :
        ∃ qleft, i.n = qleft + 2 := by
      have hn : 1 <= i.n := i.hn
      refine ⟨i.n - 2, ?_⟩
      omega
    by_cases hright_one : i.m = 1
    · exact
        nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_of_right_one_atRank
          S depth rank P A R H i qleft hqleft hright_one
          hub hanchor_hub z left hleft right theta hz
    · obtain ⟨qright, hqright⟩ :
          ∃ qright, i.m = qright + 2 := by
        have hm : 1 <= i.m := i.hm
        refine ⟨i.m - 2, ?_⟩
        omega
      exact
        nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_of_nontrivial_atRank
          S depth rank P A R H i qleft qright hqleft hqright
          hub hanchor_hub z left hleft right hright theta hz

set_option maxHeartbeats 800000 in
/-- The ranked two-carrier replacement specializes to two nontrivial rooted
blocks of one physical generator split. -/
theorem
    nonempty_rootedTargetHubAdaptedReflectedGramData_of_nontrivial_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (qleft qright : Nat)
    (hileft : i.n = qleft + 2)
    (hiright : i.m = qright + 2)
    (hub : Fin k -> Real)
    (hanchor_hub : forall j, anchor j <= hub j)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily A R H i hub z) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hileft hiright
  subst n
  subst m
  let i : GeneratorIndex k :=
    ⟨qleft + 2, qright + 2, hn, hm, hnm⟩
  let Kleft := A.rootedLeftBlockSpatialSourceCarrier R i
  let Kright := A.rootedRightBlockSpatialSourceCarrier R i
  let zleft := rootedLeftBlockTarget i z
  let zright := rootedRightBlockTarget i z
  have hzleft :
      zleft ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qleft + 1) + 1) depth rank) := by
    simpa [i, zleft] using
      rootedLeftBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
        hn hm hnm z left hleft right theta hz
  have hzright :
      zright ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qright + 1) + 1) depth rank) := by
    simpa [i, zright] using
      rootedRightBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
        hn hm hnm z left right hright theta hz
  obtain ⟨D⟩ :=
    P.nonempty_twoTargetHubAdaptedAtlasFamilyDataAtRank
      qleft Kleft
      (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
      (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i)
      (A.rootedLeftBlockSpatialSourceCarrier_lower R i)
      (rootedLeftBlockHub i hub)
      (A.rootedLeftBlockAnchor_le_hub i hub hanchor_hub)
      zleft hzleft
      qright Kright
      (A.rootedRightBlockSpatialSourceCarrier_compact R i)
      (A.rootedRightBlockSpatialSourceCarrier_positive R i)
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i)
      (A.rootedRightBlockSpatialSourceCarrier_lower R i)
      (rootedRightBlockHub i hub)
      (A.rootedRightBlockAnchor_le_hub i hub hanchor_hub)
      zright hzright
  refine ⟨{
    adapted := D.adapted
    left_segment := ?_
    right_segment := ?_ }⟩
  · change
      segment Real
          (rootedLeftBlockTarget i
            (osiiPositiveRealTimeEmbed hub -
              osiiPositiveRealTimeEmbed anchor))
          (rootedLeftBlockTarget i
            (z - osiiPositiveRealTimeEmbed anchor)) ⊆
        openZeroConvexKernel
          (((D.adapted.forCarrier
            qleft Kleft
            (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
            (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
          ).atlas).spatialLinearDomain)
    simp only [rootedLeftBlockTarget]
    rw [A.rootedLeftBlockHub_centered i hub,
      A.rootedLeftBlockTarget_centered i z]
    simpa [Kleft, zleft] using D.first_segment
  · change
      segment Real
          (rootedRightBlockTarget i
            (osiiPositiveRealTimeEmbed hub -
              osiiPositiveRealTimeEmbed anchor))
          (rootedRightBlockTarget i
            (z - osiiPositiveRealTimeEmbed anchor)) ⊆
        openZeroConvexKernel
          (((D.adapted.forCarrier
            qright Kright
            (A.rootedRightBlockSpatialSourceCarrier_compact R i)
            (A.rootedRightBlockSpatialSourceCarrier_positive R i)
          ).atlas).spatialLinearDomain)
    simp only [rootedRightBlockTarget]
    rw [A.rootedRightBlockHub_centered i hub,
      A.rootedRightBlockTarget_centered i z]
    simpa [Kright, zright] using D.second_segment

set_option maxHeartbeats 800000 in
/-- If the left block has one particle, only the ranked right carrier needs
target adaptation. -/
theorem
    nonempty_rootedTargetHubAdaptedReflectedGramData_of_left_one_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hileft : i.n = 1)
    (qright : Nat)
    (hiright : i.m = qright + 2)
    (hub : Fin k -> Real)
    (hanchor_hub : forall j, anchor j <= hub j)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily A R H i hub z) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hileft hiright
  subst n
  subst m
  let i : GeneratorIndex k :=
    ⟨1, qright + 2, hn, hm, hnm⟩
  let Kright := A.rootedRightBlockSpatialSourceCarrier R i
  let zright := rootedRightBlockTarget i z
  have hzright :
      zright ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qright + 1) + 1) depth rank) := by
    simpa [i, zright] using
      rootedRightBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
        hn hm hnm z left right hright theta hz
  let adapted :=
    P.targetHubAdaptedAtCarrierAtRank P.toAtlasFamily
      qright Kright
      (A.rootedRightBlockSpatialSourceCarrier_compact R i)
      (A.rootedRightBlockSpatialSourceCarrier_positive R i)
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i)
      (A.rootedRightBlockSpatialSourceCarrier_lower R i)
      (rootedRightBlockHub i hub)
      (A.rootedRightBlockAnchor_le_hub i hub hanchor_hub)
      zright hzright
  refine ⟨{
    adapted := adapted
    left_segment := ?_
    right_segment := ?_ }⟩
  · exact
      subset_radialLeftDomain_of_arity_one
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth adapted A R H)
        i rfl _
  · change
      segment Real
          (rootedRightBlockTarget i
            (osiiPositiveRealTimeEmbed hub -
              osiiPositiveRealTimeEmbed anchor))
          (rootedRightBlockTarget i
            (z - osiiPositiveRealTimeEmbed anchor)) ⊆
        openZeroConvexKernel
          (((adapted.forCarrier
            qright Kright
            (A.rootedRightBlockSpatialSourceCarrier_compact R i)
            (A.rootedRightBlockSpatialSourceCarrier_positive R i)
          ).atlas).spatialLinearDomain)
    simp only [rootedRightBlockTarget]
    rw [A.rootedRightBlockHub_centered i hub,
      A.rootedRightBlockTarget_centered i z]
    simpa [adapted, Kright, zright] using
      P.targetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
        P.toAtlasFamily
        qright Kright
        (A.rootedRightBlockSpatialSourceCarrier_compact R i)
        (A.rootedRightBlockSpatialSourceCarrier_positive R i)
        (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor_positive i)
        (A.rootedRightBlockSpatialSourceCarrier_lower R i)
        (rootedRightBlockHub i hub)
        (A.rootedRightBlockAnchor_le_hub i hub hanchor_hub)
        zright hzright

set_option maxHeartbeats 800000 in
/-- If the right block has one particle, only the ranked left carrier needs
target adaptation. -/
theorem
    nonempty_rootedTargetHubAdaptedReflectedGramData_of_right_one_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (qleft : Nat)
    (hileft : i.n = qleft + 2)
    (hiright : i.m = 1)
    (hub : Fin k -> Real)
    (hanchor_hub : forall j, anchor j <= hub j)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (right : Fin i.m -> Real)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily A R H i hub z) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hileft hiright
  subst n
  subst m
  let i : GeneratorIndex k :=
    ⟨qleft + 2, 1, hn, hm, hnm⟩
  let Kleft := A.rootedLeftBlockSpatialSourceCarrier R i
  let zleft := rootedLeftBlockTarget i z
  have hzleft :
      zleft ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((qleft + 1) + 1) depth rank) := by
    simpa [i, zleft] using
      rootedLeftBlockTarget_mem_mixedTailArgumentCarrier_of_ranked_generator
        hn hm hnm z left hleft right theta hz
  let adapted :=
    P.targetHubAdaptedAtCarrierAtRank P.toAtlasFamily
      qleft Kleft
      (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
      (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i)
      (A.rootedLeftBlockSpatialSourceCarrier_lower R i)
      (rootedLeftBlockHub i hub)
      (A.rootedLeftBlockAnchor_le_hub i hub hanchor_hub)
      zleft hzleft
  refine ⟨{
    adapted := adapted
    left_segment := ?_
    right_segment := ?_ }⟩
  · change
      segment Real
          (rootedLeftBlockTarget i
            (osiiPositiveRealTimeEmbed hub -
              osiiPositiveRealTimeEmbed anchor))
          (rootedLeftBlockTarget i
            (z - osiiPositiveRealTimeEmbed anchor)) ⊆
        openZeroConvexKernel
          (((adapted.forCarrier
            qleft Kleft
            (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
            (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
          ).atlas).spatialLinearDomain)
    simp only [rootedLeftBlockTarget]
    rw [A.rootedLeftBlockHub_centered i hub,
      A.rootedLeftBlockTarget_centered i z]
    simpa [adapted, Kleft, zleft] using
      P.targetHubAdaptedAtCarrierAtRank_centeredHub_target_segment_subset
        P.toAtlasFamily
        qleft Kleft
        (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
        (A.rootedLeftBlockSpatialSourceCarrier_positive R i)
        (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor_positive i)
        (A.rootedLeftBlockSpatialSourceCarrier_lower R i)
        (rootedLeftBlockHub i hub)
        (A.rootedLeftBlockAnchor_le_hub i hub hanchor_hub)
        zleft hzleft
  · exact
      subset_radialRightDomain_of_arity_one
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth adapted A R H)
        i rfl _

/-- If both rooted blocks have one particle, the original rank atlas family
already contains both zero-dimensional segments. -/
theorem
    nonempty_rootedTargetHubAdaptedReflectedGramData_of_both_one_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hileft : i.n = 1)
    (hiright : i.m = 1)
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k) :
    Nonempty
      (RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily A R H i hub z) := by
  refine ⟨{
    adapted := P.toAtlasFamily
    left_segment := ?_
    right_segment := ?_ }⟩
  · exact
      subset_radialLeftDomain_of_arity_one
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth P.toAtlasFamily A R H)
        i hileft _
  · exact
      subset_radialRightDomain_of_arity_one
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth P.toAtlasFamily A R H)
        i hiright _

set_option maxHeartbeats 800000 in
/-- Every strict rank physical generator split admits one analytic atlas
family containing both centered hub-to-target rooted block segments. -/
theorem nonempty_rootedTargetHubAdaptedReflectedGramData_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (hanchor_hub : forall j, anchor j <= hub j)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily A R H i hub z) := by
  by_cases hleft_one : i.n = 1
  · by_cases hright_one : i.m = 1
    · exact
        nonempty_rootedTargetHubAdaptedReflectedGramData_of_both_one_atRank
          S depth rank P A R H i hleft_one hright_one hub z
    · obtain ⟨qright, hqright⟩ :
          ∃ qright, i.m = qright + 2 := by
        have hm : 1 <= i.m := i.hm
        refine ⟨i.m - 2, ?_⟩
        omega
      exact
        nonempty_rootedTargetHubAdaptedReflectedGramData_of_left_one_atRank
          S depth rank P A R H i hleft_one qright hqright
          hub hanchor_hub z left right hright theta hz
  · obtain ⟨qleft, hqleft⟩ :
        ∃ qleft, i.n = qleft + 2 := by
      have hn : 1 <= i.n := i.hn
      refine ⟨i.n - 2, ?_⟩
      omega
    by_cases hright_one : i.m = 1
    · exact
        nonempty_rootedTargetHubAdaptedReflectedGramData_of_right_one_atRank
          S depth rank P A R H i qleft hqleft hright_one
          hub hanchor_hub z left hleft right theta hz
    · obtain ⟨qright, hqright⟩ :
          ∃ qright, i.m = qright + 2 := by
        have hm : 1 <= i.m := i.hm
        refine ⟨i.m - 2, ?_⟩
        omega
      exact
        nonempty_rootedTargetHubAdaptedReflectedGramData_of_nontrivial_atRank
          S depth rank P A R H i qleft qright hqleft hqright
          hub hanchor_hub z left hleft right hright theta hz

/-- Provenance retained when a pointed rooted extension is built from one
fixed rooted replacement.

The visible pointed chart hides its private packet choices behind
`RootedAllSplitSourceProvenanceData`.  These equalities make the hiding
reversible for route-owned quantitative arguments, while leaving the public
pointed-extension API unchanged. -/
structure RootedTargetHubPointedDirectExtensionConstructionDataAtRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι)
    (z : OSIITimeGapSpace k)
    (C0 : TargetHubHalfAnchorData hub z)
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackage
        S depth P.toAtlasFamily lgc C0.anchor)
    (D :
      RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily Q.packet Q.roots
          Q.holomorphic.toContinuousTranslationData i hub z) where
  current :
    RootedTargetHubPointedDirectExtensionData
      S depth P.toAtlasFamily lgc i hub z atlas
  current_anchorData_eq : current.anchorData = C0
  current_atlasFamily_eq :
    current.unsmearedSourceProvenance.atlasFamily = D.adapted
  current_approximateIdentity_eq :
    current.unsmearedSourceProvenance.approximateIdentity =
      Q.approximateIdentity
  current_anchor_eq :
    current.unsmearedSourceProvenance.anchor = C0.anchor
  current_packet_heq :
    HEq current.unsmearedSourceProvenance.packet Q.packet
  current_roots_heq :
    HEq current.unsmearedSourceProvenance.roots Q.roots
  current_translation_heq :
    HEq current.unsmearedSourceProvenance.translation
      Q.holomorphic.toContinuousTranslationData
  /-- The selected local extension has exactly the packet-scale branch value
  after the spatial Hermite shell has been completed.  The ordinary pointed
  interface retains only a cofinal two-scale diagonal; the sharp
  equation-`(6.29)` product row needs this iterated-limit identity. -/
  current_packetScaleLimit_eq : forall w, w ∈ current.carrier -> forall chi,
    current.extension.distribution i w chi =
      (rootedReflectedGramPacketScaleBranchLimitData
        S depth D.adapted lgc Q.packet Q.roots Q.holomorphic i chi
      ).limit
        (generatorChronologicalParameterComplexCLE i
          (w - osiiPositiveRealTimeEmbed C0.anchor))
  /-- Eliminate the hidden source provenance as one dependent package.

  The individual equalities above are convenient for ordinary rewriting, but
  packet, roots, translation, and atlas data occur dependently in the
  successor-room witnesses.  This recursor preserves their common origin and
  avoids pretending those fields can be transported independently. -/
  current_sourceProvenance_rec : forall
      (motive : forall
        (I' : Section43ProductTimeApproximateIdentity k)
        (anchor' : Fin k -> Real)
        (A' : AnchoredPacketTimeShellFamilyData (d := d) I' anchor')
        (R' : TripleConvolutionRootData I')
        (_H' : RootedA0BlockContinuousTranslationData OS A' R')
        (_P' : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth),
        Prop),
    motive Q.approximateIdentity C0.anchor Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData D.adapted ->
      motive current.unsmearedSourceProvenance.approximateIdentity
        current.unsmearedSourceProvenance.anchor
        current.unsmearedSourceProvenance.packet
        current.unsmearedSourceProvenance.roots
        current.unsmearedSourceProvenance.translation
        current.unsmearedSourceProvenance.atlasFamily
  /-- Reverse dependent transport from the hidden pointed-extension package
  back to the exact producer retained by this construction record. -/
  current_sourceProvenance_rec_rev : forall
      (motive : forall
        (I' : Section43ProductTimeApproximateIdentity k)
        (anchor' : Fin k -> Real)
        (A' : AnchoredPacketTimeShellFamilyData (d := d) I' anchor')
        (R' : TripleConvolutionRootData I')
        (_H' : RootedA0BlockContinuousTranslationData OS A' R')
        (_P' : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth),
        Prop),
    motive current.unsmearedSourceProvenance.approximateIdentity
        current.unsmearedSourceProvenance.anchor
        current.unsmearedSourceProvenance.packet
        current.unsmearedSourceProvenance.roots
        current.unsmearedSourceProvenance.translation
        current.unsmearedSourceProvenance.atlasFamily ->
      motive Q.approximateIdentity C0.anchor Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData D.adapted

set_option maxHeartbeats 1000000 in
/-- Build the pointed rooted extension from one already selected rooted
target-hub replacement.

Keeping this construction parameterized by the rooted replacement lets later
route-owned packages retain additional provenance about the very same cutoff
without duplicating the analytic extension proof. -/
theorem nonempty_rootedTargetHubPointedDirectExtensionData_of_rootedDataAtRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι)
    (z : OSIITimeGapSpace k)
    (C : TargetHubHalfAnchorData hub z)
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackage
        S depth P.toAtlasFamily lgc C.anchor)
    (D :
      RootedTargetHubAdaptedReflectedGramData
        S depth P.toAtlasFamily Q.packet Q.roots
          Q.holomorphic.toContinuousTranslationData i hub z) :
    Nonempty
      (RootedTargetHubPointedDirectExtensionConstructionDataAtRank
        S depth rank P lgc i hub atlas z C Q D) := by
  let Q' := Q.withStageWideReflectedGram D.adapted
  let core :=
    RelativelyCompactConvexCoreData.selectedOfSegmentSubsetOpen
      (Q'.radialData.radialChronologicalDomain_open i)
      (by
        simpa [Q',
          AnchorLocalRootedReflectedGramRadialProducerPackage.radialData,
          AnchorLocalRootedReflectedGramRadialProducerPackage.withStageWideReflectedGram]
          using
            D.centeredHub_target_segment_subset_radialChronologicalDomain
              (C.anchor_lt_hub i.bridgeGlobalIndex)
              (C.anchor_lt_target i.bridgeGlobalIndex))
  have hanchor_carrier :
      osiiPositiveRealTimeEmbed C.anchor ∈
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k).carrier :=
    (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
      (OS := OS) S k).positiveReal_mem_carrier
        C.anchor C.anchor_positive
  obtain ⟨seedChart, hseed⟩ :=
    Set.mem_iUnion.mp
      (atlas.carrier_subset_iUnion hanchor_carrier)
  let U : Set (Fin k -> Real) :=
    osiiPositiveRealTimeEmbed ⁻¹' atlas.domain seedChart
  have hU_open : IsOpen U :=
    (atlas.domain_open seedChart).preimage
      continuous_osiiPositiveRealTimeEmbed
  have hanchor_U : C.anchor ∈ U := hseed
  obtain ⟨X, hX⟩ :=
    exists_stageMatchedRootedReflectedGramRadialGeneratorData_of_anchor_mem_open
      S depth D.adapted Q.current Q.holomorphic lgc
      U hU_open hanchor_U
  have hedge_subset_atlas :
      forall u, u ∈ X.edge.realRegion ->
        osiiPositiveRealTimeEmbed u ∈
          (atlas.recenter C.anchor).domain seedChart := by
    intro u hu
    change
      osiiPositiveRealTimeEmbed u +
          osiiPositiveRealTimeEmbed C.anchor ∈
        atlas.domain seedChart
    rw [← osiiPositiveRealTimeEmbed_add]
    simpa [U] using hX u hu
  let B : GeneratorSpatialApproximationFamily d k :=
    (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily
      S depth D.adapted lgc Q.packet Q.roots Q.holomorphic).diagonal
  let unsmearedFieldData :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth D.adapted Q.packet Q.roots
        Q.holomorphic.toContinuousTranslationData
  let fieldData :=
    rootedReflectedGramRootSmearedGlobalFamily
      S depth D.adapted lgc Q.packet Q.roots Q.holomorphic
  let F := Q'.radialData
  have hcore_domain : core.carrier ⊆ B.domain i := by
    intro w hw
    change w ∈ F.radialChronologicalDomain i
    exact core.carrier_closure_subset (subset_closure hw)
  let centeredExtension :
      GeneratorStageExtensionData
        ((CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k).recenter C.anchor) :=
    B.toSingleGeneratorStageExtensionDataOfRadialPointedAtlas
      X.edge.toDiagonal F
      (by
        intro j
        rfl)
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter C.anchor)
      (by
        change
          ((CanonicalGeneratorStageLevelProvider.stage
            (OS := OS) S k).recenter C.anchor).HasPositiveRealEdge
              X.edge.orbit X.edge.realRegion
        rw [← X.predecessor_orbit]
        exact X.predecessorEdge.stageEdge)
      (atlas.recenter C.anchor)
      seedChart
      (by
        change
          (0 : OSIITimeGapSpace k) +
              osiiPositiveRealTimeEmbed C.anchor ∈
            atlas.domain seedChart
        simpa using hseed)
      hedge_subset_atlas
      i core.carrier core.carrier_open core.carrier_convex
      hcore_domain
      core.left_mem
  have hcentered_domain :
      centeredExtension.domain i = core.carrier := by
    change
      singleGeneratorChartDomain i core.carrier i =
        core.carrier
    exact singleGeneratorChartDomain_selected i core.carrier
  let absoluteExtension :
      GeneratorStageExtensionData
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k) :=
    centeredExtension.uncenter
  let absoluteCarrier : Set (OSIITimeGapSpace k) :=
    {w |
      w - osiiPositiveRealTimeEmbed C.anchor ∈ core.carrier}
  have habsolute_open : IsOpen absoluteCarrier := by
    exact
      core.carrier_open.preimage
        (continuous_id.sub continuous_const)
  have habsolute_convex : Convex Real absoluteCarrier := by
    change
      Convex Real
        {w |
          w + (-osiiPositiveRealTimeEmbed C.anchor) ∈
            core.carrier}
    exact
      core.carrier_convex.translate_preimage_left
        (-osiiPositiveRealTimeEmbed C.anchor)
  have habsolute_subset :
      absoluteCarrier ⊆ absoluteExtension.domain i := by
    intro w hw
    change w ∈ centeredExtension.uncenter.domain i
    rw [GeneratorStageExtensionData.mem_uncenter_domain_sub]
    rw [hcentered_domain]
    exact hw
  have hhub_absolute :
      osiiPositiveRealTimeEmbed hub ∈ absoluteCarrier := by
    change
      osiiPositiveRealTimeEmbed hub -
          osiiPositiveRealTimeEmbed C.anchor ∈ core.carrier
    exact core.left_mem
  have htarget_absolute : z ∈ absoluteCarrier := by
    change
      z - osiiPositiveRealTimeEmbed C.anchor ∈ core.carrier
    exact core.right_mem
  have hembed_neg :
      osiiPositiveRealTimeEmbed (-C.anchor) =
        -osiiPositiveRealTimeEmbed C.anchor := by
    ext j
    simp [osiiPositiveRealTimeEmbed]
  let E :
      RootedTargetHubPointedDirectExtensionData
        S depth P.toAtlasFamily lgc i hub z atlas := {
      anchorData := C
      extension := absoluteExtension
      carrier := absoluteCarrier
      carrier_open := habsolute_open
      carrier_convex := habsolute_convex
      carrier_subset_extensionDomain := habsolute_subset
      hub_mem_carrier := hhub_absolute
      target_mem_carrier := htarget_absolute
      unsmearedFieldData := unsmearedFieldData
      unsmearedSourceProvenance := {
        atlasFamily := D.adapted
        approximateIdentity := Q.approximateIdentity
        anchor := C.anchor
        packet := Q.packet
        roots := Q.roots
        translation := Q.holomorphic.toContinuousTranslationData
        family_eq := rfl }
      unsmearedSourceProvenance_anchor_eq := rfl
      compactCenteredParameterSet := closure core.carrier
      compactCenteredParameterSet_compact :=
        core.carrier_closure_compact
      carrier_centered_mem_compactParameterSet := by
        intro w hw
        exact subset_closure hw
      compactCenteredParameterSet_parameter_mem_unsmearedRadialNativeDomain := by
        intro v hv
        have hradial : v ∈ F.radialChronologicalDomain i :=
          core.carrier_closure_subset hv
        change
          generatorChronologicalParameterComplexCLE i v ∈
            F.radialNativeDomain i at hradial
        simpa [unsmearedFieldData, F, Q',
          AnchorLocalRootedReflectedGramRadialProducerPackage.radialData,
          AnchorLocalRootedReflectedGramRadialProducerPackage.withStageWideReflectedGram]
          using hradial
      fieldData := fieldData
      fieldData_leftDomain_eq_unsmeared := rfl
      fieldData_rightDomain_eq_unsmeared := rfl
      fieldData_leftField_eq_unsmeared := by
        intro scale mode point
        rfl
      fieldData_rightField_norm_le_unsmeared := by
        intro scale mode point
        exact
          norm_rootSmearedGeneratorOpenHilbertFieldScaleFamilyData_rightField_le
            Q.holomorphic.toContinuousTranslationData lgc
            unsmearedFieldData.toGeneratorOpenHilbertFieldScaleFamilyData
            i scale mode point
      approximation := fun scale w =>
        B.approximation i scale
          (w - osiiPositiveRealTimeEmbed C.anchor)
      approximation_eq_fieldData := by
        intro scale w
        rfl
      approximation_parameter_mem_unsmeared_radialNativeDomain := by
        intro w hw
        have hradial :
            w - osiiPositiveRealTimeEmbed C.anchor ∈
              F.radialChronologicalDomain i :=
          hcore_domain hw
        change
          generatorChronologicalParameterComplexCLE i
              (w - osiiPositiveRealTimeEmbed C.anchor) ∈
            F.radialNativeDomain i at hradial
        simpa [unsmearedFieldData, F, Q',
          AnchorLocalRootedReflectedGramRadialProducerPackage.radialData,
          AnchorLocalRootedReflectedGramRadialProducerPackage.withStageWideReflectedGram]
          using hradial
      approximation_parameter_mem_fieldData_domain := by
        intro w hw
        have hradial :
            w - osiiPositiveRealTimeEmbed C.anchor ∈
              F.radialChronologicalDomain i :=
          hcore_domain hw
        have hdomain :=
          F.radialChronologicalDomain_subset i hradial
        change
          generatorChronologicalParameterComplexCLE i
              (w - osiiPositiveRealTimeEmbed C.anchor) ∈
            unsmearedFieldData.domain i
        simpa [unsmearedFieldData, F, Q',
          AnchorLocalRootedReflectedGramRadialProducerPackage.radialData,
          AnchorLocalRootedReflectedGramRadialProducerPackage.withStageWideReflectedGram]
          using hdomain
      approximation_bridge_positive := by
        intro w hw
        have hradial :
            w - osiiPositiveRealTimeEmbed C.anchor ∈
              F.radialChronologicalDomain i :=
          hcore_domain hw
        change
          generatorChronologicalParameterComplexCLE i
              (w - osiiPositiveRealTimeEmbed C.anchor) ∈
            F.radialNativeDomain i at hradial
        have hbridge := hradial.1
        change
          0 < ((i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i
              (w - osiiPositiveRealTimeEmbed C.anchor))).1).re at hbridge
        simpa only [GeneratorIndex.splitCoordinatesCLM_fst] using hbridge
      approximation_tendsto := by
        intro w hw chi
        have hwcenter :
            w - osiiPositiveRealTimeEmbed C.anchor ∈ core.carrier :=
          hw
        have hwB := hcore_domain hwcenter
        have ht :=
          B.pointwise_tendsto i
            (w - osiiPositiveRealTimeEmbed C.anchor) hwB chi
        have heval :=
          B.distribution_apply_of_mem i
            (w - osiiPositiveRealTimeEmbed C.anchor) hwB chi
        have habsolute :
            absoluteExtension.distribution i w chi =
              B.scalarLimit i
                (w - osiiPositiveRealTimeEmbed C.anchor) chi := by
          change
            centeredExtension.distribution i
                (w + osiiPositiveRealTimeEmbed (-C.anchor)) chi = _
          rw [hembed_neg]
          change
            B.distribution i
                (w - osiiPositiveRealTimeEmbed C.anchor) chi = _
          exact heval
        rw [habsolute]
        exact ht }
  exact ⟨{
    current := E
    current_anchorData_eq := rfl
    current_atlasFamily_eq := rfl
    current_approximateIdentity_eq := rfl
    current_anchor_eq := rfl
    current_packet_heq := HEq.rfl
    current_roots_heq := HEq.rfl
    current_translation_heq := HEq.rfl
    current_packetScaleLimit_eq := by
      intro w hw chi
      have hwcenter :
          w - osiiPositiveRealTimeEmbed C.anchor ∈ core.carrier := hw
      let packetLimit :=
        rootedReflectedGramPacketScaleBranchLimitData
          S depth D.adapted lgc Q.packet Q.roots Q.holomorphic i chi
      have hdistribution :
          centeredExtension.distribution i
              (w - osiiPositiveRealTimeEmbed C.anchor) chi =
            packetLimit.limit
              (generatorChronologicalParameterComplexCLE i
                (w - osiiPositiveRealTimeEmbed C.anchor)) := by
        change B.distribution i
            (w - osiiPositiveRealTimeEmbed C.anchor) chi = _
        rw [B.distribution_apply_of_mem i
          (w - osiiPositiveRealTimeEmbed C.anchor)
          (hcore_domain hwcenter) chi]
        rfl
      change absoluteExtension.distribution i w chi = _
      change centeredExtension.distribution i
          (w + osiiPositiveRealTimeEmbed (-C.anchor)) chi = _
      rw [hembed_neg]
      simpa [packetLimit, sub_eq_add_neg] using hdistribution
    current_sourceProvenance_rec := by
      intro motive h
      exact h
    current_sourceProvenance_rec_rev := by
      intro motive h
      exact h }⟩

/-- Every rank-`rank` generator target admits a genuine pointed
target-and-hub stage extension. -/
theorem nonempty_rootedTargetHubPointedDirectExtensionData_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedTargetHubPointedDirectExtensionData
        S depth P.toAtlasFamily lgc i hub z atlas) := by
  let C := targetHubHalfAnchorData hub hhub z hz.1
  let Q :=
    selectedAnchorLocalRootedReflectedGramRadialProducer
      S depth P.toAtlasFamily lgc C.anchor C.anchor_positive
  obtain ⟨D⟩ :=
    nonempty_rootedTargetHubAdaptedReflectedGramData_atRank
      S depth rank P Q.packet Q.roots
      Q.holomorphic.toContinuousTranslationData
      i hub C.anchor_le_hub z
      left hleft right hright theta hz
  obtain ⟨E⟩ :=
    nonempty_rootedTargetHubPointedDirectExtensionData_of_rootedDataAtRank
      S depth rank P lgc i hub atlas z C Q D
  exact ⟨E.current⟩

/-- One target index for all strict rank-`rank` generator insertions at a
fixed arity and depth. -/
structure RootedStrictGeneratedTargetHubChartAtRank
    (k depth rank : Nat) where
  generator : GeneratorIndex k
  left : Fin generator.n -> Real
  left_rank :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed generator.n depth left
  theta : Real
  angle_bound : |theta| < Real.pi / 2
  right : Fin generator.m -> Real
  right_rank :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed generator.m depth right
  target : OSIITimeGapSpace k
  target_mem :
    target ∈ osiiTimeArgumentCarrier
      ({osiiArgumentGeneratorPoint generator left theta right} :
        Set (Fin k -> Real))

namespace RootedStrictGeneratedTargetHubChartAtRank

end RootedStrictGeneratedTargetHubChartAtRank

/-- Select the pointed rooted extension assigned to one ranked target
chart. -/
noncomputable def selectedRootedTargetHubPointedDirectExtensionAtRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι)
    (a : RootedStrictGeneratedTargetHubChartAtRank k depth rank) :
    RootedTargetHubPointedDirectExtensionData
      S depth P.toAtlasFamily lgc a.generator hub a.target atlas :=
  Classical.choice
    (nonempty_rootedTargetHubPointedDirectExtensionData_atRank
      S depth rank P lgc a.generator hub hhub atlas a.target
      a.left a.left_rank a.right a.right_rank
      a.theta a.target_mem)

/-- The complete pointed convex-core atlas of strict rank-`rank` generator
targets at one positive arity. -/
noncomputable def
    rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι) :
    GeneratorStageExtensionConvexCoreAtlasData
      (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k) where
  chart := RootedStrictGeneratedTargetHubChartAtRank k depth rank
  chartGenerator := fun a => a.generator
  carrier := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRank
      S depth rank P lgc hub hhub atlas a).carrier
  carrier_open := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRank
      S depth rank P lgc hub hhub atlas a).carrier_open
  carrier_convex := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRank
      S depth rank P lgc hub hhub atlas a).carrier_convex
  extension := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRank
      S depth rank P lgc hub hhub atlas a).extension
  carrier_subset_extensionDomain := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRank
      S depth rank P lgc hub hhub atlas a
      ).carrier_subset_extensionDomain
  commonPoint := osiiPositiveRealTimeEmbed hub
  commonPoint_mem_predecessor :=
    (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
      (OS := OS) S k).positiveReal_mem_carrier hub hhub
  commonPoint_mem_carrier := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRank
      S depth rank P lgc hub hhub atlas a).hub_mem_carrier

namespace RootedStrictGeneratedTargetHubPointedConvexCoreAtlasAtRank

variable
  (S : C)
  (depth rank : Nat)
  (P : StageWideStrictGeneratedMixedReflectedGramRankData
    (OS := OS) S depth rank)
  (lgc : OSLinearGrowthCondition d OS)
  (hub : Fin k -> Real)
  (hhub : hub ∈ section43TimeStrictPositiveRegion k)
  (atlas :
    GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) ι)

/-- Pointwise chart selection covers every strict rank generator fiber. -/
theorem argumentGeneratorCarrier_subset_iUnion_carrier
    (i : GeneratorIndex k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right) :
    osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real)) ⊆
      ⋃ a : RootedStrictGeneratedTargetHubChartAtRank k depth rank,
        (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
          S depth rank P lgc hub hhub atlas).carrier a := by
  intro z hz
  let a : RootedStrictGeneratedTargetHubChartAtRank k depth rank :=
    { generator := i
      left := left
      left_rank := hleft
      theta := theta
      angle_bound := htheta
      right := right
      right_rank := hright
      target := z
      target_mem := hz }
  exact
    Set.mem_iUnion_of_mem a
      (selectedRootedTargetHubPointedDirectExtensionAtRank
        S depth rank P lgc hub hhub atlas a).target_mem_carrier

/-- One glued pointed successor contains every strict rank generator fiber. -/
theorem argumentGeneratorCarrier_subset_successorCarrier
    (i : GeneratorIndex k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right) :
    osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real)) ⊆
      (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
        S depth rank P lgc hub hhub atlas).successorStage.carrier :=
  (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
      S depth rank P lgc hub hhub atlas
    ).argumentGeneratorCarrier_subset_successorCarrier
      i left theta right
      (argumentGeneratorCarrier_subset_iUnion_carrier
        S depth rank P lgc hub hhub atlas
        i left hleft theta htheta right hright)

end RootedStrictGeneratedTargetHubPointedConvexCoreAtlasAtRank

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

namespace CanonicalGeneratorPointedConvexAtlasStageLevelData

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

variable
  (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
  (depth rank : Nat)
  (P : StageWideStrictGeneratedMixedReflectedGramRankData
    (OS := OS) D depth rank)
  (lgc : OSLinearGrowthCondition d OS)

/-- The ranked rooted convex-core atlas at one positive arity. -/
noncomputable def rootedInsertionRankConvexCoreAtlas
    (q : Nat) :
    GeneratorStageExtensionConvexCoreAtlasData
      (D.stageLevel.stage (q + 1)) :=
  rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
    D depth rank P lgc
    (D.hub q) (D.hub_positive q) (D.pointedAtlas q)

/-- Retain the zero-gap predecessor and insert all strict rank generator
targets independently at every positive arity. -/
noncomputable def rootedInsertionRankStageLevel :
    SimultaneousTimeContinuationStageLevel d where
  stage
    | 0 => D.stageLevel.stage 0
    | q + 1 => (D.rootedInsertionRankConvexCoreAtlas
        depth rank P lgc q).successorStage

@[simp]
theorem rootedInsertionRankStageLevel_stage_zero :
    (D.rootedInsertionRankStageLevel depth rank P lgc).stage 0 =
      D.stageLevel.stage 0 :=
  rfl

@[simp]
theorem rootedInsertionRankStageLevel_stage_succ
    (q : Nat) :
    (D.rootedInsertionRankStageLevel depth rank P lgc).stage (q + 1) =
      (D.rootedInsertionRankConvexCoreAtlas
        depth rank P lgc q).successorStage :=
  rfl

/-- Every predecessor carrier is retained by ranked rooted insertion. -/
theorem oldCarrier_subset_rootedInsertionRankStageLevel
    (k : Nat) :
    (D.stageLevel.stage k).carrier ⊆
      ((D.rootedInsertionRankStageLevel
        depth rank P lgc).stage k).carrier := by
  cases k with
  | zero =>
      exact Set.Subset.rfl
  | succ q =>
      exact
        (D.rootedInsertionRankConvexCoreAtlas
          depth rank P lgc q).oldCarrier_subset_successorCarrier

/-- Ranked rooted insertion agrees with the predecessor on its complete old
carrier. -/
theorem rootedInsertionRankStageLevel_extends
    (k : Nat) :
    Set.EqOn
      ((D.rootedInsertionRankStageLevel
        depth rank P lgc).stage k).distribution
      (D.stageLevel.stage k).distribution
      (D.stageLevel.stage k).carrier := by
  cases k with
  | zero =>
      exact Set.eqOn_refl _ _
  | succ q =>
      exact
        (D.rootedInsertionRankConvexCoreAtlas
          depth rank P lgc q).successorStage_extends_predecessor

/-- Canonical compact positive-real edges survive ranked rooted insertion. -/
theorem rootedInsertionRankStageLevel_hasCanonicalEdges :
    (D.rootedInsertionRankStageLevel
      depth rank P lgc).HasCanonicalReducedCompactEdges OS := by
  intro k
  cases k with
  | zero =>
      exact D.canonicalEdges 0
  | succ q =>
      exact
        (D.rootedInsertionRankConvexCoreAtlas
          depth rank P lgc q).stageExtensionData
          |>.preservesCanonicalReducedCompactStageEdges
            OS (D.canonicalEdges (q + 1))

/-- Ranked rooted insertion preserves a fixed-hub pointed convex atlas at
every positive arity. -/
noncomputable def rootedInsertionRankNext :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS where
  stageLevel :=
    D.rootedInsertionRankStageLevel depth rank P lgc
  canonicalEdges :=
    D.rootedInsertionRankStageLevel_hasCanonicalEdges
      depth rank P lgc
  chart := fun q =>
    Sum
      (D.chart q)
      (RootedStrictGeneratedTargetHubChartAtRank
        (q + 1) depth rank)
  hub := D.hub
  hub_positive := D.hub_positive
  pointedAtlas := fun q =>
    (D.rootedInsertionRankConvexCoreAtlas
      depth rank P lgc q).successorPointedConvexAtlas
      (D.pointedAtlas q)

/-- Every strict rank generator fiber is contained in the simultaneous
ranked rooted successor. -/
theorem argumentGeneratorCarrier_subset_rootedInsertionRankNext
    (q : Nat)
    (i : GeneratorIndex (q + 1))
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right) :
    osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin (q + 1) -> Real)) ⊆
      ((D.rootedInsertionRankNext
        depth rank P lgc).stageLevel.stage (q + 1)).carrier := by
  exact
    RootedStrictGeneratedTargetHubPointedConvexCoreAtlasAtRank.argumentGeneratorCarrier_subset_successorCarrier
      D depth rank P lgc
      (D.hub q) (D.hub_positive q) (D.pointedAtlas q)
      i left hleft theta htheta right hright

end CanonicalGeneratorPointedConvexAtlasStageLevelData

end OSIIChapterV
end OSReconstruction
