/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTargetHubMovingSliceCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniversalCompactCarrierAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d q : ℕ} [NeZero d]

/-- A universal compact-carrier atlas whose cutoff support preserves the
complete target-and-hub parameter box. -/
structure TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (K : Set (Fin ((q + 1) + 1) → ℝ))
    (anchor hub : Fin ((q + 1) + 1) → ℝ)
    (z : Fin (q + 1) → ℂ) where
  atlas : UniversalCompactCarrierAnchoredAtlasData L OS K
  boxRegion :
    TailAnchorTargetHubBoxTimeRegionData
      (L.reflectedPairStage (q := q)) anchor hub z
      (reflectedChronologicalGapCarrier (q + 1) K)
  cutoff_support_region :
    tsupport
        (atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ) ⊆
      boxRegion.region

namespace TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {K : Set (Fin ((q + 1) + 1) → ℝ)}
  {anchor hub : Fin ((q + 1) + 1) → ℝ}
  {z : Fin (q + 1) → ℂ}

private theorem mul_mem_unitInterval
    {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    a * b ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg ha.1 hb.1
  · calc
      a * b ≤ 1 * b :=
        mul_le_mul_of_nonneg_right ha.2 hb.1
      _ = b := one_mul b
      _ ≤ 1 := hb.2

private theorem lineMap_zero_targetHubBoxPoint
    (u v t : ℝ) :
    AffineMap.lineMap
        (0 : Fin (q + 1) → ℂ)
        (tailAnchorTargetHubBoxPoint anchor hub z u v) t =
      tailAnchorTargetHubBoxPoint anchor hub z
        (t * u) (t * v) := by
  ext i
  simp [AffineMap.lineMap_apply_module,
    tailAnchorTargetHubBoxPoint_apply]
  ring

private theorem lineMap_centeredHub_centeredTarget
    (t : ℝ) :
    AffineMap.lineMap
        (tailAnchorCenteredHubPoint anchor hub)
        (tailAnchorCenteredPoint anchor z) t =
      tailAnchorTargetHubBoxPoint anchor hub z
        (1 - t) t := by
  ext i
  simp [AffineMap.lineMap_apply_module,
    tailAnchorTargetHubBoxPoint_apply,
    tailAnchorCenteredPoint]

set_option maxHeartbeats 800000 in
/-- Every point in the compact target-and-hub parameter box belongs to the
finite-chain reachable anchored domain. -/
theorem boxPoint_mem_reachableAnchoredAtlasCoveredDomain
    (D :
      TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor hub z)
    {u v : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    tailAnchorTargetHubBoxPoint anchor hub z u v ∈
      D.atlas.gram.reachableAnchoredAtlasCoveredDomain
        D.atlas.sourceStage.stage D.atlas.sourceStage.germ := by
  let f :
      UniformCompactTimeSource d ((q + 1) + 1) K →
        euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1) :=
    fun a => UniformCompactTimeSource.source a
  let P :=
    D.atlas.gram.toInitialSourceIndexedReflectedGramHilbertFieldData
      OS f D.atlas.sourceStage.stage D.atlas.sourceStage.germ
  let A₀ :=
    D.atlas.gram.toInitialSourceIndexedAnchoredReflectedGramHilbertFieldData
      D.atlas.sourceStage.stage D.atlas.sourceStage.germ
  have hzero :
      (0 : Fin (q + 1) → ℂ) ∈ P.domain := by
    change
      (0 : Fin (q + 1) → ℂ) ∈
        SCV.Polydisc
          (0 : Fin (q + 1) → ℂ)
          (fun _ => D.atlas.gram.gramRadius)
    exact
      SCV.center_mem_polydisc
        (fun _ => D.atlas.gram.gramRadius_pos)
  have hreflected :
      ∀ center ∈ segment ℝ (0 : Fin (q + 1) → ℂ)
          (tailAnchorTargetHubBoxPoint anchor hub z u v),
        reflectedCauchyCenter center ∈ P.scalarDomain := by
    intro center hcenter
    rw [segment_eq_image_lineMap] at hcenter
    obtain ⟨t, ht, rfl⟩ := hcenter
    rw [lineMap_zero_targetHubBoxPoint]
    change
      reflectedCauchyCenter
          (tailAnchorTargetHubBoxPoint
            anchor hub z (t * u) (t * v)) ∈
        reflectedMovingSliceCarrier
          D.atlas.sourceStage.stage D.atlas.sourceStage.germ.η
    rw [D.atlas.sourceStage_eq]
    exact
      D.boxRegion.reflectedCauchyCenter_box_mem_reflectedMovingSliceCarrier
        D.atlas.sourceStage.germ.η D.cutoff_support_region
        (mul_mem_unitInterval ht hu) (mul_mem_unitInterval ht hv)
  have hanchor :
      ∀ center ∈ segment ℝ (0 : Fin (q + 1) → ℂ)
          (tailAnchorTargetHubBoxPoint anchor hub z u v),
        reflectedAnchorPair (0 : Fin (q + 1) → ℂ) center ∈
          P.scalarDomain := by
    intro center hcenter
    rw [segment_eq_image_lineMap] at hcenter
    obtain ⟨t, ht, rfl⟩ := hcenter
    rw [lineMap_zero_targetHubBoxPoint]
    change
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ)
          (tailAnchorTargetHubBoxPoint
            anchor hub z (t * u) (t * v)) ∈
        reflectedMovingSliceCarrier
          D.atlas.sourceStage.stage D.atlas.sourceStage.germ.η
    rw [D.atlas.sourceStage_eq]
    exact
      D.boxRegion.zeroAnchorPair_box_mem_reflectedMovingSliceCarrier
        D.atlas.sourceStage.germ.η D.cutoff_support_region
        (mul_mem_unitInterval ht hu) (mul_mem_unitInterval ht hv)
  obtain ⟨n, C, Aterminal, htarget_terminal⟩ :=
    SourceIndexedAnchoredReflectedGramContinuationChain.exists_chain_reaching_of_segment_subsets_scalarDomain
      A₀ hzero hreflected hanchor
  exact
    Set.mem_iUnion.mpr
      ⟨{ steps := n, chain := C, anchored := Aterminal }, htarget_terminal⟩

/-- Every reachable target-and-hub box point also belongs to the maximal
anchored atlas used for qualitative gluing. -/
theorem boxPoint_mem_anchoredAtlasCoveredDomain
    (D :
      TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor hub z)
    {u v : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    tailAnchorTargetHubBoxPoint anchor hub z u v ∈
      D.atlas.gram.anchoredAtlasCoveredDomain
        D.atlas.sourceStage.stage D.atlas.sourceStage.germ :=
  D.atlas.gram.reachableAnchoredAtlasCoveredDomain_subset_anchoredAtlasCoveredDomain
    D.atlas.sourceStage.stage D.atlas.sourceStage.germ
    (D.boxPoint_mem_reachableAnchoredAtlasCoveredDomain hu hv)

/-- Every target-and-hub box point belongs to the open source-linear domain
of the selected universal atlas. -/
theorem boxPoint_mem_spatialLinearDomain
    (D :
      TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor hub z)
    {u v : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    tailAnchorTargetHubBoxPoint anchor hub z u v ∈
      D.atlas.spatialLinearDomain := by
  refine ⟨D.boxPoint_mem_anchoredAtlasCoveredDomain hu hv, ?_, ?_⟩
  · change
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ)
          (tailAnchorTargetHubBoxPoint anchor hub z u v) ∈
        reflectedMovingSliceCarrier
          D.atlas.sourceStage.stage D.atlas.sourceStage.germ.η
    rw [D.atlas.sourceStage_eq]
    exact
      D.boxRegion.zeroAnchorPair_box_mem_reflectedMovingSliceCarrier
        D.atlas.sourceStage.germ.η D.cutoff_support_region hu hv
  · change
      reflectedCauchyCenter
          (tailAnchorTargetHubBoxPoint anchor hub z u v) ∈
        reflectedMovingSliceCarrier
          D.atlas.sourceStage.stage D.atlas.sourceStage.germ.η
    rw [D.atlas.sourceStage_eq]
    exact
      D.boxRegion.reflectedCauchyCenter_box_mem_reflectedMovingSliceCarrier
        D.atlas.sourceStage.germ.η D.cutoff_support_region hu hv

/-- Every box point lies in the radial zero-convex kernel of the selected
source-linear domain. -/
theorem boxPoint_mem_openZeroConvexKernel
    (D :
      TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor hub z)
    {u v : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    tailAnchorTargetHubBoxPoint anchor hub z u v ∈
      openZeroConvexKernel D.atlas.spatialLinearDomain := by
  apply mem_openZeroConvexKernel_of_segment_subset
    D.atlas.spatialLinearDomain_open
  intro center hcenter
  have hcenter' :
      center ∈
        AffineMap.lineMap
            (0 : Fin (q + 1) → ℂ)
            (tailAnchorTargetHubBoxPoint anchor hub z u v) ''
          Set.Icc (0 : ℝ) 1 := by
    exact
      (congrArg (fun U => center ∈ U)
        (segment_eq_image_lineMap ℝ
          (0 : Fin (q + 1) → ℂ)
          (tailAnchorTargetHubBoxPoint anchor hub z u v))).mp
        hcenter
  obtain ⟨t, ht, rfl⟩ := hcenter'
  rw [lineMap_zero_targetHubBoxPoint]
  exact
    D.boxPoint_mem_spatialLinearDomain
      (mul_mem_unitInterval ht hu) (mul_mem_unitInterval ht hv)

/-- The complete segment from the centered positive-real hub to the
centered mixed target lies in the rooted radial block domain. -/
theorem centeredHub_target_segment_subset_openZeroConvexKernel
    (D :
      TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor hub z) :
    segment ℝ
        (tailAnchorCenteredHubPoint anchor hub)
        (tailAnchorCenteredPoint anchor z) ⊆
      openZeroConvexKernel D.atlas.spatialLinearDomain := by
  intro center hcenter
  rw [segment_eq_image_lineMap] at hcenter
  obtain ⟨t, ht, rfl⟩ := hcenter
  rw [lineMap_centeredHub_centeredTarget]
  have hone_sub : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩
  exact
    D.boxPoint_mem_openZeroConvexKernel
      hone_sub ht

end TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData

end OSIIChapterV
end OSReconstruction
