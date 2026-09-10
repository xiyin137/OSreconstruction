/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredGeneratedBranch
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedSources
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTargetHubReflectedGramReplacement














noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A strict-positive anchor lying below both a positive-real hub and the
real parts of one right-half-plane target. -/
structure TargetHubHalfAnchorData
    {k : ℕ}
    (hub : Fin k → ℝ)
    (z : OSIITimeGapSpace k) where
  anchor : Fin k → ℝ
  anchor_positive :
    anchor ∈ section43TimeStrictPositiveRegion k
  anchor_le_half_hub :
    ∀ i, anchor i ≤ hub i / 2
  anchor_le_half_target :
    ∀ i, anchor i ≤ (z i).re / 2
  anchor_lt_hub :
    ∀ i, anchor i < hub i
  anchor_lt_target :
    ∀ i, anchor i < (z i).re

/-- The coordinatewise half-minimum is a canonical target-and-hub anchor. -/
def targetHubHalfAnchorData
    {k : ℕ}
    (hub : Fin k → ℝ)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ osiiTimeRightHalfPlane k) :
    TargetHubHalfAnchorData hub z where
  anchor := fun i => min (hub i) (z i).re / 2
  anchor_positive := by
    intro i
    exact div_pos (lt_min (hhub i) (hz i)) (by norm_num)
  anchor_le_half_hub := by
    intro i
    have hmin := min_le_left (hub i) (z i).re
    linarith
  anchor_le_half_target := by
    intro i
    have hmin := min_le_right (hub i) (z i).re
    linarith
  anchor_lt_hub := by
    intro i
    have hhalf :
        min (hub i) (z i).re / 2 ≤ hub i / 2 := by
      have hmin := min_le_left (hub i) (z i).re
      linarith
    linarith [hhub i]
  anchor_lt_target := by
    intro i
    have hhalf :
        min (hub i) (z i).re / 2 ≤ (z i).re / 2 := by
      have hmin := min_le_right (hub i) (z i).re
      linarith
    linarith [hz i]

namespace TargetHubHalfAnchorData

variable {k : ℕ}
  {hub : Fin k → ℝ}
  {z : OSIITimeGapSpace k}

theorem anchor_le_hub
    (D : TargetHubHalfAnchorData hub z)
    (i : Fin k) :
    D.anchor i ≤ hub i :=
  (D.anchor_lt_hub i).le

theorem centeredTarget_mem_rightHalfPlane
    (D : TargetHubHalfAnchorData hub z) :
    z - osiiPositiveRealTimeEmbed D.anchor ∈
      osiiTimeRightHalfPlane k := by
  intro i
  change 0 < (z i).re - D.anchor i
  linarith [D.anchor_lt_target i]

end TargetHubHalfAnchorData

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- The rooted left source-time hub induced by a global positive-real hub. -/
def rootedLeftBlockHub
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ) :
    Fin ((i.n - 1) + 1) → ℝ :=
  Fin.cons
    (hub i.bridgeGlobalIndex / 3)
    (fun a => hub (i.leftGlobalIndex a))

/-- The rooted right source-time hub induced by a global positive-real hub. -/
def rootedRightBlockHub
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ) :
    Fin ((i.m - 1) + 1) → ℝ :=
  Fin.cons
    (hub i.bridgeGlobalIndex / 3)
    (fun b => hub (i.rightGlobalIndex b))

theorem rootedLeftBlockAnchor_le_hub
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ)
    (hanchor_hub : ∀ j, anchor j ≤ hub j) :
    ∀ a, A.rootedLeftBlockAnchor i a ≤
      rootedLeftBlockHub i hub a := by
  intro a
  refine Fin.cases ?_ ?_ a
  · simp only [rootedLeftBlockAnchor, rootedLeftBlockHub,
      Fin.cons_zero]
    linarith [hanchor_hub i.bridgeGlobalIndex]
  · intro b
    simpa [rootedLeftBlockAnchor, rootedLeftBlockHub,
      leftInternalAnchor] using hanchor_hub (i.leftGlobalIndex b)

theorem rootedRightBlockAnchor_le_hub
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ)
    (hanchor_hub : ∀ j, anchor j ≤ hub j) :
    ∀ a, A.rootedRightBlockAnchor i a ≤
      rootedRightBlockHub i hub a := by
  intro a
  refine Fin.cases ?_ ?_ a
  · simp only [rootedRightBlockAnchor, rootedRightBlockHub,
      Fin.cons_zero]
    linarith [hanchor_hub i.bridgeGlobalIndex]
  · intro b
    simpa [rootedRightBlockAnchor, rootedRightBlockHub,
      rightInternalAnchor] using hanchor_hub (i.rightGlobalIndex b)

/-- The physical reflected-left analytic target in one generator split. -/
def rootedLeftBlockTarget
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    Fin (i.n - 1) → ℂ :=
  star
    (i.splitCoordinatesCLM
      (generatorChronologicalParameterComplexCLE i z)).2.1

/-- The physical right analytic target in one generator split. -/
def rootedRightBlockTarget
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    Fin (i.m - 1) → ℂ :=
  (i.splitCoordinatesCLM
    (generatorChronologicalParameterComplexCLE i z)).2.2

@[simp]
theorem rootedLeftBlockTarget_lineMap
    (i : GeneratorIndex k)
    (x y : OSIITimeGapSpace k)
    (t : ℝ) :
    rootedLeftBlockTarget i
        (AffineMap.lineMap (k := ℝ) x y t) =
      AffineMap.lineMap (k := ℝ)
        (rootedLeftBlockTarget i x)
        (rootedLeftBlockTarget i y) t := by
  ext a
  simp [rootedLeftBlockTarget, AffineMap.lineMap_apply,
    generatorChronologicalParameterComplexCLE_real_smul]

@[simp]
theorem rootedRightBlockTarget_lineMap
    (i : GeneratorIndex k)
    (x y : OSIITimeGapSpace k)
    (t : ℝ) :
    rootedRightBlockTarget i
        (AffineMap.lineMap (k := ℝ) x y t) =
      AffineMap.lineMap (k := ℝ)
        (rootedRightBlockTarget i x)
        (rootedRightBlockTarget i y) t := by
  ext b
  simp [rootedRightBlockTarget, AffineMap.lineMap_apply,
    generatorChronologicalParameterComplexCLE_real_smul]

/-- The centered global left coordinate is exactly the tail-anchor centered
physical block target. -/
theorem rootedLeftBlockTarget_centered
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    star
        (i.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE i
            (z - osiiPositiveRealTimeEmbed anchor))).2.1 =
      tailAnchorCenteredPoint
        (A.rootedLeftBlockAnchor i)
        (rootedLeftBlockTarget i z) := by
  ext a
  simp [rootedLeftBlockTarget, tailAnchorCenteredPoint,
    rootedLeftBlockAnchor, leftInternalAnchor,
    osiiPositiveRealTimeEmbed]

/-- The centered global right coordinate is exactly the tail-anchor centered
physical block target. -/
theorem rootedRightBlockTarget_centered
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    (i.splitCoordinatesCLM
        (generatorChronologicalParameterComplexCLE i
          (z - osiiPositiveRealTimeEmbed anchor))).2.2 =
      tailAnchorCenteredPoint
        (A.rootedRightBlockAnchor i)
        (rootedRightBlockTarget i z) := by
  ext b
  simp [rootedRightBlockTarget, tailAnchorCenteredPoint,
    rootedRightBlockAnchor, rightInternalAnchor,
    osiiPositiveRealTimeEmbed]

/-- The centered global positive-real hub agrees with the reflected-left
block hub point used by the adapted atlas. -/
theorem rootedLeftBlockHub_centered
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ) :
    star
        (i.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE i
            (osiiPositiveRealTimeEmbed hub -
              osiiPositiveRealTimeEmbed anchor))).2.1 =
      tailAnchorCenteredHubPoint
        (A.rootedLeftBlockAnchor i)
        (rootedLeftBlockHub i hub) := by
  ext a
  simp [tailAnchorCenteredHubPoint, tailAnchorCenteredPoint,
    rootedLeftBlockAnchor, rootedLeftBlockHub, leftInternalAnchor,
    osiiPositiveRealTimeEmbed]

/-- The centered global positive-real hub agrees with the right block hub
point used by the adapted atlas. -/
theorem rootedRightBlockHub_centered
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ) :
    (i.splitCoordinatesCLM
        (generatorChronologicalParameterComplexCLE i
          (osiiPositiveRealTimeEmbed hub -
            osiiPositiveRealTimeEmbed anchor))).2.2 =
      tailAnchorCenteredHubPoint
        (A.rootedRightBlockAnchor i)
        (rootedRightBlockHub i hub) := by
  ext b
  simp [tailAnchorCenteredHubPoint, tailAnchorCenteredPoint,
    rootedRightBlockAnchor, rootedRightBlockHub, rightInternalAnchor,
    osiiPositiveRealTimeEmbed]

/-- The rooted left centered coordinate sends the global hub-to-target line
map to the corresponding tail-anchor centered line map, with the same
parameter. -/
theorem rootedLeftCenteredParameter_lineMap
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k)
    (t : Real) :
    (fun a =>
      -star
        ((generatorChronologicalParameterComplexCLE i
          (AffineMap.lineMap (k := Real)
              (osiiPositiveRealTimeEmbed hub) z t -
            osiiPositiveRealTimeEmbed anchor))
          (i.leftGlobalIndex a))) =
      AffineMap.lineMap (k := Real)
        (tailAnchorCenteredHubPoint
          (A.rootedLeftBlockAnchor i) (rootedLeftBlockHub i hub))
        (tailAnchorCenteredPoint
          (A.rootedLeftBlockAnchor i) (rootedLeftBlockTarget i z)) t := by
  have hcenter :
      AffineMap.lineMap (k := Real)
          (osiiPositiveRealTimeEmbed hub) z t -
          osiiPositiveRealTimeEmbed anchor =
        AffineMap.lineMap (k := Real)
          (osiiPositiveRealTimeEmbed hub -
            osiiPositiveRealTimeEmbed anchor)
          (z - osiiPositiveRealTimeEmbed anchor) t := by
    ext j
    simp [AffineMap.lineMap_apply_module, osiiPositiveRealTimeEmbed]
    ring
  rw [hcenter]
  change
    rootedLeftBlockTarget i
        (AffineMap.lineMap (k := Real)
          (osiiPositiveRealTimeEmbed hub -
            osiiPositiveRealTimeEmbed anchor)
          (z - osiiPositiveRealTimeEmbed anchor) t) = _
  rw [rootedLeftBlockTarget_lineMap]
  have hhub :
      rootedLeftBlockTarget i
          (osiiPositiveRealTimeEmbed hub -
            osiiPositiveRealTimeEmbed anchor) =
        tailAnchorCenteredHubPoint
          (A.rootedLeftBlockAnchor i) (rootedLeftBlockHub i hub) := by
    change
      star
          (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i
              (osiiPositiveRealTimeEmbed hub -
                osiiPositiveRealTimeEmbed anchor))).2.1 = _
    exact A.rootedLeftBlockHub_centered i hub
  have htarget :
      rootedLeftBlockTarget i
          (z - osiiPositiveRealTimeEmbed anchor) =
        tailAnchorCenteredPoint
          (A.rootedLeftBlockAnchor i) (rootedLeftBlockTarget i z) := by
    change
      star
          (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i
              (z - osiiPositiveRealTimeEmbed anchor))).2.1 = _
    exact A.rootedLeftBlockTarget_centered i z
  rw [hhub, htarget]

/-- Every point of the centered left tail segment comes from the global
hub-to-target segment with the same affine parameter. -/
theorem exists_globalSegment_of_mem_rootedLeftTailAnchorSegment
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k)
    {point : Fin (i.n - 1) -> Complex}
    (hpoint :
      point ∈
        segment Real
          (tailAnchorCenteredHubPoint
            (A.rootedLeftBlockAnchor i) (rootedLeftBlockHub i hub))
          (tailAnchorCenteredPoint
            (A.rootedLeftBlockAnchor i) (rootedLeftBlockTarget i z))) :
    exists w,
      w ∈ segment Real (osiiPositiveRealTimeEmbed hub) z ∧
      (fun a =>
        -star
          ((generatorChronologicalParameterComplexCLE i
            (w - osiiPositiveRealTimeEmbed anchor))
            (i.leftGlobalIndex a))) = point := by
  rw [segment_eq_image_lineMap] at hpoint
  obtain ⟨t, ht, rfl⟩ := hpoint
  refine
    ⟨AffineMap.lineMap (k := Real)
        (osiiPositiveRealTimeEmbed hub) z t, ?_, ?_⟩
  · rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  · exact A.rootedLeftCenteredParameter_lineMap i hub z t

/-- If both adapted block atlases contain their centered hub-to-target
segments, then the corresponding global segment lies in the rooted radial
chronological generator domain. -/
theorem centeredHub_target_segment_subset_radialChronologicalDomain
    {OS : OsterwalderSchraderAxioms d}
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    (hub anchor : Fin k → ℝ)
    (z : OSIITimeGapSpace k)
    (hbridge_hub :
      anchor i.bridgeGlobalIndex < hub i.bridgeGlobalIndex)
    (hbridge_target :
      anchor i.bridgeGlobalIndex <
        (z i.bridgeGlobalIndex).re)
    (hleft :
      segment ℝ
          (rootedLeftBlockTarget i
            (osiiPositiveRealTimeEmbed hub -
              osiiPositiveRealTimeEmbed anchor))
          (rootedLeftBlockTarget i
            (z - osiiPositiveRealTimeEmbed anchor)) ⊆
        E.radialLeftDomain i)
    (hright :
      segment ℝ
          (rootedRightBlockTarget i
            (osiiPositiveRealTimeEmbed hub -
              osiiPositiveRealTimeEmbed anchor))
          (rootedRightBlockTarget i
            (z - osiiPositiveRealTimeEmbed anchor)) ⊆
        E.radialRightDomain i) :
    segment ℝ
        (osiiPositiveRealTimeEmbed hub -
          osiiPositiveRealTimeEmbed anchor)
        (z - osiiPositiveRealTimeEmbed anchor) ⊆
      E.radialChronologicalDomain i := by
  intro w hw
  rw [segment_eq_image_lineMap] at hw
  rcases hw with ⟨t, ht, rfl⟩
  change
    generatorChronologicalParameterComplexCLE i
        (AffineMap.lineMap (k := ℝ)
          (osiiPositiveRealTimeEmbed hub -
            osiiPositiveRealTimeEmbed anchor)
          (z - osiiPositiveRealTimeEmbed anchor) t) ∈
      E.radialNativeDomain i
  refine ⟨?_, ?_, ?_⟩
  · rw [generatorChronological_split_fst]
    change
      0 <
        ((AffineMap.lineMap (k := ℝ)
          (osiiPositiveRealTimeEmbed hub -
            osiiPositiveRealTimeEmbed anchor)
          (z - osiiPositiveRealTimeEmbed anchor) t)
          i.bridgeGlobalIndex).re
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      Complex.real_smul, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, osiiPositiveRealTimeEmbed]
    rw [show
      t *
            ((z i.bridgeGlobalIndex).re -
              anchor i.bridgeGlobalIndex -
              (hub i.bridgeGlobalIndex -
                anchor i.bridgeGlobalIndex)) +
          (hub i.bridgeGlobalIndex -
            anchor i.bridgeGlobalIndex) =
        (1 - t) *
            (hub i.bridgeGlobalIndex -
              anchor i.bridgeGlobalIndex) +
          t *
            ((z i.bridgeGlobalIndex).re -
              anchor i.bridgeGlobalIndex) by ring]
    by_cases ht0 : t = 0
    · subst t
      simpa using sub_pos.mpr hbridge_hub
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg
          (sub_nonneg.mpr ht.2)
          (sub_pos.mpr hbridge_hub).le)
        (mul_pos
          (lt_of_le_of_ne ht.1 (Ne.symm ht0))
          (sub_pos.mpr hbridge_target))
  · change
      rootedLeftBlockTarget i
          (AffineMap.lineMap (k := ℝ)
            (osiiPositiveRealTimeEmbed hub -
              osiiPositiveRealTimeEmbed anchor)
            (z - osiiPositiveRealTimeEmbed anchor) t) ∈
        E.radialLeftDomain i
    rw [rootedLeftBlockTarget_lineMap]
    apply hleft
    rw [segment_eq_image_lineMap]
    exact Set.mem_image_of_mem _ ht
  · change
      rootedRightBlockTarget i
          (AffineMap.lineMap (k := ℝ)
            (osiiPositiveRealTimeEmbed hub -
              osiiPositiveRealTimeEmbed anchor)
            (z - osiiPositiveRealTimeEmbed anchor) t) ∈
        E.radialRightDomain i
    rw [rootedRightBlockTarget_lineMap]
    apply hright
    rw [segment_eq_image_lineMap]
    exact Set.mem_image_of_mem _ ht

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
