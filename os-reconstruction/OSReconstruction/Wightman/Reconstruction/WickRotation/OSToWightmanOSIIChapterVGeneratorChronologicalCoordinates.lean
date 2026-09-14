/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTimeGeometry












noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {k : ℕ}

/-- Real-linear chronological sign reflection.  This is the real form of the
common-to-split coordinate change and is an involution. -/
noncomputable def generatorChronologicalParameterCLE
    (i : GeneratorIndex k) :
    (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearEquiv.piCongrRight fun j =>
    if j < i.toGap then
      ContinuousLinearEquiv.neg ℝ
    else
      ContinuousLinearEquiv.refl ℝ ℝ

@[simp]
theorem generatorChronologicalParameterCLE_apply
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ) :
    generatorChronologicalParameterCLE i ξ =
      generatorChronologicalParameter i ξ := by
  ext j
  by_cases hj : j < i.toGap
  · simp [generatorChronologicalParameterCLE,
      generatorChronologicalParameter,
      GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]
  · simp [generatorChronologicalParameterCLE,
      generatorChronologicalParameter,
      GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]

/-- Complex-linear chronological sign reflection. It is the holomorphic
coordinate change from common physical gaps to one split-native generator
chart. -/
noncomputable def generatorChronologicalParameterComplexCLE
    (i : GeneratorIndex k) :
    OSIITimeGapSpace k ≃L[ℂ] OSIITimeGapSpace k :=
  ContinuousLinearEquiv.piCongrRight fun j =>
    if j < i.toGap then
      ContinuousLinearEquiv.neg ℂ
    else
      ContinuousLinearEquiv.refl ℂ ℂ

/-- The complex chronological change is the complexification of the real
change on positive-real embeddings. -/
@[simp]
theorem generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ) :
    generatorChronologicalParameterComplexCLE i
        (osiiPositiveRealTimeEmbed ξ) =
      osiiPositiveRealTimeEmbed
        (generatorChronologicalParameter i ξ) := by
  ext j
  by_cases hj : j < i.toGap
  · simp [generatorChronologicalParameterComplexCLE,
      generatorChronologicalParameter, osiiPositiveRealTimeEmbed,
      GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]
  · simp [generatorChronologicalParameterComplexCLE,
      generatorChronologicalParameter, osiiPositiveRealTimeEmbed,
      GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]

/-- Chronological sign reflection is an involution. -/
@[simp]
theorem generatorChronologicalParameter_self
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ) :
    generatorChronologicalParameter i
        (generatorChronologicalParameter i ξ) =
      ξ := by
  ext j
  by_cases hj : j < i.toGap
  · simp [generatorChronologicalParameter,
      GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]
  · simp [generatorChronologicalParameter,
      GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]

/-- The chronological change leaves the semigroup bridge in its global
coordinate. -/
@[simp]
theorem generatorChronological_split_fst
    (i : GeneratorIndex k)
    (w : OSIITimeGapSpace k) :
    (i.splitCoordinatesCLM
      (generatorChronologicalParameterComplexCLE i w)).1 =
        w i.bridgeGlobalIndex := by
  have hbridge : ¬i.bridgeGlobalIndex < i.toGap := by
    change ¬i.n - 1 < i.n - 1
    exact lt_irrefl _
  simp [generatorChronologicalParameterComplexCLE, hbridge]

/-- The chronological sign change cancels the negation built into the
split-native reflected-left coordinates. -/
@[simp]
theorem generatorChronological_split_left
    (i : GeneratorIndex k)
    (w : OSIITimeGapSpace k)
    (a : Fin (i.n - 1)) :
    (i.splitCoordinatesCLM
      (generatorChronologicalParameterComplexCLE i w)).2.1 a =
        w (i.leftGlobalIndex a) := by
  have ha : i.leftGlobalIndex a < i.toGap := by
    change (Fin.rev a).val < i.n - 1
    exact (Fin.rev a).isLt
  simp [generatorChronologicalParameterComplexCLE, ha]

/-- The chronological change preserves the right block coordinates. -/
@[simp]
theorem generatorChronological_split_right
    (i : GeneratorIndex k)
    (w : OSIITimeGapSpace k)
    (b : Fin (i.m - 1)) :
    (i.splitCoordinatesCLM
      (generatorChronologicalParameterComplexCLE i w)).2.2 b =
        w (i.rightGlobalIndex b) := by
  have hb : ¬i.rightGlobalIndex b < i.toGap := by
    change ¬i.n + b.val < i.n - 1
    omega
  simp [generatorChronologicalParameterComplexCLE, hb]

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
