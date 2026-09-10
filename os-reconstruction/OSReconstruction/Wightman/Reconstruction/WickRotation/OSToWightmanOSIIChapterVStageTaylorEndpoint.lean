/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertVectorRealEdge



















open Complex Topology Filter
open scoped BigOperators Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d q : ℕ} [NeZero d]

omit [NeZero d] in
/-- A common real-edge identity on one represented moving-slice chart is the
only source-specific input needed by the prescribed-radius family Cauchy
construction. The scalar boundary bound may depend on the source, while the
radius and complex carrier are common. -/
theorem exists_reflectedCauchyPolydiscFamilyData_of_realEdge_of_radius
    {ι : Type*}
    (A : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (η : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) ℂ)
    (hη_comp :
      HasCompactSupport
        (η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ))
    (R : ℝ)
    (hR : 0 < R)
    (hclosed :
      SCV.closedPolydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => R) ⊆
        reflectedMovingSliceCarrier A η)
    (F : ι → SchwartzNPoint d ((q + 1) + ((q + 1) + 1)))
    (g : ι → (Fin ((q + 1) + (q + 1)) → ℝ) → ℂ)
    (hreal :
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a,
          realAffineSlice
            (reflectedMovingSliceScalar A η (F a)) 0 u =
              g a u) :
    ∃ D : ι → ReflectedCauchyPolydiscData (q + 1),
      (∀ a,
        (D a).center = 0 ∧
          (D a).radius = R ∧
            (SCV.closedPolydisc (D a).center (fun _ => (D a).radius) ⊆
                reflectedMovingSliceCarrier A η) ∧
              DifferentiableOn ℂ (D a).scalar
                (reflectedMovingSliceCarrier A η) ∧
              (D a).scalar =
                reflectedMovingSliceScalar A η (F a)) ∧
        ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
          ∀ a,
            realAffineSlice (D a).scalar (D a).center u =
              g a u := by
  let scalar :
      ι → (Fin ((q + 1) + (q + 1)) → ℂ) → ℂ :=
    fun a => reflectedMovingSliceScalar A η (F a)
  let carrier : Set (Fin ((q + 1) + (q + 1)) → ℂ) :=
    reflectedMovingSliceCarrier A η
  have hscalar :
      ∀ a, DifferentiableOn ℂ (scalar a) carrier := by
    intro a
    exact differentiableOn_reflectedMovingSliceScalar A η (F a) hη_comp
  have hboundary :
      SCV.distinguishedBoundary
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => R) ⊆
        carrier :=
    fun w hw => hclosed (SCV.distinguishedBoundary_subset_closedPolydisc hw)
  have hbound :
      ∀ a, ∃ C : ℝ,
        ∀ w ∈ SCV.distinguishedBoundary
            (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => R),
          ‖scalar a w‖ ≤ C := by
    intro a
    exact
      (SCV.isCompact_distinguishedBoundary :
        IsCompact
          (SCV.distinguishedBoundary
            (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => R)))
        |>.exists_bound_of_continuousOn
          ((hscalar a).continuousOn.mono hboundary)
  choose C hC using hbound
  let D : ι → ReflectedCauchyPolydiscData (q + 1) :=
    fun a =>
      { scalar := scalar a
        center := 0
        radius := R
        bound := max (C a) 0
        radius_pos := hR
        bound_nonneg := le_max_right (C a) 0
        norm_scalar_le := by
          intro w hw
          exact (hC a w hw).trans (le_max_left (C a) 0) }
  refine ⟨D, ?_, ?_⟩
  · intro a
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · simpa [D, carrier] using hclosed
    · simpa [D, scalar, carrier] using hscalar a
    · rfl
  · simpa [D, scalar] using hreal

end OSIIChapterV
end OSReconstruction
