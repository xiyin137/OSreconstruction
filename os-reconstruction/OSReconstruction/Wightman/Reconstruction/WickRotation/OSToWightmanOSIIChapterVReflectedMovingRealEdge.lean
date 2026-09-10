import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTranslation

/-!
# OS-II Chapter V Reflected Moving Real Edge

This file identifies the pure-time translation used by the moving-slice chart
with the reflected reduced spacetime displacement. It then transports the
full reflected source through basepoint fiber reduction with the exact sign
needed by the Chapter V real edge.
-/

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

/-- The moving-slice pure-time translation is exactly the spacetime lift of
the reflected reduced time displacement. -/
theorem osiiDifferenceTimeTranslation_reflectedReducedTimeDisplacement
    {d k : ℕ} [NeZero d]
    (u : Fin (k + k) → ℝ) :
    osiiDifferenceTimeTranslation (d := d)
        (reflectedReducedTimeDisplacement u) =
      reflectedReducedSpacetimeDisplacement (d := d) u := by
  apply (nPointTimeSpatialCLE (d := d) (k + (k + 1))).injective
  rw [nPointTimeSpatialCLE_osiiDifferenceTimeTranslation]
  ext j
  · simpa [nPointTimeSpatialCLE] using
      (reflectedReducedSpacetimeDisplacement_time u j).symm
  · simp [nPointTimeSpatialCLE,
      reflectedReducedSpacetimeDisplacement_spatial]

/-- Translating the reduced source by the moving-chart reflected displacement
is the reduction of the corresponding translated full reflected source. -/
theorem translate_diffVarReduction_reflectedReducedTimeDisplacement
    {d k : ℕ} [NeZero d]
    (u : Fin (k + k) → ℝ)
    (f : SchwartzNPoint d ((k + (k + 1)) + 1)) :
    translateSchwartzConfiguration
        (osiiDifferenceTimeTranslation (d := d)
          (reflectedReducedTimeDisplacement u))
        (diffVarReduction d (k + (k + 1)) f) =
      diffVarReduction d (k + (k + 1))
        (translateSchwartzConfiguration
          (reflectedReducedAbsoluteDisplacement (d := d) u) f) := by
  rw [osiiDifferenceTimeTranslation_reflectedReducedTimeDisplacement]
  exact
    (diffVarReduction_translate_reflectedReducedAbsoluteDisplacement
      u f).symm

end OSIIChapterV
end OSReconstruction
