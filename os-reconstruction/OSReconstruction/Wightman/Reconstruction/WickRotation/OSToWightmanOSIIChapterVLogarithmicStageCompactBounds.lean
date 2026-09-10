import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeSpatialCurrying

/-!
# OS-II Chapter V compact bounds in logarithmic coordinates

Weak holomorphy of a physical continuation stage gives compact-local uniform
Schwartz bounds after pulling the stage back through coordinatewise
exponentiation. This is the distribution-valued boundedness input needed by
local envelope constructions in logarithmic coordinates.
-/

noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Compact-local Schwartz bounds for a continuation stage, expressed after
coordinatewise exponentiation from logarithmic coordinates. -/
theorem exists_uniform_schwartz_bound_logarithmicPullbackStage_on_compact
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k)
    (K : Set (Fin k → ℂ))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (logarithmicPullbackStage A).carrier) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ z ∈ K, ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ‖A.distribution (osiiLogExp z) χ‖ ≤
          C * s.sup
            (schwartzSeminormFamily ℂ
              (Section43SpatialSpace d k) ℂ) χ := by
  simpa using
    (exists_uniform_schwartz_bound_osiiStage_on_compact
      (A := logarithmicPullbackStage A)
      (K := K) hK_compact hK_subset)

end OSIIChapterV
end OSReconstruction
