import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceCanonicalEdge

/-!
# Canonical Chapter V moving-slice cutoffs

A canonical compact stage edge carries one auxiliary time cutoff, but that
cutoff need not be supported inside the open real region represented by the
edge. Moving slices therefore need a second cutoff: it is supported in the
represented region and is one on the compact source carrier.

Keeping this datum separate avoids silently reusing the wrong cutoff in the
E-to-R sourcewise handoff.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {stage : OSIITimeContinuationStage d k}
variable {compactCarrier : Set (Fin k -> Real)}

/-- A second compact time cutoff adapted to the represented neighborhood of a
canonical stage edge. Unlike the edge's own cutoff, this one is supported
inside the represented real region, so it can be used by the moving-slice
distribution. -/
structure CanonicalReducedCompactMovingSliceCutoffData
    (D : CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier) where
  cutoff : SchwartzMap (Fin k -> Real) Complex
  cutoff_support :
    tsupport (cutoff : (Fin k -> Real) -> Complex) ⊆ D.realRegion
  cutoff_compact :
    HasCompactSupport (cutoff : (Fin k -> Real) -> Complex)
  cutoff_one_on :
    forall tau, tau ∈ compactCarrier -> cutoff tau = 1

namespace CanonicalReducedCompactMovingSliceCutoffData

/-- Every canonical compact edge admits a moving-slice cutoff on the same
compact carrier. This is finite-dimensional cutoff geometry; no additional
analytic continuation input is used. -/
theorem nonempty
    (D : CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (hcompact : IsCompact compactCarrier) :
    Nonempty (CanonicalReducedCompactMovingSliceCutoffData D) := by
  obtain ⟨cutoff, hcutoff_one, hcutoff_support, hcutoff_compact⟩ :=
    exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open
      hcompact D.realRegion_open D.compactCarrier_subset
  exact ⟨{
    cutoff := cutoff
    cutoff_support := hcutoff_support
    cutoff_compact := hcutoff_compact
    cutoff_one_on := hcutoff_one }⟩

end CanonicalReducedCompactMovingSliceCutoffData

end OSIIChapterV
end OSReconstruction
