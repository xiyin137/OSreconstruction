/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.DistributionalRepresentationGluing
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReducedExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalReducedSchwinger














noncomputable section

open Complex MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d m : ℕ} [NeZero d]

/-- Absolute-coordinate carrier obtained by reconstructing a compact
basepoint fiber over a reduced carrier. -/
noncomputable def reducedTestLiftFullCarrier
    (χ : BHW.NormalizedBasepointCutoff d)
    (V : Set (NPointDomain d m)) :
    Set (NPointDomain d (m + 1)) :=
  (fun p : SpacetimeDim d × NPointDomain d m =>
    (BHW.realDiffCoordCLE (m + 1) d).symm
      (BHW.prependBasepointReal d m p.1 p.2)) ''
    (tsupport (χ.toSchwartz : SpacetimeDim d → ℂ) ×ˢ V)

omit [NeZero d] in
theorem continuous_reducedTestLiftReconstruction :
    Continuous
      (fun p : SpacetimeDim d × NPointDomain d m =>
        (BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m p.1 p.2)) := by
  apply (BHW.realDiffCoordCLE (m + 1) d).symm.continuous.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa using continuous_fst
  · intro j
    simpa using (continuous_apply j).comp continuous_snd

omit [NeZero d] in
theorem realDiffCoordCLE_symm_prependBasepointReal_self
    (x : NPointDomain d (m + 1)) :
    (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m (x 0)
          (BHW.reducedDiffMapReal (m + 1) d x)) =
      x := by
  have hcoord :
      BHW.prependBasepointReal d m (x 0)
          (BHW.reducedDiffMapReal (m + 1) d x) =
        BHW.realDiffCoordCLE (m + 1) d x := by
    ext i μ
    refine Fin.cases ?_ ?_ i
    · simp [BHW.realDiffCoordCLE_apply]
    · intro j
      change
        x j.succ μ - x j.castSucc μ =
          x j.succ μ - x j.castSucc μ
      rfl
  rw [hcoord]
  exact (BHW.realDiffCoordCLE (m + 1) d).symm_apply_apply x

theorem isCompact_reducedTestLiftFullCarrier
    (χ : BHW.NormalizedBasepointCutoff d)
    (hχ : HasCompactSupport
      (χ.toSchwartz : SpacetimeDim d → ℂ))
    (V : Set (NPointDomain d m))
    (hV : IsCompact V) :
    IsCompact (reducedTestLiftFullCarrier χ V) := by
  exact
    (hχ.isCompact.prod hV).image
      continuous_reducedTestLiftReconstruction

end OSIIChapterV
end OSReconstruction
