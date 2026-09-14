/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialReducedPhysicalCovariance
import OSReconstruction.SCV.TotallyRealIdentity



















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- Unflatten one real coordinate vector into reduced spacetime blocks. -/
def osiiAxisPairUnflattenRealBlocks
    (a : Fin (k * (d + 1)) → ℝ) :
    NPointDomain d k :=
  (flattenCLEquivReal k (d + 1)).symm a

omit [NeZero d] [NeZero k] in
@[simp]
theorem osiiAxisPairUnflattenRealBlocks_apply
    (a : Fin (k * (d + 1)) → ℝ)
    (i : Fin k) (μ : Fin (d + 1)) :
    osiiAxisPairUnflattenRealBlocks (d := d) a i μ =
      a (finProdFinEquiv (i, μ)) :=
  flattenCLEquivReal_symm_apply k (d + 1) a i μ

omit [NeZero d] [NeZero k] in
theorem unflattenSchwartzNPoint_translateSchwartz
    (a : Fin (k * (d + 1)) → ℝ)
    (ψ : SchwartzMap (Fin (k * (d + 1)) → ℝ) ℂ) :
    _root_.unflattenSchwartzNPoint (d := d) (SCV.translateSchwartz a ψ) =
      translateSchwartzConfiguration
        (osiiAxisPairUnflattenRealBlocks (d := d) a)
        (_root_.unflattenSchwartzNPoint (d := d) ψ) := by
  ext x
  simp [_root_.unflattenSchwartzNPoint_apply, SCV.translateSchwartz_apply,
    translateSchwartzConfiguration_apply,
    osiiAxisPairUnflattenRealBlocks]

namespace OSIIChapterV

end OSIIChapterV

end OSReconstruction
