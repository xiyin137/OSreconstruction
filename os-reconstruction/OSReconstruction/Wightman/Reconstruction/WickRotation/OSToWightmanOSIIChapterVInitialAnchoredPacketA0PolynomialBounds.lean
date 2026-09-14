/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketBlockFamilies
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDeltaHilbertLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialReflectedA0Factorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
import OSReconstruction.SCV.DistributionalRepresentationGluing
import Mathlib.Analysis.Complex.Tietze
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionHolomorphy












noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

/-- A two-index Schwartz family has seminorm-wise polynomial growth in its
second index, uniformly in its first index. -/
def IsUniformlyPolynomiallyBoundedSchwartzFamily
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : ℕ → ℕ → SchwartzMap E ℂ) : Prop :=
  ∀ pq : ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℕ,
    ∀ level mode,
      SchwartzMap.seminorm ℝ pq.1 pq.2 (χ level mode) ≤
        C * (1 + (mode : ℝ)) ^ r

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace ReflectedA0BlockConvergenceData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}

/-- The left product-Hermite block, transported to the syntactic particle
count used by the fixed-head A0 source. -/
noncomputable def leftHeadSpatialHermiteBlock
    (i : GeneratorIndex k) (mode : ℕ) :
    SchwartzMap (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ :=
  (cast
    (congrArg
      (fun q =>
        ContinuousMultilinearMap ℂ
          (fun _ : Fin i.n => SchwartzMap (Fin d → ℝ) ℂ)
          (SchwartzMap (Section43SpatialSpace d q) ℂ))
      (Nat.sub_add_cancel i.hn).symm)
      ((section43SpatialSchwartzParticleCLE d i.n).symm.toContinuousLinearMap
        |>.compContinuousMultilinearMap
          (SchwartzMap.productTensorMLM i.n)))
    (fun a =>
      complexifyRealSchwartz
        (GaussianField.DyninMityaginSpace.basis
          (E := SchwartzMap (Fin d → ℝ) ℝ)
          (GaussianField.productBasisIndices
            (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) mode
            (i.leftAbsoluteIndex a))))

/-- The right product-Hermite block, transported to the syntactic particle
count used by the fixed-head A0 source. -/
noncomputable def rightHeadSpatialHermiteBlock
    (i : GeneratorIndex k) (mode : ℕ) :
    SchwartzMap (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ :=
  (cast
    (congrArg
      (fun q =>
        ContinuousMultilinearMap ℂ
          (fun _ : Fin i.m => SchwartzMap (Fin d → ℝ) ℂ)
          (SchwartzMap (Section43SpatialSpace d q) ℂ))
      (Nat.sub_add_cancel i.hm).symm)
      ((section43SpatialSchwartzParticleCLE d i.m).symm.toContinuousLinearMap
        |>.compContinuousMultilinearMap
          (SchwartzMap.productTensorMLM i.m)))
    (fun b =>
      complexifyRealSchwartz
        (GaussianField.DyninMityaginSpace.basis
          (E := SchwartzMap (Fin d → ℝ) ℝ)
          (GaussianField.productBasisIndices
            (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) mode
            (i.rightAbsoluteIndex b))))

end ReflectedA0BlockConvergenceData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
