/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketA0FieldBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialProductBasepointSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialFactorExhaustion
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorCommonSpatialSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGlobalProfile



















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}

namespace ReflectedA0BlockContinuousTranslationData

private theorem cast_spatial_cmlm_apply
    {d p n m : ℕ}
    (h : n = m)
    (F :
      ContinuousMultilinearMap ℂ
        (fun _ : Fin p => SchwartzMap (Fin d → ℝ) ℂ)
        (SchwartzMap (Section43SpatialSpace d n) ℂ))
    (fs : Fin p → SchwartzMap (Fin d → ℝ) ℂ) :
    (cast
      (congrArg
        (fun q =>
          ContinuousMultilinearMap ℂ
            (fun _ : Fin p => SchwartzMap (Fin d → ℝ) ℂ)
            (SchwartzMap (Section43SpatialSpace d q) ℂ))
        h)
      F) fs =
      cast
        (congrArg
          (fun q => SchwartzMap (Section43SpatialSpace d q) ℂ)
          h)
        (F fs) := by
  subst m
  rfl

/-- The fixed-head left Hermite block is the canonical generator block,
transported only across the syntactic equality `(i.n - 1) + 1 = i.n`. -/
theorem leftHeadSpatialHermiteBlock_eq_cast_leftSpatialHermiteBlock
    (i : GeneratorIndex k)
    (mode : ℕ) :
    ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
        (d := d) i mode =
      cast
        (congrArg
          (fun q => SchwartzMap (Section43SpatialSpace d q) ℂ)
          (Nat.sub_add_cancel i.hn).symm)
        (leftSpatialHermiteBlock d i mode) := by
  unfold ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
  unfold leftSpatialHermiteBlock spatialHermiteFactor
  rw [cast_spatial_cmlm_apply]
  apply congrArg
  change
    (section43SpatialSchwartzParticleCLE d i.n).symm
        (SchwartzMap.productTensor fun a =>
          OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily.complexifyRealSchwartz
            (GaussianField.DyninMityaginSpace.basis
              (GaussianField.productBasisIndices
                (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) mode
                (i.leftAbsoluteIndex a)))) =
      (section43SpatialSchwartzParticleCLE d i.n).symm
        (SchwartzMap.productTensor fun a =>
          SCV.schwartzOfRealCLM
            (realSpatialHermiteFactor d (k + 1) (Nat.succ_pos k) mode
              (i.leftAbsoluteIndex a)))
  congr 1
  exact (Nat.sub_add_cancel i.hn).symm

/-- The fixed-head right Hermite block is the canonical generator block,
transported only across the syntactic equality `(i.m - 1) + 1 = i.m`. -/
theorem rightHeadSpatialHermiteBlock_eq_cast_rightSpatialHermiteBlock
    (i : GeneratorIndex k)
    (mode : ℕ) :
    ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
        (d := d) i mode =
      cast
        (congrArg
          (fun q => SchwartzMap (Section43SpatialSpace d q) ℂ)
          (Nat.sub_add_cancel i.hm).symm)
        (rightSpatialHermiteBlock d i mode) := by
  unfold ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
  unfold rightSpatialHermiteBlock spatialHermiteFactor
  rw [cast_spatial_cmlm_apply]
  apply congrArg
  change
    (section43SpatialSchwartzParticleCLE d i.m).symm
        (SchwartzMap.productTensor fun b =>
          OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily.complexifyRealSchwartz
            (GaussianField.DyninMityaginSpace.basis
              (GaussianField.productBasisIndices
                (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) mode
                (i.rightAbsoluteIndex b)))) =
      (section43SpatialSchwartzParticleCLE d i.m).symm
        (SchwartzMap.productTensor fun b =>
          SCV.schwartzOfRealCLM
            (realSpatialHermiteFactor d (k + 1) (Nat.succ_pos k) mode
              (i.rightAbsoluteIndex b)))
  congr 1
  exact (Nat.sub_add_cancel i.hm).symm

end ReflectedA0BlockContinuousTranslationData

namespace ReflectedA0BlockContinuousTranslationData

end ReflectedA0BlockContinuousTranslationData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
