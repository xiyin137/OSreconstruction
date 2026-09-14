/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialFields
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionHolomorphy
















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

set_option backward.isDefEq.respectTransparency false in
/-- Restrict one compact-time spatial Hilbert field to particlewise product
tests. -/
noncomputable def compactTimeSpatialProductFieldCMM
    {d n : ℕ} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {g : Section43CompactStrictPositiveTimeSource n}
    (F : CompactTimeSpatialSourceHilbertFieldFamilyData OS g)
    (z : Fin (n - 1) → ℂ) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin d → ℝ) ℂ)
      (OSHilbertSpace OS) :=
  (F.field z).compContinuousMultilinearMap
    ((section43SpatialSchwartzParticleCLE d n).symm.toContinuousLinearMap
      |>.compContinuousMultilinearMap
        (SchwartzMap.productTensorMLM n))

@[simp]
theorem compactTimeSpatialProductFieldCMM_apply
    {d n : ℕ} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {g : Section43CompactStrictPositiveTimeSource n}
    (F : CompactTimeSpatialSourceHilbertFieldFamilyData OS g)
    (z : Fin (n - 1) → ℂ)
    (fs : Fin n → SchwartzMap (Fin d → ℝ) ℂ) :
    compactTimeSpatialProductFieldCMM F z fs =
      F.field z
        ((section43SpatialSchwartzParticleCLE d n).symm
          (SchwartzMap.productTensor fs)) := rfl

namespace GeneratorHermiteHilbertFieldFamilyData

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The global Hermite code restricted to the left particle block. -/
noncomputable def leftHermiteIndices
    (i : GeneratorIndex k) (r : ℕ) (a : Fin i.n) : ℕ :=
  GaussianField.productBasisIndices
    (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) r
    (i.leftAbsoluteIndex a)

/-- The global Hermite code restricted to the right particle block. -/
noncomputable def rightHermiteIndices
    (i : GeneratorIndex k) (r : ℕ) (b : Fin i.m) : ℕ :=
  GaussianField.productBasisIndices
    (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) r
    (i.rightAbsoluteIndex b)

theorem leftHermiteIndices_polyGrowth
    (i : GeneratorIndex k) :
    ∃ C > 0, ∃ q : ℕ, ∀ r a,
      (leftHermiteIndices (d := d) i r a : ℝ) ≤
        C * (1 + (r : ℝ)) ^ q := by
  obtain ⟨C, hC, q, hq⟩ :=
    GaussianField.productBasisIndices_polyGrowth
      (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k)
  exact ⟨C, hC, q, fun r a => hq r (i.leftAbsoluteIndex a)⟩

theorem rightHermiteIndices_polyGrowth
    (i : GeneratorIndex k) :
    ∃ C > 0, ∃ q : ℕ, ∀ r b,
      (rightHermiteIndices (d := d) i r b : ℝ) ≤
        C * (1 + (r : ℝ)) ^ q := by
  obtain ⟨C, hC, q, hq⟩ :=
    GaussianField.productBasisIndices_polyGrowth
      (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k)
  exact ⟨C, hC, q, fun r b => hq r (i.rightAbsoluteIndex b)⟩

end GeneratorHermiteHilbertFieldFamilyData

end OSIIChapterV
end OSReconstruction
