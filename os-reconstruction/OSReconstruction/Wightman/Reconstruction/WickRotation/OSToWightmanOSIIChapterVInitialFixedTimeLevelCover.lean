/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialFixedTimePartition
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialFactorCover











noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace InitialBaseTimePartitionData

variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

/-- One fixed time piece after applying the level-`N` reduced spatial
truncation. -/
noncomputable def levelPiece
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (N : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1) :=
  (D.piece a).comp (initialSpatialFactorTruncationCLM d k N)

@[simp] theorem levelPiece_apply
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    D.levelPiece a N χ =
      D.piece a (initialSpatialFactorTruncationCLM d k N χ) :=
  rfl

/-- At every spatial truncation level, the fixed time pieces still sum to the
canonical factorwise compact source map. -/
theorem sum_levelPiece_eq
    (D : InitialBaseTimePartitionData (d := d) φ)
    (N : ℕ) :
    ∑ a, D.levelPiece a N =
      initialReducedSpatialFactorCompactSourceCLM (d := d) φ N := by
  apply ContinuousLinearMap.ext
  intro χ
  have hsum :=
    congrArg
      (fun L :
        SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
          SchwartzNPoint d (k + 1) =>
        L (initialSpatialFactorTruncationCLM d k N χ))
      D.sum_piece_eq
  simpa [levelPiece, ContinuousLinearMap.sum_apply,
    initialReducedSpatialFactorCompactSourceCLM_apply] using hsum

/-- Membership in a natural chronological cell depends only on the Euclidean
time coordinate when the natural rotation is the identity. -/
theorem mem_naturalChronologicalProductNeighborhood_cell_iff_of_time_eq
    (x₀ : NPointDomain d (k + 1))
    (hx₀ :
      ∀ i j : Fin (k + 1), i < j →
        x₀ i 0 < x₀ j 0)
    (i : Fin (k + 1))
    (y z : SpacetimeDim d)
    (hyz : y 0 = z 0) :
    y ∈ (naturalChronologicalProductNeighborhood x₀ hx₀).cell i ↔
      z ∈ (naturalChronologicalProductNeighborhood x₀ hx₀).cell i := by
  simp only [naturalChronologicalProductNeighborhood]
  unfold osiiOrderedTimeCell osiiRotatedTime
  simp [hyz]

/-- The fixed finite time partition equipped with one carrier family at a
single spatial truncation level. -/
structure LevelCover
    (D : InitialBaseTimePartitionData (d := d) φ)
    (N : ℕ) where
  carrier : D.index → OSIIChronologicalCompactFactors d k
  carrier_fix :
    ∀ a χ,
      SchwartzMap.smulLeftCLM ℂ
          (SchwartzMap.productTensor (carrier a).factors)
          (D.levelPiece a N χ) =
        D.levelPiece a N χ

end InitialBaseTimePartitionData

end OSIIChapterV
end OSReconstruction
