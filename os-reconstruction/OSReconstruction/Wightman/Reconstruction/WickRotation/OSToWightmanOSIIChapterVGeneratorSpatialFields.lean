/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialModes
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageCompactTimeTaylorEndpoint















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Compact-time Hilbert-field families for both blocks of every admissible
Chapter V split. The time profiles may depend on the split, while each block
family is uniform over all of its spatial Schwartz factors. -/
structure GeneratorHermiteHilbertFieldFamilyData
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (k : ℕ) where
  leftTimeProfile :
    (i : GeneratorIndex k) →
      Section43CompactStrictPositiveTimeSource i.n
  rightTimeProfile :
    (i : GeneratorIndex k) →
      Section43CompactStrictPositiveTimeSource i.m
  leftFamily :
    (i : GeneratorIndex k) →
      CompactTimeSpatialSourceHilbertFieldFamilyData OS
        (leftTimeProfile i)
  rightFamily :
    (i : GeneratorIndex k) →
      CompactTimeSpatialSourceHilbertFieldFamilyData OS
        (rightTimeProfile i)

namespace GeneratorHermiteHilbertFieldFamilyData

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The common complex domain of the left Hilbert fields for one split. -/
def leftComplexRegion
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) :
    Set (Fin (i.n - 1) → ℂ) :=
  SCV.Polydisc 0 (fun _ => (B.leftFamily i).radius)

/-- The common complex domain of the right Hilbert fields for one split. -/
def rightComplexRegion
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) :
    Set (Fin (i.m - 1) → ℂ) :=
  SCV.Polydisc 0 (fun _ => (B.rightFamily i).radius)

/-- The real trace of the left complex polydisc. -/
def leftRealComplexRegion
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) :
    Set (Fin (i.n - 1) → ℝ) :=
  {x | (fun a => (x a : ℂ)) ∈ B.leftComplexRegion i}

/-- The real trace of the right complex polydisc. -/
def rightRealComplexRegion
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) :
    Set (Fin (i.m - 1) → ℝ) :=
  {x | (fun a => (x a : ℂ)) ∈ B.rightComplexRegion i}

/-- The left real edge, restricted so it lies inside the field's common
complex domain. -/
def leftRealRegion
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) :
    Set (Fin (i.n - 1) → ℝ) :=
  (B.leftFamily i).realRegion ∩ B.leftRealComplexRegion i

/-- The right real edge, restricted so it lies inside the field's common
complex domain. -/
def rightRealRegion
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) :
    Set (Fin (i.m - 1) → ℝ) :=
  (B.rightFamily i).realRegion ∩ B.rightRealComplexRegion i

/-- The left Hilbert field selected by the `r`-th absolute product-Hermite
basis vector. -/
def leftField
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) (r : ℕ) :
    (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS :=
  fun z =>
    (B.leftFamily i).field z (leftSpatialHermiteBlock d i r)

/-- The right Hilbert field selected by the `r`-th absolute product-Hermite
basis vector. -/
def rightField
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) (r : ℕ) :
    (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS :=
  fun z =>
    (B.rightFamily i).field z (rightSpatialHermiteBlock d i r)

/-- The genuine concrete Hermite mode depends only on original OS data. -/
def modeOfOS
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) (r : ℕ) :
    OSIITimeGapSpace k → ℂ :=
  generatorSpatialHermiteModeOfOS OS i
    (B.leftField i) (B.rightField i) r

/-- Compatibility wrapper for the growth-free concrete Hermite mode. -/
def mode
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k) (r : ℕ) :
    OSIITimeGapSpace k → ℂ :=
  B.modeOfOS i r

end GeneratorHermiteHilbertFieldFamilyData

end OSIIChapterV
end OSReconstruction
