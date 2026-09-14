/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIGrowthBoundaryHandoff

















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

/-- A single Vladimirov estimate, uniform over an exhausting Chapter V
ladder.  Auxiliary parts of finite-stage carriers outside the physical right
half-plane are intentionally excluded. -/
structure OSIITimeContinuationLadderVladimirovGrowthData
    {d k : ℕ}
    (L : OSIITimeContinuationLadder d k) where
  spatialSeminorms : Finset (ℕ × ℕ)
  constant : ℝ
  polynomialDegree : ℕ
  boundaryDegree : ℕ
  constant_pos : 0 < constant
  bound :
    ∀ stageIndex : ℕ,
      ∀ ζ ∈ (L.stage stageIndex).carrier,
        ζ ∈ osiiTimeRightHalfPlane k →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            ‖(L.stage stageIndex).distribution ζ χ‖ ≤
              constant * (1 + ‖ζ‖) ^ polynomialDegree *
                (1 + (osiiTimeBoundaryDistance k ζ)⁻¹) ^ boundaryDegree *
                  spatialSeminorms.sup
                    (schwartzSeminormFamily ℂ
                      (Section43SpatialSpace d k) ℂ) χ

namespace OSIITimeContinuationLadderVladimirovGrowthData

variable {d k : ℕ}
variable {L : OSIITimeContinuationLadder d k}

/-- A uniform finite-stage estimate descends to the glued full continuation
stage. -/
def toFullTimeStageGrowthData
    (G : OSIITimeContinuationLadderVladimirovGrowthData L) :
    OSIIFullTimeStageVladimirovGrowthData
      L.toFullTimeContinuationStage where
  fullCarrier := L.toFullTimeContinuationStage_carrier
  spatialSeminorms := G.spatialSeminorms
  constant := G.constant
  polynomialDegree := G.polynomialDegree
  boundaryDegree := G.boundaryDegree
  constant_pos := G.constant_pos
  bound := by
    intro ζ hζ χ
    have hexhausted :
        ζ ∈ ⋃ stageIndex : ℕ, (L.stage stageIndex).carrier :=
      L.exhausts hζ
    obtain ⟨stageIndex, hstage⟩ := Set.mem_iUnion.mp hexhausted
    rw [L.toFullTimeContinuationStage_extends_stage stageIndex hstage]
    exact G.bound stageIndex ζ hstage hζ χ

@[simp] theorem toFullTimeStageGrowthData_spatialSeminorms
    (G : OSIITimeContinuationLadderVladimirovGrowthData L) :
    G.toFullTimeStageGrowthData.spatialSeminorms = G.spatialSeminorms :=
  rfl

@[simp] theorem toFullTimeStageGrowthData_constant
    (G : OSIITimeContinuationLadderVladimirovGrowthData L) :
    G.toFullTimeStageGrowthData.constant = G.constant :=
  rfl

@[simp] theorem toFullTimeStageGrowthData_polynomialDegree
    (G : OSIITimeContinuationLadderVladimirovGrowthData L) :
    G.toFullTimeStageGrowthData.polynomialDegree = G.polynomialDegree :=
  rfl

@[simp] theorem toFullTimeStageGrowthData_boundaryDegree
    (G : OSIITimeContinuationLadderVladimirovGrowthData L) :
    G.toFullTimeStageGrowthData.boundaryDegree = G.boundaryDegree :=
  rfl

end OSIITimeContinuationLadderVladimirovGrowthData

end OSReconstruction
