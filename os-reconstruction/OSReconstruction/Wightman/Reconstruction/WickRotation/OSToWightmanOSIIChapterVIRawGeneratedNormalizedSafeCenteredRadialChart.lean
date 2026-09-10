/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedRootedSourceCarrier
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientFullRank
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedL1RankSuccessorFlatProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorNormalizedEnvelopeHandoff










noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open StrictGeneratedScalarDepthPointedData
open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

/-- An anchor spending only the outer part of a two-stage radial contraction.
The residual ratio is reserved for a later safe VI.2 unshift. -/
structure TargetHubNormalizedRadialSlackAnchorData
    {k : Nat}
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k)
    (rho radialContraction : Real) where
  anchorData : TargetHubHalfAnchorData hub z
  outerContraction : Real
  outerContraction_pos : 0 < outerContraction
  outerContraction_lt_one : outerContraction < 1
  rho_le_radial_mul_outer :
    rho <= radialContraction * outerContraction
  anchor_le_outerSlack : forall j,
    anchorData.anchor j <= (1 - outerContraction) * (z j).re

/-- The coordinatewise minimum gives a canonical two-budget anchor whenever
the flat radius is below the residual radial contraction. -/
def targetHubNormalizedRadialSlackAnchorData
    {k : Nat}
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ osiiTimeRightHalfPlane k)
    (rho radialContraction : Real)
    (hrho_nonneg : 0 <= rho)
    (hradial_pos : 0 < radialContraction)
    (hrho_lt_radial : rho < radialContraction) :
    TargetHubNormalizedRadialSlackAnchorData
      hub z rho radialContraction := by
  let outerContraction : Real := (rho / radialContraction + 1) / 2
  have hratio_nonneg : 0 <= rho / radialContraction :=
    div_nonneg hrho_nonneg hradial_pos.le
  have hratio_lt_one : rho / radialContraction < 1 :=
    (div_lt_one hradial_pos).2 hrho_lt_radial
  have houter_pos : 0 < outerContraction := by
    dsimp [outerContraction]
    linarith
  have houter_half : 1 / 2 <= outerContraction := by
    dsimp [outerContraction]
    linarith
  have houter_lt_one : outerContraction < 1 := by
    dsimp [outerContraction]
    linarith
  let scale : Real := 1 - outerContraction
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    linarith
  have hscale_half : scale <= 1 / 2 := by
    dsimp [scale]
    linarith
  let anchor : Fin k -> Real := fun j =>
    scale * min (hub j) (z j).re
  let C : TargetHubHalfAnchorData hub z := {
    anchor := anchor
    anchor_positive := by
      intro j
      exact mul_pos hscale_pos (lt_min (hhub j) (hz j))
    anchor_le_half_hub := by
      intro j
      calc
        anchor j <= scale * hub j :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hscale_pos.le
        _ <= (1 / 2 : Real) * hub j :=
          mul_le_mul_of_nonneg_right hscale_half (hhub j).le
        _ = hub j / 2 := by ring
    anchor_le_half_target := by
      intro j
      calc
        anchor j <= scale * (z j).re :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hscale_pos.le
        _ <= (1 / 2 : Real) * (z j).re :=
          mul_le_mul_of_nonneg_right hscale_half (hz j).le
        _ = (z j).re / 2 := by ring
    anchor_lt_hub := by
      intro j
      have h : anchor j <= hub j / 2 := by
        calc
          anchor j <= scale * hub j :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hscale_pos.le
          _ <= (1 / 2 : Real) * hub j :=
            mul_le_mul_of_nonneg_right hscale_half (hhub j).le
          _ = hub j / 2 := by ring
      linarith [hhub j]
    anchor_lt_target := by
      intro j
      have h : anchor j <= (z j).re / 2 := by
        calc
          anchor j <= scale * (z j).re :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hscale_pos.le
          _ <= (1 / 2 : Real) * (z j).re :=
            mul_le_mul_of_nonneg_right hscale_half (hz j).le
          _ = (z j).re / 2 := by ring
      linarith [hz j] }
  refine {
    anchorData := C
    outerContraction := outerContraction
    outerContraction_pos := houter_pos
    outerContraction_lt_one := houter_lt_one
    rho_le_radial_mul_outer := ?_
    anchor_le_outerSlack := ?_ }
  · dsimp [outerContraction]
    have hradial_nonneg : 0 <= radialContraction := hradial_pos.le
    have hrho_le : rho <= radialContraction := hrho_lt_radial.le
    field_simp [hradial_pos.ne']
    nlinarith
  · intro j
    change anchor j <= (1 - outerContraction) * (z j).re
    dsimp [anchor, scale]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hscale_pos.le

end OSIIChapterV
end OSReconstruction
