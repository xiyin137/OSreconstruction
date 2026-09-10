/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621NormalizedFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRealEdgeDensityGrowth










noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIITimeContinuationLadderRealEdgeGrowthData

variable {d k : Nat}
variable {L : OSIITimeContinuationLadder d k}

end OSIITimeContinuationLadderRealEdgeGrowthData

namespace OSIITimeContinuationLadderRealEdgeDensityGrowthData

variable {d k : Nat}
variable {L : OSIITimeContinuationLadder d k}

/-- The spatial density of the equation-`(6.21)` normalized stage on its
positive-real edge.  Keeping this function, rather than immediately passing
to a finite Schwartz-seminorm bound, is the density-level state used in the
VI.2 induction. -/
def vi2Equation621NormalizedPositiveRealDensity
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (t : Nat) (epsilon : Real)
    (tau : Fin k -> Real) (x : Fin (k * d) -> Real) : Complex :=
  osiiVI2Equation621Normalization t k epsilon
      (osiiPositiveRealTimeEmbed tau) *
    D.density (tau + fun _ => epsilon) x

/-- The normalized density remains continuous in the spatial variable. -/
theorem continuous_vi2Equation621NormalizedPositiveRealDensity
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (t : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    Continuous (D.vi2Equation621NormalizedPositiveRealDensity t epsilon tau) := by
  apply continuous_const.mul
  apply D.density_continuous
  intro i
  change 0 < tau i + epsilon
  linarith [htau i]

/-- The density-level equation-`(6.21)` normalization represents exactly the
normalized continuation stage, not merely a seminorm majorant for it. -/
theorem vi2Equation621NormalizedPositiveRealDensity_represents
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (t : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    (L.toFullTimeContinuationStage.vi2Equation621NormalizedStage
        t epsilon).distribution (osiiPositiveRealTimeEmbed tau) chi =
      ∫ x : Fin (k * d) -> Real,
        D.vi2Equation621NormalizedPositiveRealDensity t epsilon tau x *
          (section43SpatialFlatSchwartzCLE d k chi) x := by
  let shiftedTau : Fin k -> Real := tau + fun _ => epsilon
  have hshift :
      osiiVI2Shift k epsilon (osiiPositiveRealTimeEmbed tau) =
        osiiPositiveRealTimeEmbed shiftedTau := by
    ext i
    simp [shiftedTau, osiiVI2Shift, osiiPositiveRealTimeEmbed]
  have hshiftedTau :
      shiftedTau ∈ section43TimeStrictPositiveRegion k := by
    intro i
    change 0 < tau i + epsilon
    linarith [htau i]
  rw [OSIITimeContinuationStage.vi2Equation621NormalizedStage_distribution_apply,
    hshift]
  change osiiVI2Equation621Normalization t k epsilon
      (osiiPositiveRealTimeEmbed tau) *
        L.fullDistribution (osiiPositiveRealTimeEmbed shiftedTau) chi = _
  rw [D.represents shiftedTau hshiftedTau chi]
  calc
    osiiVI2Equation621Normalization t k epsilon
          (osiiPositiveRealTimeEmbed tau) *
        ∫ x : Fin (k * d) -> Real,
          D.density shiftedTau x *
            (section43SpatialFlatSchwartzCLE d k chi) x =
      ∫ x : Fin (k * d) -> Real,
        osiiVI2Equation621Normalization t k epsilon
            (osiiPositiveRealTimeEmbed tau) *
          (D.density shiftedTau x *
            (section43SpatialFlatSchwartzCLE d k chi) x) := by
      exact (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ x : Fin (k * d) -> Real,
        D.vi2Equation621NormalizedPositiveRealDensity t epsilon tau x *
          (section43SpatialFlatSchwartzCLE d k chi) x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp only [vi2Equation621NormalizedPositiveRealDensity, shiftedTau]
      ring

/-- Pointwise form of the VI.1-to-VI.2 normalization estimate.  The complete
equation-`(6.21)` factor absorbs all time and boundary growth while leaving
the spatial polynomial weight explicit. -/
theorem norm_vi2Equation621NormalizedPositiveRealDensity_le
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (t : Nat)
    (hpolynomial : D.timeDegree <= k * t)
    (hboundary : D.boundaryDegree <= k * t)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (x : Fin (k * d) -> Real) :
    ‖D.vi2Equation621NormalizedPositiveRealDensity t epsilon tau x‖ <=
      (k : Real) ^ (2 * (k * t)) * D.constant *
        (1 + ‖x‖) ^ D.spatialDegree := by
  let shiftedTau : Fin k -> Real := tau + fun _ => epsilon
  have hshift :
      osiiVI2Shift k epsilon (osiiPositiveRealTimeEmbed tau) =
        osiiPositiveRealTimeEmbed shiftedTau := by
    ext i
    simp [shiftedTau, osiiVI2Shift, osiiPositiveRealTimeEmbed]
  have hshiftedTau :
      shiftedTau ∈ section43TimeStrictPositiveRegion k := by
    intro i
    change 0 < tau i + epsilon
    linarith [htau i]
  have hnormalize :=
    osiiVI2Equation621Normalization_positiveReal_norm_mul_growth_boundary_le
      D.arity_pos hpolynomial hboundary hepsilon htau
  rw [hshift] at hnormalize
  rw [vi2Equation621NormalizedPositiveRealDensity, norm_mul]
  calc
    ‖osiiVI2Equation621Normalization t k epsilon
          (osiiPositiveRealTimeEmbed tau)‖ *
        ‖D.density shiftedTau x‖ <=
      ‖osiiVI2Equation621Normalization t k epsilon
          (osiiPositiveRealTimeEmbed tau)‖ *
        (D.constant *
          (1 + ‖osiiPositiveRealTimeEmbed shiftedTau‖) ^ D.timeDegree *
          (1 + (osiiTimeBoundaryDistance k
            (osiiPositiveRealTimeEmbed shiftedTau))⁻¹) ^ D.boundaryDegree *
          (1 + ‖x‖) ^ D.spatialDegree) :=
      mul_le_mul_of_nonneg_left
        (D.pointwise_bound shiftedTau hshiftedTau x) (norm_nonneg _)
    _ = D.constant *
        (‖osiiVI2Equation621Normalization t k epsilon
            (osiiPositiveRealTimeEmbed tau)‖ *
          (1 + ‖osiiPositiveRealTimeEmbed shiftedTau‖) ^ D.timeDegree *
          (1 + (osiiTimeBoundaryDistance k
            (osiiPositiveRealTimeEmbed shiftedTau))⁻¹) ^ D.boundaryDegree) *
        (1 + ‖x‖) ^ D.spatialDegree := by ring
    _ <= D.constant * (k : Real) ^ (2 * (k * t)) *
        (1 + ‖x‖) ^ D.spatialDegree := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnormalize D.constant_pos.le)
        (by positivity)
    _ = (k : Real) ^ (2 * (k * t)) * D.constant *
        (1 + ‖x‖) ^ D.spatialDegree := by ring

end OSIITimeContinuationLadderRealEdgeDensityGrowthData
end OSReconstruction
