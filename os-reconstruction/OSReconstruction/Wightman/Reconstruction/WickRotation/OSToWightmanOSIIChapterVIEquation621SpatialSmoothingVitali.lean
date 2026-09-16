/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVApproxIdentityConvolution
import Init
import OSReconstruction.SCV.LocallyUniformLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization




















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

namespace OSIIEquation621SpatialApproxIdentityData

/-- Reuse the canonical spatial approximate identity in the repository's
general finite-dimensional convolution API. -/
def toSchwartzTimeApproximateIdentity
    {m : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData m) :
    OSIIChapterV.SchwartzTimeApproximateIdentity m where
  test := Q.test
  radius := Q.radius
  nonnegative := Q.nonneg
  real := Q.real
  integral_one := Q.integral_eq_one
  compact := Q.compactSupport
  support := Q.support_subset_ball
  radius_tendsto := Q.radius_tendsto

/-- The actual stage distribution evaluated on the `N`th translated spatial
kernel at center `x`. -/
def smoothedStageValue
    {d k : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData (k * d))
    (A : OSIITimeContinuationStage d k)
    (N : Nat) (zeta : OSIITimeGapSpace k)
    (x : Fin (k * d) -> Real) : Complex :=
  A.distribution zeta (Q.section43Probe x N)

/-- Every spatially smoothed stage value is continuous in its spatial
center. -/
theorem continuous_smoothedStageValue
    {d k : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData (k * d))
    (A : OSIITimeContinuationStage d k)
    (N : Nat) (zeta : OSIITimeGapSpace k) :
    Continuous (Q.smoothedStageValue A N zeta) := by
  let T := OSIIEquation621WeightedDensityAtlasData.flatDistribution A zeta
  have htranslate : Continuous
      (fun x : Fin (k * d) -> Real =>
        T (SCV.translateSchwartz (-x) (Q.test N))) :=
    (SCV.continuous_apply_translateSchwartz_of_isCompactSupport
      T (Q.test N) (Q.compactSupport N)).comp continuous_neg
  change Continuous (fun x : Fin (k * d) -> Real =>
    T (SCV.translateSchwartz (-x) (Q.test N)))
  exact htranslate

/-- The compactly supported spatial pairing of the smoothed values converges
to the actual stage distribution. -/
theorem tendsto_integral_smoothedStageValue_mul
    {d k : Nat} [Nonempty (Fin (k * d))]
    (Q : OSIIEquation621SpatialApproxIdentityData (k * d))
    (A : OSIITimeContinuationStage d k)
    (zeta : OSIITimeGapSpace k)
    (phi : SchwartzMap (Fin (k * d) -> Real) Complex)
    (hphi : HasCompactSupport
      (phi : (Fin (k * d) -> Real) -> Complex)) :
    Tendsto
      (fun N => ∫ x : Fin (k * d) -> Real,
        Q.smoothedStageValue A N zeta x * phi x)
      atTop
      (nhds
        (OSIIEquation621WeightedDensityAtlasData.flatDistribution A zeta phi)) := by
  change Tendsto
    (fun N => ∫ x : Fin (k * d) -> Real,
      (OSIIEquation621WeightedDensityAtlasData.flatDistribution A zeta)
        (SCV.translateSchwartz (-x) (Q.test N)) * phi x)
    atTop
    (nhds
      (OSIIEquation621WeightedDensityAtlasData.flatDistribution A zeta phi))
  simpa [toSchwartzTimeApproximateIdentity,
    OSIIEquation621SpatialApproxIdentityData.section43Probe,
    OSIIEquation621SpatialApproxIdentityData.translatedTest,
    OSIIEquation621WeightedDensityAtlasData.flatDistribution] using
      (Q.toSchwartzTimeApproximateIdentity
        ).tendsto_integral_apply_translate_test_mul phi hphi
          (OSIIEquation621WeightedDensityAtlasData.flatDistribution A zeta)

/-- Polynomial estimates on the canonical spatial smoothings whose
coefficients converge give the exact limiting weighted-`L1` estimate on the
flat stage distribution.

Only compactly supported tests are used in the smoothing identity.  The
estimate extends to every Schwartz test because the weighted `L1` mass is a
continuous seminorm and compactly supported Schwartz functions are dense.
Allowing the coefficient to converge is essential for the sharp rooted
equation-`(6.29)` route: the lower spatial convolutions carry a radius loss
at every finite scale, but that loss tends to one. -/
theorem norm_flatDistribution_le_weightedL1_of_smoothedStageValue_tendsto_bound
    {d k p : Nat} [Nonempty (Fin (k * d))]
    (Q : OSIIEquation621SpatialApproxIdentityData (k * d))
    (A : OSIITimeContinuationStage d k)
    (zeta : OSIITimeGapSpace k)
    (coefficient : Nat -> Real)
    (B : Real)
    (hcoefficient : Tendsto coefficient atTop (nhds B))
    (hbound : forall N x,
      ‖Q.smoothedStageValue A N zeta x‖ <=
        coefficient N * osiiSpatialPolynomialWeight p x)
    (phi : SchwartzMap (Fin (k * d) -> Real) Complex) :
    ‖OSIIEquation621WeightedDensityAtlasData.flatDistribution A zeta phi‖ <=
      B * osiiSpatialPolynomialWeightedL1 p phi := by
  let T := OSIIEquation621WeightedDensityAtlasData.flatDistribution A zeta
  let P := osiiSpatialPolynomialWeightedL1Seminorm (m := k * d) p
  let good : Set (SchwartzMap (Fin (k * d) -> Real) Complex) :=
    {phi | ‖T phi‖ <= B * P phi}
  have hgood_closed : IsClosed good := by
    exact isClosed_le T.continuous.norm
      (continuous_const.mul
        (continuous_osiiSpatialPolynomialWeightedL1Seminorm (k * d) p))
  have hcompact_good :
      {phi : SchwartzMap (Fin (k * d) -> Real) Complex |
        HasCompactSupport (phi : (Fin (k * d) -> Real) -> Complex)} ⊆ good := by
    intro psi hpsi
    have hnorm_integral : forall N,
        ‖∫ x : Fin (k * d) -> Real,
            Q.smoothedStageValue A N zeta x * psi x‖ <=
          coefficient N * osiiSpatialPolynomialWeightedL1 p psi := by
      intro N
      have hmajor_integrable : Integrable
          (fun x : Fin (k * d) -> Real =>
            coefficient N * ((1 + ‖x‖) ^ p * ‖psi x‖)) :=
        (integrable_osiiSpatialPolynomialWeightedL1 (p := p) psi).const_mul
          (coefficient N)
      have hintegrable : Integrable
          (fun x : Fin (k * d) -> Real =>
            Q.smoothedStageValue A N zeta x * psi x) := by
        refine Integrable.mono' hmajor_integrable ?_ ?_
        · exact (Q.continuous_smoothedStageValue A N zeta).aestronglyMeasurable.mul
            psi.continuous.aestronglyMeasurable
        · filter_upwards with x
          rw [norm_mul]
          calc
            ‖Q.smoothedStageValue A N zeta x‖ * ‖psi x‖ <=
                (coefficient N * osiiSpatialPolynomialWeight p x) * ‖psi x‖ :=
              mul_le_mul_of_nonneg_right (hbound N x) (norm_nonneg _)
            _ = coefficient N * ((1 + ‖x‖) ^ p * ‖psi x‖) := by
              simp [osiiSpatialPolynomialWeight]
              ring
      calc
        ‖∫ x : Fin (k * d) -> Real,
            Q.smoothedStageValue A N zeta x * psi x‖ <=
          ∫ x : Fin (k * d) -> Real,
            ‖Q.smoothedStageValue A N zeta x * psi x‖ :=
          norm_integral_le_integral_norm _
        _ <= ∫ x : Fin (k * d) -> Real,
            coefficient N * ((1 + ‖x‖) ^ p * ‖psi x‖) := by
          exact integral_mono_ae hintegrable.norm hmajor_integrable
            (Filter.Eventually.of_forall fun x => by
              change ‖Q.smoothedStageValue A N zeta x * psi x‖ <=
                coefficient N * ((1 + ‖x‖) ^ p * ‖psi x‖)
              rw [norm_mul]
              calc
                ‖Q.smoothedStageValue A N zeta x‖ * ‖psi x‖ <=
                    (coefficient N * osiiSpatialPolynomialWeight p x) * ‖psi x‖ :=
                  mul_le_mul_of_nonneg_right (hbound N x) (norm_nonneg _)
                _ = coefficient N * ((1 + ‖x‖) ^ p * ‖psi x‖) := by
                  simp [osiiSpatialPolynomialWeight]
                  ring)
        _ = coefficient N * osiiSpatialPolynomialWeightedL1 p psi := by
          rw [integral_const_mul]
          rfl
    change ‖T psi‖ <= B * P psi
    simpa [T, P] using le_of_tendsto_of_tendsto
      (tendsto_norm.comp
        (Q.tendsto_integral_smoothedStageValue_mul A zeta psi hpsi))
      (hcoefficient.mul tendsto_const_nhds)
      (Filter.Eventually.of_forall hnorm_integral)
  have hclosure : closure
      {phi : SchwartzMap (Fin (k * d) -> Real) Complex |
        HasCompactSupport (phi : (Fin (k * d) -> Real) -> Complex)} ⊆ good :=
    hgood_closed.closure_subset_iff.mpr hcompact_good
  have hphi : phi ∈ good := by
    apply hclosure
    rw [SchwartzMap.dense_hasCompactSupport.closure_eq]
    exact Set.mem_univ phi
  simpa [good, T, P] using hphi

end OSIIEquation621SpatialApproxIdentityData

namespace OSIIEquation621PointwiseVitaliAtlasData

variable {d k p : Nat}
variable {A : OSIITimeContinuationStage d k}

end OSIIEquation621PointwiseVitaliAtlasData

namespace OSIITimeContinuationLadderRealEdgeDensityGrowthData
namespace OSIIEquation621WeightedPositiveRealEdgeData

variable {d k p : Nat}
variable {A : OSIITimeContinuationStage d k}

namespace SmoothedVitaliDominationData

variable
  {E : OSIIEquation621WeightedPositiveRealEdgeData A p}
  {Q : OSIIEquation621SpatialApproxIdentityData (k * d)}

end SmoothedVitaliDominationData

namespace SmoothedPolynomialVitaliProducerData

variable
  {E : OSIIEquation621WeightedPositiveRealEdgeData A p}
  {Q : OSIIEquation621SpatialApproxIdentityData (k * d)}

end SmoothedPolynomialVitaliProducerData

end OSIIEquation621WeightedPositiveRealEdgeData
end OSIITimeContinuationLadderRealEdgeDensityGrowthData
end OSReconstruction
