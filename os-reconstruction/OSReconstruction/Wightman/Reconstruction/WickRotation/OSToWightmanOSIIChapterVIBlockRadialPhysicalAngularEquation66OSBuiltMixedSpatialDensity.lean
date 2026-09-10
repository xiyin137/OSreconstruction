import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltCenterValue
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRealEdgeDensityGrowth

/-!
# Canonical OS-built equation-(6.6) mixed-spatial density

The canonical Chapter VI radius at a positive real time point is admissible at
every mixed spacetime center.  Evaluating the OS-built equation-(6.6) center
value at those centers therefore gives a spatial density with the exact
pointwise polynomial estimate required by the non-circular VI.1 handoff.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

open OSIIStep4FullSchwartzAngularContinuationData

/-- The canonical Chapter VI radius is below every time coordinate of a mixed
spacetime center. -/
theorem osiiChapterVIRegularizationRadius_le_mixedSpatialRealPoint
    (d k : Nat)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (x : Fin (k * d) -> Real)
    (i : Fin k) :
    osiiChapterVIRegularizationRadius k (osiiPositiveRealTimeEmbed tau) <=
      osiiStep4MixedSpatialRealPoint d k tau x
        (finProdFinEquiv (i, (0 : Fin (d + 1)))) := by
  have hzeta :
      osiiPositiveRealTimeEmbed tau ∈ osiiTimeRightHalfPlane k :=
    (osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau
  simpa [osiiStep4MixedSpatialRealPoint, osiiPositiveRealTimeEmbed] using
    (osiiChapterVIRegularizationRadius_le_re hzeta i)

/-- The canonical non-circular equation-(6.6) density on a positive real time
slice and arbitrary flat spatial center. -/
noncomputable def osiiEquation66OSBuiltMixedSpatialDensity
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (x : Fin (k * d) -> Real) : Complex :=
  osiiEquation66OSBuiltCenterValue d k OS lgc
    (osiiChapterVIRegularizationRadius_pos
      (Nat.pos_of_ne_zero (NeZero.ne k))
      ((osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau))
    (osiiChapterVIRegularizationRadius_le_sixteen k
      (osiiPositiveRealTimeEmbed tau))
    (osiiStep4MixedSpatialRealPoint d k tau x)
    (osiiChapterVIRegularizationRadius_le_mixedSpatialRealPoint
      d k tau htau x)

/-- The OS-built mixed-spatial density has the pointwise time, boundary, and
spatial polynomial growth required by VI.1. -/
theorem osiiEquation66OSBuiltMixedSpatialDensity_norm_le
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (x : Fin (k * d) -> Real) :
    ‖osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau htau x‖ <=
      (equation66E0PolynomialConstant G *
          16 ^ (2 * G.scaleDegree)) *
        (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^
          (G.scaleDegree + G.growthDegree) *
        (1 + (osiiTimeBoundaryDistance k
          (osiiPositiveRealTimeEmbed tau))⁻¹) ^
          (2 * G.scaleDegree) *
        (1 + ‖x‖) ^ (G.scaleDegree + G.growthDegree) := by
  let zeta := osiiPositiveRealTimeEmbed tau
  let rho := osiiChapterVIRegularizationRadius k zeta
  let M := G.scaleDegree
  let N := G.growthDegree
  let P := M + N
  let C0 := equation66E0PolynomialConstant G
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hzeta : zeta ∈ osiiTimeRightHalfPlane k :=
    (osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau
  have hrho : 0 < rho := by
    simpa only [rho] using osiiChapterVIRegularizationRadius_pos hk hzeta
  have hrho_le : rho <= 16 := by
    simpa only [rho] using
      osiiChapterVIRegularizationRadius_le_sixteen k zeta
  have hcenter : forall i : Fin k,
      rho <= osiiStep4MixedSpatialRealPoint d k tau x
        (finProdFinEquiv (i, (0 : Fin (d + 1)))) := by
    intro i
    simpa only [rho, zeta] using
      osiiChapterVIRegularizationRadius_le_mixedSpatialRealPoint
        d k tau htau x i
  have hraw := osiiEquation66OSBuiltCenterValue_norm_le_E0Polynomial
    d k OS lgc G hrho hrho_le
      (osiiStep4MixedSpatialRealPoint d k tau x) hcenter
  have hratio :
      (16 / rho) ^ (2 * M) <=
        16 ^ (2 * M) *
          (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (2 * M) := by
    simpa only [rho] using
      osiiChapterVIRegularizationRadius_ratio_pow_le hk hzeta (2 * M)
  have hsplit :
      (1 + ‖osiiStep4MixedSpatialRealPoint d k tau x‖) ^ P <=
        (1 + ‖zeta‖) ^ P * (1 + ‖x‖) ^ P := by
    simpa only [P, zeta] using
      osiiStep4MixedSpatialRealPoint_one_add_norm_pow_le d k P tau x
  have hC0 : 0 <= C0 := by
    simpa only [C0] using equation66E0PolynomialConstant_nonneg G
  have hcenter_nonneg :
      0 <= (1 + ‖osiiStep4MixedSpatialRealPoint d k tau x‖) ^ P := by
    positivity
  have hdist : 0 < osiiTimeBoundaryDistance k zeta :=
    osiiTimeBoundaryDistance_pos hk hzeta
  have hboundary_nonneg :
      0 <= (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (2 * M) := by
    exact pow_nonneg
      (add_nonneg zero_le_one (inv_nonneg.mpr hdist.le)) _
  have hcoeff_nonneg :
      0 <= C0 *
        (16 ^ (2 * M) *
          (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (2 * M)) :=
    mul_nonneg hC0
      (mul_nonneg (pow_nonneg (by norm_num) _) hboundary_nonneg)
  calc
    ‖osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau htau x‖ <=
        C0 * (16 / rho) ^ (2 * M) *
          (1 + ‖osiiStep4MixedSpatialRealPoint d k tau x‖) ^ P := by
      simpa only [osiiEquation66OSBuiltMixedSpatialDensity, C0, rho, zeta,
        M, N, P] using hraw
    _ <= C0 *
        (16 ^ (2 * M) *
          (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (2 * M)) *
        (1 + ‖osiiStep4MixedSpatialRealPoint d k tau x‖) ^ P :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio hC0) hcenter_nonneg
    _ <= C0 *
        (16 ^ (2 * M) *
          (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (2 * M)) *
        ((1 + ‖zeta‖) ^ P * (1 + ‖x‖) ^ P) :=
      mul_le_mul_of_nonneg_left hsplit hcoeff_nonneg
    _ = (equation66E0PolynomialConstant G *
          16 ^ (2 * G.scaleDegree)) *
        (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^
          (G.scaleDegree + G.growthDegree) *
        (1 + (osiiTimeBoundaryDistance k
          (osiiPositiveRealTimeEmbed tau))⁻¹) ^
          (2 * G.scaleDegree) *
        (1 + ‖x‖) ^ (G.scaleDegree + G.growthDegree) := by
      simp only [C0, M, N, P, zeta]
      ring

end OSReconstruction
