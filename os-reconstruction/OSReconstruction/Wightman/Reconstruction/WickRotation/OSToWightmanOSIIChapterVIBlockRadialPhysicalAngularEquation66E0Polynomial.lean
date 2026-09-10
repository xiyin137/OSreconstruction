import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66QuantitativeInverseScale

/-!
# Reference-scale equation-(6.7) polynomial estimate

This is the quantitative Chapter VI.1 endpoint: the local-Weyl density at the
center has polynomial dependence on the reference inverse radius and center,
with no openness-selected scale remaining in the result.
-/

noncomputable section

open Complex Metric Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIStep4FullSchwartzAngularContinuationData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}

/-- Dimension/arity and OS-growth constant in the final reference-scale
equation-(6.7) estimate. -/
def equation66E0PolynomialConstant
    {d k : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc) : Real :=
  OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant G *
    osiiEquation66QuantitativeInverseScalePolynomialConstant d k ^
      G.scaleDegree *
    ((8 : Real) ^ (k * (d + 1)) * (4 : Real) ^ (k * (d + 1)))

theorem equation66E0PolynomialConstant_nonneg
    {d k : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc) :
    0 <= equation66E0PolynomialConstant G := by
  unfold equation66E0PolynomialConstant
  exact mul_nonneg
    (mul_nonneg
      (OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant_pos
        G).le
      (pow_nonneg
        (osiiEquation66QuantitativeInverseScalePolynomialConstant_nonneg d k) _))
    (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))

/-- Chapter VI.1 reference-scale `E0'` estimate.  All dependence on the
center and the reference radius is polynomial with explicit exponents. -/
theorem OSIIEquation66QuantitativeLocalWeylDensityData.norm_density_center_le_E0Polynomial
    {Zq : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}
    {D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Zq OS lgc}
    (A : OSIIEquation66QuantitativeLocalWeylDensityData D)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    (hrho_le : rho <= 16)
    (hZq : Zq = osiiEquation66QuantitativeSynchronizedData
      d k hrho center hcenter) :
    ‖A.data.density (osiiStep4ComplexOfRealImag
        (osiiStep4MultiGapXiHatCenter d k center) 0)‖ <=
      equation66E0PolynomialConstant G *
        (16 / rho) ^ (2 * G.scaleDegree) *
        (1 + norm center) ^ (G.scaleDegree + G.growthDegree) := by
  let M := G.scaleDegree
  let N := G.growthDegree
  let q := k * (d + 1)
  let C0 :=
    OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant G
  let C := osiiEquation66QuantitativeInverseScalePolynomialConstant d k
  let R := 16 / rho
  let X := 1 + norm center
  let V := (8 : Real) ^ q * (4 : Real) ^ q
  have hC0 : 0 <= C0 := by
    dsimp [C0]
    exact
      (OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant_pos
        G).le
  have hC : 0 <= C :=
    osiiEquation66QuantitativeInverseScalePolynomialConstant_nonneg d k
  have hR : 0 <= R := by dsimp [R]; positivity
  have hX : 0 <= X := by dsimp [X]; positivity
  have hscaleBase : 0 <= 16 / A.data.scale :=
    div_nonneg (by norm_num) A.data.scale_pos.le
  have hinverse : 16 / A.data.scale <= C * R ^ 2 * X := by
    simpa only [C, R, X] using A.inverse_scale_le hrho_le hZq
  have hinversePow :
      (16 / A.data.scale) ^ M <= (C * R ^ 2 * X) ^ M :=
    pow_le_pow_left₀ hscaleBase hinverse M
  have hscaleHalf : A.data.scale / 2 <= 8 := by
    nlinarith [A.data.scale_le_sixteen]
  have hscaleQuarter : A.data.scale / 4 <= 4 := by
    nlinarith [A.data.scale_le_sixteen]
  have hhalfPow :
      (A.data.scale / 2) ^ q <= (8 : Real) ^ q :=
    pow_le_pow_left₀ (div_nonneg A.data.scale_pos.le (by norm_num))
      hscaleHalf q
  have hquarterPow :
      (A.data.scale / 4) ^ q <= (4 : Real) ^ q :=
    pow_le_pow_left₀ (div_nonneg A.data.scale_pos.le (by norm_num))
      hscaleQuarter q
  have hvolume :
      (A.data.scale / 2) ^ q * (A.data.scale / 4) ^ q <= V := by
    dsimp only [V]
    exact mul_le_mul hhalfPow hquarterPow
      (pow_nonneg (div_nonneg A.data.scale_pos.le (by norm_num)) _)
      (pow_nonneg (by norm_num : (0 : Real) <= 8) _)
  have hvolume0 : 0 <=
      (A.data.scale / 2) ^ q * (A.data.scale / 4) ^ q :=
    mul_nonneg
      (pow_nonneg (div_nonneg A.data.scale_pos.le (by norm_num)) _)
      (pow_nonneg (div_nonneg A.data.scale_pos.le (by norm_num)) _)
  have hXN : 0 <= X ^ N := pow_nonneg hX _
  have hcoeffBound :
      C0 * (16 / A.data.scale) ^ M * X ^ N <=
        C0 * (C * R ^ 2 * X) ^ M * X ^ N :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinversePow hC0) hXN
  have hnewCoeff0 : 0 <= C0 * (C * R ^ 2 * X) ^ M * X ^ N :=
    mul_nonneg
      (mul_nonneg hC0 (pow_nonneg (by positivity) _)) hXN
  have hraw := A.norm_density_center_le_mzPolynomial_mul_supportVolume G
  calc
    ‖A.data.density (osiiStep4ComplexOfRealImag
        (osiiStep4MultiGapXiHatCenter d k center) 0)‖ <=
      (C0 * (16 / A.data.scale) ^ M * X ^ N) *
        ((A.data.scale / 2) ^ q * (A.data.scale / 4) ^ q) := by
      simpa only [C0, M, N, X, q] using hraw
    _ <= (C0 * (C * R ^ 2 * X) ^ M * X ^ N) * V := by
      calc
        (C0 * (16 / A.data.scale) ^ M * X ^ N) *
            ((A.data.scale / 2) ^ q * (A.data.scale / 4) ^ q) <=
          (C0 * (C * R ^ 2 * X) ^ M * X ^ N) *
            ((A.data.scale / 2) ^ q * (A.data.scale / 4) ^ q) :=
          mul_le_mul_of_nonneg_right hcoeffBound hvolume0
        _ <= (C0 * (C * R ^ 2 * X) ^ M * X ^ N) * V :=
          mul_le_mul_of_nonneg_left hvolume hnewCoeff0
    _ = equation66E0PolynomialConstant G *
        (16 / rho) ^ (2 * G.scaleDegree) *
        (1 + norm center) ^ (G.scaleDegree + G.growthDegree) := by
      have hpowR : (R ^ 2) ^ M = R ^ (2 * M) := by
        rw [pow_mul]
      have hpowX : X ^ M * X ^ N = X ^ (M + N) := by
        exact (pow_add X M N).symm
      have hpow : (C * R ^ 2 * X) ^ M =
          C ^ M * R ^ (2 * M) * X ^ M := by
        rw [mul_pow, mul_pow, hpowR]
      calc
        (C0 * (C * R ^ 2 * X) ^ M * X ^ N) * V =
            (C0 * C ^ M * V) * R ^ (2 * M) * (X ^ M * X ^ N) := by
          rw [hpow]
          ring
        _ = (C0 * C ^ M * V) * R ^ (2 * M) * X ^ (M + N) := by
          rw [hpowX]
        _ = equation66E0PolynomialConstant G *
            (16 / rho) ^ (2 * G.scaleDegree) *
            (1 + norm center) ^ (G.scaleDegree + G.growthDegree) := by
          simp only [equation66E0PolynomialConstant, C0, C, R, X, V,
            M, N, q]

end OSIIStep4FullSchwartzAngularContinuationData
end OSReconstruction
