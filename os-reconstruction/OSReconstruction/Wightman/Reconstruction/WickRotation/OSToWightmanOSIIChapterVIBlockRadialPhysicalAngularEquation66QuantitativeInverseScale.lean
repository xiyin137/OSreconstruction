import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66QuantitativeLocalWeyl

/-!
# Polynomial inverse-scale control for equation (6.6)

The explicit local-Weyl radius is bounded below by a fixed dimension/arity
coefficient times `rho / T`.  For the quantitative synchronized continuation,
this yields a polynomial bound with two inverse-radius powers and one center
growth factor.
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

/-- Dimension/arity coefficient in the lower bound for the explicit
first-carrier scale. -/
def osiiEquation66FirstCarrierLowerCoefficient
    (d k : Nat) [NeZero d] [NeZero k] : Real :=
  min (1 / 2)
    (osiiEquation66AngleAperture d k / (8 * (d : Real)))

theorem osiiEquation66FirstCarrierLowerCoefficient_pos
    (d k : Nat) [NeZero d] [NeZero k] :
    0 < osiiEquation66FirstCarrierLowerCoefficient d k := by
  unfold osiiEquation66FirstCarrierLowerCoefficient
  apply lt_min
  · norm_num
  · have hd : 0 < (d : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact div_pos (osiiEquation66AngleAperture_pos d k)
      (mul_pos (by norm_num) hd)

/-- The explicit first-carrier radius is bounded below by a fixed coefficient
times `rho / T`. -/
theorem osiiEquation66FirstCarrierScale_lower_bound
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T) :
    osiiEquation66FirstCarrierLowerCoefficient d k * rho / T <=
      osiiEquation66FirstCarrierScale d k rho T := by
  let c := osiiEquation66FirstCarrierLowerCoefficient d k
  let eta := osiiEquation66AngleAperture d k
  have hc : 0 < c :=
    osiiEquation66FirstCarrierLowerCoefficient_pos d k
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hd : 0 < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hcHalf : c <= 1 / 2 := by
    exact min_le_left _ _
  have hcAngle : c <= eta / (8 * (d : Real)) := by
    exact min_le_right _ _
  unfold osiiEquation66FirstCarrierScale
  apply le_min
  · calc
      c * rho / T <= (1 / 2) * rho / T := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcHalf hrho.le) hT0.le
      _ <= rho / 2 := by
        apply (div_le_iff₀ hT0).2
        have hmul := mul_le_mul_of_nonneg_left hT.le
          (show 0 <= rho / 2 by positivity)
        nlinarith
  · calc
      c * rho / T <= (eta / (8 * (d : Real))) * rho / T := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcAngle hrho.le) hT0.le
      _ = eta * rho / (8 * (d : Real) * T) := by
        field_simp [hd.ne', hT0.ne']

/-- Dimension/arity-only loss converting the explicit local-Weyl radius into
an inverse-scale estimate. -/
def osiiEquation66InverseLocalWeylScaleConstant
    (d k : Nat) [NeZero d] [NeZero k] : Real :=
  32 / osiiEquation66FirstCarrierLowerCoefficient d k

theorem osiiEquation66InverseLocalWeylScaleConstant_pos
    (d k : Nat) [NeZero d] [NeZero k] :
    0 < osiiEquation66InverseLocalWeylScaleConstant d k := by
  unfold osiiEquation66InverseLocalWeylScaleConstant
  exact div_pos (by norm_num)
    (osiiEquation66FirstCarrierLowerCoefficient_pos d k)

/-- Inverse explicit local-Weyl scale is linear in the common slope and the
reference inverse radius. -/
theorem osiiEquation66_inverse_quantitativeLocalWeylScale_le
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T) :
    16 / osiiEquation66QuantitativeLocalWeylScale d k rho T <=
      osiiEquation66InverseLocalWeylScaleConstant d k * T * (16 / rho) := by
  let c := osiiEquation66FirstCarrierLowerCoefficient d k
  let sigma := osiiEquation66QuantitativeLocalWeylScale d k rho T
  let C := osiiEquation66InverseLocalWeylScaleConstant d k
  have hc : 0 < c :=
    osiiEquation66FirstCarrierLowerCoefficient_pos d k
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hsigma : 0 < sigma := by
    dsimp [sigma, osiiEquation66QuantitativeLocalWeylScale]
    exact div_pos
      (osiiEquation66FirstCarrierScale_pos d k hrho hT0) (by norm_num)
  have hlower : c * rho / T / 32 <= sigma := by
    have h := osiiEquation66FirstCarrierScale_lower_bound d k hrho hT
    dsimp [sigma, osiiEquation66QuantitativeLocalWeylScale, c]
    exact div_le_div_of_nonneg_right h (by norm_num)
  have hfactor : 0 <= C * T * (16 / rho) := by
    exact mul_nonneg
      (mul_nonneg
        (osiiEquation66InverseLocalWeylScaleConstant_pos d k).le hT0.le)
      (div_nonneg (by norm_num) hrho.le)
  apply (div_le_iff₀ hsigma).2
  calc
    16 = (C * T * (16 / rho)) * (c * rho / T / 32) := by
      dsimp [C, c, osiiEquation66InverseLocalWeylScaleConstant]
      field_simp [hc.ne', hrho.ne', hT0.ne']
      rw [div_self
        (osiiEquation66FirstCarrierLowerCoefficient_pos d k).ne']
    _ <= (C * T * (16 / rho)) * sigma :=
      mul_le_mul_of_nonneg_left hlower hfactor

/-- Canonical synchronized continuation used by the quantitative
equation-(6.6) route. -/
noncomputable def osiiEquation66QuantitativeSynchronizedData
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter) :=
  osiiStep4QuantitativeSynchronizedMultiGapContinuationData
    d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)

theorem osiiEquation66QuantitativeSynchronizedData_T_le
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    (osiiEquation66QuantitativeSynchronizedData
      d k hrho center hcenter).uniform.T <=
      osiiStep4SynchronizedSlopePolynomialConstant d k *
        (16 / rho) * (1 + norm center) := by
  have hraw :=
    osiiStep4QuantitativeSynchronizedMultiGapContinuationData_T_le
      d k hrho hrho_le
        (osiiStep4MultiGapXiHatCenter d k center)
        (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)
  have hXi :=
    OSIIStep4MultiGapSelectedCommonSlopeData.norm_osiiStep4MultiGapXiHatCenter_le
      d k center
  have hcoeff : 0 <=
      osiiStep4SynchronizedSlopePolynomialConstant d k * (16 / rho) :=
    mul_nonneg
      (osiiStep4SynchronizedSlopePolynomialConstant_nonneg d k)
      (div_nonneg (by norm_num) hrho.le)
  calc
    (osiiEquation66QuantitativeSynchronizedData
      d k hrho center hcenter).uniform.T <=
        osiiStep4SynchronizedSlopePolynomialConstant d k *
          (16 / rho) *
            (1 + norm (osiiStep4MultiGapXiHatCenter d k center)) := by
      simpa only [osiiEquation66QuantitativeSynchronizedData] using hraw
    _ <= osiiStep4SynchronizedSlopePolynomialConstant d k *
        (16 / rho) * (1 + norm center) :=
      mul_le_mul_of_nonneg_left (by linarith) hcoeff

/-- Combined dimension/arity loss for the explicit synchronized local-Weyl
inverse scale. -/
def osiiEquation66QuantitativeInverseScalePolynomialConstant
    (d k : Nat) [NeZero d] [NeZero k] : Real :=
  osiiEquation66InverseLocalWeylScaleConstant d k *
    osiiStep4SynchronizedSlopePolynomialConstant d k

theorem osiiEquation66QuantitativeInverseScalePolynomialConstant_nonneg
    (d k : Nat) [NeZero d] [NeZero k] :
    0 <= osiiEquation66QuantitativeInverseScalePolynomialConstant d k := by
  unfold osiiEquation66QuantitativeInverseScalePolynomialConstant
  exact mul_nonneg
    (osiiEquation66InverseLocalWeylScaleConstant_pos d k).le
    (osiiStep4SynchronizedSlopePolynomialConstant_nonneg d k)

/-- Final inverse-radius estimate for the explicit synchronized local-Weyl
scale. -/
theorem osiiEquation66_quantitativeSynchronized_inverseLocalWeylScale_le
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    let Zq := osiiEquation66QuantitativeSynchronizedData
      d k hrho center hcenter
    16 / osiiEquation66QuantitativeLocalWeylScale
        d k rho Zq.uniform.T <=
      osiiEquation66QuantitativeInverseScalePolynomialConstant d k *
        (16 / rho) ^ 2 * (1 + norm center) := by
  dsimp only
  let Zq := osiiEquation66QuantitativeSynchronizedData
    d k hrho center hcenter
  let Cinv := osiiEquation66InverseLocalWeylScaleConstant d k
  let Cslope := osiiStep4SynchronizedSlopePolynomialConstant d k
  let R := 16 / rho
  let N := 1 + norm center
  have hCinv : 0 <= Cinv :=
    (osiiEquation66InverseLocalWeylScaleConstant_pos d k).le
  have hR : 0 <= R := by dsimp [R]; positivity
  have hT := osiiEquation66QuantitativeSynchronizedData_T_le
    d k hrho hrho_le center hcenter
  have hinv := osiiEquation66_inverse_quantitativeLocalWeylScale_le
    d k hrho Zq.uniform.hT
  calc
    16 / osiiEquation66QuantitativeLocalWeylScale d k rho Zq.uniform.T <=
        Cinv * Zq.uniform.T * R := by
      simpa only [Cinv, R] using hinv
    _ <= Cinv * (Cslope * R * N) * R := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (by simpa only [Zq, Cslope, R, N] using hT) hCinv) hR
    _ = osiiEquation66QuantitativeInverseScalePolynomialConstant d k *
        (16 / rho) ^ 2 * (1 + norm center) := by
      simp only [osiiEquation66QuantitativeInverseScalePolynomialConstant,
        Cinv, Cslope, R, N]
      ring

/-- The scale stored by the quantitative density package satisfies the final
polynomial inverse-radius bound when the synchronized continuation is the
explicit one. -/
theorem OSIIEquation66QuantitativeLocalWeylDensityData.inverse_scale_le
    {Zq : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}
    {D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Zq OS lgc}
    (A : OSIIEquation66QuantitativeLocalWeylDensityData D)
    (hrho_le : rho <= 16)
    (hZq : Zq = osiiEquation66QuantitativeSynchronizedData
      d k hrho center hcenter) :
    16 / A.data.scale <=
      osiiEquation66QuantitativeInverseScalePolynomialConstant d k *
        (16 / rho) ^ 2 * (1 + norm center) := by
  rw [A.scale_eq, hZq]
  exact osiiEquation66_quantitativeSynchronized_inverseLocalWeylScale_le
    d k hrho hrho_le center hcenter

end OSIIStep4FullSchwartzAngularContinuationData
end OSReconstruction
