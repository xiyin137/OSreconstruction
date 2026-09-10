/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformMultiGapDegree
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltRealEdgeGrowth














noncomputable section

open Complex Metric Set
open scoped BigOperators Classical

namespace OSReconstruction

open OSIIStep4FullSchwartzAngularContinuationData

/-- The first-carrier coefficient is bounded below by one explicit inverse
linear arity factor.  The estimate uses only tan x >= x and pi >= 1. -/
theorem osiiEquation66FirstCarrierLowerCoefficient_ge_inv_arity
    (d k : Nat) [NeZero d] [NeZero k] :
    1 / (128 * (d : Real) *
        (Fintype.card (osiiAxisPairIndex d) : Real) * (k : Real)) <=
      osiiEquation66FirstCarrierLowerCoefficient d k := by
  let c : Real := Fintype.card (osiiAxisPairIndex d)
  let x : Real := Real.pi /
    (16 * ((k * Fintype.card (osiiAxisPairIndex d) : Nat) : Real))
  have hd_nat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hk_nat : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hc_nat : 0 < Fintype.card (osiiAxisPairIndex d) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨0, hd_nat⟩, true)⟩
  have hd_one : (1 : Real) <= d := by exact_mod_cast hd_nat
  have hk_one : (1 : Real) <= k := by exact_mod_cast hk_nat
  have hc_one : (1 : Real) <= c := by
    dsimp [c]
    exact_mod_cast hc_nat
  have hd_pos : (0 : Real) < d := lt_of_lt_of_le (by norm_num) hd_one
  have hk_pos : (0 : Real) < k := lt_of_lt_of_le (by norm_num) hk_one
  have hc_pos : 0 < c := lt_of_lt_of_le (by norm_num) hc_one
  have hkc :
      ((k * Fintype.card (osiiAxisPairIndex d) : Nat) : Real) =
        (k : Real) * c := by
    dsimp [c]
    norm_num
  have hx_nonneg : 0 <= x := by
    dsimp [x]
    positivity
  have hx_lt : x < Real.pi / 2 := by
    dsimp [x]
    have hden : (2 : Real) <
        16 * ((k * Fintype.card (osiiAxisPairIndex d) : Nat) : Real) := by
      rw [hkc]
      nlinarith [mul_pos hk_pos hc_pos]
    exact (div_lt_div_iff_of_pos_left Real.pi_pos (by positivity)
      (by positivity)).mpr hden
  have htan : x <= Real.tan x := Real.le_tan hx_nonneg hx_lt
  have hpi : (1 : Real) <= Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hbase :
      1 / (16 * (k : Real) * c) <=
        Real.pi / (16 * (k : Real) * c) := by
    exact div_le_div_of_nonneg_right hpi (by positivity)
  have hangle :
      1 / (16 * (k : Real) * c) <=
        osiiEquation66AngleAperture d k := by
    calc
      1 / (16 * (k : Real) * c) <=
          Real.pi / (16 * (k : Real) * c) := hbase
      _ = x := by
        dsimp [x]
        rw [hkc]
        ring
      _ <= osiiEquation66AngleAperture d k := by
        simpa [x, osiiEquation66AngleAperture] using htan
  have hangle_div :
      1 / (128 * (d : Real) * c * (k : Real)) <=
        osiiEquation66AngleAperture d k / (8 * (d : Real)) := by
    calc
      1 / (128 * (d : Real) * c * (k : Real)) =
          (1 / (16 * (k : Real) * c)) / (8 * (d : Real)) := by
        field_simp
        ring
      _ <= osiiEquation66AngleAperture d k / (8 * (d : Real)) :=
        div_le_div_of_nonneg_right hangle (by positivity)
  have hden_ge :
      (2 : Real) <= 128 * (d : Real) * c * (k : Real) := by
    calc
      (2 : Real) <= 128 * 1 * 1 * 1 := by norm_num
      _ <= 128 * (d : Real) * c * (k : Real) := by gcongr
  have hhalf :
      1 / (128 * (d : Real) * c * (k : Real)) <= (1 : Real) / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hden_ge
  unfold osiiEquation66FirstCarrierLowerCoefficient
  apply le_min
  · simpa [c] using hhalf
  · simpa [c] using hangle_div

/-- The inverse local-Weyl scale loses only one arity power. -/
theorem osiiEquation66InverseLocalWeylScaleConstant_le_arity
    (d k : Nat) [NeZero d] [NeZero k] :
    osiiEquation66InverseLocalWeylScaleConstant d k <=
      4096 * (d : Real) *
        (Fintype.card (osiiAxisPairIndex d) : Real) * (k : Real) := by
  let c : Real := Fintype.card (osiiAxisPairIndex d)
  let a : Real := 1 / (128 * (d : Real) * c * (k : Real))
  have hc_pos : 0 < c := by
    dsimp [c]
    exact_mod_cast
      (Fintype.card_pos_iff.mpr
        ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)⟩ :
          0 < Fintype.card (osiiAxisPairIndex d))
  have ha_pos : 0 < a := by
    dsimp [a]
    apply one_div_pos.mpr
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num)
          (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)))
        hc_pos)
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k))
  have hlo :
      a <= osiiEquation66FirstCarrierLowerCoefficient d k := by
    simpa [a, c] using
      osiiEquation66FirstCarrierLowerCoefficient_ge_inv_arity d k
  calc
    osiiEquation66InverseLocalWeylScaleConstant d k =
        32 / osiiEquation66FirstCarrierLowerCoefficient d k := by
      rfl
    _ <= 32 / a :=
      div_le_div_of_nonneg_left (by norm_num) ha_pos hlo
    _ = 4096 * (d : Real) * c * (k : Real) := by
      dsimp [a]
      field_simp
      ring
    _ = 4096 * (d : Real) *
        (Fintype.card (osiiAxisPairIndex d) : Real) * (k : Real) := by
      rfl

/-- The sum of selected inverse difference-coordinate norms is quadratic in
ambient arity. -/
theorem osiiStep4MultiGapReconstructionNormSum_le_arity_sq
    (d k : Nat) [NeZero d] [NeZero k] :
    osiiStep4MultiGapReconstructionNormSum d k <=
      4 * (k : Real) ^ 2 := by
  have hk_nat : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hk_one : (1 : Real) <= k := by exact_mod_cast hk_nat
  unfold osiiStep4MultiGapReconstructionNormSum
  calc
    ∑ i : Fin k,
        (‖(BHW.realDiffCoordCLE
              (i.val + 1) d).symm.toContinuousLinearMap‖ +
          ‖(BHW.realDiffCoordCLE
              (osiiStep4MultiGapAfterCount i + 1) d
            ).symm.toContinuousLinearMap‖) <=
      ∑ _i : Fin k, (2 * ((k : Real) + 1)) := by
        apply Finset.sum_le_sum
        intro i _hi
        have hleft :
            ‖(BHW.realDiffCoordCLE
                (i.val + 1) d).symm.toContinuousLinearMap‖ <=
              (k : Real) + 1 := by
          calc
            ‖(BHW.realDiffCoordCLE
                (i.val + 1) d).symm.toContinuousLinearMap‖ <=
              ((i.val + 1 : Nat) : Real) + 1 :=
              norm_realDiffCoordCLE_symm_le_arity_add_one (i.val + 1) d
            _ <= (k : Real) + 1 := by
              norm_cast
              omega
        have hright :
            ‖(BHW.realDiffCoordCLE
                (osiiStep4MultiGapAfterCount i + 1) d
              ).symm.toContinuousLinearMap‖ <=
              (k : Real) + 1 := by
          calc
            ‖(BHW.realDiffCoordCLE
                (osiiStep4MultiGapAfterCount i + 1) d
              ).symm.toContinuousLinearMap‖ <=
              ((osiiStep4MultiGapAfterCount i + 1 : Nat) : Real) + 1 :=
              norm_realDiffCoordCLE_symm_le_arity_add_one
                (osiiStep4MultiGapAfterCount i + 1) d
            _ <= (k : Real) + 1 := by
              norm_cast
              unfold osiiStep4MultiGapAfterCount
              omega
        linarith
    _ = (k : Real) * (2 * ((k : Real) + 1)) := by simp
    _ <= (k : Real) * (2 * (2 * (k : Real))) := by
      apply mul_le_mul_of_nonneg_left
      · nlinarith
      · positivity
    _ = 4 * (k : Real) ^ 2 := by ring

/-- Fixed coefficient for the coherent synchronized-slope contribution. -/
def osiiStep4CoherentSlopeArityConstant (d : Nat) [NeZero d] : Real :=
  10 + 6 * (osiiStep4PositiveTimeBasepointCutoffNormBound d + 17)

theorem osiiStep4CoherentSlopePolynomialConstant_le_arity
    (d k : Nat) [NeZero d] [NeZero k] :
    osiiStep4CoherentSlopePolynomialConstant d k <=
      osiiStep4CoherentSlopeArityConstant d * (k : Real) := by
  have hk_nat : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hk_one : (1 : Real) <= k := by exact_mod_cast hk_nat
  let B := osiiStep4PositiveTimeBasepointCutoffNormBound d
  have hB : 0 <= B := by
    dsimp [B]
    exact osiiStep4PositiveTimeBasepointCutoffNormBound_nonneg d
  have hnorm :
      ‖(BHW.realDiffCoordCLE
          (k + 1) d).symm.toContinuousLinearMap‖ <=
        (k : Real) + 2 := by
    calc
      ‖(BHW.realDiffCoordCLE
          (k + 1) d).symm.toContinuousLinearMap‖ <=
        ((k + 1 : Nat) : Real) + 1 :=
        norm_realDiffCoordCLE_symm_le_arity_add_one (k + 1) d
      _ = (k : Real) + 2 := by push_cast; ring
  have hnorm_three :
      ‖(BHW.realDiffCoordCLE
          (k + 1) d).symm.toContinuousLinearMap‖ <=
        3 * (k : Real) := by
    exact hnorm.trans (by nlinarith)
  have hB17 : 0 <= B + 17 := by linarith
  unfold osiiStep4CoherentSlopePolynomialConstant
  calc
    10 + 2 *
        ‖(BHW.realDiffCoordCLE
          (k + 1) d).symm.toContinuousLinearMap‖ *
          (osiiStep4PositiveTimeBasepointCutoffNormBound d + 17) <=
      10 + 2 * (3 * (k : Real)) * (B + 17) := by
        dsimp [B] at hB17 ⊢
        gcongr
    _ = 10 + 6 * (B + 17) * (k : Real) := by ring
    _ <= (10 + 6 * (B + 17)) * (k : Real) := by
      have hmul : 0 <= 6 * (B + 17) * (k : Real) := by positivity
      nlinarith
    _ = osiiStep4CoherentSlopeArityConstant d * (k : Real) := by
      rfl

/-- Fixed coefficient for the full synchronized-slope quadratic bound. -/
def osiiStep4SynchronizedSlopeArityConstant (d : Nat) [NeZero d] : Real :=
  2 + 128 + osiiStep4CoherentSlopeArityConstant d

theorem osiiStep4SynchronizedSlopePolynomialConstant_le_arity_sq
    (d k : Nat) [NeZero d] [NeZero k] :
    osiiStep4SynchronizedSlopePolynomialConstant d k <=
      osiiStep4SynchronizedSlopeArityConstant d * (k : Real) ^ 2 := by
  have hk_nat : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hk_one : (1 : Real) <= k := by exact_mod_cast hk_nat
  have hk_sq_one : (1 : Real) <= (k : Real) ^ 2 := by
    nlinarith [sq_nonneg ((k : Real) - 1)]
  have hk_le_sq : (k : Real) <= (k : Real) ^ 2 := by
    nlinarith [sq_nonneg ((k : Real) - 1)]
  have hsum := osiiStep4MultiGapReconstructionNormSum_le_arity_sq d k
  have hcoh := osiiStep4CoherentSlopePolynomialConstant_le_arity d k
  have hcoh_nonneg : 0 <= osiiStep4CoherentSlopeArityConstant d := by
    unfold osiiStep4CoherentSlopeArityConstant
    have hB := osiiStep4PositiveTimeBasepointCutoffNormBound_nonneg d
    positivity
  unfold osiiStep4SynchronizedSlopePolynomialConstant
  calc
    (2 + 32 * osiiStep4MultiGapReconstructionNormSum d k) +
        osiiStep4CoherentSlopePolynomialConstant d k <=
      (2 + 32 * (4 * (k : Real) ^ 2)) +
        osiiStep4CoherentSlopeArityConstant d * (k : Real) := by
        gcongr
    _ <= (2 + 128 + osiiStep4CoherentSlopeArityConstant d) *
        (k : Real) ^ 2 := by
      calc
        (2 + 32 * (4 * (k : Real) ^ 2)) +
            osiiStep4CoherentSlopeArityConstant d * (k : Real) =
          2 + 128 * (k : Real) ^ 2 +
            osiiStep4CoherentSlopeArityConstant d * (k : Real) := by ring
        _ <= 2 * (k : Real) ^ 2 + 128 * (k : Real) ^ 2 +
            osiiStep4CoherentSlopeArityConstant d * (k : Real) ^ 2 := by
          apply add_le_add
          · apply add_le_add
            · nlinarith
            · exact le_rfl
          · exact mul_le_mul_of_nonneg_left hk_le_sq hcoh_nonneg
        _ = (2 + 128 + osiiStep4CoherentSlopeArityConstant d) *
            (k : Real) ^ 2 := by ring
    _ = osiiStep4SynchronizedSlopeArityConstant d * (k : Real) ^ 2 := by
      rfl

/-- Fixed coefficient for the cubic synchronized inverse-scale bound. -/
def osiiEquation66QuantitativeInverseScaleArityConstant
    (d : Nat) [NeZero d] : Real :=
  4096 * (d : Real) *
    (Fintype.card (osiiAxisPairIndex d) : Real) *
    osiiStep4SynchronizedSlopeArityConstant d

theorem osiiEquation66QuantitativeInverseScalePolynomialConstant_le_arity_cube
    (d k : Nat) [NeZero d] [NeZero k] :
    osiiEquation66QuantitativeInverseScalePolynomialConstant d k <=
      osiiEquation66QuantitativeInverseScaleArityConstant d *
        (k : Real) ^ 3 := by
  have hinv := osiiEquation66InverseLocalWeylScaleConstant_le_arity d k
  have hslope :=
    osiiStep4SynchronizedSlopePolynomialConstant_le_arity_sq d k
  have hslope_nonneg : 0 <= osiiStep4SynchronizedSlopePolynomialConstant d k :=
    osiiStep4SynchronizedSlopePolynomialConstant_nonneg d k
  have hinv_rhs_nonneg :
      0 <= 4096 * (d : Real) *
        (Fintype.card (osiiAxisPairIndex d) : Real) * (k : Real) := by
    positivity
  unfold osiiEquation66QuantitativeInverseScalePolynomialConstant
  calc
    osiiEquation66InverseLocalWeylScaleConstant d k *
        osiiStep4SynchronizedSlopePolynomialConstant d k <=
      (4096 * (d : Real) *
          (Fintype.card (osiiAxisPairIndex d) : Real) * (k : Real)) *
        (osiiStep4SynchronizedSlopeArityConstant d * (k : Real) ^ 2) :=
      mul_le_mul hinv hslope hslope_nonneg hinv_rhs_nonneg
    _ = osiiEquation66QuantitativeInverseScaleArityConstant d *
        (k : Real) ^ 3 := by
      unfold osiiEquation66QuantitativeInverseScaleArityConstant
      rw [show (k : Real) ^ 3 = (k : Real) * (k : Real) ^ 2 by ring]
      ring

/-- A fixed polynomial base raised to an arity-linear degree still has the
standard all-arity shape.  The fixed coefficient C^S is absorbed once,
while the k^p part contributes p*S to the arity rate. -/
theorem polynomialBase_pow_arityLinear_le_arityMajorant
    (C : Real) (hC : 0 <= C) (p S k : Nat) (hk : 0 < k) :
    (C * (k : Real) ^ p) ^ (k * S) <=
      max (C ^ S) 1 *
        (k : Real) ^
          (k * (Nat.ceil (max (C ^ S) 1) + p * S)) := by
  let A := Nat.ceil (max (C ^ S) 1)
  have hfixed :
      (C ^ S) ^ k <=
        max (C ^ S) 1 * (k : Real) ^ (k * A) := by
    simpa [A] using
      nonneg_pow_le_max_mul_arityPow
        (C ^ S) (pow_nonneg hC _) k hk
  have hkp_nonneg : 0 <= (k : Real) ^ (k * (p * S)) := by positivity
  have hCpow : C ^ (k * S) = (C ^ S) ^ k := by
    rw [show k * S = S * k by ring, ← pow_mul]
  have hkpow :
      ((k : Real) ^ p) ^ (k * S) =
        (k : Real) ^ (k * (p * S)) := by
    rw [← pow_mul]
    congr 1
    ring
  calc
    (C * (k : Real) ^ p) ^ (k * S) =
        (C ^ S) ^ k * (k : Real) ^ (k * (p * S)) := by
      rw [mul_pow, hCpow, hkpow]
    _ <= (max (C ^ S) 1 * (k : Real) ^ (k * A)) *
        (k : Real) ^ (k * (p * S)) :=
      mul_le_mul_of_nonneg_right hfixed hkp_nonneg
    _ = max (C ^ S) 1 *
        (k : Real) ^
          (k * (Nat.ceil (max (C ^ S) 1) + p * S)) := by
      dsimp [A]
      rw [show k * (Nat.ceil (max (C ^ S) 1) + p * S) =
          k * Nat.ceil (max (C ^ S) 1) + k * (p * S) by ring]
      calc
        max (C ^ S) 1 * (k : Real) ^ (k * Nat.ceil (max (C ^ S) 1)) *
            (k : Real) ^ (k * (p * S)) =
          max (C ^ S) 1 *
            ((k : Real) ^ (k * Nat.ceil (max (C ^ S) 1)) *
              (k : Real) ^ (k * (p * S))) := by ring
        _ = max (C ^ S) 1 *
            (k : Real) ^
              (k * Nat.ceil (max (C ^ S) 1) + k * (p * S)) := by
          rw [← pow_add]

/-- Fixed coefficient for the linear centered-target growth factor. -/
def osiiEquation66CenteredTargetArityConstant
    (d : Nat) [NeZero d] : Real :=
  1 + Real.exp osiiEquation66UniversalStripParameters.radius *
    (Fintype.card (osiiAxisPairIndex d) : Real) * 3

theorem osiiEquation66CenteredTargetGrowthFactor_le_arity
    (d k : Nat) [NeZero d] [NeZero k] :
    osiiEquation66CenteredTargetGrowthFactor d k <=
      osiiEquation66CenteredTargetArityConstant d * (k : Real) := by
  have hk_nat : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hk_one : (1 : Real) <= k := by exact_mod_cast hk_nat
  let L : Real :=
    Real.exp osiiEquation66UniversalStripParameters.radius *
      (Fintype.card (osiiAxisPairIndex d) : Real) * 3
  have hL : 0 <= L := by
    dsimp [L]
    positivity
  unfold osiiEquation66CenteredTargetGrowthFactor
    osiiEquation66CenteredTargetArityConstant
  dsimp [L] at hL
  calc
    1 + Real.exp osiiEquation66UniversalStripParameters.radius *
        ((k : Real) * (Fintype.card (osiiAxisPairIndex d) : Real) * 3) =
      1 + L * (k : Real) := by
        dsimp [L]
        ring
    _ <= (k : Real) + L * (k : Real) := by nlinarith
    _ = (1 + Real.exp osiiEquation66UniversalStripParameters.radius *
        (Fintype.card (osiiAxisPairIndex d) : Real) * 3) *
          (k : Real) := by
        dsimp [L]
        ring

/-- Per-particle rate for the fixed equation-(6.6) volume factor. -/
def osiiEquation66VolumeArityRate (d : Nat) : Nat :=
  Nat.ceil (max ((32 : Real) ^ (d + 1)) 1)

/-- Fixed coefficient for the equation-(6.6) volume factor. -/
def osiiEquation66VolumeArityConstant (d : Nat) : Real :=
  max ((32 : Real) ^ (d + 1)) 1

theorem osiiEquation66VolumeFactor_le_arityMajorant
    (d k : Nat) (hk : 0 < k) :
    (8 : Real) ^ (k * (d + 1)) *
        (4 : Real) ^ (k * (d + 1)) <=
      osiiEquation66VolumeArityConstant d *
        (k : Real) ^ (k * osiiEquation66VolumeArityRate d) := by
  have hfixed :
      (((32 : Real) ^ (d + 1)) ^ k) <=
        max ((32 : Real) ^ (d + 1)) 1 *
          (k : Real) ^
            (k * Nat.ceil (max ((32 : Real) ^ (d + 1)) 1)) := by
    exact nonneg_pow_le_max_mul_arityPow
      ((32 : Real) ^ (d + 1)) (by positivity) k hk
  calc
    (8 : Real) ^ (k * (d + 1)) *
        (4 : Real) ^ (k * (d + 1)) =
      ((32 : Real) ^ (d + 1)) ^ k := by
        rw [← mul_pow]
        norm_num
        rw [show k * (d + 1) = (d + 1) * k by ring, ← pow_mul]
    _ <= max ((32 : Real) ^ (d + 1)) 1 *
          (k : Real) ^
            (k * Nat.ceil (max ((32 : Real) ^ (d + 1)) 1)) := hfixed
    _ = osiiEquation66VolumeArityConstant d *
        (k : Real) ^ (k * osiiEquation66VolumeArityRate d) := by
      rfl

/-- Per-particle rate for the fixed equation-(6.21) normalization base. -/
def osiiEquation621NormalizationArityRate (S : Nat) : Nat :=
  Nat.ceil (max ((16 : Real) ^ (2 * S)) 1)

/-- Fixed coefficient for the equation-(6.21) normalization base. -/
def osiiEquation621NormalizationArityConstant (S : Nat) : Real :=
  max ((16 : Real) ^ (2 * S)) 1

theorem osiiEquation621NormalizationFactor_le_arityMajorant
    (S k : Nat) (hk : 0 < k) :
    (16 : Real) ^ (2 * (k * S)) <=
      osiiEquation621NormalizationArityConstant S *
        (k : Real) ^ (k * osiiEquation621NormalizationArityRate S) := by
  have hfixed :
      (((16 : Real) ^ (2 * S)) ^ k) <=
        max ((16 : Real) ^ (2 * S)) 1 *
          (k : Real) ^
            (k * Nat.ceil (max ((16 : Real) ^ (2 * S)) 1)) := by
    exact nonneg_pow_le_max_mul_arityPow
      ((16 : Real) ^ (2 * S)) (by positivity) k hk
  calc
    (16 : Real) ^ (2 * (k * S)) =
        ((16 : Real) ^ (2 * S)) ^ k := by
      rw [show 2 * (k * S) = (2 * S) * k by ring, ← pow_mul]
    _ <= max ((16 : Real) ^ (2 * S)) 1 *
          (k : Real) ^
            (k * Nat.ceil (max ((16 : Real) ^ (2 * S)) 1)) := hfixed
    _ = osiiEquation621NormalizationArityConstant S *
        (k : Real) ^ (k * osiiEquation621NormalizationArityRate S) := by
      rfl

namespace OSIIUniformMultiGapGrowthData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}

/-- One arity rate absorbs the packet coefficient, centered target, cubic
inverse radius, volume, and VI.1 normalization factors. -/
def densityArityRate (D : OSIIUniformMultiGapGrowthData d OS lgc) : Nat :=
  D.arityRate +
    (Nat.ceil (max (osiiEquation66CenteredTargetArityConstant d ^ D.growthRate) 1) +
      D.growthRate) +
    (Nat.ceil (max (osiiEquation66QuantitativeInverseScaleArityConstant d ^
      D.scaleRate) 1) + 3 * D.scaleRate) +
    osiiEquation66VolumeArityRate d +
    osiiEquation621NormalizationArityRate D.scaleRate

/-- A coefficient fixed before arity for the actual OS-built density. -/
def densityArityConstant (D : OSIIUniformMultiGapGrowthData d OS lgc) : Real :=
  1 +
    (1 + D.coefficient *
      max (osiiEquation66CenteredTargetArityConstant d ^ D.growthRate) 1) *
    max (osiiEquation66QuantitativeInverseScaleArityConstant d ^ D.scaleRate) 1 *
    osiiEquation66VolumeArityConstant d *
    osiiEquation621NormalizationArityConstant D.scaleRate

theorem densityArityConstant_pos
    (D : OSIIUniformMultiGapGrowthData d OS lgc) :
    0 < D.densityArityConstant := by
  have hA := D.coefficient_nonneg
  unfold densityArityConstant osiiEquation66VolumeArityConstant
    osiiEquation621NormalizationArityConstant
  positivity

/-- The exact coefficient produced by the non-circular VI.1 density
constructor has the required all-arity bound. -/
theorem densityConstant_le_arityMajorant
    (D : OSIIUniformMultiGapGrowthData d OS lgc)
    (k : Nat) [NeZero k] :
    equation66E0PolynomialConstant (D.toScaleBoundData k) *
        (16 : Real) ^ (2 * (D.toScaleBoundData k).scaleDegree) + 1 <=
      D.densityArityConstant * (k : Real) ^ (k * D.densityArityRate) := by
  let G := D.toScaleBoundData k
  let T := max (osiiEquation66CenteredTargetArityConstant d ^ D.growthRate) 1
  let I := max (osiiEquation66QuantitativeInverseScaleArityConstant d ^
    D.scaleRate) 1
  let V := osiiEquation66VolumeArityConstant d
  let N := osiiEquation621NormalizationArityConstant D.scaleRate
  let t := Nat.ceil T + D.growthRate
  let s := Nat.ceil I + 3 * D.scaleRate
  let v := osiiEquation66VolumeArityRate d
  let n := osiiEquation621NormalizationArityRate D.scaleRate
  let M := 1 + D.coefficient * T
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkOne : (1 : Real) <= k := by exact_mod_cast hk
  have hA := D.coefficient_nonneg
  have hT : 0 <= T := le_trans (by norm_num) (le_max_right _ _)
  have hI : 0 <= I := le_trans (by norm_num) (le_max_right _ _)
  have hV : 0 <= V := le_trans (by norm_num) (le_max_right _ _)
  have hN : 0 <= N := le_trans (by norm_num) (le_max_right _ _)
  have hM : 0 <= M := by dsimp [M]; positivity
  have hscale : G.scaleDegree = k * D.scaleRate := D.scaleDegree_eq k
  have hgrowth : G.growthDegree = k * D.growthRate := D.growthDegree_eq k
  have htarget :
      osiiEquation66CenteredTargetGrowthFactor d k ^ G.growthDegree <=
        T * (k : Real) ^ (k * t) := by
    rw [hgrowth]
    calc
      _ <= (osiiEquation66CenteredTargetArityConstant d * (k : Real)) ^
          (k * D.growthRate) :=
        pow_le_pow_left₀ (osiiEquation66CenteredTargetGrowthFactor_pos d k).le
          (osiiEquation66CenteredTargetGrowthFactor_le_arity d k) _
      _ <= T * (k : Real) ^ (k * t) := by
        simpa [T, t] using
          polynomialBase_pow_arityLinear_le_arityMajorant
            (osiiEquation66CenteredTargetArityConstant d)
            (by unfold osiiEquation66CenteredTargetArityConstant; positivity)
            1 D.growthRate k hk
  have hpacket : G.constant <= D.coefficient * (k : Real) ^ (k * D.arityRate) :=
    D.constant_le k
  have hMZ :
      OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant G <=
        M * (k : Real) ^ (k * (D.arityRate + t)) := by
    have hmul := mul_le_mul hpacket htarget
      (pow_nonneg (osiiEquation66CenteredTargetGrowthFactor_pos d k).le _)
      (mul_nonneg hA (by positivity))
    have hpow : (1 : Real) <= (k : Real) ^ (k * (D.arityRate + t)) :=
      one_le_pow₀ hkOne
    have hproduct :
        (D.coefficient * (k : Real) ^ (k * D.arityRate)) *
            (T * (k : Real) ^ (k * t)) =
          (D.coefficient * T) *
            (k : Real) ^ (k * (D.arityRate + t)) := by
      rw [Nat.mul_add, pow_add]
      ring
    rw [hproduct] at hmul
    dsimp [OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant, M]
    nlinarith
  have hinverse :
      osiiEquation66QuantitativeInverseScalePolynomialConstant d k ^ G.scaleDegree <=
        I * (k : Real) ^ (k * s) := by
    rw [hscale]
    calc
      _ <= (osiiEquation66QuantitativeInverseScaleArityConstant d *
          (k : Real) ^ 3) ^ (k * D.scaleRate) :=
        pow_le_pow_left₀
          (osiiEquation66QuantitativeInverseScalePolynomialConstant_nonneg d k)
          (osiiEquation66QuantitativeInverseScalePolynomialConstant_le_arity_cube d k) _
      _ <= I * (k : Real) ^ (k * s) := by
        simpa [I, s] using
          polynomialBase_pow_arityLinear_le_arityMajorant
            (osiiEquation66QuantitativeInverseScaleArityConstant d)
            (by
              unfold osiiEquation66QuantitativeInverseScaleArityConstant
                osiiStep4SynchronizedSlopeArityConstant
                osiiStep4CoherentSlopeArityConstant
              have hB := osiiStep4PositiveTimeBasepointCutoffNormBound_nonneg d
              positivity)
            3 D.scaleRate k hk
  have hvolume :
      (8 : Real) ^ (k * (d + 1)) * (4 : Real) ^ (k * (d + 1)) <=
        V * (k : Real) ^ (k * v) :=
    osiiEquation66VolumeFactor_le_arityMajorant d k hk
  have hnormalization : (16 : Real) ^ (2 * G.scaleDegree) <=
      N * (k : Real) ^ (k * n) := by
    rw [hscale]
    exact osiiEquation621NormalizationFactor_le_arityMajorant D.scaleRate k hk
  have hfirst := mul_le_mul hMZ hinverse
    (pow_nonneg
      (osiiEquation66QuantitativeInverseScalePolynomialConstant_nonneg d k) _)
    (mul_nonneg hM (by positivity))
  have hsecond := mul_le_mul hfirst hvolume (by positivity) (by positivity)
  have hthird := mul_le_mul hsecond hnormalization (by positivity) (by positivity)
  have hproduct :
      equation66E0PolynomialConstant G * (16 : Real) ^ (2 * G.scaleDegree) <=
        (M * I * V * N) *
          (k : Real) ^ (k * (D.arityRate + t + s + v + n)) := by
    calc
      _ <= ((M * (k : Real) ^ (k * (D.arityRate + t))) *
          (I * (k : Real) ^ (k * s))) *
          (V * (k : Real) ^ (k * v)) *
          (N * (k : Real) ^ (k * n)) := by
        simpa only [equation66E0PolynomialConstant] using hthird
      _ = _ := by
        simp only [Nat.mul_add, pow_add]
        ring
  have hpow : (1 : Real) <=
      (k : Real) ^ (k * (D.arityRate + t + s + v + n)) := one_le_pow₀ hkOne
  change equation66E0PolynomialConstant G *
      (16 : Real) ^ (2 * G.scaleDegree) + 1 <= _
  change _ <= (1 + M * I * V * N) *
      (k : Real) ^ (k * (D.arityRate + t + s + v + n))
  nlinarith

end OSIIUniformMultiGapGrowthData

end OSReconstruction
