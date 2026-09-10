/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRealEdgeRegularizedGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveAngleStageSelection














noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

/-- Degree added to each final Vladimirov growth factor by the VI.2 depth
loss. -/
def osiiVI2DepthDegree (beta k : Nat) : Nat :=
  2 * beta * k

/-- The finite-depth loss in OS II `(6.28)`. -/
def osiiVI2DepthFactor (beta k N : Nat) : Real :=
  2 ^ (beta * k * N)

/-- Finite-arity constant produced by quantitative recursive-angle stage
selection. -/
noncomputable def osiiVI2SelectedDepthConstant
    (k : Nat) [NeZero k] : Real :=
  Real.sqrt 2 * (1 + recursiveAngleQuantitativeEnvelope k)

/-- Rewrite the `(6.28)` depth factor as the power controlled by recursive
angle selection. -/
theorem osiiVI2DepthFactor_eq_sqrtTwo
    (beta k N : Nat) :
    osiiVI2DepthFactor beta k N =
      ((Real.sqrt 2) ^ N) ^ osiiVI2DepthDegree beta k := by
  unfold osiiVI2DepthFactor osiiVI2DepthDegree
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : Real) :=
    Real.sq_sqrt (by norm_num)
  calc
    (2 : Real) ^ (beta * k * N) =
        ((Real.sqrt 2) ^ 2) ^ (beta * k * N) := by
      rw [hsqrt_sq]
    _ = (Real.sqrt 2) ^ (2 * (beta * k * N)) := by
      exact (pow_mul (Real.sqrt 2) 2 (beta * k * N)).symm
    _ = (Real.sqrt 2) ^ (N * (2 * beta * k)) := by
      congr 1
      ring
    _ = ((Real.sqrt 2) ^ N) ^ (2 * beta * k) := by
      exact pow_mul (Real.sqrt 2) N (2 * beta * k)

theorem osiiVI2SelectedDepthConstant_pos
    (k : Nat) [NeZero k] :
    0 < osiiVI2SelectedDepthConstant k := by
  exact mul_pos (Real.sqrt_pos.2 (by norm_num))
    (by
      have := recursiveAngleQuantitativeEnvelope_pos k
      linarith)

/-- Stage selection introduces at most an explicit exponential-in-arity
constant, with no opaque coordinatewise choices. -/
theorem osiiVI2SelectedDepthConstant_le_three_pow
    (k : Nat) [NeZero k] :
    osiiVI2SelectedDepthConstant k ≤ 16 * (3 : Real) ^ k := by
  have hpow_one : (1 : Real) ≤ 3 ^ k :=
    one_le_pow₀ (by norm_num)
  have hsqrt : Real.sqrt 2 ≤ (2 : Real) := by
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : Real) :=
      Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hpi : Real.pi / 2 ≤ (2 : Real) := by
    nlinarith [Real.pi_le_four]
  calc
    osiiVI2SelectedDepthConstant k =
        Real.sqrt 2 * (1 + recursiveAngleQuantitativeEnvelope k) := rfl
    _ ≤ Real.sqrt 2 *
          (1 + Real.pi / 2 * (1 + (3 : Real) ^ k)) := by
      gcongr
      exact recursiveAngleQuantitativeEnvelope_le_three_pow k
    _ ≤ 2 * (1 + 2 * (1 + (3 : Real) ^ k)) := by
      gcongr
    _ ≤ 16 * (3 : Real) ^ k := by
      nlinarith

/-- Select a containing recursive-angle stage and control its exact `(6.28)`
depth loss by the standard final growth factors. -/
theorem exists_recursiveAngle_stage_depthFactor_le
    {k : Nat} [NeZero k]
    (beta : Nat)
    (zeta : Fin k -> Complex)
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k) :
    exists N : Nat,
      zeta ∈ OSIIChapterV.osiiTimeArgumentSector
        (fun i : Fin k => OSIIChapterV.recursiveAngle (i.val + 1) N) ∧
      osiiVI2DepthFactor beta k N <=
        osiiVI2SelectedDepthConstant k ^ osiiVI2DepthDegree beta k *
          (1 + ‖zeta‖) ^ osiiVI2DepthDegree beta k *
          (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^
            osiiVI2DepthDegree beta k := by
  obtain ⟨N, hsector, hdepth⟩ :=
    exists_recursiveAngle_stage_with_standard_growth_depth zeta hzeta
  refine ⟨N, hsector, ?_⟩
  rw [osiiVI2DepthFactor_eq_sqrtTwo]
  have hpow := pow_le_pow_left₀
    (pow_nonneg (Real.sqrt_nonneg 2) N) hdepth
    (osiiVI2DepthDegree beta k)
  simpa [osiiVI2SelectedDepthConstant, mul_pow, mul_assoc] using hpow

namespace OSIITimeContinuationLadderRealEdgeGrowthData

variable {d k : Nat}
variable {L : OSIITimeContinuationLadder d k}

end OSIITimeContinuationLadderRealEdgeGrowthData

namespace OSIITimeContinuationLadderVI2RecursiveSectorEquation628Data

variable {d k : Nat} [NeZero k]
variable {L : OSIITimeContinuationLadder d k}
variable {E : OSIITimeContinuationLadderRealEdgeGrowthData L}
variable {beta : Nat}

end OSIITimeContinuationLadderVI2RecursiveSectorEquation628Data

namespace OSIITimeContinuationLadderVI2Equation628Data

variable {d k : Nat} [NeZero k]
variable {L : OSIITimeContinuationLadder d k}
variable {E : OSIITimeContinuationLadderRealEdgeGrowthData L}
variable {beta : Nat}

end OSIITimeContinuationLadderVI2Equation628Data

end OSReconstruction
