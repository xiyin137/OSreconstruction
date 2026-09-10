/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import Init
import OSReconstruction.GeneralResults.SchwartzFlatness
import OSReconstruction.Wightman.Reconstruction.SchwingerOS





































































open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]


































































/-- `(volume : Measure (NPointDomain d n))` is `IsAddHaarMeasure`. -/
instance NPointDomain.volume_isAddHaarMeasure (d n : ℕ) :
    (MeasureTheory.volume :
      MeasureTheory.Measure (NPointDomain d n)).IsAddHaarMeasure :=
  MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite











/-- For a Schwartz function `f` on a finite-dim real inner-product space,
the function `(1 + ‖x‖)^k · ‖f x‖` is integrable.

Proof: bound `(1 + ‖x‖)^k ≤ 2^(k-1) · (1 + ‖x‖^k)`, splitting into a
`‖f x‖` term (integrable: Schwartz functions are integrable) and a
`‖x‖^k · ‖f x‖` term (integrable by `SchwartzMap.integrable_pow_mul`). -/
lemma schwartz_integrable_add_pow_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : MeasureTheory.Measure E} [μ.HasTemperateGrowth]
    (f : SchwartzMap E ℂ) (k : ℕ) :
    MeasureTheory.Integrable
      (fun x : E => (1 + ‖x‖) ^ k * ‖f x‖) (μ := μ) := by
  -- Bound: (1 + ‖x‖)^k ≤ 2^(k-1) · (1 + ‖x‖^k).
  -- (Uses Mathlib's add_pow_le.)
  -- The dominator: 2^(k-1) · (‖f x‖ + ‖x‖^k · ‖f x‖). Each summand integrable.
  have h_dominator_int : MeasureTheory.Integrable
      (fun x : E => ((2 : ℝ) ^ (k - 1)) * (‖f x‖ + ‖x‖^k * ‖f x‖)) μ := by
    refine MeasureTheory.Integrable.const_mul ?_ _
    refine MeasureTheory.Integrable.add ?_ ?_
    · exact (f.integrable (μ := μ)).norm
    · exact f.integrable_pow_mul μ k
  -- Pointwise bound
  refine h_dominator_int.mono' ?_ ?_
  · -- AEStronglyMeasurable
    refine ((continuous_const.add continuous_norm).pow k).mul ?_ |>.aestronglyMeasurable
    exact f.continuous.norm
  · -- |(1+‖x‖)^k * ‖f x‖| ≤ 2^(k-1) * (‖f x‖ + ‖x‖^k * ‖f x‖)
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h_pos : (0 : ℝ) ≤ (1 + ‖x‖) ^ k * ‖f x‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h_pos]
    have h_apl := add_pow_le (zero_le_one (α := ℝ)) (norm_nonneg x) k
    -- h_apl : (1 + ‖x‖) ^ k ≤ 2^(k-1) * (1^k + ‖x‖^k)
    have h_apl' : (1 + ‖x‖) ^ k ≤ 2^(k-1) * (1 + ‖x‖^k) := by
      simpa using h_apl
    have h_fnonneg : 0 ≤ ‖f x‖ := norm_nonneg _
    calc (1 + ‖x‖) ^ k * ‖f x‖
        ≤ 2^(k-1) * (1 + ‖x‖^k) * ‖f x‖ := by
          exact mul_le_mul_of_nonneg_right h_apl' h_fnonneg
      _ = 2^(k-1) * (‖f x‖ + ‖x‖^k * ‖f x‖) := by ring
































end OSReconstruction
