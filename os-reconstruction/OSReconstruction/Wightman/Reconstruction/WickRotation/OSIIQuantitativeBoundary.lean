import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIQuantitativeDecay
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalTimeBoundary

/-!
# Uniform constants for the native OS II boundary

All estimates concern the existing chronological boundary. The explicit
weighted-L1 and singular-Taylor constants are retained across arities.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction

theorem section43SpatialFlatCLE_opNorm_le_one (d k : Nat) :
    ‖(section43SpatialFlatCLE d k).toContinuousLinearMap‖ <= 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  exact PiLp.norm_apply_le x (finProdFinEquiv.symm j)

theorem section43SpatialFlat_zeroOrderFactor_le (d k r : Nat) :
    schwartzCompEquivFinsetFactor (section43SpatialFlatCLE d k).symm
      (Finset.Iic (r, 0)) <= (r + 1 : Real) := by
  unfold schwartzCompEquivFinsetFactor
  calc
    _ <= ∑ _j ∈ Finset.Iic (r, 0), (1 : Real) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj0 : j.2 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp hj).2
      simp only [hj0, pow_zero, mul_one, ContinuousLinearEquiv.symm_symm]
      exact (pow_le_pow_left₀ (norm_nonneg _)
        (section43SpatialFlatCLE_opNorm_le_one d k) j.1).trans_eq (one_pow _)
    _ = (r + 1 : Real) := by simp [Finset.card_Iic_prod, Nat.card_Iic]

theorem explicitWeightedL1Constant_le_three_pow (d k p : Nat) :
    (OSIIEquation621WeightedL1Section43BoundData.explicitIndexPreserving d k p).constant <=
      (3 : Real) ^ (2 * p + 4 * (k * d) + 6) := by
  let m := k * d
  let J : Real := ∫ x : Fin m -> Real, (1 + ‖x‖) ^ (-((m + 1 : Nat) : Real))
  let factor := schwartzCompEquivFinsetFactor (section43SpatialFlatCLE d k).symm
    (Finset.Iic (p + (m + 1), 0))
  have hJ0 : 0 <= J := integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _
  have hJ : J <= (3 : Real) ^ (2 * m + 1) :=
    integral_one_add_pi_norm_neg_succ_le_three_pow m
  have hJplus : 1 + J <= (3 : Real) ^ (2 * m + 2) := by
    have hone : (1 : Real) <= 3 ^ (2 * m + 1) := one_le_pow₀ (by norm_num)
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ]
    nlinarith
  have hfactor0 : 0 <= factor := schwartzCompEquivFinsetFactor_nonneg _ _
  have hfactor : factor + 1 <= (3 : Real) ^ (p + m + 3) := by
    have h := section43SpatialFlat_zeroOrderFactor_le d k (p + (m + 1))
    have hn := natCast_le_three_pow (p + m + 3)
    dsimp [factor] at *
    push_cast at h hn
    linarith
  change (2 ^ (p + (m + 1)) * (1 + J)) * (factor + 1) <= _
  calc
    _ <= (3 : Real) ^ (p + (m + 1)) * 3 ^ (2 * m + 2) *
        3 ^ (p + m + 3) := by
      gcongr
      norm_num
    _ = (3 : Real) ^ (2 * p + 4 * (k * d) + 6) := by
      rw [← pow_add, ← pow_add]
      congr 1
      dsimp [m]
      omega

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem strictGeneratedGrowthConstant_eq
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) [NeZero k] :
    let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
    let beta := osiiEquation621CanonicalSeedArityRate lgc
    let alpha := osiiEquation621CanonicalSeedArityConstant lgc
    (initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc k).constant =
      (osiiVI2NormalizedRawGlobalCoefficient alpha t beta k + 1) *
        (OSIIEquation621WeightedL1Section43BoundData.explicitIndexPreserving
          d k (k * t)).constant := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

/-- The original global growth package has one exponential-quadratic
coefficient bound, before taking its boundary value. -/
theorem strictGeneratedGrowthConstant_le_three_pow
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) [NeZero k] :
    let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
    let beta := osiiEquation621CanonicalSeedArityRate lgc
    (initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc k).constant <=
      (osiiEquation621CanonicalSeedArityConstant lgc + 1) *
        (3 : Real) ^ ((15 * beta + 3 * t + 4 * d + 6) * k * k) := by
  let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
  let beta := osiiEquation621CanonicalSeedArityRate lgc
  let alpha := osiiEquation621CanonicalSeedArityConstant lgc
  have halpha : 0 <= alpha := osiiEquation621CanonicalSeedArityConstant_nonneg lgc
  have hk : 1 <= k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hraw := osiiVI2NormalizedRawGlobalCoefficient_le_three_pow halpha t beta k
  have hone : (1 : Real) <= 3 ^ ((15 * beta + t) * k * k) :=
    one_le_pow₀ (by norm_num)
  have hplus : osiiVI2NormalizedRawGlobalCoefficient alpha t beta k + 1 <=
      (alpha + 1) * (3 : Real) ^ ((15 * beta + t) * k * k) := by nlinarith
  have hL := explicitWeightedL1Constant_le_three_pow d k (k * t)
  have hL0 := (OSIIEquation621WeightedL1Section43BoundData.explicitIndexPreserving
    d k (k * t)).constant_pos.le
  have hkk : k <= k * k := by nlinarith
  have hexp : (15 * beta + t) * k * k + (2 * (k * t) + 4 * (k * d) + 6) <=
      (15 * beta + 3 * t + 4 * d + 6) * k * k := by
    have hlinear : 2 * (k * t) + 4 * (k * d) + 6 <= (2 * t + 4 * d + 6) * k := by
      nlinarith
    have hscaled := Nat.mul_le_mul_left (2 * t + 4 * d + 6) hkk
    nlinarith
  dsimp only
  rw [initial.strictGeneratedGrowthConstant_eq lgc k]
  change (osiiVI2NormalizedRawGlobalCoefficient alpha t beta k + 1) *
      (OSIIEquation621WeightedL1Section43BoundData.explicitIndexPreserving
        d k (k * t)).constant <= _
  calc
    _ <= ((alpha + 1) * (3 : Real) ^ ((15 * beta + t) * k * k)) *
        3 ^ (2 * (k * t) + 4 * (k * d) + 6) :=
      mul_le_mul hplus hL hL0 (by positivity)
    _ = (alpha + 1) * (3 : Real) ^
        ((15 * beta + t) * k * k + (2 * (k * t) + 4 * (k * d) + 6)) := by
      rw [pow_add]
      ring
    _ <= (alpha + 1) * (3 : Real) ^ ((15 * beta + 3 * t + 4 * d + 6) * k * k) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hexp) (by positivity)

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

theorem osiiUnitDirection_mem (k : Nat) :
    (fun _ : Fin k => (1 : Real)) ∈ osiiTimePositiveCone k := by
  intro i
  norm_num

theorem osiiUnitDirection_norm_le (k : Nat) :
    ‖fun _ : Fin k => (1 : Real)‖ <= 1 := by
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by intro i; simp)

theorem osiiUnitDirection_margin_ge_one (k : Nat) [NeZero k] :
    1 <= Metric.infDist (fun _ : Fin k => (1 : Real)) (osiiTimePositiveCone k)ᶜ := by
  refine (Metric.le_infDist (osiiTimePositiveCone_compl_nonempty
    (Nat.pos_of_ne_zero (NeZero.ne k)))).mpr ?_
  intro v hv
  have hv' : v ∉ osiiTimePositiveCone k := hv
  simp only [osiiTimePositiveCone, section43TimeStrictPositiveRegion,
    Set.mem_setOf_eq, not_forall, not_lt] at hv'
  obtain ⟨i, hi⟩ := hv'
  calc
    (1 : Real) <= 1 - v i := by linarith
    _ <= |1 - v i| := le_abs_self _
    _ = dist (1 : Real) (v i) := (Real.dist_eq _ _).symm
    _ <= dist (fun _ : Fin k => (1 : Real)) v :=
      dist_le_pi_dist (fun _ : Fin k => (1 : Real)) v i

namespace OSIIFullTimeStageVladimirovGrowthData

/-- The fixed unit time direction introduces only explicitly bounded factors. -/
theorem coupledBoundaryConstant_unit_le {d k : Nat} [NeZero k]
    {A : OSIITimeContinuationStage d k} (G : OSIIFullTimeStageVladimirovGrowthData A) :
    G.coupledBoundaryConstant (fun _ => 1) * (2 * G.boundaryDegree + 2 : Nat) <=
      G.constant * (3 : Real) ^
        (2 * G.polynomialDegree + 3 * G.boundaryDegree +
          G.spatialSeminorms.sup Prod.fst + 3 * k + 4) := by
  have hnorm := osiiUnitDirection_norm_le k
  have hmargin := osiiUnitDirection_margin_ge_one k
  have hinv : (Metric.infDist (fun _ : Fin k => (1 : Real))
      (osiiTimePositiveCone k)ᶜ)⁻¹ <= 1 := by
    exact (inv_le_one₀ (by linarith)).mpr hmargin
  have hdecay : OSIIChapterVI.timeDecayIntegral k <= (3 : Real) ^ (2 * k + 1) :=
    integral_one_add_pi_norm_neg_succ_le_three_pow k
  have hnat := natCast_le_three_pow (2 * G.boundaryDegree + 2)
  have hC0 := G.constant_pos.le
  have hJ0 := OSIIChapterVI.timeDecayIntegral_nonneg k
  unfold coupledBoundaryConstant coupledSliceConstant coupledSourceConstant
  rw [max_eq_left hnorm, one_pow, mul_one]
  calc
    _ <= (G.constant * 3 ^ G.polynomialDegree * 3 ^ G.boundaryDegree) *
        (3 ^ (G.polynomialDegree + (k + 1) + G.spatialSeminorms.sup Prod.fst) *
          3 ^ (2 * k + 1)) * 3 ^ (2 * G.boundaryDegree + 2) := by
      gcongr
      all_goals linarith
    _ = G.constant * (3 : Real) ^
        (G.polynomialDegree + G.boundaryDegree +
          (G.polynomialDegree + (k + 1) + G.spatialSeminorms.sup Prod.fst) +
            (2 * k + 1) + (2 * G.boundaryDegree + 2)) := by
      simp only [pow_add]
      ring
    _ = _ := by
      congr 2
      omega

end OSIIFullTimeStageVladimirovGrowthData

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem strictGeneratedBoundaryConstant_le_three_pow
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) [NeZero k] :
    let G := initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc k
    let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
    let beta := osiiEquation621CanonicalSeedArityRate lgc
    G.coupledBoundaryConstant (fun _ => 1) * (2 * G.boundaryDegree + 2 : Nat) <=
      (osiiEquation621CanonicalSeedArityConstant lgc + 1) *
        (3 : Real) ^ ((25 * beta + 9 * t + 5 * d + 14) * k * k) := by
  let G := initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc k
  let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
  let beta := osiiEquation621CanonicalSeedArityRate lgc
  obtain ⟨hN, hM, hs⟩ :=
    initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII_parameters lgc k
  have hweight : G.spatialSeminorms.sup Prod.fst = k * t + (k * d + 1) := by
    change schwartzSeminormWeightOrder G.spatialSeminorms = _
    rw [hs, schwartzSeminormWeightOrder_Iic_zero]
  have hC := initial.strictGeneratedGrowthConstant_le_three_pow lgc k
  have hk : 1 <= k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkk : k <= k * k := by nlinarith
  have he : 2 * G.polynomialDegree + 3 * G.boundaryDegree +
      G.spatialSeminorms.sup Prod.fst + 3 * k + 4 <=
        (6 * t + 10 * beta + d + 8) * k * k := by
    rw [hN, hM, hweight]
    change 2 * (k * (t + 2 * beta)) + 3 * (k * (t + 2 * beta)) +
      (k * t + (k * d + 1)) + 3 * k + 4 <= _
    have hh := Nat.mul_le_mul_left (6 * t + 10 * beta + d + 8) hkk
    nlinarith
  dsimp only
  calc
    _ <= G.constant * (3 : Real) ^
        (2 * G.polynomialDegree + 3 * G.boundaryDegree +
          G.spatialSeminorms.sup Prod.fst + 3 * k + 4) :=
      G.coupledBoundaryConstant_unit_le
    _ <= ((osiiEquation621CanonicalSeedArityConstant lgc + 1) *
        (3 : Real) ^ ((15 * beta + 3 * t + 4 * d + 6) * k * k)) *
          3 ^ ((6 * t + 10 * beta + d + 8) * k * k) := by
      apply mul_le_mul hC (pow_le_pow_right₀ (by norm_num) he) (by positivity)
      have ha := osiiEquation621CanonicalSeedArityConstant_nonneg lgc
      positivity
    _ = _ := by
      rw [mul_assoc, ← pow_add]
      congr 2
      ring

/-- Uniform quantitative control of the same mixed-variable boundary used by
the native reconstruction, with arity-linear Schwartz orders. -/
theorem norm_strictGeneratedTimeSpatialBoundary_le
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) [NeZero k]
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
    let beta := osiiEquation621CanonicalSeedArityRate lgc
    ‖(initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).timeSpatialBoundary Phi‖ <=
      ((osiiEquation621CanonicalSeedArityConstant lgc + 1) *
        (3 : Real) ^ ((25 * beta + 9 * t + 5 * d + 14) * k * k)) *
      (Finset.Iic (k * (2 * t + 2 * beta + d + 3),
        k * (2 * t + 2 * beta + d + 3))).sup
          (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi := by
  let G := initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc k
  have hbase := G.norm_timeSpatialBoundary_le
    (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k)
      (fun _ => 1) (osiiUnitDirection_mem k) Phi
  have hcoeff := initial.strictGeneratedBoundaryConstant_le_three_pow lgc k
  have hk : 1 <= k := Nat.pos_of_ne_zero (NeZero.ne k)
  dsimp only
  apply hbase.trans
  apply mul_le_mul hcoeff ?_ (apply_nonneg _ _) ?_
  · apply Seminorm.le_def.mp (Finset.sup_mono ?_) Phi
    rw [initial.strictGeneratedCoupledBoundaryIndicesOfOSII lgc k]
    exact Finset.Iic_subset_Iic.mpr ⟨by nlinarith, by nlinarith⟩
  · have ha := osiiEquation621CanonicalSeedArityConstant_nonneg lgc
    positivity

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

end OSReconstruction
