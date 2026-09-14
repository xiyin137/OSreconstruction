import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1Successor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFullStageHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformWeightedL1Degree

/-!
# Global growth from the normalized raw induction

The recursive-angle sectors admit genuine first-bridge generator
presentations. Their raw scalar bounds can therefore be evaluated directly
on the completed full-time stage, with quantitative sector selection and
the complete equation-(6.21) recovery factor.
-/

noncomputable section

open Complex Set
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

open StrictGeneratedScalarDepthPointedData
open StrictGeneratedScalarDepthPointedData.RecursiveSectorAdaptiveZeroBetaSelectedVI2GramChartPackageData

/-- A raw radial generator remains in the raw scalar successor after its
recorded contraction. This does not insert a vacuum-tail constructor. -/
theorem RawRecursiveAngleRadialGeneratorChartAtRank.target_mem_rawScalarCarrier
    {k depth rank : Nat}
    (R : RawRecursiveAngleRadialGeneratorChartAtRank k depth rank) :
    R.radial.chart.target ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase k (depth + 1)) := by
  refine ⟨R.radial.chart.target_mem.1, ?_⟩
  rw [R.radial.target_argument_eq]
  exact (OSIIRawStrictGeneratedLogarithmicArgument.generatorMemSucc
    R.radial.chart.generator depth R.radial.expandedLeft
    R.radial.expandedTheta R.radial.expandedRight
    R.expanded_left_raw R.expanded_right_raw R.radial.expanded_angle_bound
    ).smul_of_nonneg_le_one _
      (recursiveAngle_explicitContraction_pos depth).le
      (recursiveAngle_explicitContraction_lt_one depth).le

/-- Every nonempty recursive-angle sector is already in the raw scalar
carrier at the same depth, through its genuine first-bridge generator. -/
theorem rawStrict_recursiveAngle_sector_subset_scalarCarrier
    (k N : Nat) [NeZero k] :
    osiiTimeArgumentSector (osiiRecursiveAngleAperture k N) ⊆
      osiiTimeArgumentCarrier (osiiRawStrictGeneratedLogarithmicBase k N) := by
  intro z hz
  cases N with
  | zero =>
    have hdepth := arity_le_depth_of_mem_recursiveAngleTimeArgumentSector hz
    have hk := Nat.pos_of_ne_zero (NeZero.ne k)
    omega
  | succ depth =>
    cases k with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
      obtain ⟨rank, hcharts⟩ :=
        exists_rank_rawRecursiveAngleFirstBridgeRadialGeneratorChart_eq_on_recursiveAngleSector
          q depth
      obtain ⟨R, _hgenerator, htarget⟩ := hcharts z hz
      simpa only [htarget] using R.target_mem_rawScalarCarrier

private theorem canonicalUnshift_norm_le
    {k : Nat} (hk : 0 < k)
    {z : OSIITimeGapSpace k} (hz : z ∈ osiiTimeRightHalfPlane k) :
    1 + ‖osiiVI2Unshift k (osiiVI2CanonicalEpsilon k z) z‖ <=
      9 * (1 + ‖z‖) := by
  let epsilon := osiiVI2CanonicalEpsilon k z
  have hepsilon : 0 < epsilon := osiiVI2CanonicalEpsilon_pos hk hz
  have hepsilon_le : epsilon <= 8 := by
    dsimp [epsilon, osiiVI2CanonicalEpsilon]
    linarith [osiiChapterVIRegularizationRadius_le_sixteen k z]
  have hconstant : ‖(fun _ : Fin k => (epsilon : Complex))‖ <= 8 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : Real) <= 8)).2
    intro j
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hepsilon] using hepsilon_le
  have hnorm : ‖osiiVI2Unshift k epsilon z‖ <= ‖z‖ + 8 := by
    exact (norm_sub_le z (fun _ => (epsilon : Complex))).trans
      (add_le_add (le_refl ‖z‖) hconstant)
  change 1 + ‖osiiVI2Unshift k epsilon z‖ <= _
  linarith [norm_nonneg z]

private theorem canonicalUnshift_boundaryFactor_le
    {k : Nat} (hk : 0 < k)
    {z : OSIITimeGapSpace k} (hz : z ∈ osiiTimeRightHalfPlane k) :
    1 + (osiiTimeBoundaryDistance k
      (osiiVI2Unshift k (osiiVI2CanonicalEpsilon k z) z))⁻¹ <=
      2 * (1 + (osiiTimeBoundaryDistance k z)⁻¹) := by
  let epsilon := osiiVI2CanonicalEpsilon k z
  let w := osiiVI2Unshift k epsilon z
  have hepsilon : 0 < epsilon := osiiVI2CanonicalEpsilon_pos hk hz
  have hepsilon_le : epsilon <= osiiTimeBoundaryDistance k z / 2 := by
    dsimp [epsilon, osiiVI2CanonicalEpsilon]
    linarith [osiiChapterVIRegularizationRadius_le_boundaryDistance k z]
  have hdist : dist (fun i => (z i).re) (fun i => (w i).re) <= epsilon := by
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg hepsilon.le).2
    intro j
    simp [w, abs_of_pos hepsilon]
  have hboundary : osiiTimeBoundaryDistance k z / 2 <=
      osiiTimeBoundaryDistance k w := by
    have h := Metric.infDist_le_infDist_add_dist
      (x := fun i => (z i).re) (y := fun i => (w i).re)
      (s := (osiiTimePositiveCone k)ᶜ)
    change osiiTimeBoundaryDistance k z <=
      osiiTimeBoundaryDistance k w +
        dist (fun i => (z i).re) (fun i => (w i).re) at h
    linarith
  have hpositive := osiiTimeBoundaryDistance_pos hk hz
  have hinv := one_div_le_one_div_of_le
    (div_pos hpositive (by norm_num : (0 : Real) < 2)) hboundary
  have hinv' : (osiiTimeBoundaryDistance k w)⁻¹ <=
      2 * (osiiTimeBoundaryDistance k z)⁻¹ := by
    simpa only [one_div, inv_div, inv_inv] using hinv
  change 1 + (osiiTimeBoundaryDistance k w)⁻¹ <= _
  linarith

/-- The explicit coefficient remaining after normalized depth selection and
equation-(6.21) recovery. Its spatial norm is still the weighted-L1 norm. -/
noncomputable def osiiVI2NormalizedRawGlobalCoefficient
    (alpha : Real) (t beta k : Nat) [NeZero k] : Real :=
  alpha * (k : Real) ^ (beta * k) * 3 ^ (k * t) *
    (18 * osiiVI2SelectedDepthConstant k) ^ osiiVI2DepthDegree beta k

theorem osiiVI2NormalizedRawGlobalCoefficient_nonneg
    {alpha : Real} (halpha : 0 <= alpha)
    (t beta k : Nat) [NeZero k] :
    0 <= osiiVI2NormalizedRawGlobalCoefficient alpha t beta k := by
  have hselected := (osiiVI2SelectedDepthConstant_pos k).le
  unfold osiiVI2NormalizedRawGlobalCoefficient
  positivity

/-- The exact weighted-L1 coefficient grows at most exponentially in the
square of the arity, with its original common coefficient unchanged. -/
theorem osiiVI2NormalizedRawGlobalCoefficient_le_three_pow
    {alpha : Real} (halpha : 0 <= alpha)
    (t beta k : Nat) [NeZero k] :
    osiiVI2NormalizedRawGlobalCoefficient alpha t beta k <=
      alpha * (3 : Real) ^ ((15 * beta + t) * k * k) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hnat : forall n : Nat, (n : Real) <= (3 : Real) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      have hone : (1 : Real) <= 3 ^ n := one_le_pow₀ (by norm_num)
      nlinarith
  have hselected : 18 * osiiVI2SelectedDepthConstant k <=
      (3 : Real) ^ (k + 6) := by
    calc
      18 * osiiVI2SelectedDepthConstant k <= 18 * (16 * (3 : Real) ^ k) :=
        mul_le_mul_of_nonneg_left
          (osiiVI2SelectedDepthConstant_le_three_pow k) (by norm_num)
      _ <= (3 : Real) ^ 6 * 3 ^ k := by
        nlinarith [pow_nonneg (by norm_num : (0 : Real) <= 3) k]
      _ = (3 : Real) ^ (k + 6) := by rw [pow_add]; ring
  have hselected_nonneg := (osiiVI2SelectedDepthConstant_pos k).le
  have hkk : k <= k * k := by nlinarith
  have hexponent :
      k * (beta * k) + k * t + (k + 6) * (2 * beta * k) <=
        (15 * beta + t) * k * k := by
    have hscaled := Nat.mul_le_mul_left (12 * beta + t) hkk
    nlinarith
  calc
    osiiVI2NormalizedRawGlobalCoefficient alpha t beta k <=
        alpha * ((3 : Real) ^ k) ^ (beta * k) * 3 ^ (k * t) *
          ((3 : Real) ^ (k + 6)) ^ (2 * beta * k) := by
      unfold osiiVI2NormalizedRawGlobalCoefficient osiiVI2DepthDegree
      gcongr
      exact hnat k
    _ = alpha * (3 : Real) ^
        (k * (beta * k) + k * t + (k + 6) * (2 * beta * k)) := by
      simp only [pow_add, pow_mul]
      ring
    _ <= alpha * (3 : Real) ^ ((15 * beta + t) * k * k) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hexponent) halpha

private theorem exists_rawStage_canonicalUnshift_depthFactor_le
    {k : Nat} [NeZero k] (beta : Nat)
    {z : OSIITimeGapSpace k} (hz : z ∈ osiiTimeRightHalfPlane k) :
    exists N,
      osiiVI2Unshift k (osiiVI2CanonicalEpsilon k z) z ∈
        osiiTimeArgumentCarrier (osiiRawStrictGeneratedLogarithmicBase k N) ∧
      osiiVI2DepthFactor beta k N <=
        (18 * osiiVI2SelectedDepthConstant k) ^ osiiVI2DepthDegree beta k *
          (1 + ‖z‖) ^ osiiVI2DepthDegree beta k *
          (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^
            osiiVI2DepthDegree beta k := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  let w := osiiVI2Unshift k (osiiVI2CanonicalEpsilon k z) z
  have hw : w ∈ osiiTimeRightHalfPlane k :=
    osiiVI2CanonicalUnshift_mem_rightHalfPlane hk hz
  obtain ⟨N, hsector, hdepth⟩ :=
    exists_recursiveAngle_stage_depthFactor_le beta w hw
  refine ⟨N, rawStrict_recursiveAngle_sector_subset_scalarCarrier k N hsector, ?_⟩
  have hselected := (osiiVI2SelectedDepthConstant_pos k).le
  have hboundary := (osiiTimeBoundaryDistance_pos hk hz).le
  have hwboundary := (osiiTimeBoundaryDistance_pos hk hw).le
  calc
    osiiVI2DepthFactor beta k N <=
        osiiVI2SelectedDepthConstant k ^ osiiVI2DepthDegree beta k *
          (1 + ‖w‖) ^ osiiVI2DepthDegree beta k *
          (1 + (osiiTimeBoundaryDistance k w)⁻¹) ^
            osiiVI2DepthDegree beta k := hdepth
    _ <= osiiVI2SelectedDepthConstant k ^ osiiVI2DepthDegree beta k *
          (9 * (1 + ‖z‖)) ^ osiiVI2DepthDegree beta k *
          (2 * (1 + (osiiTimeBoundaryDistance k z)⁻¹)) ^
            osiiVI2DepthDegree beta k := by
      gcongr
      · exact canonicalUnshift_norm_le hk hz
      · exact canonicalUnshift_boundaryFactor_le hk hz
    _ = (18 * osiiVI2SelectedDepthConstant k) ^ osiiVI2DepthDegree beta k *
          (1 + ‖z‖) ^ osiiVI2DepthDegree beta k *
          (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^
            osiiVI2DepthDegree beta k := by
      rw [show (18 : Real) = 9 * 2 by norm_num]
      simp only [mul_pow]
      ring

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData

/-- The raw normalized estimate is an estimate for the same glued full-time
distribution, not for an independently selected analytic family. -/
theorem fullTimePointBound_of_mem_rawCarrier
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {t beta depth k : Nat} [NeZero k]
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta depth)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (zeta : OSIITimeGapSpace k)
    (hzeta : zeta ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase k depth)) :
    OSIIEquation621WeightedL1PointBoundData
      (((initial.toStrictGeneratedFullTimeContinuationStage lgc k
        ).vi2Equation621TotalNormalizedStage t epsilon).distribution zeta)
      (k * t) B.alpha beta depth := by
  apply (B.pointBound hepsilon zeta hzeta).congr
  ext chi
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  rw [OSIITimeContinuationStage.vi2Equation621TotalNormalizedStage_eq_of_pos _ hk,
    OSIITimeContinuationStage.vi2Equation621TotalNormalizedStage_eq_of_pos _ hk,
    OSIITimeContinuationStage.vi2Equation621NormalizedStage_distribution_apply,
    OSIITimeContinuationStage.vi2Equation621NormalizedStage_distribution_apply]
  have hstage : osiiVI2Shift k epsilon zeta ∈
      ((initial.toStrictGeneratedTimeContinuationLadder lgc k).stage depth).carrier := by
    exact (initial.toStrictGeneratedScalarDepthZeroPointedData.depthInduction
      lgc depth).rawStrictGeneratedScalarCarrier_subset_stage k
        (osiiVI2Shift_mem_rawStrictGeneratedScalarCarrier hzeta hepsilon.le)
  rw [InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedFullTimeContinuationStage,
    (initial.toStrictGeneratedTimeContinuationLadder lgc k
      ).toFullTimeContinuationStage_extends_stage depth hstage]

/-- A coefficient-preserving normalized raw induction gives global growth
of the actual full-time distribution. Both time degrees are linear in arity. -/
theorem norm_fullTimeDistribution_le_of_uniformDepth
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {t beta k : Nat} [NeZero k] {alpha : Real}
    (source : forall depth,
      RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
        initial lgc t beta depth)
    (hsource : forall depth, (source depth).alpha = alpha)
    {z : OSIITimeGapSpace k} (hz : z ∈ osiiTimeRightHalfPlane k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖(initial.toStrictGeneratedFullTimeContinuationStage lgc k
      ).distribution z chi‖ <=
      osiiVI2NormalizedRawGlobalCoefficient alpha t beta k *
        (1 + ‖z‖) ^ (k * t + osiiVI2DepthDegree beta k) *
        (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^
          (k * t + osiiVI2DepthDegree beta k) *
        osiiSpatialPolynomialWeightedL1 (k * t)
          (section43SpatialFlatSchwartzCLE d k chi) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have halpha : 0 <= alpha := by
    simpa only [hsource 0] using (source 0).alpha_nonneg
  let A := initial.toStrictGeneratedFullTimeContinuationStage lgc k
  let p := osiiSpatialPolynomialWeightedL1 (k * t)
    (section43SpatialFlatSchwartzCLE d k chi)
  have hp : 0 <= p := osiiSpatialPolynomialWeightedL1_nonneg _
  have hboundary := (osiiTimeBoundaryDistance_pos hk hz).le
  obtain ⟨N, hraw, hdepth⟩ :=
    exists_rawStage_canonicalUnshift_depthFactor_le beta hz
  have hnormalized := ((source N).fullTimePointBound_of_mem_rawCarrier
    (osiiVI2CanonicalEpsilon_pos hk hz) _ hraw).norm_distribution_le chi
  rw [OSIITimeContinuationStage.vi2Equation621TotalNormalizedStage_eq_of_pos _ hk,
    hsource N] at hnormalized
  have hrecovery := A.norm_distribution_le_of_equation621Normalized_canonical
    hk t hz chi (osiiVI2ArityDepthMajorant alpha beta k N * p) hnormalized
  have hmajorant : osiiVI2ArityDepthMajorant alpha beta k N <=
      alpha * (k : Real) ^ (beta * k) *
        ((18 * osiiVI2SelectedDepthConstant k) ^ osiiVI2DepthDegree beta k *
          (1 + ‖z‖) ^ osiiVI2DepthDegree beta k *
          (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^
            osiiVI2DepthDegree beta k) := by
    exact mul_le_mul_of_nonneg_left hdepth (mul_nonneg halpha (by positivity))
  calc
    ‖A.distribution z chi‖ <=
        3 ^ (k * t) * (1 + ‖z‖) ^ (k * t) *
          (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^ (k * t) *
          (osiiVI2ArityDepthMajorant alpha beta k N * p) := hrecovery
    _ <= 3 ^ (k * t) * (1 + ‖z‖) ^ (k * t) *
          (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^ (k * t) *
          (alpha * (k : Real) ^ (beta * k) *
            ((18 * osiiVI2SelectedDepthConstant k) ^ osiiVI2DepthDegree beta k *
              (1 + ‖z‖) ^ osiiVI2DepthDegree beta k *
              (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^
                osiiVI2DepthDegree beta k) * p) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmajorant hp) (by positivity)
    _ = osiiVI2NormalizedRawGlobalCoefficient alpha t beta k *
          (1 + ‖z‖) ^ (k * t + osiiVI2DepthDegree beta k) *
          (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^
            (k * t + osiiVI2DepthDegree beta k) * p := by
      simp only [osiiVI2NormalizedRawGlobalCoefficient, pow_add]
      ring

/-- The normalized raw induction supplies the existing global growth
interface with explicit, index-preserving spatial Schwartz seminorms. -/
noncomputable def toFullTimeStageGrowthData_of_uniformDepth
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {t beta k : Nat} [NeZero k] {alpha : Real}
    (source : forall depth,
      RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
        initial lgc t beta depth)
    (hsource : forall depth, (source depth).alpha = alpha) :
    OSIIFullTimeStageVladimirovGrowthData
      (initial.toStrictGeneratedFullTimeContinuationStage lgc k) := by
  let L := OSIIEquation621WeightedL1Section43BoundData.explicitIndexPreserving
    d k (k * t)
  let C := osiiVI2NormalizedRawGlobalCoefficient alpha t beta k
  have halpha : 0 <= alpha := by
    simpa only [hsource 0] using (source 0).alpha_nonneg
  have hC : 0 <= C :=
    osiiVI2NormalizedRawGlobalCoefficient_nonneg halpha t beta k
  refine {
    fullCarrier := initial.toStrictGeneratedFullTimeContinuationStage_carrier lgc k
    spatialSeminorms := L.spatialSeminorms
    constant := (C + 1) * L.constant
    polynomialDegree := k * t + osiiVI2DepthDegree beta k
    boundaryDegree := k * t + osiiVI2DepthDegree beta k
    constant_pos := mul_pos (by linarith) L.constant_pos
    bound := ?_ }
  intro z hz chi
  have hboundary := (osiiTimeBoundaryDistance_pos
    (Nat.pos_of_ne_zero (NeZero.ne k)) hz).le
  let timeWeight :=
    (1 + ‖z‖) ^ (k * t + osiiVI2DepthDegree beta k) *
    (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^
      (k * t + osiiVI2DepthDegree beta k)
  let p := L.spatialSeminorms.sup
    (schwartzSeminormFamily Complex (Section43SpatialSpace d k) Complex) chi
  have htime : 0 <= timeWeight := by dsimp [timeWeight]; positivity
  have hp : 0 <= p := apply_nonneg _ _
  calc
    ‖(initial.toStrictGeneratedFullTimeContinuationStage lgc k
      ).distribution z chi‖ <= C * timeWeight *
        osiiSpatialPolynomialWeightedL1 (k * t)
          (section43SpatialFlatSchwartzCLE d k chi) := by
      simpa only [C, timeWeight, mul_assoc] using
        norm_fullTimeDistribution_le_of_uniformDepth source hsource hz chi
    _ <= C * timeWeight * (L.constant * p) :=
      mul_le_mul_of_nonneg_left (L.bound chi) (mul_nonneg hC htime)
    _ <= (C + 1) * timeWeight * (L.constant * p) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C <= C + 1) htime)
        (mul_nonneg L.constant_pos.le hp)
    _ = (C + 1) * L.constant *
          (1 + ‖z‖) ^ (k * t + osiiVI2DepthDegree beta k) *
          (1 + (osiiTimeBoundaryDistance k z)⁻¹) ^
            (k * t + osiiVI2DepthDegree beta k) * p := by
      dsimp [timeWeight]
      ring

end RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData

namespace InitialGeneratedLogarithmicStageLevelData

/-- Global Chapter VI growth for the OS-built full-time stage. The corrected
VI.1 seed, normalized VI.2 successor, and every source estimate are internal. -/
noncomputable def toStrictGeneratedFullTimeStageGrowthDataOfOSII
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    OSIIFullTimeStageVladimirovGrowthData
      (initial.toStrictGeneratedFullTimeContinuationStage lgc k) := by
  cases k with
  | zero => exact initial.toStrictGeneratedZeroArityFullTimeStageGrowthData lgc
  | succ q =>
    let S := canonicalRawNormalizedDepthSuccessorData initial lgc
    exact RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData.toFullTimeStageGrowthData_of_uniformDepth
      S.atDepth S.atDepth_alpha

/-- The actual OS-II global growth package retains linear time and spatial
orders. No fresh seminorm family is selected at each continuation depth. -/
theorem toStrictGeneratedFullTimeStageGrowthDataOfOSII_parameters
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) [NeZero k] :
    let G := initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc k
    let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
    let beta := osiiEquation621CanonicalSeedArityRate lgc
    G.polynomialDegree = k * (t + 2 * beta) ∧
      G.boundaryDegree = k * (t + 2 * beta) ∧
      G.spatialSeminorms = Finset.Iic (k * t + (k * d + 1), 0) := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    dsimp [toStrictGeneratedFullTimeStageGrowthDataOfOSII,
      RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData.toFullTimeStageGrowthData_of_uniformDepth,
      OSIIEquation621WeightedL1Section43BoundData.explicitIndexPreserving,
      osiiSpatialPolynomialWeightedL1ExplicitFlatSeminorms, osiiVI2DepthDegree]
    constructor
    · ring
    constructor
    · ring
    · rfl

end InitialGeneratedLogarithmicStageLevelData

end OSIIChapterV
end OSReconstruction
