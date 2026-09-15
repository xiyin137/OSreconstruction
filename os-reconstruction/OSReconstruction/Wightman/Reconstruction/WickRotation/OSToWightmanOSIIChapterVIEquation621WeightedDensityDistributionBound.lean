/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.SCV.DistributionalEOWKernel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery












noncomputable section

open Complex Filter MeasureTheory
open scoped Classical

namespace OSReconstruction

/-- Polynomially weighted `L1` mass of a flat spatial Schwartz test. -/
def osiiSpatialPolynomialWeightedL1
    {m : Nat} (p : Nat)
    (phi : SchwartzMap (Fin m -> Real) Complex) : Real :=
  ∫ x : Fin m -> Real, (1 + ‖x‖) ^ p * ‖phi x‖

theorem osiiSpatialPolynomialWeightedL1_nonneg
    {m p : Nat}
    (phi : SchwartzMap (Fin m -> Real) Complex) :
    0 <= osiiSpatialPolynomialWeightedL1 p phi :=
  integral_nonneg fun _ => mul_nonneg (by positivity) (norm_nonneg _)

theorem integrable_osiiSpatialPolynomialWeightedL1
    {m p : Nat}
    (phi : SchwartzMap (Fin m -> Real) Complex) :
    Integrable fun x : Fin m -> Real =>
      (1 + ‖x‖) ^ p * ‖phi x‖ :=
  SCV.schwartzMap_polynomial_norm_integrable phi p

/-- Polynomially weighted `L1` mass is absolutely homogeneous. -/
theorem osiiSpatialPolynomialWeightedL1_smul
    {m p : Nat}
    (c : Complex)
    (phi : SchwartzMap (Fin m -> Real) Complex) :
    osiiSpatialPolynomialWeightedL1 p (c • phi) =
      ‖c‖ * osiiSpatialPolynomialWeightedL1 p phi := by
  unfold osiiSpatialPolynomialWeightedL1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [SchwartzMap.smul_apply, norm_smul]
  ring

/-- Polynomially weighted `L1` mass, bundled as a seminorm on flat Schwartz
space. -/
noncomputable def osiiSpatialPolynomialWeightedL1Seminorm
    {m : Nat} (p : Nat) :
    Seminorm Complex (SchwartzMap (Fin m -> Real) Complex) :=
  Seminorm.of (osiiSpatialPolynomialWeightedL1 p) (by
    intro phi psi
    unfold osiiSpatialPolynomialWeightedL1
    rw [← integral_add
      (integrable_osiiSpatialPolynomialWeightedL1 (p := p) phi)
      (integrable_osiiSpatialPolynomialWeightedL1 (p := p) psi)]
    apply integral_mono_ae
      (integrable_osiiSpatialPolynomialWeightedL1 (p := p) (phi + psi))
      ((integrable_osiiSpatialPolynomialWeightedL1 (p := p) phi).add
        (integrable_osiiSpatialPolynomialWeightedL1 (p := p) psi))
    filter_upwards with x
    rw [SchwartzMap.add_apply]
    calc
      (1 + ‖x‖) ^ p * ‖phi x + psi x‖ <=
          (1 + ‖x‖) ^ p * (‖phi x‖ + ‖psi x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = (1 + ‖x‖) ^ p * ‖phi x‖ +
          (1 + ‖x‖) ^ p * ‖psi x‖ := by ring)
    (osiiSpatialPolynomialWeightedL1_smul (p := p))

@[simp]
theorem osiiSpatialPolynomialWeightedL1Seminorm_apply
    {m p : Nat} (phi : SchwartzMap (Fin m -> Real) Complex) :
    osiiSpatialPolynomialWeightedL1Seminorm p phi =
      osiiSpatialPolynomialWeightedL1 p phi := rfl

/-- The polynomially weighted flat `L1` mass is controlled by one explicit
finite family of Schwartz seminorms.  The family and constant depend only on
the flat dimension and the polynomial degree. -/
theorem exists_osiiSpatialPolynomialWeightedL1_schwartz_bound
    (m p : Nat) :
    ∃ s : Finset (Nat × Nat), ∃ K : Real, 0 < K ∧
      ∀ phi : SchwartzMap (Fin m -> Real) Complex,
        osiiSpatialPolynomialWeightedL1 p phi <=
          K * s.sup
            (schwartzSeminormFamily Complex (Fin m -> Real) Complex) phi := by
  let n : Nat := (volume : Measure (Fin m -> Real)).integrablePower
  let s : Finset (Nat × Nat) := Finset.Iic (p + n, 0)
  let decay : (Fin m -> Real) -> Real := fun x =>
    (1 + ‖x‖) ^ (-(n : Real))
  have hdecay_integrable : Integrable decay := by
    simpa [decay, n] using
      (MeasureTheory.Measure.integrable_pow_neg_integrablePower
        (μ := (volume : Measure (Fin m -> Real))))
  let J : Real := ∫ x : Fin m -> Real, decay x
  have hJ_nonneg : 0 <= J := by
    dsimp [J]
    exact integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
  let K : Real := 2 ^ (p + n) * (1 + J)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨s, K, hK, ?_⟩
  intro phi
  let sem : Real :=
    s.sup (schwartzSeminormFamily Complex (Fin m -> Real) Complex) phi
  have hsem : 0 <= sem := apply_nonneg _ _
  have hpointwise : ∀ x : Fin m -> Real,
      (1 + ‖x‖) ^ p * ‖phi x‖ <=
        decay x * (2 ^ (p + n) * sem) := by
    intro x
    have hsch :
        (1 + ‖x‖) ^ (p + n) * ‖phi x‖ <=
          2 ^ (p + n) * sem := by
      change (1 + ‖x‖) ^ (p + n) * ‖phi x‖ <=
        2 ^ (p + n) *
          (Finset.Iic (p + n, 0)).sup
            (fun i : Nat × Nat =>
              SchwartzMap.seminorm (E := Fin m -> Real) (F := Complex)
                Complex i.1 i.2) phi
      simpa using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := Complex) (m := (p + n, 0)) (k := p + n) (n := 0)
          le_rfl le_rfl phi x)
    rw [show decay x = (1 + ‖x‖) ^ (-(n : Real)) by rfl]
    rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
      le_div_iff₀' (by positivity), Real.rpow_natCast]
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hsch
  calc
    osiiSpatialPolynomialWeightedL1 p phi <=
        ∫ x : Fin m -> Real,
          decay x * (2 ^ (p + n) * sem) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x =>
          mul_nonneg (by positivity) (norm_nonneg (phi x))
      · exact hdecay_integrable.mul_const _
      · exact Filter.Eventually.of_forall hpointwise
    _ = 2 ^ (p + n) * J * sem := by
      rw [integral_mul_const]
      dsimp [J]
      ring
    _ <= K * sem := by
      apply mul_le_mul_of_nonneg_right _ hsem
      dsimp [K]
      have hpow : 0 <= (2 : Real) ^ (p + n) := pow_nonneg (by norm_num) _
      nlinarith

/-- The polynomially weighted `L1` seminorm is continuous in the Schwartz
topology. -/
theorem continuous_osiiSpatialPolynomialWeightedL1Seminorm
    (m p : Nat) :
    Continuous (osiiSpatialPolynomialWeightedL1Seminorm (m := m) p) := by
  obtain ⟨s, K, hK, hbound⟩ :=
    exists_osiiSpatialPolynomialWeightedL1_schwartz_bound m p
  let q : Seminorm Complex (SchwartzMap (Fin m -> Real) Complex) :=
    s.sup (schwartzSeminormFamily Complex (Fin m -> Real) Complex)
  have hq : Continuous q := by
    dsimp [q]
    have hq_all : ∀ t : Finset (Nat × Nat), Continuous
        ((t.sup (schwartzSeminormFamily Complex
          (Fin m -> Real) Complex) :
            Seminorm Complex (SchwartzMap (Fin m -> Real) Complex)) :
          SchwartzMap (Fin m -> Real) Complex -> Real) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
          change Continuous (fun _ :
            SchwartzMap (Fin m -> Real) Complex => (0 : Real))
          fun_prop
      | insert i t hi ih =>
          rw [Finset.sup_insert]
          change Continuous (fun phi : SchwartzMap (Fin m -> Real) Complex =>
            max ((schwartzSeminormFamily Complex
              (Fin m -> Real) Complex i) phi)
              ((t.sup (schwartzSeminormFamily Complex
                (Fin m -> Real) Complex)) phi))
          exact ((schwartz_withSeminorms Complex
            (Fin m -> Real) Complex).continuous_seminorm i).max ih
    exact hq_all s
  let K' : NNReal := ⟨K, hK.le⟩
  have hKq : Continuous (K' • q) := by
    change Continuous (fun phi => K * q phi)
    exact continuous_const.mul hq
  refine Seminorm.continuous_of_le hKq ?_
  apply Seminorm.le_def.mpr
  intro phi
  change osiiSpatialPolynomialWeightedL1 p phi <=
    K * (s.sup
      (schwartzSeminormFamily Complex (Fin m -> Real) Complex)) phi
  exact hbound phi

/-- Native Section-4.3 form of the weighted-`L1` seminorm estimate. -/
structure OSIIEquation621WeightedL1Section43BoundData
    (d k p : Nat) where
  spatialSeminorms : Finset (Nat × Nat)
  constant : Real
  constant_pos : 0 < constant
  bound : ∀ chi : SchwartzMap (Section43SpatialSpace d k) Complex,
    osiiSpatialPolynomialWeightedL1 p
        (section43SpatialFlatSchwartzCLE d k chi) <=
      constant * spatialSeminorms.sup
        (schwartzSeminormFamily Complex
          (Section43SpatialSpace d k) Complex) chi

namespace OSIIEquation621WeightedL1Section43BoundData

end OSIIEquation621WeightedL1Section43BoundData

/-- The exact weighted-`L1` estimate on one spatial distribution value.

This is weaker than choosing a represented continuous weighted density.  It
is nevertheless the invariant consumed by the first-bridge Hermite-mode
argument, and unlike a chosen density it is preserved directly by scalar
Malgrange--Zerner continuation. -/
structure OSIIEquation621WeightedL1PointBoundData
    {d k : Nat}
    (T : OSIISpatialDistribution d k)
    (p : Nat) (alpha : Real) (beta depth : Nat) where
  alpha_nonneg : 0 <= alpha
  norm_distribution_le : forall chi : SchwartzMap
      (Section43SpatialSpace d k) Complex,
    ‖T chi‖ <=
      osiiVI2ArityDepthMajorant alpha beta k depth *
        osiiSpatialPolynomialWeightedL1 p
          (section43SpatialFlatSchwartzCLE d k chi)

namespace OSIIEquation621WeightedL1PointBoundData

variable {d k p beta depth : Nat}
variable {T : OSIISpatialDistribution d k}
variable {alpha : Real}

/-- Transport a weighted-`L1` estimate across equality of spatial
distributions. -/
def congr
    {T' : OSIISpatialDistribution d k}
    (D : OSIIEquation621WeightedL1PointBoundData
      T p alpha beta depth)
    (h : T' = T) :
    OSIIEquation621WeightedL1PointBoundData
      T' p alpha beta depth := by
  rw [h]
  exact D

end OSIIEquation621WeightedL1PointBoundData

namespace OSIIEquation621WeightedL1RestrictedBoundData

variable {d k p beta depth : Nat}
variable {A B : OSIITimeContinuationStage d k}
variable {target : Set (Fin k -> Complex)}
variable {alpha : Real}

end OSIIEquation621WeightedL1RestrictedBoundData

/-- A common weighted-`L1` estimate at every point of a continuation stage.

This is the rank-stable scalar invariant.  It records precisely the family
of inequalities to which the coefficient-space maximum principle applies,
without imposing a stronger Banach-valued continuation. -/
structure OSIIEquation621WeightedL1ArityDepthBoundData
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (p : Nat) (alpha : Real) (beta depth : Nat) where
  alpha_nonneg : 0 <= alpha
  pointBound : forall zeta, zeta ∈ A.carrier ->
    OSIIEquation621WeightedL1PointBoundData
      (A.distribution zeta) p alpha beta depth

namespace OSIIEquation621WeightedL1ArityDepthBoundData

variable {d k p beta depth : Nat}
variable {A B : OSIITimeContinuationStage d k}
variable {alpha : Real}

end OSIIEquation621WeightedL1ArityDepthBoundData

namespace OSIIEquation621WeightedDensityPointBoundData

variable {d k p beta depth : Nat}
variable {T : OSIISpatialDistribution d k}
variable {alpha : Real}

end OSIIEquation621WeightedDensityPointBoundData

namespace OSIIEquation621PointwiseWeightedDensityArityDepthBoundData

variable {d k p beta depth : Nat}
variable {A B : OSIITimeContinuationStage d k}
variable {alpha : Real}

end OSIIEquation621PointwiseWeightedDensityArityDepthBoundData

namespace OSIIEquation621WeightedDensityArityDepthBoundData

end OSIIEquation621WeightedDensityArityDepthBoundData

namespace OSIIEquation621WeightedDensityPointBoundData

end OSIIEquation621WeightedDensityPointBoundData

namespace OSIIEquation621WeightedDensityContinuationData

end OSIIEquation621WeightedDensityContinuationData

namespace OSIITimeContinuationLadderRealEdgeDensityGrowthData
namespace OSIIEquation621WeightedPositiveRealRepresentationData

/-- A represented positive-real weighted density bounds its stage
distribution by the weighted `L1` mass of the spatial test. -/
theorem norm_distribution_le_weightedL1
    {d k p : Nat}
    {A : OSIITimeContinuationStage d k}
    (E : OSIIEquation621WeightedPositiveRealRepresentationData A p)
    (tau : {tau : Fin k -> Real //
      tau ∈ section43TimeStrictPositiveRegion k})
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖A.distribution (osiiPositiveRealTimeEmbed tau.1) chi‖ <=
      ‖E.density tau‖ *
        osiiSpatialPolynomialWeightedL1 p
          (section43SpatialFlatSchwartzCLE d k chi) := by
  rw [E.represents tau chi]
  calc
    ‖∫ x : Fin (k * d) -> Real,
        OSIISpatialPolynomialGrowthFunction.value (E.density tau) x *
          (section43SpatialFlatSchwartzCLE d k chi) x‖ <=
      ∫ x : Fin (k * d) -> Real,
        ‖OSIISpatialPolynomialGrowthFunction.value (E.density tau) x *
          (section43SpatialFlatSchwartzCLE d k chi) x‖ :=
      norm_integral_le_integral_norm _
    _ <= ∫ x : Fin (k * d) -> Real,
        ‖E.density tau‖ *
          ((1 + ‖x‖) ^ p *
            ‖(section43SpatialFlatSchwartzCLE d k chi) x‖) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
      · exact
          (integrable_osiiSpatialPolynomialWeightedL1
            (p := p) (section43SpatialFlatSchwartzCLE d k chi)).const_mul _
      · filter_upwards with x
        rw [norm_mul]
        have hvalue :
            ‖OSIISpatialPolynomialGrowthFunction.value (E.density tau) x‖ <=
              ‖E.density tau‖ * (1 + ‖x‖) ^ p := by
          simpa only [osiiSpatialPolynomialWeight] using
            (OSIISpatialPolynomialGrowthFunction.norm_value_le
              (E.density tau) x)
        calc
          ‖OSIISpatialPolynomialGrowthFunction.value (E.density tau) x‖ *
              ‖(section43SpatialFlatSchwartzCLE d k chi) x‖ <=
            (‖E.density tau‖ * (1 + ‖x‖) ^ p) *
              ‖(section43SpatialFlatSchwartzCLE d k chi) x‖ :=
            mul_le_mul_of_nonneg_right hvalue (norm_nonneg _)
          _ = ‖E.density tau‖ *
              ((1 + ‖x‖) ^ p *
                ‖(section43SpatialFlatSchwartzCLE d k chi) x‖) := by ring
    _ = ‖E.density tau‖ *
        osiiSpatialPolynomialWeightedL1 p
          (section43SpatialFlatSchwartzCLE d k chi) := by
      unfold osiiSpatialPolynomialWeightedL1
      rw [integral_const_mul]

end OSIIEquation621WeightedPositiveRealRepresentationData

namespace OSIIEquation621WeightedPositiveRealEdgeData

/-- The globally bounded edge package inherits the representation-only
weighted-`L1` distribution estimate. -/
theorem norm_distribution_le_weightedL1
    {d k p : Nat}
    {A : OSIITimeContinuationStage d k}
    (E : OSIIEquation621WeightedPositiveRealEdgeData A p)
    (tau : {tau : Fin k -> Real //
      tau ∈ section43TimeStrictPositiveRegion k})
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖A.distribution (osiiPositiveRealTimeEmbed tau.1) chi‖ <=
      ‖E.density tau‖ *
        osiiSpatialPolynomialWeightedL1 p
          (section43SpatialFlatSchwartzCLE d k chi) :=
  E.toRepresentationData.norm_distribution_le_weightedL1 tau chi

end OSIIEquation621WeightedPositiveRealEdgeData
end OSIITimeContinuationLadderRealEdgeDensityGrowthData

namespace OSIIEquation621SpatialApproxIdentityData

/-- Translation preserves the ordinary `L1` mass of a flat spatial probe. -/
theorem integral_norm_translatedTest_eq_one
    {m : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData m)
    (x : Fin m -> Real) (N : Nat) :
    (∫ y : Fin m -> Real, ‖Q.translatedTest x N y‖) = 1 := by
  calc
    (∫ y : Fin m -> Real, ‖Q.translatedTest x N y‖) =
        ∫ y : Fin m -> Real, ‖Q.test N y‖ := by
      simpa [translatedTest, SCV.translateSchwartz_apply] using
        (MeasureTheory.integral_add_right_eq_self
          (f := fun y : Fin m -> Real => ‖Q.test N y‖) (-x))
    _ = 1 :=
      integral_norm_eq_one_of_nonnegative_real_schwartz
        (Q.test N) (Q.nonneg N) (Q.real N) (Q.integral_eq_one N)

/-- The polynomially weighted mass of a translated spatial probe has the
sharp radius-dependent loss.  Unlike a fixed uniform constant, this
coefficient tends to one with the approximate-identity radius. -/
theorem weightedL1_translatedTest_le_radius
    {m p : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData m)
    (N : Nat) (x : Fin m -> Real) :
    osiiSpatialPolynomialWeightedL1 p (Q.translatedTest x N) <=
      (1 + |Q.radius N|) ^ p * (1 + ‖x‖) ^ p := by
  let C : Real := (1 + |Q.radius N|) ^ p
  have hpoint : forall y : Fin m -> Real,
      (1 + ‖y‖) ^ p * ‖Q.translatedTest x N y‖ <=
        (C * (1 + ‖x‖) ^ p) * ‖Q.translatedTest x N y‖ := by
    intro y
    by_cases hy : Q.translatedTest x N y = 0
    · simp [hy]
    · have hsupport : y + (-x) ∈
          Function.support (Q.test N : (Fin m -> Real) -> Complex) := by
        simpa [translatedTest, SCV.translateSchwartz_apply,
          Function.mem_support] using hy
      have hball := Q.support_subset_ball N hsupport
      have hdiff : ‖y - x‖ <= |Q.radius N| := by
        have hlt : ‖y - x‖ < Q.radius N := by
          simpa [Metric.mem_ball, sub_eq_add_neg, dist_eq_norm] using hball
        exact hlt.le.trans (le_abs_self (Q.radius N))
      have hy_norm : ‖y‖ <= ‖x‖ + ‖y - x‖ := by
        have h := norm_add_le x (y - x)
        simpa [add_sub_cancel] using h
      have hbase :
          1 + ‖y‖ <= (1 + |Q.radius N|) * (1 + ‖x‖) := by
        nlinarith [norm_nonneg x, abs_nonneg (Q.radius N)]
      have hweight : (1 + ‖y‖) ^ p <=
          C * (1 + ‖x‖) ^ p := by
        calc
          (1 + ‖y‖) ^ p <=
              ((1 + |Q.radius N|) * (1 + ‖x‖)) ^ p :=
            pow_le_pow_left₀ (by positivity) hbase p
          _ = C * (1 + ‖x‖) ^ p := by
            simp only [C, mul_pow]
      exact mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
  calc
    osiiSpatialPolynomialWeightedL1 p (Q.translatedTest x N) <=
        ∫ y : Fin m -> Real,
          (C * (1 + ‖x‖) ^ p) * ‖Q.translatedTest x N y‖ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ =>
          mul_nonneg (by positivity) (norm_nonneg _)
      · exact (Q.translatedTest x N).integrable.norm.const_mul _
      · exact Filter.Eventually.of_forall hpoint
    _ = (C * (1 + ‖x‖) ^ p) *
        ∫ y : Fin m -> Real, ‖Q.translatedTest x N y‖ := by
      rw [integral_const_mul]
    _ = (1 + |Q.radius N|) ^ p * (1 + ‖x‖) ^ p := by
      rw [Q.integral_norm_translatedTest_eq_one x N, mul_one]

/-- The sharp radius-dependent coefficient in the preceding estimate tends
to one. -/
theorem tendsto_radiusPolynomialCoefficient_one
    {m p : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData m) :
    Tendsto (fun N => (1 + |Q.radius N|) ^ p) atTop (nhds 1) := by
  have hcontinuous : Continuous (fun r : Real => (1 + |r|) ^ p) := by
    fun_prop
  change Tendsto (((fun r : Real => (1 + |r|) ^ p) ∘ Q.radius))
    atTop (nhds 1)
  convert hcontinuous.continuousAt.tendsto.comp Q.radius_tendsto using 1 <;>
    norm_num

/-- Section-4.3 form of the sharp radius-dependent probe estimate. -/
theorem weightedL1_section43Probe_le_radius
    {d k p : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData (k * d))
    (N : Nat) (x : Fin (k * d) -> Real) :
    osiiSpatialPolynomialWeightedL1 p
        (section43SpatialFlatSchwartzCLE d k (Q.section43Probe x N)) <=
      (1 + |Q.radius N|) ^ p * osiiSpatialPolynomialWeight p x := by
  simpa [section43Probe, osiiSpatialPolynomialWeight] using
    Q.weightedL1_translatedTest_le_radius (p := p) N x

end OSIIEquation621SpatialApproxIdentityData

namespace OSIIEquation621WeightedL1PointBoundData

end OSIIEquation621WeightedL1PointBoundData

namespace OSIITimeContinuationLadderRealEdgeDensityGrowthData
namespace OSIIEquation621WeightedPositiveRealEdgeData

end OSIIEquation621WeightedPositiveRealEdgeData
end OSIITimeContinuationLadderRealEdgeDensityGrowthData

namespace OSIIEquation621WeightedDensityContinuationData

end OSIIEquation621WeightedDensityContinuationData
end OSReconstruction
