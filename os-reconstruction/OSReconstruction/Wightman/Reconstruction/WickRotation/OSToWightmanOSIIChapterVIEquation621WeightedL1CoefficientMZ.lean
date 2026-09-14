/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientAmbientAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace StrictScalarSeedCoefficientMZBoundData

variable {d : Nat} [NeZero d]
variable {n k : Nat} [NeZero n]
variable {A : OSIITimeContinuationStage d k}
variable {S rho : Real}
variable {P : SCV.StripCompactificationParameters S rho}
variable {seed : Fin n -> Fin k -> Real}

/-- The selected scalar MZ continuation preserves any nonnegative bound
already valid on its complete flat coefficient window.

The existing `norm_extension_le` is the specialization to the finite
Schwartz-seminorm bound stored in `B`.  Keeping the bound abstract is what
allows the equation-`(6.28)` weighted-`L1` profile to pass through analytic
rank convexification without profile growth. -/
theorem norm_extension_le_of_flat_bound
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (C : Real)
    (hC : 0 <= C)
    (hbound : forall r,
      r ∈ osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ->
        ‖osiiStrictScalarSeedCoefficientPairing A seed chi r‖ <= C)
    (z : osiiAxisPairIndex n -> Complex)
    (hz : z ∈ osiiAxisPairLogDomain (d := n)) :
    ‖B.extension chi z‖ <= C := by
  let F : (Fin n -> Complex) -> Complex :=
    osiiStrictScalarSeedCoefficientPairing A seed chi
  let U : Set (Fin n -> Complex) :=
    osiiStrictScalarSeedCoefficientCarrier A seed
  have hF : DifferentiableOn Complex F U :=
    differentiableOn_osiiStrictScalarSeedCoefficientPairing A seed chi
  have hwindow :
      osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ⊆ U :=
    strictScalarSeedCoefficientFlatWindow_subset_carrier_of_flat
      A seed B.flatCoefficientTube_subset
      (P.radius + rho) rho B.rho_lt_one
  let X := osiiStrictCoefficientCompactifiedFlatCrossData
    P B.rho_pos F U hF hwindow
  have hreal : forall x : osiiAxisPairIndex n -> Real,
      B.extension chi (osiiAxisPairLogRealEmbed x) =
        X.family.realEdge x := by
    intro x
    simpa [X, F, U, realEdge,
      osiiStrictCoefficientCompactifiedFlatCrossData,
      osiiStrictCoefficientCompactifiedDirectionalFamily] using
        B.extension_realEdge chi x
  have hreal_bound : forall x : osiiAxisPairIndex n -> Real,
      ‖X.family.realEdge x‖ <= C := by
    intro x
    let a0 : osiiAxisPairIndex n :=
      (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, false)
    have hstrip :
        osiiAxisPairLogRealEmbed x ∈
          osiiAxisPairCoordinateLogStrip a0 := by
      simp [osiiAxisPairCoordinateLogStrip,
        osiiAxisPairLogRealEmbed]
      positivity
    have hmem :=
      osiiStrictCoefficientCompactifiedDirectionalInput_mem_flatWindow
        P B.rho_pos x a0 hstrip
    simpa [X, F, U, realEdge,
      osiiStrictCoefficientCompactifiedFlatCrossData,
      osiiStrictCoefficientCompactifiedDirectionalFamily,
      osiiStrictCoefficientCompactifiedDirectionalInput_real] using
        hbound _ hmem
  have hchart_bound : forall a : osiiAxisPairIndex n,
      forall (x : osiiAxisPairIndex n -> Real) (w : Complex),
        |w.im| < Real.pi / 2 ->
          ‖X.family.flatTubeBranch
            (Function.update
              (osiiAxisPairLogRealEmbed x) a w)‖ <= C := by
    intro a x w hw
    rw [X.family.flatTubeBranch_coordinate_line_eq_branch x a hw]
    apply hbound
    apply
      osiiStrictCoefficientCompactifiedDirectionalInput_mem_flatWindow
        P B.rho_pos x a
    simpa [osiiAxisPairCoordinateLogStrip] using hw
  by_cases hCzero : C = 0
  · have hzero_real : forall x : osiiAxisPairIndex n -> Real,
        B.extension chi (osiiAxisPairLogRealEmbed x) =
          (0 : Complex) := by
      intro x
      apply norm_eq_zero.mp
      apply le_antisymm
      · rw [hreal x]
        simpa [hCzero] using hreal_bound x
      · exact norm_nonneg _
    have hzero : B.extension chi z = 0 :=
      eqOn_logDomain_of_eq_realEdge
        (B.extension_differentiableOn chi)
        (differentiableOn_const (0 : Complex))
        hzero_real hz
    rw [hzero, norm_zero, hCzero]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    exact
      X.norm_holomorphic_realEdge_extension_le
        C hreal_bound C hCpos hchart_bound
        (B.extension chi)
        (B.extension_differentiableOn chi)
        hreal z hz

/-- A weighted-`L1` estimate on exactly the flat coefficient window extends
to every point of the coefficient germ.

This is the minimal quantitative input to coefficient MZ.  In particular it
does not require the same bound at incidental points of the larger seed
continuation stage. -/
def coefficientGermWeightedL1PointBoundDataOfFlatWindow
    {p beta depth : Nat} {alpha : Real}
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (halpha : 0 <= alpha)
    (flatBound : forall q,
      q ∈ osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ->
        OSIIEquation621WeightedL1PointBoundData
          (A.distribution
            (osiiLogExp (osiiStrictScalarSeedCoefficientMap seed q)))
          p alpha beta depth)
    (r : Fin n -> Complex)
    (hr : r ∈ osiiStrictCoefficientGermDomain P) :
    OSIIEquation621WeightedL1PointBoundData
      (B.coefficientGermDistribution r) p alpha beta depth where
  alpha_nonneg := halpha
  norm_distribution_le := by
    intro chi
    let C := osiiVI2ArityDepthMajorant alpha beta k depth *
      osiiSpatialPolynomialWeightedL1 p
        (section43SpatialFlatSchwartzCLE d k chi)
    have hC : 0 <= C := mul_nonneg
      (osiiVI2ArityDepthMajorant_nonneg
        halpha beta k depth)
      (osiiSpatialPolynomialWeightedL1_nonneg _)
    rw [B.coefficientGermDistribution_apply_of_mem r hr chi]
    change ‖B.extension chi
      (osiiStrictCoefficientLocalInverseLift P r)‖ <= C
    apply B.norm_extension_le_of_flat_bound chi C hC
    intro q hq
    have hpoint := flatBound q hq
    simpa [C, osiiStrictScalarSeedCoefficientPairing] using
      hpoint.norm_distribution_le chi
    exact hr.2

end StrictScalarSeedCoefficientMZBoundData

/-- A zero-pointed ambient coefficient chart together with the weighted-`L1`
estimate inherited by every point of that chart.

Keeping the quantitative statement attached to its actual chart avoids any
claim that an independently chosen ambient chart has the same global bound.
Only target-point compatibility is used when passing to a canonical atlas. -/
structure WeightedL1ZeroPointedAmbientChartData
    {d k : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d k)
    (z : Fin k -> Complex)
    (p : Nat) (alpha : Real) (beta depth : Nat) where
  chart : ZeroPointedAmbientChartData A z
  weightedL1 : OSIIEquation621WeightedL1ArityDepthBoundData
    chart.stage p alpha beta depth

namespace StrictCoefficientTargetSectionData

variable {d : Nat} [NeZero d]
variable {n k : Nat} [NeZero n]
variable {A : OSIITimeContinuationStage d k}
variable {S rho : Real}
variable {P : SCV.StripCompactificationParameters S rho}
variable {seed : Fin n -> Fin k -> Real}
variable {r0 : Fin n -> Complex}

/-- Pulling the coefficient MZ germ back through a target section preserves
a weighted-`L1` bound known only on the required flat coefficient window. -/
def toAmbientStageWeightedL1ArityDepthBoundDataOfFlatWindow
    {p beta depth : Nat} {alpha : Real}
    (R : StrictCoefficientTargetSectionData seed r0)
    (C : StrictCoefficientTargetConvexChartData P r0)
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (halpha : 0 <= alpha)
    (flatBound : forall q,
      q ∈ osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ->
        OSIIEquation621WeightedL1PointBoundData
          (A.distribution
            (osiiLogExp (osiiStrictScalarSeedCoefficientMap seed q)))
          p alpha beta depth) :
    OSIIEquation621WeightedL1ArityDepthBoundData
      (R.toAmbientStage C B) p alpha beta depth where
  alpha_nonneg := halpha
  pointBound := by
    intro z hz
    apply B.coefficientGermWeightedL1PointBoundDataOfFlatWindow
      halpha flatBound
    exact C.domain_subset hz

/-- Assemble a quantitative zero-pointed chart from the minimal flat-window
weighted-`L1` input. -/
noncomputable def toWeightedL1ZeroPointedAmbientChartDataOfFlatWindow
    {p beta depth : Nat} {alpha : Real}
    {z : Fin k -> Complex}
    (R : StrictCoefficientTargetSectionData seed r0)
    (C : StrictCoefficientTargetConvexChartData P r0)
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (halpha : 0 <= alpha)
    (flatBound : forall q,
      q ∈ osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ->
        OSIIEquation621WeightedL1PointBoundData
          (A.distribution
            (osiiLogExp (osiiStrictScalarSeedCoefficientMap seed q)))
          p alpha beta depth)
    (htarget : osiiStrictScalarSeedCoefficientCLM seed r0 = z) :
    WeightedL1ZeroPointedAmbientChartData
      A z p alpha beta depth := by
  let hU := R.exists_open_seed_toAmbientStage_eq_predecessor C B
  let U := Classical.choose hU
  have hU_spec := Classical.choose_spec hU
  let Q : ZeroPointedAmbientChartData A z := {
    stage := R.toAmbientStage C B
    carrier_convex := R.ambientDomain_convex C
    zero_mem := R.zero_mem_ambientDomain C
    target_mem := by
      rw [← htarget]
      exact R.target_mem_ambientDomain C
    seedDomain := U
    seed_open := hU_spec.1
    zero_mem_seed := hU_spec.2.1
    seed_subset_overlap := hU_spec.2.2.1
    seed_agreesPredecessor := hU_spec.2.2.2 }
  refine ⟨Q, ?_⟩
  change OSIIEquation621WeightedL1ArityDepthBoundData
    (R.toAmbientStage C B) p alpha beta depth
  exact R.toAmbientStageWeightedL1ArityDepthBoundDataOfFlatWindow
    C B halpha flatBound

end StrictCoefficientTargetSectionData

namespace WeightedL1ZeroPointedAmbientChartData

end WeightedL1ZeroPointedAmbientChartData

namespace ZeroPointedAmbientAtlasData

end ZeroPointedAmbientAtlasData
end OSIIChapterV
end OSReconstruction
