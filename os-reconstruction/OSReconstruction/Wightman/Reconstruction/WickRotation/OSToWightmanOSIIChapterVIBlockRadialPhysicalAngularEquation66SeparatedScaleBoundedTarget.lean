import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66FixedBoundedTarget

/-!
# Separated radial and carrier scales for equation (6.6)

The bounded-MZ radial kernel scale and the angular first-carrier scale play
different roles.  This module separates them: inverse powers use the kernel
scale, while sector and target estimates use the independent carrier scale.
-/

noncomputable section

open Complex Metric Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIStep4MultiGapSelectedCommonSlopeData

set_option maxHeartbeats 1200000

/-- The MZ kernel radius and the angular first-carrier radius are independent.
The former controls the radial source and inverse-scale bound; the latter is
used only to place the physical target in the universal narrow sector. -/
theorem exists_boundedScalarTargetChart_equation66_fixedData_of_carrierScale
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    {r : Real} (hr : 0 < r) (hr_le : r <= 16)
    {rho : Real} (hrho : 0 < rho)
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall i : Fin k,
      r <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))}
    (hcenterCarrier : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hr (osiiStep4MultiGapXiHatCenter d k center) y y'
        (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))
    (hp : (y, y') ∈
      osiiStep4PartialConvolutionClosedImaginaryBox (d + 1) k r)
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho D.T / 4)) :
    let shift := Real.log (osiiNarrowTimeLogScale (d := d) D.T)
    let u := osiiStep4MultiGapTargetCenteredInput
      d k shift D.T center y
    let B := osiiStep4MultiGapCenteredCompactifiedBound
      G.constant G.scaleDegree G.growthDegree r
        (osiiStep4MultiGapXiHatCenter d k center)
        osiiEquation66UniversalStripParameters.radius u
    0 < B ∧
      exists Gamma0 :
          (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex,
        DifferentiableOn Complex Gamma0
            (osiiAxisPairMultiGapLogDomain d k) ∧
        (forall x : Fin k -> osiiAxisPairIndex d -> Real,
          Gamma0 (osiiAxisPairSimultaneousLogRealEmbed x) =
            osiiStep4FixedRadiusCenteredSchwinger d OS k hr
              (osiiStep4MultiGapXiHatCenter d k center +
                osiiStep4AxisPairGapTranslationFlat d D.T x) y y'
              (osiiStep4MultiGapTranslatedCenter_time_lower d k
                (osiiStep4MultiGapXiHatCenter d k center)
                (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)
                D.T D.hT x)) ∧
        exists A : OSIIChapterV.BoundedScalarContinuationData
            (Fintype.card (osiiAxisPairMultiGapIndex d k)) B,
          (forall x :
              Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Real,
            (fun j => (x j : Complex)) ∈ A.carrier ->
              A.toFun (fun j => (x j : Complex)) =
                (D.flatCrossData OS lgc).realEdge
                  (osiiStep4MultiGapCenteredCoefficientBase shift u +
                    osiiAxisPairMultiGapFinUnflatten x)) ∧
          exists Q : OSIIChapterV.BoundedScalarTargetChartData A
              (osiiStep4MultiGapTargetDisplacementFin d k D.T center y),
            Q.toFun
                (osiiStep4MultiGapTargetDisplacementFin d k D.T center y) =
              Gamma0 (osiiStep4MultiGapTargetLog d k D.T center y) := by
  dsimp only
  have hbudget8 :=
    osiiStep4MultiGapTarget_argumentBudget_lt_pi_div_eight
      d k hrho D.hT center y hcenterCarrier hy
  have hS :
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |(osiiStep4MultiGapTargetLog d k D.T center y i a).im|) <=
          Real.pi / 8 := by
    apply le_of_lt
    simpa only [osiiStep4MultiGapTargetLog, Complex.log_im] using hbudget8
  have hsigma : Real.pi / 4 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hbudget :
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |Complex.arg
          (osiiStep4MultiGapTargetCoeff d k D.T center y i a)|) <
        Real.pi / 2 :=
    hbudget8.trans (by nlinarith [Real.pi_pos])
  exact D.exists_boundedScalarTargetChart_fixedData_of_parameters
    (hcenter := hcenter)
    d k OS lgc G hr hr_le hp
    osiiEquation66UniversalStripParameters hsigma hS hbudget

/-- Route-facing separated-scale projection of the bounded-MZ continuation. -/
theorem exists_centeredSchwingerExtension_equation66_fixedData_bound_of_carrierScale
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    {r : Real} (hr : 0 < r) (hr_le : r <= 16)
    {rho : Real} (hrho : 0 < rho)
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall i : Fin k,
      r <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))}
    (hcenterCarrier : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hr (osiiStep4MultiGapXiHatCenter d k center) y y'
        (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))
    (hp : (y, y') ∈
      osiiStep4PartialConvolutionClosedImaginaryBox (d + 1) k r)
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho D.T / 4)) :
    let shift := Real.log (osiiNarrowTimeLogScale (d := d) D.T)
    let u := osiiStep4MultiGapTargetCenteredInput
      d k shift D.T center y
    let B := osiiStep4MultiGapCenteredCompactifiedBound
      G.constant G.scaleDegree G.growthDegree r
        (osiiStep4MultiGapXiHatCenter d k center)
        osiiEquation66UniversalStripParameters.radius u
    exists Gamma0 :
        (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex,
      DifferentiableOn Complex Gamma0
          (osiiAxisPairMultiGapLogDomain d k) ∧
      (forall x : Fin k -> osiiAxisPairIndex d -> Real,
        Gamma0 (osiiAxisPairSimultaneousLogRealEmbed x) =
          osiiStep4FixedRadiusCenteredSchwinger d OS k hr
            (osiiStep4MultiGapXiHatCenter d k center +
              osiiStep4AxisPairGapTranslationFlat d D.T x) y y'
            (osiiStep4MultiGapTranslatedCenter_time_lower d k
              (osiiStep4MultiGapXiHatCenter d k center)
              (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)
              D.T D.hT x)) ∧
      norm (Gamma0
        (osiiStep4MultiGapTargetLog d k D.T center y)) <= B := by
  dsimp only
  obtain ⟨_hB, Gamma0, hGamma0, hreal, A, _hAreal, Q, hQtarget⟩ :=
    D.exists_boundedScalarTargetChart_equation66_fixedData_of_carrierScale
      (hcenter := hcenter)
      d k OS lgc G hr hr_le hrho hcenterCarrier hp hy
  refine ⟨Gamma0, hGamma0, hreal, ?_⟩
  calc
    norm (Gamma0 (osiiStep4MultiGapTargetLog d k D.T center y)) =
        norm (Q.toFun
          (osiiStep4MultiGapTargetDisplacementFin d k D.T center y)) :=
      congrArg norm hQtarget.symm
    _ <= osiiStep4MultiGapCenteredCompactifiedBound
          G.constant G.scaleDegree G.growthDegree r
          (osiiStep4MultiGapXiHatCenter d k center)
          osiiEquation66UniversalStripParameters.radius
          (osiiStep4MultiGapTargetCenteredInput d k
            (Real.log (osiiNarrowTimeLogScale (d := d) D.T))
            D.T center y) :=
      Q.norm_toFun_le
        (z := osiiStep4MultiGapTargetDisplacementFin d k D.T center y)
        Q.target_mem_domain

/-- Polynomial target bound with the radial inverse scale and angular carrier
scale kept separate. -/
theorem centeredCompactifiedBound_equation66_le_polynomial_of_carrierScale
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    {r rho T : Real} (hr : 0 < r) (hr_le : r <= 16)
    (hrho : 0 < rho) (hT : 1 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenterCarrier : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho T / 4)) :
    osiiStep4MultiGapCenteredCompactifiedBound
        G.constant G.scaleDegree G.growthDegree r
        (osiiStep4MultiGapXiHatCenter d k center)
        osiiEquation66UniversalStripParameters.radius
        (osiiStep4MultiGapTargetCenteredInput d k
          (Real.log (osiiNarrowTimeLogScale (d := d) T)) T center y) <=
      equation66MZPolynomialConstant G *
        (16 / r) ^ G.scaleDegree *
        (1 + norm center) ^ G.growthDegree := by
  let K := osiiEquation66CenteredTargetGrowthFactor d k
  let scale := (16 / r) ^ G.scaleDegree
  let centerPower := (1 + norm center) ^ G.growthDegree
  have hXi := norm_osiiStep4MultiGapXiHatCenter_le d k center
  have htarget := osiiStep4MultiGapTargetCenteredInput_polynomial_bound
    d k hrho hT center y hcenterCarrier hy
  have hinner :
      1 + norm (osiiStep4MultiGapXiHatCenter d k center) +
          Real.exp osiiEquation66UniversalStripParameters.radius *
            (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
              Real.exp
                (osiiStep4MultiGapTargetCenteredInput d k
                  (Real.log (osiiNarrowTimeLogScale (d := d) T))
                  T center y i a)) <=
        K * (1 + norm center) := by
    calc
      1 + norm (osiiStep4MultiGapXiHatCenter d k center) +
          Real.exp osiiEquation66UniversalStripParameters.radius *
            (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
              Real.exp
                (osiiStep4MultiGapTargetCenteredInput d k
                  (Real.log (osiiNarrowTimeLogScale (d := d) T))
                  T center y i a)) <=
        1 + norm center +
          Real.exp osiiEquation66UniversalStripParameters.radius *
            (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
              Real.exp
                (osiiStep4MultiGapTargetCenteredInput d k
                  (Real.log (osiiNarrowTimeLogScale (d := d) T))
                  T center y i a)) := by gcongr
      _ <= K * (1 + norm center) := htarget
  have hscaleBase : 1 <= 16 / r := by
    apply (le_div_iff₀ hr).2
    nlinarith
  have hscale : 1 <= scale := one_le_pow₀ hscaleBase
  have hcenterPower : 1 <= centerPower := by
    exact one_le_pow₀ (by linarith [norm_nonneg center])
  have hbase : 1 <= scale * centerPower := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ <= scale * centerPower :=
        mul_le_mul hscale hcenterPower (by norm_num) (by linarith)
  have hK : 0 <= K :=
    (osiiEquation66CenteredTargetGrowthFactor_pos d k).le
  have hinner0 :
      0 <= 1 + norm (osiiStep4MultiGapXiHatCenter d k center) +
        Real.exp osiiEquation66UniversalStripParameters.radius *
          (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
            Real.exp
              (osiiStep4MultiGapTargetCenteredInput d k
                (Real.log (osiiNarrowTimeLogScale (d := d) T))
                T center y i a)) := by positivity
  have hpow := pow_le_pow_left₀ hinner0 hinner G.growthDegree
  unfold osiiStep4MultiGapCenteredCompactifiedBound
  calc
    1 + G.constant * (16 / r) ^ G.scaleDegree *
        (1 + norm (osiiStep4MultiGapXiHatCenter d k center) +
          Real.exp osiiEquation66UniversalStripParameters.radius *
            (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
              Real.exp
                (osiiStep4MultiGapTargetCenteredInput d k
                  (Real.log (osiiNarrowTimeLogScale (d := d) T))
                  T center y i a))) ^ G.growthDegree <=
      1 + G.constant * scale *
        (K * (1 + norm center)) ^ G.growthDegree := by
      have hcoeff :
          0 <= G.constant * (16 / r) ^ G.scaleDegree :=
        mul_nonneg G.constant_nonneg (pow_nonneg (by positivity) _)
      dsimp only [scale]
      exact add_le_add (le_refl 1)
        (mul_le_mul_of_nonneg_left hpow hcoeff)
    _ = 1 +
        (G.constant * K ^ G.growthDegree) *
          (scale * centerPower) := by
      dsimp only [centerPower]
      rw [mul_pow]
      ring
    _ <= (1 + G.constant * K ^ G.growthDegree) *
        (scale * centerPower) := by
      have htail : 0 <= G.constant * K ^ G.growthDegree :=
        mul_nonneg G.constant_nonneg (pow_nonneg hK _)
      nlinarith
    _ = equation66MZPolynomialConstant G *
        (16 / r) ^ G.scaleDegree *
        (1 + norm center) ^ G.growthDegree := by
      simp only [equation66MZPolynomialConstant, K, scale, centerPower]
      ring

end OSIIStep4MultiGapSelectedCommonSlopeData
end OSReconstruction
