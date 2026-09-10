/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66ComplexTargetRadius
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66SeparatedScaleBoundedTarget
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66LocalWeylDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedTargetIdentification

/-!
# Quantitative local-Weyl density for equation (6.6)

This module replaces openness-based scale selection by the explicit fraction
`firstCarrierScale / 32`, and proves one fixed-data MZ bound uniformly over the
complete support box at that scale.
-/

noncomputable section

open Complex MeasureTheory Metric Set Topology
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
variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}

private abbrev FlatSource := Fin (k * (d + 1)) -> Real

/-- Fixed local-Weyl scale selected from the explicit complex first-carrier
ball. -/
def osiiEquation66QuantitativeLocalWeylScale
    (d k : Nat) [NeZero d] [NeZero k]
    (rho T : Real) : Real :=
  osiiEquation66FirstCarrierScale d k rho T / 32

/-- Stable local-Weyl data together with the exact quantitative scale used to
construct it. -/
structure OSIIEquation66QuantitativeLocalWeylDensityData
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc) where
  data : OSIIEquation66LocalWeylDensityData D
  scale_eq : data.scale =
    osiiEquation66QuantitativeLocalWeylScale d k rho Z.uniform.T

/-- Every retained continuation admits local-Weyl density recovery at the
explicit first-carrier fraction. -/
theorem nonempty_equation66QuantitativeLocalWeylDensityData
    (hrho_le : rho <= 16)
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc) :
    Nonempty (OSIIEquation66QuantitativeLocalWeylDensityData D) := by
  let carrierScale :=
    osiiEquation66FirstCarrierScale d k rho Z.uniform.T
  let sigma := osiiEquation66QuantitativeLocalWeylScale
    d k rho Z.uniform.T
  have hcarrierScale : 0 < carrierScale :=
    osiiEquation66FirstCarrierScale_pos d k hrho
      (lt_trans zero_lt_one Z.uniform.hT)
  have hsigma : 0 < sigma := by
    dsimp [sigma, osiiEquation66QuantitativeLocalWeylScale]
    positivity
  have hsigma_rho : sigma <= rho / 2 := by
    have hhalf := osiiEquation66FirstCarrierScale_le_half
      d k rho Z.uniform.T
    dsimp [sigma, osiiEquation66QuantitativeLocalWeylScale, carrierScale]
    nlinarith
  have hsigma_sixteen : sigma <= 16 := by
    nlinarith
  let R : Real := 8 * sigma
  have hsigma_R : sigma <= R / 8 := by
    dsimp only [R]
    linarith
  have hball : Metric.ball
      (0 : Fin (k * (d + 1)) -> Complex) R ⊆
        D.complexTargetDomain := by
    have htarget := D.equation66ComplexBall_subset_complexTargetDomain
    intro z hz
    apply htarget
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    have hR : R = carrierScale / 4 := by
      dsimp [R, sigma, osiiEquation66QuantitativeLocalWeylScale,
        carrierScale]
      ring
    rwa [hR] at hz
  obtain ⟨F, hF_holo, hF_rep⟩ :=
    D.equation66_exists_holomorphic_density_representsOnSupport
      R sigma hsigma hsigma_R hsigma_rho hball
  have hfirst : forall y : FlatSource (d := d) (k := k),
      y ∈ Metric.closedBall 0 (sigma / 4) ->
        osiiStep4MultiGapTargetLog d k Z.uniform.T center y ∈
          osiiAxisPairMultiGapLogDomain d k := by
    intro y hy
    have hy' : y ∈ Metric.closedBall 0 (carrierScale / 4) := by
      apply Metric.closedBall_subset_closedBall (show sigma / 4 <= carrierScale / 4 by
        dsimp [sigma, osiiEquation66QuantitativeLocalWeylScale, carrierScale]
        nlinarith) hy
    have hbudget :=
      osiiStep4MultiGapTarget_argumentBudget_lt_pi_div_eight
        d k hrho Z.uniform.hT center y hcenter hy'
    exact osiiStep4MultiGapTargetLog_mem_logDomain_of_argumentBudget
      d k Z.uniform.T center y
        (hbudget.trans (by nlinarith [Real.pi_pos]))
  have hradial : ∀ z,
      z ∈ osiiStep4FullBlockRadialClosedSupport
        (d + 1) k (3 * sigma) ->
      osiiStep4ComplexOfRealImag
          (osiiStep4MultiGapXiHatCenter d k center) 0 + z ∈
        Metric.ball
          (SCV.realEmbed
            (osiiStep4MultiGapXiHatCenter d k center)) sigma := by
    intro z hz
    have h := localBallDensityGeometry_radialSupport
      (d := d) (k := k) (center := center)
      (2 * sigma) sigma (by positivity) hsigma (by linarith) z hz
    simpa [osiiLocalBallDensityGeometry] using h
  have hmean : F (osiiStep4ComplexOfRealImag
        (osiiStep4MultiGapXiHatCenter d k center) 0) =
      ∫ y' : FlatSource (d := d) (k := k),
        ∫ y : FlatSource (d := d) (k := k),
          osiiStep4DistributionalPartialConvolutionTransform
            D.imaginarySliceFamily hsigma
              (osiiStep4MultiGapXiHatCenter d k center) y y' :=
    D.distributionalPartialConvolutionTransform_meanValue_of_representsOnSupport_atScale
      hsigma F
      (Metric.ball
        (SCV.realEmbed
          (osiiStep4MultiGapXiHatCenter d k center)) sigma)
      hF_rep hF_holo hradial
  let A : OSIIEquation66LocalWeylDensityData D := {
    scale := sigma
    scale_pos := hsigma
    scale_le := hsigma_rho
    scale_le_sixteen := hsigma_sixteen
    density := F
    holomorphic := hF_holo
    represents := hF_rep
    firstCarrierCoverage := hfirst
    meanValue := hmean }
  exact ⟨{
    data := A
    scale_eq := by
      rfl }⟩

/-- The exact equation-(6.6) integrand is uniformly bounded on its complete
support box by the separated-scale fixed-data MZ polynomial. -/
theorem OSIIEquation66QuantitativeLocalWeylDensityData.distributionalTransform_le_mzPolynomial
    {D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc}
    (A : OSIIEquation66QuantitativeLocalWeylDensityData D)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    (p : FlatSource (d := d) (k := k) ×
      FlatSource (d := d) (k := k))
    (hp : p ∈ osiiStep4PartialConvolutionClosedImaginaryBox
      (d + 1) k A.data.scale) :
    ‖osiiStep4DistributionalPartialConvolutionTransform
        D.imaginarySliceFamily A.data.scale_pos
          (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2‖ <=
      OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant G *
        (16 / A.data.scale) ^ G.scaleDegree *
        (1 + norm center) ^ G.growthDegree := by
  have hscale : A.data.scale <= rho :=
    A.data.scale_le.trans (by linarith [hrho])
  have hcenterScale : forall i : Fin k,
      A.data.scale <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))) :=
    fun i => hscale.trans (hcenter i)
  let hxi := osiiStep4MultiGapXiHatCenter_time_lower
    d k center hcenterScale
  let U := Z.uniform.shrink (hsigma := A.data.scale_pos) hscale hxi
  let Q := U.toSelectedCommonSlopeData p.1 p.2
  have hQT : Q.T = Z.uniform.T := rfl
  have hy : p.1 ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho Q.T / 4) := by
    have hpNorm : norm p.1 <= A.data.scale / 4 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hp.1
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [hQT]
    calc
      norm p.1 <= A.data.scale / 4 := hpNorm
      _ = osiiEquation66FirstCarrierScale d k rho Z.uniform.T / 128 := by
        rw [A.scale_eq]
        simp only [osiiEquation66QuantitativeLocalWeylScale]
        ring
      _ <= osiiEquation66FirstCarrierScale d k rho Z.uniform.T / 4 := by
        have hpos := osiiEquation66FirstCarrierScale_pos d k hrho
          (lt_trans zero_lt_one Z.uniform.hT)
        nlinarith
  obtain ⟨Gamma, hGamma, hreal, hGammaBound⟩ :=
    Q.exists_centeredSchwingerExtension_equation66_fixedData_bound_of_carrierScale
      (hcenter := hcenterScale)
      d k OS lgc G A.data.scale_pos A.data.scale_le_sixteen
        hrho hcenter hp hy
  have hT : Q.T = Z.coherent.T := by
    rw [hQT]
    exact Z.slope_eq.symm
  have hrealCoherent : forall x : Fin k -> osiiAxisPairIndex d -> Real,
      Gamma (osiiAxisPairSimultaneousLogRealEmbed x) =
        osiiStep4FixedRadiusCenteredSchwinger d OS k A.data.scale_pos
          (osiiStep4MultiGapXiHatCenter d k center +
            osiiStep4AxisPairGapTranslationFlat d Z.coherent.T x) p.1 p.2
          (osiiStep4MultiGapTranslatedCenter_time_lower
            d k (osiiStep4MultiGapXiHatCenter d k center)
              hxi Z.coherent.T Z.coherent.hT x) := by
    intro x
    simpa only [hT] using hreal x
  have hGammaEq :=
    Z.holomorphicCenteredSchwingerExtension_eq_coherentPairing_atScale
      (lgc := lgc) hcenter A.data.scale_pos hscale hxi p.1 p.2
        Gamma hGamma hrealCoherent
  have hw := A.data.firstCarrierCoverage p.1 hp.1
  have hvalue :
      Gamma (osiiStep4MultiGapTargetLog
          d k Z.uniform.T center p.1) =
        osiiStep4DistributionalPartialConvolutionTransform
          D.imaginarySliceFamily A.data.scale_pos
            (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2 := by
    calc
      Gamma (osiiStep4MultiGapTargetLog
          d k Z.uniform.T center p.1) = Z.coherent.pairing OS lgc
          (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
            d k A.data.scale_pos (osiiStep4MultiGapXiHatCenter d k center)
              p.1 p.2)
          (osiiStep4MultiGapTargetLog d k Z.uniform.T center p.1) :=
        hGammaEq hw
      _ = osiiStep4DistributionalPartialConvolutionTransform
            D.imaginarySliceFamily A.data.scale_pos
              (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2 :=
        (A.data.distributionalPartialConvolutionTransform_eq_coherentPairing
          p hp).symm
  have hpoly :=
    OSIIStep4MultiGapSelectedCommonSlopeData.centeredCompactifiedBound_equation66_le_polynomial_of_carrierScale
      d k OS lgc G A.data.scale_pos A.data.scale_le_sixteen
        hrho Q.hT center p.1 hcenter hy
  calc
    ‖osiiStep4DistributionalPartialConvolutionTransform
        D.imaginarySliceFamily A.data.scale_pos
          (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2‖ =
      norm (Gamma (osiiStep4MultiGapTargetLog
        d k Z.uniform.T center p.1)) := congrArg norm hvalue.symm
    _ = norm (Gamma (osiiStep4MultiGapTargetLog
        d k Q.T center p.1)) := by rw [hQT]
    _ <= osiiStep4MultiGapCenteredCompactifiedBound
        G.constant G.scaleDegree G.growthDegree A.data.scale
        (osiiStep4MultiGapXiHatCenter d k center)
        osiiEquation66UniversalStripParameters.radius
        (osiiStep4MultiGapTargetCenteredInput d k
          (Real.log (osiiNarrowTimeLogScale (d := d) Q.T))
          Q.T center p.1) := hGammaBound
    _ <= OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant G *
        (16 / A.data.scale) ^ G.scaleDegree *
        (1 + norm center) ^ G.growthDegree := hpoly

/-- Quantitative equation (6.7), before eliminating the explicit local scale. -/
theorem OSIIEquation66QuantitativeLocalWeylDensityData.norm_density_center_le_mzPolynomial_mul_supportVolume
    {D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc}
    (A : OSIIEquation66QuantitativeLocalWeylDensityData D)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc) :
    ‖A.data.density (osiiStep4ComplexOfRealImag
        (osiiStep4MultiGapXiHatCenter d k center) 0)‖ <=
      (OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant G *
        (16 / A.data.scale) ^ G.scaleDegree *
        (1 + norm center) ^ G.growthDegree) *
      ((A.data.scale / 2) ^ (k * (d + 1)) *
        (A.data.scale / 4) ^ (k * (d + 1))) := by
  exact A.data.norm_density_center_le_supportVolume_mul_bound
    (OSIIStep4MultiGapSelectedCommonSlopeData.equation66MZPolynomialConstant G *
      (16 / A.data.scale) ^ G.scaleDegree *
      (1 + norm center) ^ G.growthDegree)
    (fun p hp => A.distributionalTransform_le_mzPolynomial G p hp)

end OSIIStep4FullSchwartzAngularContinuationData
end OSReconstruction
