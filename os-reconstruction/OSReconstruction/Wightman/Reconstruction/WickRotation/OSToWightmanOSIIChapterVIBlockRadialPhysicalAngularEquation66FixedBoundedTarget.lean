/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66CenteredTargetBound












noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIStep4MultiGapSelectedCommonSlopeData

set_option maxHeartbeats 1200000 in
/-- The compactified MZ extension with its globally selected growth data
kept explicit. -/
theorem exists_centeredCompactifiedMZExtension_fixedData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (hp : (y, y') ∈
      osiiStep4PartialConvolutionClosedImaginaryBox (d + 1) k rho)
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (hsigma : sigma < Real.pi / 2)
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    exists Gamma :
        (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex,
      DifferentiableOn Complex Gamma
          (osiiAxisPairMultiGapLogDomain d k) ∧
      (forall x : Fin k -> osiiAxisPairIndex d -> Real,
        Gamma (osiiAxisPairSimultaneousLogRealEmbed x) =
          (D.centeredCompactifiedFlatCross OS lgc P hsigma u).realEdge x) ∧
      (forall (x : Fin k -> osiiAxisPairIndex d -> Real)
        (q : osiiAxisPairMultiGapIndex d k) (w : Complex),
        |w.im| < Real.pi / 2 ->
          Gamma (osiiAxisPairMultiGapUpdate
              (osiiAxisPairSimultaneousLogRealEmbed x) q w) =
            (D.centeredCompactifiedFlatCross OS lgc P hsigma u).branch x q
              (osiiAxisPairMultiGapUpdate
                (osiiAxisPairSimultaneousLogRealEmbed x) q w)) ∧
      forall z : Fin k -> osiiAxisPairIndex d -> Complex,
        z ∈ osiiAxisPairMultiGapLogDomain d k ->
          norm (Gamma z) <=
            osiiStep4MultiGapCenteredCompactifiedBound
              G.constant G.scaleDegree G.growthDegree
                rho center P.radius u := by
  obtain ⟨hB, hrealBound, hchartBound⟩ :=
    D.centeredCompactifiedFlatCross_bounds
      d k OS lgc G hrho hrho_le center y y' hcenter hp P hsigma u
  let Q := D.centeredCompactifiedFlatCross OS lgc P hsigma u
  let B := osiiStep4MultiGapCenteredCompactifiedBound
    G.constant G.scaleDegree G.growthDegree rho center P.radius u
  obtain ⟨Gamma, hGamma, hreal⟩ :=
    Q.exists_holomorphic_realEdge_extension_of_bounds
      B (by simpa only [Q, B] using hrealBound)
      B (by simpa only [B] using hB)
      (by simpa only [Q, B] using hchartBound)
  refine ⟨Gamma, hGamma, ?_, ?_, ?_⟩
  · simpa only [Q] using hreal
  · intro x q w hw
    exact Q.coordinateLine_eq_of_holomorphic_realEdge
      Gamma hGamma hreal x q hw
  · intro z hz
    have hnorm := Q.norm_holomorphic_realEdge_extension_le
      B (by simpa only [Q, B] using hrealBound)
      B (by simpa only [B] using hB)
      (by simpa only [Q, B] using hchartBound)
      Gamma hGamma hreal z hz
    simpa only [B] using hnorm

set_option maxHeartbeats 1200000 in
/-- Original coefficient germ retaining the same globally selected constants. -/
theorem exists_centeredBoundedCoefficientGerm_fixedData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (hp : (y, y') ∈
      osiiStep4PartialConvolutionClosedImaginaryBox (d + 1) k rho)
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (hsigma : sigma < Real.pi / 2)
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    exists Gamma :
        (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex,
      DifferentiableOn Complex Gamma
          (osiiAxisPairMultiGapLogDomain d k) ∧
      DifferentiableOn Complex
        (osiiStep4MultiGapCenteredCoefficientGerm P
          (Real.log (osiiNarrowTimeLogScale (d := d) D.T)) u Gamma)
        (osiiStep4MultiGapCenteredCoefficientGermDomain P
          (Real.log (osiiNarrowTimeLogScale (d := d) D.T)) u) ∧
      (forall x : Fin k -> osiiAxisPairIndex d -> Real,
        osiiStep4MultiGapCenteredCoefficientOffset
            (Real.log (osiiNarrowTimeLogScale (d := d) D.T)) u
            (osiiAxisPairSimultaneousLogRealEmbed x) ∈
              Metric.ball 0 P.radius ->
          osiiStep4MultiGapCenteredCoefficientGerm P
              (Real.log (osiiNarrowTimeLogScale (d := d) D.T)) u Gamma
              (osiiAxisPairSimultaneousLogRealEmbed x) =
            (D.flatCrossData OS lgc).realEdge x) ∧
      forall z : Fin k -> osiiAxisPairIndex d -> Complex,
        z ∈ osiiStep4MultiGapCenteredCoefficientGermDomain P
            (Real.log (osiiNarrowTimeLogScale (d := d) D.T)) u ->
          norm (osiiStep4MultiGapCenteredCoefficientGerm P
              (Real.log (osiiNarrowTimeLogScale (d := d) D.T)) u Gamma z) <=
            osiiStep4MultiGapCenteredCompactifiedBound
              G.constant G.scaleDegree G.growthDegree
                rho center P.radius u := by
  obtain ⟨Gamma, hGamma, hreal, _hchart, hbound⟩ :=
    D.exists_centeredCompactifiedMZExtension_fixedData
      d k OS lgc G hrho hrho_le center y y' hcenter hp P hsigma u
  refine ⟨Gamma, hGamma, ?_, ?_, ?_⟩
  · exact differentiableOn_osiiStep4MultiGapCenteredCoefficientGerm
      P _ u Gamma hGamma
  · intro x hx
    exact
      (D.flatCrossData OS lgc).centeredCoefficientGerm_realEdge
        P hsigma
        (Real.log (osiiNarrowTimeLogScale (d := d) D.T))
        u Gamma hreal x hx
  · intro z hz
    exact norm_osiiStep4MultiGapCenteredCoefficientGerm_le
      P _ u Gamma hbound hz

set_option maxHeartbeats 1200000 in
/-- Bounded radial target chart with both compactification parameters and
global growth data fixed before the physical source. -/
theorem exists_boundedScalarTargetChart_fixedData_of_parameters
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho (osiiStep4MultiGapXiHatCenter d k center) y y'
        (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))
    (hp : (y, y') ∈
      osiiStep4PartialConvolutionClosedImaginaryBox (d + 1) k rho)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (hsigma : sigma < Real.pi / 2)
    (hS :
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |(osiiStep4MultiGapTargetLog d k D.T center y i a).im|) <= S)
    (hbudget :
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |Complex.arg
          (osiiStep4MultiGapTargetCoeff d k D.T center y i a)|) <
        Real.pi / 2) :
    let shift := Real.log (osiiNarrowTimeLogScale (d := d) D.T)
    let u := osiiStep4MultiGapTargetCenteredInput
      d k shift D.T center y
    let B := osiiStep4MultiGapCenteredCompactifiedBound
      G.constant G.scaleDegree G.growthDegree rho
        (osiiStep4MultiGapXiHatCenter d k center) P.radius u
    0 < B ∧
      exists Gamma0 :
          (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex,
        DifferentiableOn Complex Gamma0
            (osiiAxisPairMultiGapLogDomain d k) ∧
        (forall x : Fin k -> osiiAxisPairIndex d -> Real,
          Gamma0 (osiiAxisPairSimultaneousLogRealEmbed x) =
            osiiStep4FixedRadiusCenteredSchwinger d OS k hrho
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
  let shift := Real.log (osiiNarrowTimeLogScale (d := d) D.T)
  let u := osiiStep4MultiGapTargetCenteredInput d k shift D.T center y
  obtain ⟨Gamma, _hGamma, hGerm, hreal, hbound⟩ :=
    D.exists_centeredBoundedCoefficientGerm_fixedData
      d k OS lgc G hrho hrho_le
      (osiiStep4MultiGapXiHatCenter d k center) y y'
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)
      hp P hsigma u
  let B := osiiStep4MultiGapCenteredCompactifiedBound
    G.constant G.scaleDegree G.growthDegree rho
      (osiiStep4MultiGapXiHatCenter d k center) P.radius u
  have hB : 0 < B :=
    osiiStep4MultiGapCenteredCompactifiedBound_pos
      G.constant_nonneg hrho G.scaleDegree G.growthDegree
      _ P.radius u
  let target := osiiStep4MultiGapTargetDisplacementFin
    d k D.T center y
  obtain ⟨_eps, _heps, A, hAreal, Q, hQfun, hQdomain⟩ :=
    exists_centeredBoundedScalarContinuationWithTargetChart
      (D.flatCrossData OS lgc) P shift u Gamma B
      hGerm hreal hbound target
      (by
        intro z hz
        simpa only [target,
          osiiAxisPairMultiGapFinFlattenCLE_symm_apply] using
          (osiiStep4MultiGapTargetDisplacementFin_segment_mem_centeredCoefficientGermDomain
            P shift d k D.T center y u hS z hz))
  obtain ⟨Gamma0, hGamma0, hGamma0realSchwinger⟩ :=
    D.exists_holomorphic_centeredSchwinger_extension OS lgc
  have hGamma0real : forall x :
      Fin k -> osiiAxisPairIndex d -> Real,
      Gamma0 (osiiAxisPairSimultaneousLogRealEmbed x) =
        (D.flatCrossData OS lgc).realEdge x := by
    intro x
    simpa [flatCrossData,
      OSIIAxisPairMultiGapSemigroupPacketFamily.toFlatCrossData,
      packetFamily] using hGamma0realSchwinger x
  let translateFin :=
    fun z : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex =>
      osiiStep4MultiGapCenteredCoefficientTranslate shift u
        ((osiiAxisPairMultiGapFinFlattenCLE
          (d := d) (k := k)).symm z)
  let W : Set
      (Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex) :=
    translateFin ⁻¹' osiiAxisPairMultiGapLogDomain d k
  have htranslate : Differentiable Complex translateFin :=
    differentiable_osiiStep4MultiGapCenteredCoefficientTranslate_fin
      shift u
  have hWopen : IsOpen W :=
    isOpen_osiiAxisPairMultiGapLogDomain.preimage htranslate.continuous
  have hlogbudget :
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |(osiiStep4MultiGapTargetLog d k D.T center y i a).im|) <
          Real.pi / 2 := by
    simpa only [osiiStep4MultiGapTargetLog, Complex.log_im] using hbudget
  have hsegmentW : segment Real 0 target ⊆ W := by
    intro z hz
    simpa only [W, translateFin, Set.mem_preimage, target,
      osiiAxisPairMultiGapFinFlattenCLE_symm_apply] using
      (osiiStep4MultiGapTargetDisplacementFin_segment_mem_centeredLogDomain
        shift d k D.T center y u hlogbudget z hz)
  let V := Q.domain ∩ W
  have hVopen : IsOpen V := Q.domain_open.inter hWopen
  have hsegmentV : segment Real 0 target ⊆ V := by
    intro z hz
    exact ⟨Q.domain_convex.segment_subset
      Q.zero_mem_domain Q.target_mem_domain hz, hsegmentW hz⟩
  obtain ⟨U, hUopen, hUzero, hUsub, hUeq⟩ :=
    Q.exists_open_eq_predecessor
  let U' := U ∩ W
  have hU'open : IsOpen U' := hUopen.inter hWopen
  have hzeroW :
      (0 : Fin (Fintype.card
        (osiiAxisPairMultiGapIndex d k)) -> Complex) ∈ W :=
    hsegmentW (left_mem_segment Real 0 target)
  have hU'zero :
      (0 : Fin (Fintype.card
        (osiiAxisPairMultiGapIndex d k)) -> Complex) ∈ U' :=
    ⟨hUzero, hzeroW⟩
  obtain ⟨Q', hQ'fun, hQ'domain⟩ :=
    OSIIChapterV.BoundedScalarTargetChartData.exists_ofBoundedHolomorphicExtension
      (A := A) (target := target)
      V hVopen hsegmentV Q.toFun
      (Q.toFun_differentiableOn.mono Set.inter_subset_left)
      (fun z hz => Q.norm_toFun_le hz.1)
      U' hU'open hU'zero
      (by
        intro z hz
        exact ⟨⟨(hUsub hz.1).1, hz.2⟩, (hUsub hz.1).2⟩)
      (by
        intro z hz
        exact hUeq hz.1)
  have hQ'connected : IsConnected Q'.domain :=
    Q'.domain_convex.isConnected ⟨0, Q'.zero_mem_domain⟩
  have hcommon := centeredCoefficientGerm_eq_originalExtension_on_connected
    (D.flatCrossData OS lgc) P shift u Gamma Gamma0
    hGerm hreal hGamma0 hGamma0real Q'.domain
    Q'.domain_open hQ'connected Q'.zero_mem_domain
    (by
      intro z hz
      exact hQdomain z (hQ'domain hz).1)
    (by
      intro z hz
      exact (hQ'domain hz).2)
  have htargetCommon := hcommon target Q'.target_mem_domain
  have htranslateTarget :
      translateFin target =
        osiiStep4MultiGapTargetLog d k D.T center y := by
    simpa only [translateFin, target,
      osiiAxisPairMultiGapFinFlattenCLE_symm_apply] using
      (osiiStep4MultiGapCenteredTranslate_targetDisplacement
        d k shift D.T center y)
  refine ⟨hB, Gamma0, hGamma0, hGamma0realSchwinger,
    A, hAreal, Q', ?_⟩
  calc
    Q'.toFun target = Q.toFun target := by
      rw [hQ'fun]
    _ = osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
          (translateFin target) := by
      rw [hQfun]
    _ = Gamma0 (translateFin target) := htargetCommon
    _ = Gamma0 (osiiStep4MultiGapTargetLog d k D.T center y) := by
      rw [htranslateTarget]

theorem norm_osiiStep4MultiGapXiHatCenter_le
    (d k : Nat) [NeZero d]
    (center : Fin (k * (d + 1)) -> Real) :
    norm (osiiStep4MultiGapXiHatCenter d k center) <= norm center := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg center)).2
  intro p
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective p
  rw [osiiStep4MultiGapXiHatCenter_finProdFinEquiv]
  refine Fin.cases ?_ (fun j => ?_) mu
  · change norm (center (finProdFinEquiv (i, (0 : Fin (d + 1)))) / 2) <=
      norm center
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      |center (finProdFinEquiv (i, (0 : Fin (d + 1))))| / 2 <=
          |center (finProdFinEquiv (i, (0 : Fin (d + 1))))| := by
        nlinarith [abs_nonneg
          (center (finProdFinEquiv (i, (0 : Fin (d + 1)))))]
      _ <= norm center := by
        simpa [Real.norm_eq_abs] using
          norm_le_pi_norm center
            (finProdFinEquiv (i, (0 : Fin (d + 1))))
  · change norm (center (finProdFinEquiv (i, Fin.succ j))) <= norm center
    exact norm_le_pi_norm center (finProdFinEquiv (i, Fin.succ j))

/-- Global coefficient multiplying the standard inverse-scale and center
polynomial after the equation-(6.6) target losses are absorbed. -/
def equation66MZPolynomialConstant
    {d k : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc) : Real :=
  1 + G.constant *
    osiiEquation66CenteredTargetGrowthFactor d k ^ G.growthDegree

theorem equation66MZPolynomialConstant_pos
    {d k : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc) :
    0 < equation66MZPolynomialConstant G := by
  unfold equation66MZPolynomialConstant
  have hpow : 0 <=
      osiiEquation66CenteredTargetGrowthFactor d k ^ G.growthDegree :=
    pow_nonneg (osiiEquation66CenteredTargetGrowthFactor_pos d k).le _
  nlinarith [G.constant_nonneg]

end OSIIStep4MultiGapSelectedCommonSlopeData
end OSReconstruction
