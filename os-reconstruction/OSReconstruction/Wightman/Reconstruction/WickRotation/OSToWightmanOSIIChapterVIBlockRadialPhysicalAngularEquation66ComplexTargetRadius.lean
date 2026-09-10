import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66SynchronizedQuantitativeSlope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66LocalWeylDensity

/-!
# Explicit complex equation-(6.6) target radius

The quantitative first-carrier scale controls genuinely complex displacement,
not only the physical imaginary slice.  On one explicit ball all coefficients
remain in the universal narrow sector, the complete logarithmic target stays
in the first multi-gap carrier, and every retained continuation is therefore
defined on that ball.
-/

noncomputable section

open Complex Metric Set Topology
open scoped BigOperators Classical

namespace OSReconstruction

set_option maxHeartbeats 1200000

/-- The quantitative first-carrier scale controls genuinely complex, not only
purely imaginary, physical displacements. -/
theorem osiiStep4MultiGapComplexTargetCoeff_mem_equation66_narrowSector
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (z : Fin (k * (d + 1)) -> Complex)
    (hz : z ∈ Metric.ball 0
      (osiiEquation66FirstCarrierScale d k rho T / 4)) :
    forall i : Fin k,
      osiiStep4MultiGapComplexTargetCoeff d k T center z i ∈
        osiiAxisPairNarrowSector
          (d := d) (osiiEquation66AngleAperture d k) := by
  let eta := osiiEquation66AngleAperture d k
  let sigma := osiiEquation66FirstCarrierScale d k rho T
  have heta0 : 0 < eta := osiiEquation66AngleAperture_pos d k
  have heta1 : eta < 1 := osiiEquation66AngleAperture_lt_one d k
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hd : 0 < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hdT : 0 < (d : Real) * T := mul_pos hd hT0
  have hdT_one : 1 < (d : Real) * T := by
    have hd_one : 1 <= (d : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    nlinarith
  have hsigma : sigma <= eta * rho / (8 * (d : Real) * T) :=
    osiiEquation66FirstCarrierScale_le_angle d k rho T
  have hznorm : norm z < sigma / 4 := by
    simpa [Metric.mem_ball, dist_zero_right, sigma] using hz
  have hcoord (i : Fin k) (mu : Fin (d + 1)) :
      norm (z (finProdFinEquiv (i, mu))) <
        eta * center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
          (8 * (d : Real) * T) := by
    have hcomponent : norm (z (finProdFinEquiv (i, mu))) <= norm z :=
      norm_le_pi_norm z (finProdFinEquiv (i, mu))
    have hsmall : norm (z (finProdFinEquiv (i, mu))) <
        eta * rho / (32 * (d : Real) * T) := by
      calc
        norm (z (finProdFinEquiv (i, mu))) <= norm z := hcomponent
        _ < sigma / 4 := hznorm
        _ <= (eta * rho / (8 * (d : Real) * T)) / 4 :=
          div_le_div_of_nonneg_right hsigma (by norm_num)
        _ = eta * rho / (32 * (d : Real) * T) := by ring
    have hcenterPos : 0 <
        center (finProdFinEquiv (i, (0 : Fin (d + 1)))) :=
      hrho.trans_le (hcenter i)
    have hlarge : eta * rho / (32 * (d : Real) * T) <
        eta * center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
          (8 * (d : Real) * T) := by
      field_simp [hd.ne', hT0.ne']
      nlinarith [hcenter i, mul_pos heta0 hcenterPos]
    exact hsmall.trans hlarge
  intro i
  let xi := osiiStep4MultiGapRealBlock (d + 1) k center i
  let zeta := osiiStep4MultiGapComplexBlock (d + 1) k z i
  have hxi : 0 < xi 0 := by
    simpa [xi, osiiStep4MultiGapRealBlock] using
      hrho.trans_le (hcenter i)
  apply osiiAxisPairCoeff_mem_narrowSector_of_small_perturbation
    T hT0 xi hxi zeta eta heta0
  · have hc := hcoord i 0
    have hre : abs ((zeta 0).re) <= norm (zeta 0) :=
      Complex.abs_re_le_norm _
    have hsmall : abs ((zeta 0).re) < xi 0 / 8 := by
      have hetaDiv : eta * xi 0 / (8 * (d : Real) * T) <= xi 0 / 8 := by
        have hxi0 : 0 <= xi 0 := hxi.le
        field_simp [hd.ne', hT0.ne']
        nlinarith [mul_nonneg heta0.le hxi0]
      have hnorm : norm (zeta 0) <
          eta * xi 0 / (8 * (d : Real) * T) := by
        simpa [zeta, osiiStep4MultiGapComplexBlock, xi,
          osiiStep4MultiGapRealBlock] using hc
      exact hre.trans_lt (hnorm.trans_le hetaDiv)
    rw [Complex.div_ofReal_re]
    rw [abs_div, abs_of_pos (show 0 < 2 * (d : Real) * T by positivity)]
    dsimp [zeta, xi]
    field_simp [hd.ne', hT0.ne'] at hsmall ⊢
    nlinarith
  · intro j
    have hc := hcoord i (Fin.succ j)
    have hre : abs ((zeta (Fin.succ j)).re) <=
        norm (zeta (Fin.succ j)) := Complex.abs_re_le_norm _
    have hnorm : norm (zeta (Fin.succ j)) <
        eta * xi 0 / (8 * (d : Real) * T) := by
      simpa [zeta, osiiStep4MultiGapComplexBlock, xi,
        osiiStep4MultiGapRealBlock] using hc
    have htarget : eta * xi 0 / (8 * (d : Real) * T) <
        xi 0 / (8 * (d : Real) * T) := by
      apply (div_lt_div_iff_of_pos_right (by positivity)).2
      nlinarith
    have hsmall := hre.trans_lt (hnorm.trans htarget)
    dsimp [zeta, xi]
    field_simp [hd.ne', hT0.ne'] at hsmall ⊢
    nlinarith
  · have hc := hcoord i 0
    have him : abs ((zeta 0).im) <= norm (zeta 0) :=
      Complex.abs_im_le_norm _
    have hnorm : norm (zeta 0) <
        eta * xi 0 / (8 * (d : Real) * T) := by
      simpa [zeta, osiiStep4MultiGapComplexBlock, xi,
        osiiStep4MultiGapRealBlock] using hc
    have hsmall := him.trans_lt hnorm
    rw [Complex.div_ofReal_im]
    rw [abs_div, abs_of_pos (show 0 < 2 * (d : Real) * T by positivity)]
    dsimp [zeta, xi]
    field_simp [hd.ne', hT0.ne'] at hsmall ⊢
    have hmono :
        abs ((osiiStep4MultiGapComplexBlock (d + 1) k z i 0).im) * 8 <=
          abs ((osiiStep4MultiGapComplexBlock (d + 1) k z i 0).im) * 8 *
            ((d : Real) * T) := by
      have hnonneg : 0 <=
          abs ((osiiStep4MultiGapComplexBlock (d + 1) k z i 0).im) * 8 :=
        mul_nonneg (abs_nonneg _) (by norm_num)
      calc
        abs ((osiiStep4MultiGapComplexBlock (d + 1) k z i 0).im) * 8 =
            abs ((osiiStep4MultiGapComplexBlock (d + 1) k z i 0).im) * 8 * 1 := by
          ring
        _ <= abs ((osiiStep4MultiGapComplexBlock (d + 1) k z i 0).im) * 8 *
            ((d : Real) * T) :=
          mul_le_mul_of_nonneg_left hdT_one.le hnonneg
    nlinarith [mul_pos heta0 hxi]
  · intro j
    have hc := hcoord i (Fin.succ j)
    have him : abs ((zeta (Fin.succ j)).im) <=
        norm (zeta (Fin.succ j)) := Complex.abs_im_le_norm _
    have hnorm : norm (zeta (Fin.succ j)) <
        eta * xi 0 / (8 * (d : Real) * T) := by
      simpa [zeta, osiiStep4MultiGapComplexBlock, xi,
        osiiStep4MultiGapRealBlock] using hc
    have hsmall := him.trans_lt hnorm
    dsimp [zeta, xi]
    field_simp [hd.ne', hT0.ne'] at hsmall ⊢
    nlinarith [mul_pos heta0 hxi]

/-- The genuinely complex equation-(6.6) target has the same fixed global
argument budget as the physical imaginary slice. -/
theorem osiiStep4MultiGapComplexTarget_argumentBudget_lt_pi_div_eight
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (z : Fin (k * (d + 1)) -> Complex)
    (hz : z ∈ Metric.ball 0
      (osiiEquation66FirstCarrierScale d k rho T / 4)) :
    (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
      |Complex.arg
        (osiiStep4MultiGapComplexTargetCoeff d k T center z i a)|) <
      Real.pi / 8 := by
  let eta := osiiEquation66AngleAperture d k
  have hsector :=
    osiiStep4MultiGapComplexTargetCoeff_mem_equation66_narrowSector
      d k hrho hT center hcenter z hz
  have harg : forall i : Fin k, forall a : osiiAxisPairIndex d,
      |Complex.arg
        (osiiStep4MultiGapComplexTargetCoeff d k T center z i a)| <
        Real.arctan eta := by
    intro i a
    have hs := hsector i a
    have hratio :
        |(osiiStep4MultiGapComplexTargetCoeff d k T center z i a).im /
          (osiiStep4MultiGapComplexTargetCoeff d k T center z i a).re| < eta := by
      rw [abs_div, abs_of_pos hs.1]
      exact (div_lt_iff₀ hs.1).2 hs.2
    rw [osiiLemma51_abs_arg_eq_arctan_abs_im_div_re hs.1]
    exact Real.arctan_strictMono hratio
  have hk : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  have ha :
      (Finset.univ : Finset (osiiAxisPairIndex d)).Nonempty :=
    ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true),
      Finset.mem_univ _⟩
  calc
    (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |Complex.arg
          (osiiStep4MultiGapComplexTargetCoeff d k T center z i a)|) <
      ∑ _i : Fin k, ∑ _a : osiiAxisPairIndex d,
        Real.arctan eta :=
      Finset.sum_lt_sum_of_nonempty hk fun i _ =>
        Finset.sum_lt_sum_of_nonempty ha fun a _ => harg i a
    _ = (k : Real) * (Fintype.card (osiiAxisPairIndex d) : Real) *
        Real.arctan eta := by
      simp
      ring
    _ < Real.pi / 8 := osiiEquation66AngleAperture_budget d k

/-- Every displacement in the explicit complex equation-(6.6) ball maps into
the canonical first multi-gap logarithmic carrier. -/
theorem osiiStep4MultiGapComplexTargetLog_mem_equation66_logDomain
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (z : Fin (k * (d + 1)) -> Complex)
    (hz : z ∈ Metric.ball 0
      (osiiEquation66FirstCarrierScale d k rho T / 4)) :
    osiiStep4MultiGapComplexTargetLog d k T center z ∈
      osiiAxisPairMultiGapLogDomain d k := by
  have hbudget :=
    osiiStep4MultiGapComplexTarget_argumentBudget_lt_pi_div_eight
      d k hrho hT center hcenter z hz
  simp only [osiiAxisPairMultiGapLogDomain, Set.mem_setOf_eq,
    osiiStep4MultiGapComplexTargetLog, Complex.log_im]
  exact hbudget.trans (by nlinarith [Real.pi_pos])

namespace OSIIStep4FullSchwartzAngularContinuationData

/-- The explicit first-carrier scale supplies a genuinely complex ball inside
the natural equation-(6.6) target domain of every retained continuation. -/
theorem equation66ComplexBall_subset_complexTargetDomain
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc) :
    Metric.ball 0
        (osiiEquation66FirstCarrierScale d k rho Z.uniform.T / 4) ⊆
      D.complexTargetDomain := by
  intro z hz
  have hsector :=
    osiiStep4MultiGapComplexTargetCoeff_mem_equation66_narrowSector
      d k hrho Z.uniform.hT center hcenter z hz
  constructor
  · exact fun i a => (hsector i a).1
  · exact D.firstCarrier_subset
      (osiiStep4MultiGapComplexTargetLog_mem_equation66_logDomain
        d k hrho Z.uniform.hT center hcenter z hz)

end OSIIStep4FullSchwartzAngularContinuationData
end OSReconstruction
