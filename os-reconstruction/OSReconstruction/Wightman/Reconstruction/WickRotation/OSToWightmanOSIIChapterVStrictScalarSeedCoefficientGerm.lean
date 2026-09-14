/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.StripCompactificationLocalInverse
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientMZTarget













noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Coordinatewise local inverse, embedded into the false half of the doubled
MZ variables. -/
def osiiStrictCoefficientLocalInverseLift
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (r : Fin n -> Complex) :
    osiiAxisPairIndex n -> Complex :=
  fun a =>
    if a.2 then 0
    else SCV.stripCompactificationLocalInverse P (r a.1)

theorem differentiableOn_osiiStrictCoefficientLocalInverseLift
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho) :
    DifferentiableOn Complex
      (osiiStrictCoefficientLocalInverseLift (n := n) P)
      (Metric.ball (0 : Fin n -> Complex) P.radius) := by
  rw [differentiableOn_pi]
  intro a r hr
  rcases a with ⟨i, b⟩
  cases b with
  | false =>
      simp only [osiiStrictCoefficientLocalInverseLift, Bool.false_eq_true,
        if_false]
      have hri :
          r i ∈ Metric.ball (0 : Complex) P.radius := by
        rw [Metric.mem_ball, dist_zero_right]
        rw [Metric.mem_ball, dist_zero_right,
          pi_norm_lt_iff P.radius_pos] at hr
        exact hr i
      have hinv :=
        SCV.differentiableOn_stripCompactificationLocalInverse
          P _ hri
      have happly :
          DifferentiableWithinAt Complex
            (fun q : Fin n -> Complex => q i)
            (Metric.ball (0 : Fin n -> Complex) P.radius) r :=
        (differentiable_apply i r).differentiableWithinAt
      simpa only [Function.comp_apply] using
        DifferentiableWithinAt.comp r hinv happly
          (fun q hq => by
            rw [Metric.mem_ball, dist_zero_right]
            rw [Metric.mem_ball, dist_zero_right,
              pi_norm_lt_iff P.radius_pos] at hq
            exact hq i)
  | true =>
      simpa [osiiStrictCoefficientLocalInverseLift] using
        (differentiableWithinAt_const
          (c := (0 : Complex)) :
            DifferentiableWithinAt Complex
              (fun _ : Fin n -> Complex => (0 : Complex))
              (Metric.ball (0 : Fin n -> Complex) P.radius) r)

/-- Open coefficient-space carrier on which the doubled MZ continuation can
be pulled back through the local inverse. -/
def osiiStrictCoefficientGermDomain
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho) :
    Set (Fin n -> Complex) :=
  Metric.ball (0 : Fin n -> Complex) P.radius ∩
    osiiStrictCoefficientLocalInverseLift P ⁻¹'
      osiiAxisPairLogDomain (d := n)

theorem isOpen_osiiStrictCoefficientGermDomain
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho) :
    IsOpen (osiiStrictCoefficientGermDomain (n := n) P) := by
  rw [isOpen_iff_mem_nhds]
  intro r hr
  change
    r ∈ Metric.ball (0 : Fin n -> Complex) P.radius ∧
      osiiStrictCoefficientLocalInverseLift P r ∈
        osiiAxisPairLogDomain (d := n) at hr
  have hlift :
      DifferentiableAt Complex
        (osiiStrictCoefficientLocalInverseLift P) r :=
    (differentiableOn_osiiStrictCoefficientLocalInverseLift P r hr.1)
      |>.differentiableAt
        (Metric.isOpen_ball.mem_nhds hr.1)
  have hball :
      Metric.ball (0 : Fin n -> Complex) P.radius ∈ nhds r :=
    Metric.isOpen_ball.mem_nhds hr.1
  have hpre :
      osiiStrictCoefficientLocalInverseLift P ⁻¹'
          osiiAxisPairLogDomain (d := n) ∈ nhds r :=
    hlift.continuousAt.preimage_mem_nhds
      (isOpen_osiiAxisPairLogDomain.mem_nhds hr.2)
  simpa [osiiStrictCoefficientGermDomain] using
    Filter.inter_mem hball hpre

theorem osiiStrictCoefficientLocalInverseLift_target
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (w : Fin n -> Real) :
    osiiStrictCoefficientLocalInverseLift P
        (osiiStrictScalarSeedCoefficientTarget w) =
      osiiStrictCoefficientCompactifiedMZTarget P w := by
  funext a
  rcases a with ⟨i, b⟩
  cases b <;>
    simp [osiiStrictCoefficientLocalInverseLift,
      osiiStrictScalarSeedCoefficientTarget,
      osiiStrictCoefficientCompactifiedMZTarget,
      SCV.stripCompactificationLocalInverse_pureImaginary]

theorem osiiStrictScalarSeedCoefficientTarget_mem_germDomain
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S) :
    osiiStrictScalarSeedCoefficientTarget w ∈
      osiiStrictCoefficientGermDomain P := by
  constructor
  · rw [Metric.mem_ball, dist_zero_right,
      pi_norm_lt_iff P.radius_pos]
    intro i
    have hwi_sum :
        w i <= ∑ j, w j :=
      Finset.single_le_sum
        (fun j _ => hw j) (Finset.mem_univ i)
    have hwi_radius :
        w i < P.radius :=
      hwi_sum.trans_lt
        (hsum.trans_lt P.targetBudget_lt_radius)
    simpa [osiiStrictScalarSeedCoefficientTarget,
      abs_of_nonneg (hw i)] using hwi_radius
  · change
      osiiStrictCoefficientLocalInverseLift P
          (osiiStrictScalarSeedCoefficientTarget w) ∈
        osiiAxisPairLogDomain
    rw [osiiStrictCoefficientLocalInverseLift_target]
    exact
      osiiStrictCoefficientCompactifiedMZTarget_mem_logDomain
        P w hw hsum

namespace StrictScalarSeedCoefficientMZBoundData

variable
  {d : Nat} [NeZero d]
  {n k : Nat} [NeZero n]
  {A : OSIITimeContinuationStage d k}
  {S rho : Real}
  {P : SCV.StripCompactificationParameters S rho}
  {seed : Fin n -> Fin k -> Real}

/-- The selected doubled-coordinate MZ continuation pulled back to its
coefficient-space germ. -/
def coefficientGerm
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (r : Fin n -> Complex) :
    Complex :=
  B.extension chi
    (osiiStrictCoefficientLocalInverseLift P r)

theorem coefficientGerm_differentiableOn
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    DifferentiableOn Complex
      (B.coefficientGerm chi)
      (osiiStrictCoefficientGermDomain P) := by
  intro r hr
  change
    r ∈ Metric.ball (0 : Fin n -> Complex) P.radius ∧
      osiiStrictCoefficientLocalInverseLift P r ∈
        osiiAxisPairLogDomain (d := n) at hr
  have hGamma :=
    B.extension_differentiableOn chi
      (osiiStrictCoefficientLocalInverseLift P r) hr.2
  have hlift :=
    differentiableOn_osiiStrictCoefficientLocalInverseLift
      P r hr.1
  change
    DifferentiableWithinAt Complex
      (fun q =>
        B.extension chi
          (osiiStrictCoefficientLocalInverseLift P q))
      (osiiStrictCoefficientGermDomain P) r
  simpa only [Function.comp_apply] using
    DifferentiableWithinAt.comp r hGamma
      (hlift.mono Set.inter_subset_left)
      (fun q hq => hq.2)

omit [NeZero n] in
theorem osiiStrictCoefficientLocalInverseLift_real
    (x : Fin n -> Real)
    (hx :
      (fun i => (x i : Complex)) ∈
        Metric.ball (0 : Fin n -> Complex) P.radius) :
    osiiStrictCoefficientLocalInverseLift P
        (fun i => (x i : Complex)) =
      osiiAxisPairLogRealEmbed
        (fun a =>
          if a.2 then 0
          else
            (SCV.stripCompactificationLocalInverse
              P (x a.1 : Complex)).re) := by
  funext a
  rcases a with ⟨i, b⟩
  cases b with
  | false =>
      have hxi : |x i| < P.radius := by
        rw [Metric.mem_ball, dist_zero_right,
          pi_norm_lt_iff P.radius_pos] at hx
        simpa [Real.norm_eq_abs] using hx i
      simp only [osiiStrictCoefficientLocalInverseLift,
        Bool.false_eq_true, if_false,
        osiiAxisPairLogRealEmbed]
      rw [SCV.stripCompactificationLocalInverse_ofReal P hxi]
      rfl
  | true =>
      simp [osiiStrictCoefficientLocalInverseLift,
        osiiAxisPairLogRealEmbed]

/-- On the bounded real coefficient slice, the pulled-back germ is exactly
the original predecessor-stage coefficient pairing. -/
theorem coefficientGerm_real
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (x : Fin n -> Real)
    (hx :
      (fun i => (x i : Complex)) ∈
        osiiStrictCoefficientGermDomain P) :
    B.coefficientGerm chi (fun i => (x i : Complex)) =
      osiiStrictScalarSeedCoefficientPairing
        A seed chi
        (fun i => (x i : Complex)) := by
  let q : osiiAxisPairIndex n -> Real :=
    fun a =>
      if a.2 then 0
      else
        (SCV.stripCompactificationLocalInverse
          P (x a.1 : Complex)).re
  have hlift :
      osiiStrictCoefficientLocalInverseLift P
          (fun i => (x i : Complex)) =
        osiiAxisPairLogRealEmbed q :=
    osiiStrictCoefficientLocalInverseLift_real
      (P := P) x hx.1
  rw [coefficientGerm, hlift, B.extension_realEdge]
  apply congrArg
    (osiiStrictScalarSeedCoefficientPairing
      A seed chi)
  funext i
  have hxi_norm :
      ‖(x i : Complex)‖ < P.radius := by
    have hxball :
        (fun j => (x j : Complex)) ∈
          Metric.ball (0 : Fin n -> Complex) P.radius :=
      hx.1
    rw [Metric.mem_ball, dist_zero_right,
      pi_norm_lt_iff P.radius_pos] at hxball
    exact hxball i
  have hq :
      (q (i, false) : Complex) =
        SCV.stripCompactificationLocalInverse
          P (x i : Complex) := by
    dsimp [q]
    have hxi : |x i| < P.radius := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hxi_norm
    rw [SCV.stripCompactificationLocalInverse_ofReal P hxi]
    rfl
  rw [hq]
  exact
    SCV.stripCompactification_localInverse P hxi_norm

end StrictScalarSeedCoefficientMZBoundData
end OSIIChapterV
end OSReconstruction
