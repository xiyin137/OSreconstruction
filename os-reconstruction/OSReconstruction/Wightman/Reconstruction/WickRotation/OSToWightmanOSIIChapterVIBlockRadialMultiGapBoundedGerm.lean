/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.StripCompactificationLocalInverse
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedMZ















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

/-- Displacement from the real center used by the centered strip
compactification. -/
def osiiStep4MultiGapCenteredCoefficientOffset
    {d k : Nat}
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (z : Fin k -> osiiAxisPairIndex d -> Complex) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i a => z i a - (u i a - shift : Complex)

/-- Coordinatewise local inverse of the centered strip compactification. -/
def osiiStep4MultiGapCenteredCoefficientLift
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (z : Fin k -> osiiAxisPairIndex d -> Complex) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i a =>
    SCV.stripCompactificationLocalInverse P
      (osiiStep4MultiGapCenteredCoefficientOffset shift u z i a)

/-- The original-coordinate germ carrier selected by the centered
compactification.  Every coordinate displacement lies in the local inverse
disc, and the lifted tuple lies in the bounded MZ carrier. -/
def osiiStep4MultiGapCenteredCoefficientGermDomain
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    Set (Fin k -> osiiAxisPairIndex d -> Complex) :=
  osiiStep4MultiGapCenteredCoefficientOffset shift u ⁻¹'
      Metric.ball 0 P.radius ∩
    osiiStep4MultiGapCenteredCoefficientLift P shift u ⁻¹'
      osiiAxisPairMultiGapLogDomain d k

theorem continuous_osiiStep4MultiGapCenteredCoefficientOffset
    {d k : Nat}
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    Continuous
      (osiiStep4MultiGapCenteredCoefficientOffset shift u) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro a
  exact
    ((continuous_apply a).comp (continuous_apply i)).sub
      continuous_const

/-- Membership in the centered coefficient ball controls every nested
coordinate separately. -/
theorem osiiStep4MultiGapCenteredCoefficientOffset_coord_norm_lt
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    {z : Fin k -> osiiAxisPairIndex d -> Complex}
    (hz : osiiStep4MultiGapCenteredCoefficientOffset shift u z ∈
      Metric.ball 0 P.radius) :
    forall i a,
      ‖osiiStep4MultiGapCenteredCoefficientOffset shift u z i a‖ <
        P.radius := by
  rw [Metric.mem_ball, dist_zero_right,
    pi_norm_lt_iff P.radius_pos] at hz
  intro i a
  have hi := hz i
  rw [pi_norm_lt_iff P.radius_pos] at hi
  exact hi a

/-- The coordinatewise centered local-inverse lift is holomorphic wherever
all coefficient displacements lie in the inverse disc. -/
theorem differentiableOn_osiiStep4MultiGapCenteredCoefficientLift
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    DifferentiableOn Complex
      (osiiStep4MultiGapCenteredCoefficientLift P shift u)
      (osiiStep4MultiGapCenteredCoefficientOffset shift u ⁻¹'
        Metric.ball 0 P.radius) := by
  rw [differentiableOn_pi]
  intro i
  rw [differentiableOn_pi]
  intro a z hz
  have hcoord :
      osiiStep4MultiGapCenteredCoefficientOffset shift u z i a ∈
        Metric.ball (0 : Complex) P.radius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact
      osiiStep4MultiGapCenteredCoefficientOffset_coord_norm_lt
        P shift u hz i a
  have hinverse :=
    SCV.differentiableOn_stripCompactificationLocalInverse
      P _ hcoord
  have hoffset :
      DifferentiableWithinAt Complex
        (fun q : Fin k -> osiiAxisPairIndex d -> Complex =>
          osiiStep4MultiGapCenteredCoefficientOffset shift u q i a)
        (osiiStep4MultiGapCenteredCoefficientOffset shift u ⁻¹'
          Metric.ball 0 P.radius) z := by
    change DifferentiableWithinAt Complex
      (fun q : Fin k -> osiiAxisPairIndex d -> Complex =>
        q i a - (u i a - shift : Complex))
      (osiiStep4MultiGapCenteredCoefficientOffset shift u ⁻¹'
        Metric.ball 0 P.radius) z
    fun_prop
  change
    DifferentiableWithinAt Complex
      (fun q : Fin k -> osiiAxisPairIndex d -> Complex =>
        SCV.stripCompactificationLocalInverse P
          (osiiStep4MultiGapCenteredCoefficientOffset shift u q i a))
      (osiiStep4MultiGapCenteredCoefficientOffset shift u ⁻¹'
        Metric.ball 0 P.radius) z
  exact
    DifferentiableWithinAt.comp z hinverse hoffset
      (fun q hq => by
        rw [Metric.mem_ball, dist_zero_right]
        exact
          osiiStep4MultiGapCenteredCoefficientOffset_coord_norm_lt
            P shift u hq i a)

theorem isOpen_osiiStep4MultiGapCenteredCoefficientGermDomain
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat} [NeZero d]
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    IsOpen
      (osiiStep4MultiGapCenteredCoefficientGermDomain P shift u) := by
  let V : Set (Fin k -> osiiAxisPairIndex d -> Complex) :=
    osiiStep4MultiGapCenteredCoefficientOffset shift u ⁻¹'
      Metric.ball 0 P.radius
  have hVopen : IsOpen V :=
    Metric.isOpen_ball.preimage
      (continuous_osiiStep4MultiGapCenteredCoefficientOffset shift u)
  rw [isOpen_iff_mem_nhds]
  intro z hz
  change z ∈ V ∧
    osiiStep4MultiGapCenteredCoefficientLift P shift u z ∈
      osiiAxisPairMultiGapLogDomain d k at hz
  have hlift :
      DifferentiableAt Complex
        (osiiStep4MultiGapCenteredCoefficientLift P shift u) z :=
    (differentiableOn_osiiStep4MultiGapCenteredCoefficientLift
      P shift u z hz.1).differentiableAt
        (hVopen.mem_nhds hz.1)
  have hpre :
      osiiStep4MultiGapCenteredCoefficientLift P shift u ⁻¹'
          osiiAxisPairMultiGapLogDomain d k ∈ nhds z :=
    hlift.continuousAt.preimage_mem_nhds
      (isOpen_osiiAxisPairMultiGapLogDomain.mem_nhds hz.2)
  simpa [osiiStep4MultiGapCenteredCoefficientGermDomain, V] using
    Filter.inter_mem (hVopen.mem_nhds hz.1) hpre

/-- Forward centered compactification in the original multi-gap logarithmic
coordinates. -/
def osiiStep4MultiGapCenteredCoefficientForward
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (w : Fin k -> osiiAxisPairIndex d -> Complex) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i a =>
    (u i a - shift : Complex) +
      SCV.stripCompactification P.radius P.slope (w i a)

/-- On the centered coefficient ball, compactification after the local lift
is exactly the identity. -/
theorem osiiStep4MultiGapCenteredCoefficientForward_lift
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    {z : Fin k -> osiiAxisPairIndex d -> Complex}
    (hz : osiiStep4MultiGapCenteredCoefficientOffset shift u z ∈
      Metric.ball 0 P.radius) :
    osiiStep4MultiGapCenteredCoefficientForward P shift u
        (osiiStep4MultiGapCenteredCoefficientLift P shift u z) = z := by
  funext i a
  rw [osiiStep4MultiGapCenteredCoefficientForward,
    osiiStep4MultiGapCenteredCoefficientLift,
    SCV.stripCompactification_localInverse P
      (osiiStep4MultiGapCenteredCoefficientOffset_coord_norm_lt
        P shift u hz i a)]
  simp [osiiStep4MultiGapCenteredCoefficientOffset]

/-- The forward map on real lifted variables is the real centered
compactification used to construct the bounded flat cross. -/
theorem osiiStep4MultiGapCenteredCoefficientForward_realEmbed
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real) :
    osiiStep4MultiGapCenteredCoefficientForward P shift u
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      osiiAxisPairSimultaneousLogRealEmbed
        (osiiStep4MultiGapCompactifiedRealBase P shift u x) := by
  funext i a
  simp [osiiStep4MultiGapCenteredCoefficientForward,
    osiiAxisPairSimultaneousLogRealEmbed,
    osiiAxisPairLogRealEmbed,
    osiiStep4MultiGapCompactifiedRealBase,
    SCV.stripCompactification_ofReal]

/-- Real part of the centered local-inverse lift. -/
def osiiStep4MultiGapCenteredCoefficientRealLift
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real) :
    Fin k -> osiiAxisPairIndex d -> Real :=
  fun i a =>
    (SCV.stripCompactificationLocalInverse P
      (x i a - (u i a - shift) : Complex)).re

/-- The centered lift of a real point in the coefficient ball is again a
simultaneous real logarithmic point. -/
theorem osiiStep4MultiGapCenteredCoefficientLift_realEmbed
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : osiiStep4MultiGapCenteredCoefficientOffset shift u
        (osiiAxisPairSimultaneousLogRealEmbed x) ∈
      Metric.ball 0 P.radius) :
    osiiStep4MultiGapCenteredCoefficientLift P shift u
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      osiiAxisPairSimultaneousLogRealEmbed
        (osiiStep4MultiGapCenteredCoefficientRealLift P shift u x) := by
  funext i a
  apply Complex.ext
  · rfl
  · simp only [osiiStep4MultiGapCenteredCoefficientLift,
      osiiStep4MultiGapCenteredCoefficientRealLift,
      osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed, Complex.ofReal_im]
    have hcoord :=
      osiiStep4MultiGapCenteredCoefficientOffset_coord_norm_lt
        P shift u hx i a
    have hoffset :
        osiiStep4MultiGapCenteredCoefficientOffset shift u
            (osiiAxisPairSimultaneousLogRealEmbed x) i a =
          (x i a - (u i a - shift) : Complex) := by
      simp [osiiStep4MultiGapCenteredCoefficientOffset,
        osiiAxisPairSimultaneousLogRealEmbed,
        osiiAxisPairLogRealEmbed]
    rw [hoffset] at hcoord
    have hcast :
        (x i a : Complex) - (u i a - shift : Complex) =
          (x i a - (u i a - shift) : Real) := by
      push_cast
      ring
    rw [hcast] at hcoord
    have habs : |x i a - (u i a - shift)| < P.radius := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hcoord
    rw [hoffset]
    rw [hcast]
    exact
      SCV.stripCompactificationLocalInverse_ofReal_im
        P (w := x i a - (u i a - shift)) habs

/-- The real local lift is an actual inverse of the centered real
compactification. -/
theorem osiiStep4MultiGapCompactifiedRealBase_realLift
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : osiiStep4MultiGapCenteredCoefficientOffset shift u
        (osiiAxisPairSimultaneousLogRealEmbed x) ∈
      Metric.ball 0 P.radius) :
    osiiStep4MultiGapCompactifiedRealBase P shift u
        (osiiStep4MultiGapCenteredCoefficientRealLift P shift u x) = x := by
  have hforward :=
    osiiStep4MultiGapCenteredCoefficientForward_lift
      P shift u hx
  rw [osiiStep4MultiGapCenteredCoefficientLift_realEmbed
    P shift u x hx,
    osiiStep4MultiGapCenteredCoefficientForward_realEmbed] at hforward
  funext i a
  have hcoord := congrArg Complex.re (congrFun (congrFun hforward i) a)
  simpa [osiiAxisPairSimultaneousLogRealEmbed,
    osiiAxisPairLogRealEmbed] using hcoord

/-- Every real point of the centered coefficient ball belongs to the
original-coordinate germ domain. -/
theorem osiiAxisPairSimultaneousLogRealEmbed_mem_centeredCoefficientGermDomain
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat} [NeZero d]
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : osiiStep4MultiGapCenteredCoefficientOffset shift u
        (osiiAxisPairSimultaneousLogRealEmbed x) ∈
      Metric.ball 0 P.radius) :
    osiiAxisPairSimultaneousLogRealEmbed x ∈
      osiiStep4MultiGapCenteredCoefficientGermDomain P shift u := by
  refine ⟨hx, ?_⟩
  change
    osiiStep4MultiGapCenteredCoefficientLift P shift u
        (osiiAxisPairSimultaneousLogRealEmbed x) ∈
      osiiAxisPairMultiGapLogDomain d k
  rw [osiiStep4MultiGapCenteredCoefficientLift_realEmbed
    P shift u x hx]
  exact
    osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap
      (osiiStep4MultiGapCenteredCoefficientRealLift P shift u x)

/-- Pull a bounded compactified continuation back to the original
multi-gap logarithmic variables. -/
def osiiStep4MultiGapCenteredCoefficientGerm
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (Gamma : (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex)
    (z : Fin k -> osiiAxisPairIndex d -> Complex) : Complex :=
  Gamma (osiiStep4MultiGapCenteredCoefficientLift P shift u z)

theorem differentiableOn_osiiStep4MultiGapCenteredCoefficientGerm
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (Gamma : (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex)
    (hGamma : DifferentiableOn Complex Gamma
      (osiiAxisPairMultiGapLogDomain d k)) :
    DifferentiableOn Complex
      (osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma)
      (osiiStep4MultiGapCenteredCoefficientGermDomain P shift u) := by
  change DifferentiableOn Complex
    (fun z => Gamma
      (osiiStep4MultiGapCenteredCoefficientLift P shift u z))
    (osiiStep4MultiGapCenteredCoefficientGermDomain P shift u)
  exact hGamma.comp
    ((differentiableOn_osiiStep4MultiGapCenteredCoefficientLift
      P shift u).mono (fun _ hz => hz.1))
    (fun _ hz => hz.2)

theorem norm_osiiStep4MultiGapCenteredCoefficientGerm_le
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (Gamma : (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex)
    {B : Real}
    (hGammaBound : forall w,
      w ∈ osiiAxisPairMultiGapLogDomain d k -> ‖Gamma w‖ <= B)
    {z : Fin k -> osiiAxisPairIndex d -> Complex}
    (hz : z ∈
      osiiStep4MultiGapCenteredCoefficientGermDomain P shift u) :
    ‖osiiStep4MultiGapCenteredCoefficientGerm
      P shift u Gamma z‖ <= B :=
  hGammaBound _ hz.2

/-- The pulled-back germ recovers the original, uncompactified flat-cross
real edge throughout its centered real coefficient ball. -/
theorem OSIIAxisPairMultiGapFlatCrossData.centeredCoefficientGerm_realEdge
    {d k : Nat} [NeZero d] [NeZero k]
    (X : OSIIAxisPairMultiGapFlatCrossData d k)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (hsigma : sigma < Real.pi / 2)
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (Gamma : (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex)
    (hreal : forall q : Fin k -> osiiAxisPairIndex d -> Real,
      Gamma (osiiAxisPairSimultaneousLogRealEmbed q) =
        (X.centeredCompactified P hsigma shift u).realEdge q)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : osiiStep4MultiGapCenteredCoefficientOffset shift u
        (osiiAxisPairSimultaneousLogRealEmbed x) ∈
      Metric.ball 0 P.radius) :
    osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      X.realEdge x := by
  rw [osiiStep4MultiGapCenteredCoefficientGerm,
    osiiStep4MultiGapCenteredCoefficientLift_realEmbed
      P shift u x hx,
    hreal]
  change
    X.realEdge
        (osiiStep4MultiGapCompactifiedRealBase P shift u
          (osiiStep4MultiGapCenteredCoefficientRealLift P shift u x)) =
      X.realEdge x
  rw [osiiStep4MultiGapCompactifiedRealBase_realLift
    P shift u x hx]

namespace OSIIStep4MultiGapSelectedCommonSlopeData

end OSIIStep4MultiGapSelectedCommonSlopeData

end OSReconstruction
