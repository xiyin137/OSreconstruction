/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.StripCompactification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMZApproximation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientCompactWindow











noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {n : Nat}

/-- The selected doubled coordinate is compactified into its corresponding
coefficient coordinate; every inactive coefficient is frozen at the real
base. -/
def osiiStrictCoefficientCompactifiedDirectionalInput
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (x : osiiAxisPairIndex n -> Real)
    (a : osiiAxisPairIndex n)
    (r : osiiAxisPairIndex n -> Complex) :
    Fin n -> Complex :=
  fun j =>
    SCV.stripCompactification P.radius P.slope
      (if a = (j, false) then r a else (x (j, false) : Complex))

/-- At a real axis-pair point, the directional compactified input is
independent of the selected doubled coordinate. -/
theorem osiiStrictCoefficientCompactifiedDirectionalInput_real
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (x : osiiAxisPairIndex n -> Real)
    (a : osiiAxisPairIndex n) :
    osiiStrictCoefficientCompactifiedDirectionalInput P x a
        (osiiAxisPairLogRealEmbed x) =
      fun j =>
        SCV.stripCompactification P.radius P.slope
          (x (j, false) : Complex) := by
  funext j
  by_cases h : a = (j, false)
  · simp [osiiStrictCoefficientCompactifiedDirectionalInput,
      h, osiiAxisPairLogRealEmbed]
  · simp [osiiStrictCoefficientCompactifiedDirectionalInput, h]

/-- Changing the inactive real base away from the selected doubled
coordinate does not alter the compactified directional input. -/
theorem osiiStrictCoefficientCompactifiedDirectionalInput_congr
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    {x y : osiiAxisPairIndex n -> Real}
    (a : osiiAxisPairIndex n)
    (hxy : forall b, b ≠ a -> x b = y b) :
    osiiStrictCoefficientCompactifiedDirectionalInput P x a =
      osiiStrictCoefficientCompactifiedDirectionalInput P y a := by
  funext r j
  by_cases h : a = (j, false)
  · simp [osiiStrictCoefficientCompactifiedDirectionalInput, h]
  · have hj : (j, false) ≠ a := by
      intro hj
      exact h hj.symm
    simp [osiiStrictCoefficientCompactifiedDirectionalInput,
      h, hxy (j, false) hj]

/-- The compactified directional input is holomorphic on its selected
axis-pair coordinate strip. -/
theorem differentiableOn_osiiStrictCoefficientCompactifiedDirectionalInput
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (x : osiiAxisPairIndex n -> Real)
    (a : osiiAxisPairIndex n) :
    DifferentiableOn Complex
      (osiiStrictCoefficientCompactifiedDirectionalInput P x a)
      (osiiAxisPairCoordinateLogStrip a) := by
  rw [differentiableOn_pi]
  intro j
  by_cases h : a = (j, false)
  · simp only [osiiStrictCoefficientCompactifiedDirectionalInput, h,
      if_pos]
    exact
      P.differentiableOn_stripCompactification.comp
        (differentiable_apply (j, false)).differentiableOn
        (fun r hr => hr)
  · simp [osiiStrictCoefficientCompactifiedDirectionalInput, h]

/-- Every selected doubled coordinate strip is sent into one compact
coefficient flat window. -/
theorem osiiStrictCoefficientCompactifiedDirectionalInput_mem_flatWindow
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (hrho : 0 < rho)
    (x : osiiAxisPairIndex n -> Real)
    (a : osiiAxisPairIndex n)
    {r : osiiAxisPairIndex n -> Complex}
    (hr : r ∈ osiiAxisPairCoordinateLogStrip a) :
    osiiStrictCoefficientCompactifiedDirectionalInput P x a r ∈
      osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho := by
  let input :=
    osiiStrictCoefficientCompactifiedDirectionalInput P x a r
  have hcoordinate (j : Fin n) :
      |(input j).re| < P.radius ∧
        |(input j).im| < rho := by
    apply P.stripCompactification_mem_rectangle
    by_cases h : a = (j, false)
    · simpa [h] using hr
    · simp [h]
      positivity
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right]
    apply
      (pi_norm_le_iff_of_nonneg
        (add_nonneg P.radius_pos.le hrho.le)).2
    intro j
    calc
      ‖input j‖ <= |(input j).re| + |(input j).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ <= P.radius + rho :=
        add_le_add (hcoordinate j).1.le (hcoordinate j).2.le
  · change
      (fun j => (input j).im) ∈
        osiiCoefficientClosedFlatImaginaryUnion (Fin n) rho
    refine ⟨a.1, (hcoordinate a.1).2.le, ?_⟩
    intro j hj
    have hne : a ≠ (j, false) := by
      intro h
      apply hj
      simpa using (congrArg Prod.fst h).symm
    have hinput :
        input j =
          SCV.stripCompactification P.radius P.slope
            (x (j, false) : Complex) := by
      simp [input,
        osiiStrictCoefficientCompactifiedDirectionalInput, hne]
    change (input j).im = 0
    rw [hinput]
    exact
      SCV.stripCompactification_ofReal_im
        P.radius P.slope (x (j, false))

/-- The compactified chart input depends continuously on the inactive real
base and the active standard-strip coordinate. -/
theorem continuousOn_osiiStrictCoefficientCompactifiedDirectionalInput_chart
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (a : osiiAxisPairIndex n) :
    ContinuousOn
      (fun p : (osiiAxisPairIndex n -> Real) × Complex =>
        osiiStrictCoefficientCompactifiedDirectionalInput
          P p.1 a
          (Function.update
            (osiiAxisPairLogRealEmbed p.1) a p.2))
      (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2}) := by
  rw [continuousOn_pi]
  intro j
  by_cases h : a = (j, false)
  · have hcomp :
        ContinuousOn
          (fun p :
              (osiiAxisPairIndex n -> Real) × Complex =>
            SCV.stripCompactification
              P.radius P.slope p.2)
          (Set.univ ×ˢ
            {w : Complex | |w.im| < Real.pi / 2}) :=
      P.differentiableOn_stripCompactification.continuousOn.comp
        continuous_snd.continuousOn
        (fun p hp => hp.2)
    simpa [osiiStrictCoefficientCompactifiedDirectionalInput,
      h, Function.update] using hcomp
  · let q :
        ((osiiAxisPairIndex n -> Real) × Complex) -> Complex :=
      fun p => (p.1 (j, false) : Complex)
    have hq : Continuous q := by
      exact
        Complex.continuous_ofReal.comp
          ((continuous_apply (j, false)).comp continuous_fst)
    have hmaps :
        Set.MapsTo q
          (Set.univ ×ˢ
            {w : Complex | |w.im| < Real.pi / 2})
          {w : Complex | |w.im| < Real.pi / 2} := by
      intro p hp
      simp [q]
      positivity
    have hcomp :
        ContinuousOn
          (fun p =>
            SCV.stripCompactification
              P.radius P.slope (q p))
          (Set.univ ×ˢ
            {w : Complex | |w.im| < Real.pi / 2}) :=
      P.differentiableOn_stripCompactification.continuousOn.comp
        hq.continuousOn hmaps
    simpa [osiiStrictCoefficientCompactifiedDirectionalInput,
      h, q] using hcomp

/-- A coefficient-space holomorphic function on the compact window gives a
coherent doubled-coordinate directional family. -/
def osiiStrictCoefficientCompactifiedDirectionalFamily
    {S rho : Real}
    [NeZero n]
    (P : SCV.StripCompactificationParameters S rho)
    (hrho : 0 < rho)
    (F : (Fin n -> Complex) -> Complex)
    (U : Set (Fin n -> Complex))
    (hF : DifferentiableOn Complex F U)
    (hwindow :
      osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ⊆ U) :
    OSIIAxisPairDirectionalBranchFamily n where
  branch := fun x a r =>
    F (osiiStrictCoefficientCompactifiedDirectionalInput
      P x a r)
  realEdge := fun x =>
    F (fun j =>
      SCV.stripCompactification P.radius P.slope
        (x (j, false) : Complex))
  branch_differentiableOn := by
    intro x a
    exact
      hF.comp
        (differentiableOn_osiiStrictCoefficientCompactifiedDirectionalInput
          P x a)
        (fun r hr =>
          hwindow
            (osiiStrictCoefficientCompactifiedDirectionalInput_mem_flatWindow
              P hrho x a hr))
  branch_congr_of_eq_off_selected := by
    intro x y a hxy
    funext r
    apply congrArg F
    exact congrFun
      (osiiStrictCoefficientCompactifiedDirectionalInput_congr
        P a hxy) r
  branch_real_edge := by
    intro x a
    rw [osiiStrictCoefficientCompactifiedDirectionalInput_real]

/-- The compactified directional family is a continuous bounded-flat-cross
datum, ready for the existing Gaussian MZ theorem. -/
def osiiStrictCoefficientCompactifiedFlatCrossData
    {S rho : Real}
    [NeZero n]
    (P : SCV.StripCompactificationParameters S rho)
    (hrho : 0 < rho)
    (F : (Fin n -> Complex) -> Complex)
    (U : Set (Fin n -> Complex))
    (hF : DifferentiableOn Complex F U)
    (hwindow :
      osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ⊆ U) :
    OSIIAxisPairFlatCrossData n := by
  let family :=
    osiiStrictCoefficientCompactifiedDirectionalFamily
      P hrho F U hF hwindow
  refine
    { family := family
      chart_continuous := ?_ }
  intro a
  let chartInput :
      ((osiiAxisPairIndex n -> Real) × Complex) ->
        (Fin n -> Complex) :=
    fun p =>
      osiiStrictCoefficientCompactifiedDirectionalInput
        P p.1 a
        (Function.update
          (osiiAxisPairLogRealEmbed p.1) a p.2)
  have hinput :
      ContinuousOn chartInput
        (Set.univ ×ˢ
          {w : Complex | |w.im| < Real.pi / 2}) := by
    simpa [chartInput] using
      continuousOn_osiiStrictCoefficientCompactifiedDirectionalInput_chart
        P a
  have hmaps :
      Set.MapsTo chartInput
        (Set.univ ×ˢ
          {w : Complex | |w.im| < Real.pi / 2})
        U := by
    intro p hp
    apply hwindow
    apply
      osiiStrictCoefficientCompactifiedDirectionalInput_mem_flatWindow
        P hrho p.1 a
    simpa [osiiAxisPairCoordinateLogStrip, chartInput] using hp.2
  have hsimple :
      ContinuousOn
        (fun p => F (chartInput p))
        (Set.univ ×ˢ
          {w : Complex | |w.im| < Real.pi / 2}) :=
    hF.continuousOn.comp hinput hmaps
  refine hsimple.congr ?_
  intro p hp
  change
    family.flatTubeBranch
        (Function.update
          (osiiAxisPairLogRealEmbed p.1) a p.2) =
      F (chartInput p)
  rw [family.flatTubeBranch_coordinate_line_eq_branch
    p.1 a hp.2]
  rfl

/-- Doubled-coordinate point whose false coordinates are the
target-adapted compactification preimages and whose true coordinates vanish. -/
def osiiStrictCoefficientCompactifiedMZTarget
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (w : Fin n -> Real) :
    osiiAxisPairIndex n -> Complex :=
  fun a =>
    if a.2 then 0 else P.preimage (w a.1)

/-- The doubled target lies in the full logarithmic MZ carrier whenever the
original nonnegative weights fit the parameter's inverse budget. -/
theorem osiiStrictCoefficientCompactifiedMZTarget_mem_logDomain
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S) :
    osiiStrictCoefficientCompactifiedMZTarget P w ∈
      osiiAxisPairLogDomain (d := n) := by
  have hpreimage :=
    P.sum_abs_preimage_im_lt w hw hsum
  simp only [osiiAxisPairLogDomain, Set.mem_setOf_eq,
    osiiStrictCoefficientCompactifiedMZTarget]
  rw [Fintype.sum_prod_type]
  simpa using hpreimage

/-- A coefficient pairing bounded on the compactified window admits a
bounded holomorphic continuation on the complete doubled-coordinate MZ
domain. -/
theorem exists_osiiStrictCoefficientCompactifiedMZExtension
    {S rho : Real}
    [NeZero n]
    (P : SCV.StripCompactificationParameters S rho)
    (hrho : 0 < rho)
    (F : (Fin n -> Complex) -> Complex)
    (U : Set (Fin n -> Complex))
    (hF : DifferentiableOn Complex F U)
    (hwindow :
      osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ⊆ U)
    (B : Real)
    (hB : 0 < B)
    (hbound :
      ∀ r,
        r ∈
            osiiStrictScalarSeedCoefficientFlatWindow
              (Fin n) (P.radius + rho) rho →
          ‖F r‖ <= B) :
    ∃ Gamma : (osiiAxisPairIndex n -> Complex) -> Complex,
      DifferentiableOn Complex Gamma
        (osiiAxisPairLogDomain (d := n)) ∧
      (forall x : osiiAxisPairIndex n -> Real,
        Gamma (osiiAxisPairLogRealEmbed x) =
          (osiiStrictCoefficientCompactifiedFlatCrossData
            P hrho F U hF hwindow).family.realEdge x) ∧
      Set.EqOn Gamma
        (osiiStrictCoefficientCompactifiedFlatCrossData
          P hrho F U hF hwindow).family.flatTubeBranch
        (osiiAxisPairFlatLogTubeUnion (d := n)) ∧
      ∀ z,
        z ∈ osiiAxisPairLogDomain (d := n) →
          ‖Gamma z‖ <= B := by
  let X :=
    osiiStrictCoefficientCompactifiedFlatCrossData
      P hrho F U hF hwindow
  let a0 : osiiAxisPairIndex n :=
    (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, false)
  have hreal_bound :
      forall x : osiiAxisPairIndex n -> Real,
        ‖X.family.realEdge x‖ <= B := by
    intro x
    have hstrip :
        osiiAxisPairLogRealEmbed x ∈
          osiiAxisPairCoordinateLogStrip a0 := by
      simp [osiiAxisPairCoordinateLogStrip,
        osiiAxisPairLogRealEmbed]
      positivity
    have hmem :=
      osiiStrictCoefficientCompactifiedDirectionalInput_mem_flatWindow
        P hrho x a0 hstrip
    apply hbound
    simpa [X, osiiStrictCoefficientCompactifiedFlatCrossData,
      osiiStrictCoefficientCompactifiedDirectionalFamily,
      osiiStrictCoefficientCompactifiedDirectionalInput_real] using hmem
  have hchart_bound :
      forall a : osiiAxisPairIndex n,
        forall (x : osiiAxisPairIndex n -> Real) (z : Complex),
          |z.im| < Real.pi / 2 ->
          ‖X.family.flatTubeBranch
            (Function.update
              (osiiAxisPairLogRealEmbed x) a z)‖ <= B := by
    intro a x z hz
    rw [X.family.flatTubeBranch_coordinate_line_eq_branch
      x a hz]
    apply hbound
    apply
      osiiStrictCoefficientCompactifiedDirectionalInput_mem_flatWindow
        P hrho x a
    simpa [osiiAxisPairCoordinateLogStrip] using hz
  obtain ⟨Gamma, hGamma, hreal⟩ :=
    X.exists_holomorphic_realEdge_extension_of_bounds
      B hreal_bound B hB hchart_bound
  refine ⟨Gamma, hGamma, hreal, ?_, ?_⟩
  · exact
      X.family.eqOn_flatTubeBranch_of_holomorphic_realEdge
        Gamma hGamma hreal
  · intro z hz
    exact
      X.norm_holomorphic_realEdge_extension_le
        B hreal_bound B hB hchart_bound
        Gamma hGamma hreal z hz

end OSIIChapterV
end OSReconstruction
