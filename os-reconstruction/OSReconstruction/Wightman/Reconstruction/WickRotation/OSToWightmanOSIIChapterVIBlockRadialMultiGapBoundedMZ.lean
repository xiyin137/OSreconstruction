/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.StripCompactification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapUniform












noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

/-- Real base obtained by compactifying centered logarithmic coordinates and
then undoing the common logarithmic shift. -/
def osiiStep4MultiGapCompactifiedRealBase
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real) :
    Fin k -> osiiAxisPairIndex d -> Real :=
  fun i a =>
    u i a - shift +
      P.radius * Real.tanh ((P.slope / P.radius) * x i a)

/-- Selected-coordinate compactified input.  Inactive coordinates are frozen
at the compactified real base, so no holomorphy outside the selected standard
strip is requested. -/
def osiiStep4MultiGapCompactifiedDirectionalInput
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (r : Fin k -> osiiAxisPairIndex d -> Complex) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i a =>
    if (i, a) = q then
      (u q.1 q.2 - shift : Complex) +
        SCV.stripCompactification P.radius P.slope (r q.1 q.2)
    else
      (osiiStep4MultiGapCompactifiedRealBase P shift u x i a : Complex)

theorem continuous_osiiStep4MultiGapCompactifiedRealBase
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    Continuous (osiiStep4MultiGapCompactifiedRealBase P shift u) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro a
  simp only [osiiStep4MultiGapCompactifiedRealBase]
  have hz : Continuous
      (fun x : Fin k -> osiiAxisPairIndex d -> Real => (x i a : Complex)) :=
    Complex.continuous_ofReal.comp
      ((continuous_apply a).comp (continuous_apply i))
  have hmaps : Set.MapsTo
      (fun x : Fin k -> osiiAxisPairIndex d -> Real => (x i a : Complex))
      Set.univ {z : Complex | |z.im| < Real.pi / 2} := by
    intro x _hx
    simp
    positivity
  have hcompact : Continuous
      (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
        SCV.stripCompactification P.radius P.slope (x i a : Complex)) :=
    continuousOn_univ.mp
      (P.differentiableOn_stripCompactification.continuousOn.comp
        hz.continuousOn hmaps)
  have hre : Continuous
      (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
        (SCV.stripCompactification P.radius P.slope
          (x i a : Complex)).re) :=
    Complex.continuous_re.comp hcompact
  have htanh : Continuous
      (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
        P.radius * Real.tanh ((P.slope / P.radius) * x i a)) := by
    simpa only [SCV.stripCompactification_ofReal,
      Complex.ofReal_re] using hre
  exact continuous_const.add htanh

@[simp] theorem osiiStep4MultiGapCompactifiedDirectionalInput_selected
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (r : Fin k -> osiiAxisPairIndex d -> Complex) :
    osiiStep4MultiGapCompactifiedDirectionalInput
        P shift u x q r q.1 q.2 =
      (u q.1 q.2 - shift : Complex) +
        SCV.stripCompactification P.radius P.slope (r q.1 q.2) := by
  simp [osiiStep4MultiGapCompactifiedDirectionalInput]

theorem osiiStep4MultiGapCompactifiedDirectionalInput_eq_realEmbed
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    osiiStep4MultiGapCompactifiedDirectionalInput P shift u x q
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      osiiAxisPairSimultaneousLogRealEmbed
        (osiiStep4MultiGapCompactifiedRealBase P shift u x) := by
  funext i a
  by_cases h : (i, a) = q
  · obtain ⟨rfl, rfl⟩ := h
    simp [osiiStep4MultiGapCompactifiedDirectionalInput,
      osiiStep4MultiGapCompactifiedRealBase,
      osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed,
      SCV.stripCompactification_ofReal]
  · simp [osiiStep4MultiGapCompactifiedDirectionalInput,
      osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed, h]

theorem osiiStep4MultiGapCompactifiedDirectionalInput_mem_strip
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (hsigma : sigma < Real.pi / 2)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    {r : Fin k -> osiiAxisPairIndex d -> Complex}
    (hr : r ∈ osiiAxisPairMultiGapCoordinateLogStrip q) :
    osiiStep4MultiGapCompactifiedDirectionalInput P shift u x q r ∈
      osiiAxisPairMultiGapCoordinateLogStrip q := by
  change
    |(osiiStep4MultiGapCompactifiedDirectionalInput
      P shift u x q r q.1 q.2).im| < Real.pi / 2
  rw [osiiStep4MultiGapCompactifiedDirectionalInput_selected]
  have hreal : ((u q.1 q.2 - shift : Complex)).im = 0 := by simp
  rw [Complex.add_im, hreal, zero_add]
  exact (P.stripCompactification_mem_rectangle hr).2.trans hsigma

theorem differentiableOn_osiiStep4MultiGapCompactifiedDirectionalInput
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    DifferentiableOn Complex
      (osiiStep4MultiGapCompactifiedDirectionalInput P shift u x q)
      (osiiAxisPairMultiGapCoordinateLogStrip q) := by
  rw [differentiableOn_pi]
  intro i
  rw [differentiableOn_pi]
  intro a
  by_cases h : (i, a) = q
  · obtain ⟨rfl, rfl⟩ := h
    simp only [osiiStep4MultiGapCompactifiedDirectionalInput, if_pos]
    exact (differentiableOn_const
      (c := (u i a - shift : Complex))).add
      (P.differentiableOn_stripCompactification.comp
        (by fun_prop)
        (fun r hr => hr))
  · simp [osiiStep4MultiGapCompactifiedDirectionalInput, h]

/-- The transformed directional input is an ordinary selected update of its
compactified real base. -/
theorem osiiStep4MultiGapCompactifiedDirectionalInput_eq_update
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (r : Fin k -> osiiAxisPairIndex d -> Complex) :
    osiiStep4MultiGapCompactifiedDirectionalInput P shift u x q r =
      osiiAxisPairMultiGapUpdate
        (osiiAxisPairSimultaneousLogRealEmbed
          (osiiStep4MultiGapCompactifiedRealBase P shift u x)) q
        ((u q.1 q.2 - shift : Complex) +
          SCV.stripCompactification P.radius P.slope (r q.1 q.2)) := by
  funext i a
  by_cases h : (i, a) = q
  · obtain ⟨rfl, rfl⟩ := h
    simp [osiiStep4MultiGapCompactifiedDirectionalInput,
      osiiAxisPairMultiGapUpdate]
  · have houter : i ≠ q.1 ∨ a ≠ q.2 := by
      by_cases hi : i = q.1
      · exact Or.inr (by
          intro ha
          exact h (Prod.ext hi ha))
      · exact Or.inl hi
    rcases houter with hi | ha
    · simp [osiiStep4MultiGapCompactifiedDirectionalInput,
        osiiAxisPairMultiGapUpdate, osiiAxisPairSimultaneousLogRealEmbed,
        osiiAxisPairLogRealEmbed, h, hi]
    · by_cases hi : i = q.1
      · subst i
        simp [osiiStep4MultiGapCompactifiedDirectionalInput,
          osiiAxisPairMultiGapUpdate, osiiAxisPairSimultaneousLogRealEmbed,
          osiiAxisPairLogRealEmbed, h, ha]
      · simp [osiiStep4MultiGapCompactifiedDirectionalInput,
          osiiAxisPairMultiGapUpdate, osiiAxisPairSimultaneousLogRealEmbed,
          osiiAxisPairLogRealEmbed, h, hi]

theorem osiiStep4MultiGapCompactifiedRealBase_congr_of_eq_off_selected
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    {x y : Fin k -> osiiAxisPairIndex d -> Real}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : forall p, p ≠ q -> x p.1 p.2 = y p.1 p.2) :
    forall p, p ≠ q ->
      osiiStep4MultiGapCompactifiedRealBase P shift u x p.1 p.2 =
        osiiStep4MultiGapCompactifiedRealBase P shift u y p.1 p.2 := by
  intro p hp
  simp only [osiiStep4MultiGapCompactifiedRealBase]
  rw [hxy p hp]

/-- Compactification places every recentered real logarithmic coordinate in
the common upper window of radius `P.radius`. -/
theorem osiiNarrowTimeCenteredRealLogCoordinate_compactifiedRealBase_le
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (T : Real)
    {d k : Nat}
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    osiiNarrowTimeCenteredRealLogCoordinate T
        (osiiStep4MultiGapCompactifiedRealBase P
          (Real.log (osiiNarrowTimeLogScale (d := d) T)) u x) i a <=
      u i a + P.radius := by
  have htanh :
      Real.tanh ((P.slope / P.radius) * x i a) <= 1 :=
    (Real.tanh_lt_one _).le
  have hscaled :
      P.radius * Real.tanh ((P.slope / P.radius) * x i a) <=
        P.radius := by
    simpa using mul_le_mul_of_nonneg_left htanh P.radius_pos.le
  simp only [osiiNarrowTimeCenteredRealLogCoordinate,
    osiiStep4MultiGapCompactifiedRealBase]
  linarith

theorem osiiStep4MultiGapCompactifiedDirectionalInput_congr_of_eq_off_selected
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat}
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    {x y : Fin k -> osiiAxisPairIndex d -> Real}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : forall p, p ≠ q -> x p.1 p.2 = y p.1 p.2)
    (r : Fin k -> osiiAxisPairIndex d -> Complex) :
    osiiStep4MultiGapCompactifiedDirectionalInput P shift u x q r =
      osiiStep4MultiGapCompactifiedDirectionalInput P shift u y q r := by
  funext i a
  by_cases h : (i, a) = q
  · simp [osiiStep4MultiGapCompactifiedDirectionalInput, h]
  · simp only [osiiStep4MultiGapCompactifiedDirectionalInput, if_neg h]
    rw [osiiStep4MultiGapCompactifiedRealBase_congr_of_eq_off_selected
      P shift u q hxy (i, a) h]

/-- Apply centered strip compactification to every chart of a multi-gap flat
cross. -/
def OSIIAxisPairMultiGapFlatCrossData.centeredCompactified
    {d k : Nat} [NeZero d] [NeZero k]
    (X : OSIIAxisPairMultiGapFlatCrossData d k)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (hsigma : sigma < Real.pi / 2)
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    OSIIAxisPairMultiGapFlatCrossData d k where
  branch := fun x q r =>
    X.branch (osiiStep4MultiGapCompactifiedRealBase P shift u x) q
      (osiiStep4MultiGapCompactifiedDirectionalInput P shift u x q r)
  realEdge := fun x =>
    X.realEdge (osiiStep4MultiGapCompactifiedRealBase P shift u x)
  branch_differentiableOn := by
    intro x q
    exact (X.branch_differentiableOn
      (osiiStep4MultiGapCompactifiedRealBase P shift u x) q).comp
        (differentiableOn_osiiStep4MultiGapCompactifiedDirectionalInput
          P shift u x q)
        (fun r hr =>
          osiiStep4MultiGapCompactifiedDirectionalInput_mem_strip
            P hsigma shift u x q hr)
  branch_congr_of_eq_off_selected := by
    intro x y q hxy
    have hbase := X.branch_congr_of_eq_off_selected q
      (osiiStep4MultiGapCompactifiedRealBase_congr_of_eq_off_selected
        P shift u q hxy)
    funext r
    rw [hbase]
    rw [osiiStep4MultiGapCompactifiedDirectionalInput_congr_of_eq_off_selected
      P shift u q hxy r]
  branch_real_edge := by
    intro x q
    rw [osiiStep4MultiGapCompactifiedDirectionalInput_eq_realEmbed]
    exact X.branch_real_edge
      (osiiStep4MultiGapCompactifiedRealBase P shift u x) q
  chart_continuous := by
    intro q
    let chartMap :
        ((Fin k -> osiiAxisPairIndex d -> Real) × Complex) ->
          ((Fin k -> osiiAxisPairIndex d -> Real) × Complex) :=
      fun p =>
        (osiiStep4MultiGapCompactifiedRealBase P shift u p.1,
          (u q.1 q.2 - shift : Complex) +
            SCV.stripCompactification P.radius P.slope p.2)
    have hbase : Continuous
        (fun p : (Fin k -> osiiAxisPairIndex d -> Real) × Complex =>
          osiiStep4MultiGapCompactifiedRealBase P shift u p.1) :=
      (continuous_osiiStep4MultiGapCompactifiedRealBase P shift u).comp
        continuous_fst
    have hstrip : ContinuousOn
        (fun p : (Fin k -> osiiAxisPairIndex d -> Real) × Complex =>
          SCV.stripCompactification P.radius P.slope p.2)
        (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2}) :=
      P.differentiableOn_stripCompactification.continuousOn.comp
        continuous_snd.continuousOn (fun p hp => hp.2)
    have hselected : ContinuousOn
        (fun p : (Fin k -> osiiAxisPairIndex d -> Real) × Complex =>
          (u q.1 q.2 - shift : Complex) +
            SCV.stripCompactification P.radius P.slope p.2)
        (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2}) :=
      (continuousOn_const.add hstrip)
    have hmap : ContinuousOn chartMap
        (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2}) :=
      hbase.continuousOn.prodMk hselected
    have hmaps : Set.MapsTo chartMap
        (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2})
        (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2}) := by
      intro p hp
      refine ⟨Set.mem_univ _, ?_⟩
      change
        |((u q.1 q.2 - shift : Complex) +
          SCV.stripCompactification P.radius P.slope p.2).im| <
            Real.pi / 2
      have hreal : ((u q.1 q.2 - shift : Complex)).im = 0 := by simp
      rw [Complex.add_im, hreal, zero_add]
      exact (P.stripCompactification_mem_rectangle hp.2).2.trans hsigma
    refine ((X.chart_continuous q).comp hmap hmaps).congr ?_
    intro p hp
    change
      X.branch
          (osiiStep4MultiGapCompactifiedRealBase P shift u p.1) q
          (osiiStep4MultiGapCompactifiedDirectionalInput P shift u p.1 q
            (osiiAxisPairMultiGapUpdate
              (osiiAxisPairSimultaneousLogRealEmbed p.1) q p.2)) =
        X.branch (chartMap p).1 q
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed (chartMap p).1) q
            (chartMap p).2)
    rw [osiiStep4MultiGapCompactifiedDirectionalInput_eq_update]
    simp [chartMap, osiiAxisPairMultiGapUpdate]

/-- A selected chart of the compactified cross is the corresponding chart of
the original cross at the compactified real base and selected scaled-tanh
coordinate. -/
theorem OSIIAxisPairMultiGapFlatCrossData.centeredCompactified_branch_update
    {d k : Nat} [NeZero d] [NeZero k]
    (X : OSIIAxisPairMultiGapFlatCrossData d k)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (hsigma : sigma < Real.pi / 2)
    (shift : Real)
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (w : Complex) :
    (X.centeredCompactified P hsigma shift u).branch x q
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) q w) =
      X.branch
        (osiiStep4MultiGapCompactifiedRealBase P shift u x) q
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed
            (osiiStep4MultiGapCompactifiedRealBase P shift u x)) q
          ((u q.1 q.2 - shift : Complex) +
            SCV.stripCompactification P.radius P.slope w)) := by
  change
    X.branch
        (osiiStep4MultiGapCompactifiedRealBase P shift u x) q
        (osiiStep4MultiGapCompactifiedDirectionalInput P shift u x q
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed x) q w)) = _
  rw [osiiStep4MultiGapCompactifiedDirectionalInput_eq_update]
  simp [osiiAxisPairMultiGapUpdate]

/-- Explicit common bound for the centered compactified real edge and all of
its coordinate charts.  The leading `1` supplies the strict positivity
required by the bounded MZ theorem even when the underlying growth constant
vanishes. -/
def osiiStep4MultiGapCenteredCompactifiedBound
    {d k : Nat}
    (C : Real) (M N : Nat) (rho : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (R : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real) : Real :=
  1 + C * (16 / rho) ^ M *
    (1 + norm center + Real.exp R *
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        Real.exp (u i a))) ^ N

theorem osiiStep4MultiGapCenteredCompactifiedBound_pos
    {d k : Nat}
    {C rho : Real} (hC : 0 <= C) (hrho : 0 < rho)
    (M N : Nat)
    (center : Fin (k * (d + 1)) -> Real)
    (R : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    0 < osiiStep4MultiGapCenteredCompactifiedBound
      C M N rho center R u := by
  have hscale : 0 <= (16 / rho) ^ M :=
    pow_nonneg (by positivity) M
  have hsum :
      0 <= ∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        Real.exp (u i a) :=
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun a _ => (Real.exp_pos (u i a)).le
  have hbase :
      0 <= 1 + norm center + Real.exp R *
        (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
          Real.exp (u i a)) := by
    positivity
  have htail :
      0 <= C * (16 / rho) ^ M *
        (1 + norm center + Real.exp R *
          (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
            Real.exp (u i a))) ^ N :=
    mul_nonneg (mul_nonneg hC hscale) (pow_nonneg hbase N)
  simp only [osiiStep4MultiGapCenteredCompactifiedBound]
  linarith

/-- One choice of the packet-growth constants, made before the radial source,
compactification, and logarithmic base.  Keeping this quantifier order
explicit is what later gives a genuinely parameter-uniform MZ family. -/
structure OSIIStep4MultiGapCenteredWindowScaleBoundData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) where
  constant : Real
  scaleDegree : Nat
  growthDegree : Nat
  constant_nonneg : 0 <= constant
  bound :
    ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
      ∀ (center y y' : Fin (k * (d + 1)) -> Real),
        ∀ hcenter : ∀ j : Fin k,
          rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))),
          (y, y') ∈
              osiiStep4PartialConvolutionClosedImaginaryBox
                (d + 1) k rho ->
            ∀ (D : OSIIStep4MultiGapSelectedCommonSlopeData
                  d k hrho center y y' hcenter)
              (u x : Fin k -> osiiAxisPairIndex d -> Real)
              (R : Real),
              (forall i a,
                osiiNarrowTimeCenteredRealLogCoordinate D.T x i a <=
                  u i a + R) ->
                ∀ (q : osiiAxisPairMultiGapIndex d k) (w : Complex),
                |w.im| < Real.pi / 2 ->
                  norm ((D.packetFamily OS lgc).logBranch x q
                    (osiiAxisPairMultiGapUpdate
                      (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
                    constant * (16 / rho) ^ scaleDegree *
                      (1 + norm center + Real.exp R *
                        (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
                          Real.exp (u i a))) ^ growthDegree

/-- The slope-independent packet estimate supplies global centered-window
constants before any radial source is chosen. -/
theorem nonempty_osiiStep4MultiGapCenteredWindowScaleBoundData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    Nonempty (OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc) := by
  obtain ⟨C, M, N, hC, hbound⟩ :=
    OSIIStep4MultiGapSelectedCommonSlopeData.exists_packetFamily_logBranch_scale_bound_on_centered_log_window
      d k OS lgc
  exact ⟨{
    constant := C
    scaleDegree := M
    growthDegree := N
    constant_nonneg := hC
    bound := hbound }⟩

/-- A fixed global witness used by the parametric bounded MZ construction. -/
noncomputable def osiiStep4MultiGapCenteredWindowScaleBoundData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc :=
  Classical.choice
    (nonempty_osiiStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)

namespace OSIIStep4MultiGapSelectedCommonSlopeData

/-- The radial packet flat cross after centered strip compactification. -/
noncomputable def centeredCompactifiedFlatCross
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (hsigma : sigma < Real.pi / 2)
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    OSIIAxisPairMultiGapFlatCrossData d k :=
  (D.flatCrossData OS lgc).centeredCompactified P hsigma
    (Real.log (osiiNarrowTimeLogScale (d := d) D.T)) u

/-- Fixed global packet-growth constants bound one centered compactified
cross, uniformly in the radial source parameter. -/
theorem centeredCompactifiedFlatCross_bounds
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
      0 < osiiStep4MultiGapCenteredCompactifiedBound
        G.constant G.scaleDegree G.growthDegree
          rho center P.radius u ∧
      (forall x : Fin k -> osiiAxisPairIndex d -> Real,
        norm ((D.centeredCompactifiedFlatCross OS lgc P hsigma u).realEdge x) <=
          osiiStep4MultiGapCenteredCompactifiedBound
            G.constant G.scaleDegree G.growthDegree
              rho center P.radius u) ∧
      forall (q : osiiAxisPairMultiGapIndex d k)
        (x : Fin k -> osiiAxisPairIndex d -> Real) (w : Complex),
        |w.im| < Real.pi / 2 ->
          norm ((D.centeredCompactifiedFlatCross OS lgc P hsigma u).branch x q
            (osiiAxisPairMultiGapUpdate
              (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
            osiiStep4MultiGapCenteredCompactifiedBound
              G.constant G.scaleDegree G.growthDegree
                rho center P.radius u := by
  let C := G.constant
  let M := G.scaleDegree
  let N := G.growthDegree
  have hC : 0 <= C := G.constant_nonneg
  have hbound := G.bound (rho := rho) hrho hrho_le
  let shift := Real.log (osiiNarrowTimeLogScale (d := d) D.T)
  let Q := D.centeredCompactifiedFlatCross OS lgc P hsigma u
  let B := osiiStep4MultiGapCenteredCompactifiedBound
    C M N rho center P.radius u
  have hB : 0 < B := by
    simpa only [B] using
      osiiStep4MultiGapCenteredCompactifiedBound_pos
        hC hrho M N center P.radius u
  have hchart :
      forall (q : osiiAxisPairMultiGapIndex d k)
        (x : Fin k -> osiiAxisPairIndex d -> Real) (w : Complex),
        |w.im| < Real.pi / 2 ->
          norm (Q.branch x q
            (osiiAxisPairMultiGapUpdate
              (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <= B := by
    intro q x w hw
    let xb := osiiStep4MultiGapCompactifiedRealBase P shift u x
    let wc : Complex :=
      (u q.1 q.2 - shift : Complex) +
        SCV.stripCompactification P.radius P.slope w
    have hwc : |wc.im| < Real.pi / 2 := by
      have hrect := (P.stripCompactification_mem_rectangle hw).2
      have hreal : ((u q.1 q.2 - shift : Complex)).im = 0 := by simp
      dsimp only [wc]
      rw [Complex.add_im, hreal, zero_add]
      exact hrect.trans hsigma
    have hxb : forall i a,
        osiiNarrowTimeCenteredRealLogCoordinate D.T xb i a <=
          u i a + P.radius := by
      intro i a
      simpa only [xb, shift] using
        osiiNarrowTimeCenteredRealLogCoordinate_compactifiedRealBase_le
          P D.T u x i a
    have hraw := hbound center y y' hcenter hp D
      u xb P.radius hxb q wc hwc
    have horiginal :
        norm ((D.flatCrossData OS lgc).branch xb q
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed xb) q wc)) <=
          C * (16 / rho) ^ M *
            (1 + norm center + Real.exp P.radius *
              (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
                Real.exp (u i a))) ^ N := by
      simpa only [flatCrossData,
        OSIIAxisPairMultiGapSemigroupPacketFamily.toFlatCrossData] using hraw
    calc
      norm (Q.branch x q
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed x) q w)) =
          norm ((D.flatCrossData OS lgc).branch xb q
            (osiiAxisPairMultiGapUpdate
              (osiiAxisPairSimultaneousLogRealEmbed xb) q wc)) := by
        dsimp only [Q, centeredCompactifiedFlatCross]
        rw [OSIIAxisPairMultiGapFlatCrossData.centeredCompactified_branch_update]
      _ <= C * (16 / rho) ^ M *
            (1 + norm center + Real.exp P.radius *
              (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
                Real.exp (u i a))) ^ N := horiginal
      _ <= B := by
        simp only [B, osiiStep4MultiGapCenteredCompactifiedBound]
        linarith
  have hreal : forall x : Fin k -> osiiAxisPairIndex d -> Real,
      norm (Q.realEdge x) <= B := by
    intro x
    let q0 : osiiAxisPairMultiGapIndex d k := default
    have hupdate :
        osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed x) q0
            (x q0.1 q0.2 : Complex) =
          osiiAxisPairSimultaneousLogRealEmbed x := by
      funext i a
      by_cases hi : i = q0.1
      · subst i
        by_cases ha : a = q0.2
        · subst a
          simp [osiiAxisPairMultiGapUpdate,
            osiiAxisPairSimultaneousLogRealEmbed,
            osiiAxisPairLogRealEmbed]
        · simp [osiiAxisPairMultiGapUpdate,
            osiiAxisPairSimultaneousLogRealEmbed,
            osiiAxisPairLogRealEmbed, ha]
      · simp [osiiAxisPairMultiGapUpdate,
          osiiAxisPairSimultaneousLogRealEmbed,
          osiiAxisPairLogRealEmbed, hi]
    calc
      norm (Q.realEdge x) =
          norm (Q.branch x q0
            (osiiAxisPairSimultaneousLogRealEmbed x)) :=
        congrArg norm (Q.branch_real_edge x q0).symm
      _ = norm (Q.branch x q0
            (osiiAxisPairMultiGapUpdate
              (osiiAxisPairSimultaneousLogRealEmbed x) q0
              (x q0.1 q0.2 : Complex))) := by rw [hupdate]
      _ <= B := hchart q0 x (x q0.1 q0.2 : Complex) (by
        simp
        positivity)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [B, C, M, N] using hB
  · simpa only [Q, B, C, M, N] using hreal
  · simpa only [Q, B, C, M, N] using hchart

end OSIIStep4MultiGapSelectedCommonSlopeData

end OSReconstruction
