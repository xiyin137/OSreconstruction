import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMZApproximation
import OSReconstruction.SCV.CoshDamping

/-!
# Growth-admissible OS-II axis-pair MZ continuation

The physical multi-gap packets are tempered in their translation parameters,
not globally bounded in logarithmic coordinates.  This file removes the
artificial global-bound requirement without changing the Gaussian MZ proof:
multiply the flat cross by a nonvanishing entire cosh weight, apply the
bounded theorem, and divide the resulting continuation by the same weight.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

namespace OSIIAxisPairDirectionalBranchFamily

/-- Multiply a coherent directional family by the entire cosh damping
weight. -/
def coshDamped
    (F : OSIIAxisPairDirectionalBranchFamily d)
    (rate : ℝ) :
    OSIIAxisPairDirectionalBranchFamily d where
  branch := fun x a z => SCV.logCoshDamping rate z * F.branch x a z
  realEdge := fun x =>
    SCV.logCoshDamping rate (osiiAxisPairLogRealEmbed x) * F.realEdge x
  branch_differentiableOn := by
    intro x a
    exact
      SCV.differentiable_logCoshDamping rate
        |>.differentiableOn.mul (F.branch_differentiableOn x a)
  branch_congr_of_eq_off_selected := by
    intro x y a hxy
    funext z
    rw [F.branch_congr_of_eq_off_selected a hxy]
  branch_real_edge := by
    intro x a
    rw [F.branch_real_edge]

end OSIIAxisPairDirectionalBranchFamily

namespace OSIIAxisPairFlatCrossData

/-- Continuous flat-cross data after multiplication by the cosh damping
weight. -/
def coshDamped
    (X : OSIIAxisPairFlatCrossData d)
    (rate : ℝ) :
    OSIIAxisPairFlatCrossData d where
  family := X.family.coshDamped rate
  chart_continuous := by
    intro a
    let line :
        ((osiiAxisPairIndex d → ℝ) × ℂ) →
          (osiiAxisPairIndex d → ℂ) :=
      fun p => Function.update (osiiAxisPairLogRealEmbed p.1) a p.2
    have hline : Continuous line := by
      apply continuous_pi
      intro b
      by_cases hba : b = a
      · subst b
        simpa [line] using
          (continuous_snd :
            Continuous
              (fun p :
                (osiiAxisPairIndex d → ℝ) × ℂ => p.2))
      · simp [line, Function.update, hba, osiiAxisPairLogRealEmbed]
        fun_prop
    have hweight :
        Continuous fun p =>
          SCV.logCoshDamping rate (line p) :=
      SCV.differentiable_logCoshDamping rate
        |>.continuous.comp hline
    refine (hweight.continuousOn.mul (X.chart_continuous a)).congr ?_
    intro p hp
    have hw : |p.2.im| < Real.pi / 2 := hp.2
    change
      (X.family.coshDamped rate).flatTubeBranch
          (Function.update (osiiAxisPairLogRealEmbed p.1) a p.2) =
        SCV.logCoshDamping rate (line p) *
          X.family.flatTubeBranch
            (Function.update (osiiAxisPairLogRealEmbed p.1) a p.2)
    rw [OSIIAxisPairDirectionalBranchFamily.flatTubeBranch_coordinate_line_eq_branch
      (F := X.family.coshDamped rate) p.1 a hw]
    rw [OSIIAxisPairDirectionalBranchFamily.flatTubeBranch_coordinate_line_eq_branch
      (F := X.family) p.1 a hw]
    rfl

@[simp]
theorem coshDamped_realEdge
    (X : OSIIAxisPairFlatCrossData d)
    (rate : ℝ)
    (x : osiiAxisPairIndex d → ℝ) :
    (X.coshDamped rate).family.realEdge x =
      SCV.logCoshDamping rate (osiiAxisPairLogRealEmbed x) *
        X.family.realEdge x :=
  rfl

theorem coshDamped_flatTubeBranch_coordinate_line
    (X : OSIIAxisPairFlatCrossData d)
    (rate : ℝ)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d)
    (w : ℂ)
    (hw : |w.im| < Real.pi / 2) :
    (X.coshDamped rate).family.flatTubeBranch
        (Function.update (osiiAxisPairLogRealEmbed x) a w) =
      SCV.logCoshDamping rate
          (Function.update (osiiAxisPairLogRealEmbed x) a w) *
        X.family.flatTubeBranch
          (Function.update (osiiAxisPairLogRealEmbed x) a w) := by
  change
    (X.family.coshDamped rate).flatTubeBranch
        (Function.update (osiiAxisPairLogRealEmbed x) a w) =
      SCV.logCoshDamping rate
          (Function.update (osiiAxisPairLogRealEmbed x) a w) *
        X.family.flatTubeBranch
          (Function.update (osiiAxisPairLogRealEmbed x) a w)
  rw [OSIIAxisPairDirectionalBranchFamily.flatTubeBranch_coordinate_line_eq_branch
    (F := X.family.coshDamped rate) x a hw]
  rw [OSIIAxisPairDirectionalBranchFamily.flatTubeBranch_coordinate_line_eq_branch
    (F := X.family) x a hw]
  rfl

end OSIIAxisPairFlatCrossData

/-- Exact growth hypothesis needed for cosh-damped MZ continuation.  It is
stable under polynomial growth in the physical translations
`exp (rᵢᵃ)`. -/
structure OSIIAxisPairFlatCrossCoshGrowthData
    (X : OSIIAxisPairFlatCrossData d) where
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  realEdgeConstant : ℝ
  realEdgeConstant_nonneg : 0 ≤ realEdgeConstant
  realEdge_bound :
    ∀ x : osiiAxisPairIndex d → ℝ,
      ‖X.family.realEdge x‖ ≤
        realEdgeConstant *
          Real.exp (rate * SCV.logCoshGauge x)
  chartConstant : ℝ
  chartConstant_pos : 0 < chartConstant
  chart_bound :
    ∀ (a : osiiAxisPairIndex d)
      (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
      |w.im| < Real.pi / 2 →
        ‖X.family.flatTubeBranch
          (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤
          chartConstant *
            Real.exp
              (rate * SCV.logCoshGauge
                (fun b =>
                  (Function.update
                    (osiiAxisPairLogRealEmbed x) a w b).re))

namespace OSIIAxisPairFlatCrossCoshGrowthData

private theorem update_strip_im
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d)
    (w : ℂ)
    (hw : |w.im| < Real.pi / 2) :
    ∀ b,
      |(Function.update
        (osiiAxisPairLogRealEmbed x) a w b).im| <
        Real.pi / 2 := by
  intro b
  by_cases hba : b = a
  · subst b
    simpa using hw
  · simp [Function.update, hba, osiiAxisPairLogRealEmbed]
    positivity

/-- The damped real edge is globally bounded. -/
theorem coshDamped_realEdge_bound
    {X : OSIIAxisPairFlatCrossData d}
    (G : OSIIAxisPairFlatCrossCoshGrowthData X)
    (x : osiiAxisPairIndex d → ℝ) :
    ‖(X.coshDamped G.rate).family.realEdge x‖ ≤
      G.realEdgeConstant := by
  rw [OSIIAxisPairFlatCrossData.coshDamped_realEdge]
  let edge : (osiiAxisPairIndex d → ℂ) → ℂ :=
    fun z => X.family.realEdge (fun i => (z i).re)
  have hbound :=
    SCV.norm_mul_logCoshDamping_le
      G.rate G.realEdgeConstant G.rate_nonneg
      G.realEdgeConstant_nonneg edge
      (osiiAxisPairLogRealEmbed x)
      (by
        intro i
        simp [osiiAxisPairLogRealEmbed]
        positivity)
      (by
        simpa [edge, osiiAxisPairLogRealEmbed] using
          G.realEdge_bound x)
  simpa [edge, osiiAxisPairLogRealEmbed] using hbound

/-- Every damped coordinate chart is globally bounded by one common
constant. -/
theorem coshDamped_chart_bound
    {X : OSIIAxisPairFlatCrossData d}
    (G : OSIIAxisPairFlatCrossCoshGrowthData X)
    (a : osiiAxisPairIndex d)
    (x : osiiAxisPairIndex d → ℝ)
    (w : ℂ)
    (hw : |w.im| < Real.pi / 2) :
    ‖(X.coshDamped G.rate).family.flatTubeBranch
        (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤
      G.chartConstant := by
  rw [X.coshDamped_flatTubeBranch_coordinate_line G.rate x a w hw]
  apply SCV.norm_mul_logCoshDamping_le
      G.rate G.chartConstant G.rate_nonneg
      G.chartConstant_pos.le
      X.family.flatTubeBranch
      (Function.update (osiiAxisPairLogRealEmbed x) a w)
      (update_strip_im x a w hw)
  exact G.chart_bound a x w hw

/-- Cosh-growth flat crosses admit the same holomorphic MZ continuation as
globally bounded crosses. -/
theorem exists_holomorphic_realEdge_extension
    {X : OSIIAxisPairFlatCrossData d}
    (G : OSIIAxisPairFlatCrossCoshGrowthData X) :
    ∃ Gamma : (osiiAxisPairIndex d → ℂ) → ℂ,
      DifferentiableOn ℂ Gamma
        (osiiAxisPairLogDomain (d := d)) ∧
      ∀ x : osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairLogRealEmbed x) =
          X.family.realEdge x := by
  obtain ⟨GammaD, hGammaD, hGammaD_real⟩ :=
    (X.coshDamped G.rate).exists_holomorphic_realEdge_extension_of_bounds
      G.realEdgeConstant G.coshDamped_realEdge_bound
      G.chartConstant G.chartConstant_pos
      G.coshDamped_chart_bound
  refine
    ⟨fun z => GammaD z / SCV.logCoshDamping G.rate z, ?_, ?_⟩
  · have hweight :
        DifferentiableOn ℂ (SCV.logCoshDamping G.rate)
          (osiiAxisPairLogDomain (d := d)) :=
      (SCV.differentiable_logCoshDamping G.rate).differentiableOn
    have hinv :=
      hweight.inv
        (fun z _hz => SCV.logCoshDamping_ne_zero G.rate z)
    simpa [div_eq_mul_inv] using hGammaD.mul hinv
  · intro x
    change
      GammaD (osiiAxisPairLogRealEmbed x) /
          SCV.logCoshDamping G.rate (osiiAxisPairLogRealEmbed x) =
        X.family.realEdge x
    rw [hGammaD_real x]
    rw [OSIIAxisPairFlatCrossData.coshDamped_realEdge]
    exact mul_div_cancel_left₀
      (X.family.realEdge x)
      (SCV.logCoshDamping_ne_zero G.rate
        (osiiAxisPairLogRealEmbed x))

/-- After restoring the damping weight, every holomorphic continuation with
the prescribed real edge is bounded by the original chart constant. -/
theorem norm_holomorphic_realEdge_extension_mul_logCoshDamping_le
    {X : OSIIAxisPairFlatCrossData d}
    (G : OSIIAxisPairFlatCrossCoshGrowthData X)
    (Gamma : (osiiAxisPairIndex d → ℂ) → ℂ)
    (hGamma :
      DifferentiableOn ℂ Gamma
        (osiiAxisPairLogDomain (d := d)))
    (hreal :
      ∀ x : osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairLogRealEmbed x) =
          X.family.realEdge x)
    (z : osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairLogDomain (d := d)) :
    ‖Gamma z * SCV.logCoshDamping G.rate z‖ ≤
      G.chartConstant := by
  apply
    (X.coshDamped G.rate).norm_holomorphic_realEdge_extension_le
      G.realEdgeConstant G.coshDamped_realEdge_bound
      G.chartConstant G.chartConstant_pos
      G.coshDamped_chart_bound
      (fun w => Gamma w * SCV.logCoshDamping G.rate w)
  · exact hGamma.mul
      (SCV.differentiable_logCoshDamping G.rate
        |>.differentiableOn)
  · intro x
    change
      Gamma (osiiAxisPairLogRealEmbed x) *
          SCV.logCoshDamping G.rate
            (osiiAxisPairLogRealEmbed x) =
        (X.coshDamped G.rate).family.realEdge x
    rw [hreal x, X.coshDamped_realEdge]
    exact mul_comm _ _
  · exact hz

end OSIIAxisPairFlatCrossCoshGrowthData

end OSReconstruction
