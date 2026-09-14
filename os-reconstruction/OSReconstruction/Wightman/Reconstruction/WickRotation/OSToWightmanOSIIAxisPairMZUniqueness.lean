/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairParametricBranch
import OSReconstruction.SCV.TotallyRealIdentity










noncomputable section

open Complex Topology
open scoped Classical BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The one-coordinate logarithmic strip used by every axis-pair branch. -/
def osiiAxisPairOpenStrip : Set ℂ :=
  {w : ℂ | |w.im| < Real.pi / 2}

theorem isOpen_osiiAxisPairOpenStrip :
    IsOpen osiiAxisPairOpenStrip := by
  have hcont : Continuous fun w : ℂ => |w.im| :=
    Complex.continuous_im.abs
  simpa [osiiAxisPairOpenStrip] using
    isOpen_lt hcont continuous_const

theorem convex_osiiAxisPairOpenStrip :
    Convex ℝ osiiAxisPairOpenStrip := by
  intro z hz w hw a b ha hb hab
  simp only [osiiAxisPairOpenStrip, Set.mem_setOf_eq] at hz hw ⊢
  have hpoint :
      |(a • z + b • w).im| ≤ a * |z.im| + b * |w.im| := by
    calc
      |(a • z + b • w).im|
          = |a * z.im + b * w.im| := by
              simp [Complex.add_im]
      _ ≤ |a * z.im| + |b * w.im| := abs_add_le _ _
      _ = a * |z.im| + b * |w.im| := by
              rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hweighted :
      a * |z.im| + b * |w.im| < Real.pi / 2 := by
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      simpa [hb1] using hw
    · by_cases hb0 : b = 0
      · subst hb0
        have ha1 : a = 1 := by linarith
        simpa [ha1] using hz
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hzmul : a * |z.im| < a * (Real.pi / 2) :=
          mul_lt_mul_of_pos_left hz ha_pos
        have hwmul : b * |w.im| < b * (Real.pi / 2) :=
          mul_lt_mul_of_pos_left hw hb_pos
        have hcombine :
            a * (Real.pi / 2) + b * (Real.pi / 2) =
              Real.pi / 2 := by
          calc
            a * (Real.pi / 2) + b * (Real.pi / 2) =
                (a + b) * (Real.pi / 2) := by ring
            _ = Real.pi / 2 := by rw [hab]; ring
        linarith
  exact hpoint.trans_lt hweighted

/-- Two holomorphic functions on the axis-pair strip agree everywhere once
they agree on one nonempty open real interval. -/
theorem eqOn_osiiAxisPairOpenStrip_of_differentiableOn_of_realInterval
    (g h : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g osiiAxisPairOpenStrip)
    (hh : DifferentiableOn ℂ h osiiAxisPairOpenStrip)
    (x0 epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hreal : ∀ t : ℝ, |t - x0| < epsilon →
      g (t : ℂ) = h (t : ℂ)) :
    Set.EqOn g h osiiAxisPairOpenStrip := by
  have hsub_analytic :
      AnalyticAt ℂ (fun w => g w - h w) (x0 : ℂ) := by
    exact
      (hg.sub hh).analyticAt
        (isOpen_osiiAxisPairOpenStrip.mem_nhds
          (by simp [osiiAxisPairOpenStrip]; positivity))
  have hlocal_sub :
      (fun w => g w - h w) =ᶠ[nhds (x0 : ℂ)] 0 := by
    apply SCV.analyticAt_eq_zero_of_vanish_on_reals_1d
      hsub_analytic hepsilon
    intro t ht
    simp [hreal t ht]
  have hlocal : g =ᶠ[nhds (x0 : ℂ)] h := by
    filter_upwards [hlocal_sub] with w hw
    exact sub_eq_zero.mp hw
  exact
    (hg.analyticOnNhd isOpen_osiiAxisPairOpenStrip
      ).eqOn_of_preconnected_of_eventuallyEq
      (hh.analyticOnNhd isOpen_osiiAxisPairOpenStrip)
      convex_osiiAxisPairOpenStrip.isPreconnected
      (by simp [osiiAxisPairOpenStrip]; positivity) hlocal

/-- All-real-edge convenience form of strip uniqueness. -/
theorem eqOn_osiiAxisPairOpenStrip_of_differentiableOn_of_real
    (g h : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g osiiAxisPairOpenStrip)
    (hh : DifferentiableOn ℂ h osiiAxisPairOpenStrip)
    (hreal : ∀ t : ℝ, g (t : ℂ) = h (t : ℂ)) :
    Set.EqOn g h osiiAxisPairOpenStrip := by
  apply eqOn_osiiAxisPairOpenStrip_of_differentiableOn_of_realInterval
    g h hg hh 0 1 (by norm_num)
  intro t _ht
  exact hreal t

omit [NeZero d] in
private theorem osiiAxisPair_logCoordinateLine_mem
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d)
    {w : ℂ} (hw : w ∈ osiiAxisPairOpenStrip) :
    Function.update (osiiAxisPairLogRealEmbed x) a w ∈
      osiiAxisPairLogDomain (d := d) := by
  classical
  simp only [osiiAxisPairOpenStrip, Set.mem_setOf_eq] at hw
  simp only [osiiAxisPairLogDomain, Set.mem_setOf_eq]
  calc
    (∑ b : osiiAxisPairIndex d,
        |(Function.update (osiiAxisPairLogRealEmbed x) a w b).im|)
        = |w.im| := by
            rw [Finset.sum_eq_single a]
            · simp [Function.update]
            · intro b _ hba
              simp [Function.update, hba,
                osiiAxisPairLogRealEmbed]
            · simp
    _ < Real.pi / 2 := hw

omit [NeZero d] in
private theorem osiiAxisPair_logCoordinateLine_differentiable
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    Differentiable ℂ
      (fun w : ℂ =>
        Function.update (osiiAxisPairLogRealEmbed x) a w) := by
  rw [differentiable_pi]
  intro b
  by_cases hba : b = a
  · subst b
    simp [Function.update]
  · simp [Function.update, hba]

omit [NeZero d] in
private theorem osiiAxisPair_logCoordinateLine_real
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d)
    (t : ℝ) :
    Function.update (osiiAxisPairLogRealEmbed x) a (t : ℂ) =
      osiiAxisPairLogRealEmbed (Function.update x a t) := by
  ext b
  by_cases hba : b = a
  · subst b
    simp [osiiAxisPairLogRealEmbed, Function.update]
  · simp [osiiAxisPairLogRealEmbed, Function.update, hba]

/-- A holomorphic simultaneous representative with the correct real edge
agrees with the supplied flat-cross branch on every coordinate strip. -/
theorem OSIIAxisPairDirectionalBranchFamily.coordinateLine_eq_of_holomorphic_realEdge
    (F : OSIIAxisPairDirectionalBranchFamily d)
    (Gamma : (osiiAxisPairIndex d → ℂ) → ℂ)
    (hGamma :
      DifferentiableOn ℂ Gamma (osiiAxisPairLogDomain (d := d)))
    (hreal :
      ∀ x : osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairLogRealEmbed x) = F.realEdge x)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    Set.EqOn
      (fun w : ℂ =>
        Gamma (Function.update (osiiAxisPairLogRealEmbed x) a w))
      (fun w : ℂ =>
        F.flatTubeBranch
          (Function.update (osiiAxisPairLogRealEmbed x) a w))
      osiiAxisPairOpenStrip := by
  let line : ℂ → osiiAxisPairIndex d → ℂ :=
    fun w => Function.update (osiiAxisPairLogRealEmbed x) a w
  let g : ℂ → ℂ := fun w => Gamma (line w)
  let h : ℂ → ℂ := fun w => F.flatTubeBranch (line w)
  have hline :
      Differentiable ℂ line := by
    simpa [line] using
      osiiAxisPair_logCoordinateLine_differentiable x a
  have hmaps :
      Set.MapsTo line osiiAxisPairOpenStrip
        (osiiAxisPairLogDomain (d := d)) := by
    intro w hw
    simpa [line] using
      osiiAxisPair_logCoordinateLine_mem x a hw
  have hg :
      DifferentiableOn ℂ g osiiAxisPairOpenStrip := by
    exact hGamma.comp hline.differentiableOn hmaps
  have hh :
      DifferentiableOn ℂ h osiiAxisPairOpenStrip := by
    simpa [h, line, osiiAxisPairOpenStrip] using
      F.flatTubeBranch_coordinate_line_differentiableOn x a
  have hreal_line : ∀ t : ℝ, g (t : ℂ) = h (t : ℂ) := by
    intro t
    have hline_real :=
      osiiAxisPair_logCoordinateLine_real x a t
    calc
      g (t : ℂ) =
          Gamma
            (osiiAxisPairLogRealEmbed (Function.update x a t)) := by
              simp only [g, line]
              rw [hline_real]
      _ = F.realEdge (Function.update x a t) :=
        hreal (Function.update x a t)
      _ = F.flatTubeBranch
          (osiiAxisPairLogRealEmbed (Function.update x a t)) :=
        (F.flatTubeBranch_real_edge (Function.update x a t)).symm
      _ = h (t : ℂ) := by
        simp only [h, line]
        rw [hline_real]
  have heq : Set.EqOn g h osiiAxisPairOpenStrip :=
    eqOn_osiiAxisPairOpenStrip_of_differentiableOn_of_real
      g h hg hh hreal_line
  simpa [g, h, line] using heq

/-- Agreement with the complete flat cross follows from holomorphy and the
common real-edge identity. This removes `agrees_flatCross` from the minimal
Malgrange-Zerner producer contract. -/
theorem OSIIAxisPairDirectionalBranchFamily.eqOn_flatTubeBranch_of_holomorphic_realEdge
    (F : OSIIAxisPairDirectionalBranchFamily d)
    (Gamma : (osiiAxisPairIndex d → ℂ) → ℂ)
    (hGamma :
      DifferentiableOn ℂ Gamma (osiiAxisPairLogDomain (d := d)))
    (hreal :
      ∀ x : osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairLogRealEmbed x) = F.realEdge x) :
    Set.EqOn Gamma F.flatTubeBranch
      (osiiAxisPairFlatLogTubeUnion (d := d)) := by
  intro r hr
  rcases hr with ⟨a, hra, hflat⟩
  let x := osiiAxisPairRealLogBase r
  have hr_line :
      Function.update (osiiAxisPairLogRealEmbed x) a (r a) = r := by
    ext b
    by_cases hba : b = a
    · subst b
      simp [Function.update]
    · apply Complex.ext
      · simp [x, osiiAxisPairRealLogBase, osiiAxisPairLogRealEmbed,
          Function.update, hba]
      · simp [osiiAxisPairLogRealEmbed, Function.update, hba, hflat b hba]
  have hstrip :
      r a ∈ osiiAxisPairOpenStrip := by
    simpa [osiiAxisPairOpenStrip] using hra
  have hline_eq :=
    F.coordinateLine_eq_of_holomorphic_realEdge
      Gamma hGamma hreal x a hstrip
  simpa [hr_line] using hline_eq

end OSReconstruction
