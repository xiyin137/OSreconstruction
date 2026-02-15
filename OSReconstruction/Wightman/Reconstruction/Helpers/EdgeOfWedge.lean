/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Connected.Basic

/-!
# Edge-of-the-Wedge Theorem

This file develops the edge-of-the-wedge theorem of Bogoliubov (1956),
a fundamental result in several complex variables.

## The Theorem (1D case)

If `f₊` is holomorphic on the upper half-plane and `f₋` is holomorphic on the
lower half-plane, and their boundary values agree (as continuous limits) on an
open interval `E ⊂ ℝ`, then there exists a holomorphic function `F` on a complex
neighborhood of `E` that agrees with `f₊` above and `f₋` below.

## Proof Strategy

We use the **Morera / removable singularity** approach:

1. **Glue**: Define `F(z) = f₊(z)` for `Im z > 0`, `F(z) = f₋(z)` for `Im z < 0`,
   and `F(x) = bv(x)` (the common boundary value) for `x ∈ E`.
2. **Continuity**: `F` is continuous on `{Im z > 0} ∪ E ∪ {Im z < 0}` by the
   boundary value condition.
3. **Holomorphicity**: Apply the removable singularity theorem or Morera's theorem
   to conclude `F` is holomorphic on the combined domain.

## Multi-dimensional Generalization

The multi-dimensional version for tube domains with cone `C`:
- `T₊ = ℝⁿ + iC` and `T₋ = ℝⁿ - iC`
- Matching boundary values on `E ⊂ ℝⁿ`
- Conclusion: holomorphic extension to a complex neighborhood of `E`

This is proved by induction on the number of variables, applying the 1D result
in each variable while keeping the others fixed.

## References

* Bogoliubov, "Introduction to Axiomatic Quantum Field Theory" (1956)
* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 2
* Epstein, "Generalization of the Edge-of-the-Wedge Theorem" (1960)
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped Interval

/-! ### 1D Edge-of-the-Wedge -/

/-- The upper half-plane: {z ∈ ℂ : Im z > 0}. -/
def EOW.UpperHalfPlane : Set ℂ := { z | z.im > 0 }

/-- The lower half-plane: {z ∈ ℂ : Im z < 0}. -/
def EOW.LowerHalfPlane : Set ℂ := { z | z.im < 0 }

/-- The real line viewed as a subset of ℂ. -/
def EOW.RealLine : Set ℂ := { z | z.im = 0 }

/-- Embed a real interval into ℂ. -/
def EOW.realInterval (a b : ℝ) : Set ℂ := { z | z.im = 0 ∧ a < z.re ∧ z.re < b }

theorem EOW.upperHalfPlane_isOpen : IsOpen EOW.UpperHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_im

theorem EOW.lowerHalfPlane_isOpen : IsOpen EOW.LowerHalfPlane := by
  exact isOpen_lt Complex.continuous_im continuous_const

/-- The glued function: f₊ on the upper half-plane, f₋ on the lower half-plane,
    and the common boundary value bv on the real interval. -/
def gluedFunction (f_plus f_minus : ℂ → ℂ) (bv : ℝ → ℂ) : ℂ → ℂ :=
  fun z =>
    if z.im > 0 then f_plus z
    else if z.im < 0 then f_minus z
    else bv z.re

/-- The glued function agrees with f₊ on the upper half-plane. -/
theorem gluedFunction_upper {f_plus f_minus : ℂ → ℂ} {bv : ℝ → ℂ} {z : ℂ}
    (hz : z.im > 0) : gluedFunction f_plus f_minus bv z = f_plus z := by
  simp [gluedFunction, hz]

/-- The glued function agrees with f₋ on the lower half-plane. -/
theorem gluedFunction_lower {f_plus f_minus : ℂ → ℂ} {bv : ℝ → ℂ} {z : ℂ}
    (hz : z.im < 0) : gluedFunction f_plus f_minus bv z = f_minus z := by
  simp [gluedFunction, hz, not_lt.mpr (le_of_lt hz)]

/-- The glued function agrees with bv on the real line. -/
theorem gluedFunction_real {f_plus f_minus : ℂ → ℂ} {bv : ℝ → ℂ} {z : ℂ}
    (hz : z.im = 0) : gluedFunction f_plus f_minus bv z = bv z.re := by
  simp [gluedFunction, hz]

/-- The 1D edge-of-the-wedge theorem.

    If `f₊` is holomorphic on the upper half-plane and `f₋` is holomorphic on
    the lower half-plane, and they have continuous boundary values that agree
    on an open interval `(a, b)`, then there exists a holomorphic function `F`
    on an open set containing `(a, b)` that agrees with `f₊` above and `f₋` below.

    The hypotheses require:
    - Holomorphic boundary values from above and below that match on (a,b)
    - Boundary values continuous along the real interval (hbv_cont) -/
theorem edge_of_the_wedge_1d (a b : ℝ) (hab : a < b)
    (f_plus f_minus : ℂ → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus EOW.UpperHalfPlane)
    (hf_minus : DifferentiableOn ℂ f_minus EOW.LowerHalfPlane)
    -- Continuous boundary values from above
    (hcont_plus : ∀ x : ℝ, a < x → x < b →
      Filter.Tendsto f_plus (nhdsWithin (x : ℂ) EOW.UpperHalfPlane) (nhds (f_plus x)))
    -- Continuous boundary values from below
    (hcont_minus : ∀ x : ℝ, a < x → x < b →
      Filter.Tendsto f_minus (nhdsWithin (x : ℂ) EOW.LowerHalfPlane) (nhds (f_minus x)))
    -- Boundary values match on the interval
    (hmatch : ∀ x : ℝ, a < x → x < b → f_plus x = f_minus x)
    -- Boundary values are continuous along the real interval
    (hbv_cont : ∀ x₀ : ℝ, a < x₀ → x₀ < b →
      Filter.Tendsto f_plus (nhdsWithin (x₀ : ℂ) {c : ℂ | c.im = 0})
        (nhds (f_plus x₀))) :
    ∃ (U : Set ℂ) (F : ℂ → ℂ),
      IsOpen U ∧
      -- U contains the real interval
      (∀ x : ℝ, a < x → x < b → (x : ℂ) ∈ U) ∧
      -- F is holomorphic on U
      DifferentiableOn ℂ F U ∧
      -- F agrees with f₊ on U ∩ upper half-plane
      (∀ z ∈ U ∩ EOW.UpperHalfPlane, F z = f_plus z) ∧
      -- F agrees with f₋ on U ∩ lower half-plane
      (∀ z ∈ U ∩ EOW.LowerHalfPlane, F z = f_minus z) := by
  -- Step 1: Define the ball
  let mid : ℂ := ((a + b) / 2 : ℝ)
  let rad : ℝ := (b - a) / 2
  have hrad : rad > 0 := by show (b - a) / 2 > 0; linarith
  -- Step 2: Define the glued function
  let F : ℂ → ℂ := fun z =>
    if z.im > 0 then f_plus z
    else if z.im < 0 then f_minus z
    else f_plus z  -- on the real line, both agree by hmatch
  -- Helper: real points of the ball are in (a,b)
  have ball_real_in_interval : ∀ z : ℂ, z ∈ Metric.ball mid rad → z.im = 0 →
      a < z.re ∧ z.re < b := by
    intro z hz hzim
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hsub : z - mid = ((z.re - (a + b) / 2 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [mid]
    rw [hsub, hzim, Complex.ofReal_zero, zero_mul, add_zero] at hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt] at hz
    have : rad = (b - a) / 2 := rfl
    exact ⟨by linarith, by linarith⟩
  -- Helper: z = ↑z.re when z.im = 0
  have real_eq : ∀ z : ℂ, z.im = 0 → (z.re : ℂ) = z := by
    intro z hz; exact Complex.ext (by simp) (by simp [hz])
  -- Step 3: Prove ContinuousOn F ball
  have hFcont : ContinuousOn F (Metric.ball mid rad) := by
    intro z hz
    by_cases hzim : z.im = 0
    · -- z is on the real line: use filter decomposition
      obtain ⟨hza, hzb⟩ := ball_real_in_interval z hz hzim
      -- F(z) = f_plus(z)
      have hFz : F z = f_plus z := by
        simp only [F]; split_ifs with h1 h2 <;> [linarith; linarith; rfl]
      -- Key: ↑z.re = z when z.im = 0
      have hzeq : (z.re : ℂ) = z := real_eq z hzim
      -- Convert hypotheses to use z instead of ↑z.re
      have hcp : Tendsto f_plus (𝓝[EOW.UpperHalfPlane] z) (nhds (f_plus z)) := by
        have := hcont_plus z.re hza hzb; rwa [hzeq] at this
      have hcm : Tendsto f_minus (𝓝[EOW.LowerHalfPlane] z) (nhds (f_minus z)) := by
        have := hcont_minus z.re hza hzb; rwa [hzeq] at this
      have hbvc : Tendsto f_plus (𝓝[{c | c.im = 0}] z) (nhds (f_plus z)) := by
        have := hbv_cont z.re hza hzb; rwa [hzeq] at this
      have hmz : f_plus z = f_minus z := by rw [← hzeq]; exact hmatch z.re hza hzb
      rw [ContinuousWithinAt]
      rw [nhdsWithin_eq_nhds.mpr (Metric.isOpen_ball.mem_nhds hz)]
      -- Decompose nhds z = nhdsWithin z {im > 0} ⊔ nhdsWithin z {im ≤ 0}
      have huniv : (Set.univ : Set ℂ) = {c | c.im > 0} ∪ {c | c.im ≤ 0} := by
        ext c; simp only [mem_univ, mem_union, mem_setOf_eq, true_iff]
        exact lt_or_ge 0 c.im
      rw [nhds_eq_nhdsWithin_sup_nhdsWithin z huniv, hFz]
      apply Filter.Tendsto.sup
      · -- From above: F =ᶠ f_plus on {im > 0}
        exact hcp.congr' (by
          filter_upwards [self_mem_nhdsWithin] with w (hw : w.im > 0)
          show f_plus w = F w
          simp only [F, hw, ite_true])
      · -- From {im ≤ 0}: split into {im < 0} ∪ {im = 0}
        rw [show ({c : ℂ | c.im ≤ 0} : Set ℂ) = {c | c.im < 0} ∪ {c | c.im = 0} from by
          ext c; simp only [mem_setOf_eq, mem_union]; exact le_iff_lt_or_eq]
        rw [nhdsWithin_union]
        apply Filter.Tendsto.sup
        · -- From below: F =ᶠ f_minus, use matching
          rw [hmz]
          exact hcm.congr' (by
            filter_upwards [self_mem_nhdsWithin] with w (hw : w.im < 0)
            show f_minus w = F w
            simp only [F]; split_ifs with h1 <;> [linarith; rfl])
        · -- Along real line: F =ᶠ f_plus
          exact hbvc.congr' (by
            filter_upwards [self_mem_nhdsWithin] with w (hw : w.im = 0)
            show f_plus w = F w
            simp only [F]; split_ifs with h1 h2 <;> [linarith; linarith; rfl])
    · -- z not on real line: F is locally f_plus or f_minus
      rcases lt_or_gt_of_ne hzim with hlt | hgt
      · -- Im z < 0: F = f_minus near z
        exact ((hf_minus.differentiableAt (EOW.lowerHalfPlane_isOpen.mem_nhds hlt)).continuousAt.congr
          (by filter_upwards [EOW.lowerHalfPlane_isOpen.mem_nhds hlt] with w (hw : w.im < 0)
              simp only [F]; split_ifs with h1 <;> [linarith; rfl])).continuousWithinAt
      · -- Im z > 0: F = f_plus near z
        exact ((hf_plus.differentiableAt (EOW.upperHalfPlane_isOpen.mem_nhds hgt)).continuousAt.congr
          (by filter_upwards [EOW.upperHalfPlane_isOpen.mem_nhds hgt] with w (hw : w.im > 0)
              simp only [F, hw, ite_true])).continuousWithinAt
  -- Step 4: Prove IsConservativeOn F ball
  -- Helper: F = f_plus when im > 0, F = f_minus when im < 0
  have hFup : ∀ c : ℂ, c.im > 0 → F c = f_plus c := fun c hc => if_pos hc
  have hFdn : ∀ c : ℂ, c.im < 0 → F c = f_minus c := by
    intro c hc; simp only [F, show ¬(c.im > 0) from by linarith, ite_false, hc, ite_true]
  -- Helper: DifferentiableAt for points off the real line
  have hFdiff_upper : ∀ c : ℂ, c.im > 0 → DifferentiableAt ℂ F c := by
    intro c hc
    exact ((show f_plus =ᶠ[𝓝 c] F from by
      filter_upwards [EOW.upperHalfPlane_isOpen.mem_nhds hc] with w hw
      exact (hFup w hw).symm).differentiableAt_iff).mp
        (hf_plus.differentiableAt (EOW.upperHalfPlane_isOpen.mem_nhds hc))
  have hFdiff_lower : ∀ c : ℂ, c.im < 0 → DifferentiableAt ℂ F c := by
    intro c hc
    exact ((show f_minus =ᶠ[𝓝 c] F from by
      filter_upwards [EOW.lowerHalfPlane_isOpen.mem_nhds hc] with w hw
      exact (hFdn w hw).symm).differentiableAt_iff).mp
        (hf_minus.differentiableAt (EOW.lowerHalfPlane_isOpen.mem_nhds hc))
  have hFcons : IsConservativeOn F (Metric.ball mid rad) := by
    intro z w hrect
    apply eq_neg_of_add_eq_zero_left
    rw [wedgeIntegral_add_wedgeIntegral_eq]
    -- Goal: boundary integral = 0
    by_cases hcross : min z.im w.im < 0 ∧ 0 < max z.im w.im
    · -- CROSSING: rectangle straddles the real line, split at im = 0
      obtain ⟨hmin_neg, hmax_pos⟩ := hcross
      let z₀ : ℂ := ⟨z.re, 0⟩
      let w₀ : ℂ := ⟨w.re, 0⟩
      -- 0 ∈ [[z.im, w.im]] since one is negative and the other positive
      have h0_mem : (0 : ℝ) ∈ [[z.im, w.im]] := by
        rcases le_total z.im w.im with h | h
        · rw [Set.mem_uIcc]; left
          exact ⟨le_of_lt (by rwa [min_eq_left h] at hmin_neg),
                 le_of_lt (by rwa [max_eq_right h] at hmax_pos)⟩
        · rw [Set.mem_uIcc]; right
          exact ⟨le_of_lt (by rwa [min_eq_right h] at hmin_neg),
                 le_of_lt (by rwa [max_eq_left h] at hmax_pos)⟩
      -- z.im and w.im are both nonzero in crossing case
      have hzim_ne : z.im ≠ 0 := by
        intro heq; rw [heq] at hmin_neg hmax_pos
        rcases le_or_gt w.im 0 with h | h
        · linarith [max_eq_left h (a := (0 : ℝ))]
        · linarith [min_eq_left (le_of_lt h) (a := (0 : ℝ))]
      have hwim_ne : w.im ≠ 0 := by
        intro heq; rw [heq] at hmin_neg hmax_pos
        rcases le_or_gt z.im 0 with h | h
        · linarith [max_eq_right h (a := z.im) (b := (0 : ℝ))]
        · linarith [min_eq_right (le_of_lt h) (a := z.im) (b := (0 : ℝ))]
      -- ContinuousOn for sub-rectangles (subsets of Rectangle z w ⊆ ball)
      have hcont_sub1 : ContinuousOn F ([[z.re, w.re]] ×ℂ [[z.im, (0 : ℝ)]]) :=
        hFcont.mono (fun c hc => hrect (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
          rw [mem_reProdIm] at hc ⊢
          exact ⟨hc.1, Set.uIcc_subset_uIcc_left h0_mem hc.2⟩))
      have hcont_sub2 : ContinuousOn F ([[z.re, w.re]] ×ℂ [[(0 : ℝ), w.im]]) :=
        hFcont.mono (fun c hc => hrect (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
          rw [mem_reProdIm] at hc ⊢
          exact ⟨hc.1, Set.uIcc_subset_uIcc_right h0_mem hc.2⟩))
      -- DifferentiableOn for sub-rectangles: open interior is off the real line
      have hdiff_sub1 : DifferentiableOn ℂ F
          (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im 0) (max z.im 0)) := by
        intro c hc; rw [mem_reProdIm] at hc
        have hcim := mem_Ioo.mp hc.2
        rcases lt_or_gt_of_ne hzim_ne with hz | hz
        · -- z.im < 0: Ioo = (z.im, 0), so c.im < 0
          have : c.im < 0 := by
            have h2 := hcim.2; rwa [max_eq_right (le_of_lt hz)] at h2
          exact (hFdiff_lower c this).differentiableWithinAt
        · -- z.im > 0: Ioo = (0, z.im), so c.im > 0
          have : c.im > 0 := by
            have h1 := hcim.1; rwa [min_eq_right (le_of_lt hz)] at h1
          exact (hFdiff_upper c this).differentiableWithinAt
      have hdiff_sub2 : DifferentiableOn ℂ F
          (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min 0 w.im) (max 0 w.im)) := by
        intro c hc; rw [mem_reProdIm] at hc
        have hcim := mem_Ioo.mp hc.2
        rcases lt_or_gt_of_ne hwim_ne with hw | hw
        · -- w.im < 0: Ioo = (w.im, 0), so c.im < 0
          have : c.im < 0 := by
            have h2 := hcim.2; rwa [max_eq_left (le_of_lt hw)] at h2
          exact (hFdiff_lower c this).differentiableWithinAt
        · -- w.im > 0: Ioo = (0, w.im), so c.im > 0
          have : c.im > 0 := by
            have h1 := hcim.1; rwa [min_eq_left (le_of_lt hw)] at h1
          exact (hFdiff_upper c this).differentiableWithinAt
      -- Sub-rectangle Cauchy-Goursat
      have h_sub1 := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        F z w₀ (by convert hcont_sub1 using 2) (by convert hdiff_sub1 using 2)
      have h_sub2 := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        F z₀ w (by convert hcont_sub2 using 2) (by convert hdiff_sub2 using 2)
      -- Simplify z₀, w₀ fields
      simp only [show (z₀.im : ℝ) = 0 from rfl, show (w₀.im : ℝ) = 0 from rfl,
        show re z₀ = z.re from rfl, show re w₀ = w.re from rfl,
        Complex.ofReal_zero, zero_mul, add_zero] at h_sub1 h_sub2
      simp only [smul_eq_mul] at h_sub1 h_sub2 ⊢
      -- IntervalIntegrable for y-integral splitting at 0
      have hint : ∀ (r : ℝ), r ∈ [[z.re, w.re]] →
          ∀ a' b', [[a', b']] ⊆ [[z.im, w.im]] →
          IntervalIntegrable (fun y => F (↑r + ↑y * I)) volume a' b' := by
        intro r hr a' b' hab'
        apply ContinuousOn.intervalIntegrable
        apply hFcont.comp ((continuousOn_const).add
          ((Complex.continuous_ofReal.continuousOn).mul continuousOn_const))
        intro y hy
        apply hrect
        show (↑r + ↑(y : ℝ) * I) ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]
        rw [mem_reProdIm]
        constructor
        · simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]; exact hr
        · simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]; exact hab' hy
      -- Specific integrability instances
      have hw_mem : w.re ∈ [[z.re, w.re]] := Set.right_mem_uIcc
      have hz_mem : z.re ∈ [[z.re, w.re]] := Set.left_mem_uIcc
      have hsub1 : [[z.im, (0 : ℝ)]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc_left h0_mem
      have hsub2 : [[(0 : ℝ), w.im]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc_right h0_mem
      -- Split y-integrals at 0
      rw [← integral_add_adjacent_intervals (hint w.re hw_mem z.im 0 hsub1)
            (hint w.re hw_mem 0 w.im hsub2),
          ← integral_add_adjacent_intervals (hint z.re hz_mem z.im 0 hsub1)
            (hint z.re hz_mem 0 w.im hsub2)]
      linear_combination h_sub1 + h_sub2
    · -- NON-CROSSING: F holomorphic on open interior, direct Cauchy-Goursat
      push_neg at hcross
      exact integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F z w
        (hFcont.mono hrect) (by
          intro c hc; rw [mem_reProdIm] at hc
          rcases le_or_gt 0 (min z.im w.im) with hge | hlt
          · exact (hFdiff_upper c
              (lt_of_le_of_lt hge (mem_Ioo.mp hc.2).1)).differentiableWithinAt
          · exact (hFdiff_lower c (lt_of_lt_of_le (mem_Ioo.mp hc.2).2
              (hcross hlt))).differentiableWithinAt)
  -- Step 5: Apply Morera's theorem
  refine ⟨Metric.ball mid rad, F, Metric.isOpen_ball, ?_, ?_, ?_, ?_⟩
  · -- The interval (a,b) is contained in the ball
    intro x hax hxb
    show dist (x : ℂ) mid < rad
    rw [Complex.dist_eq]
    have hsub : (↑x - mid) = ((x - (a + b) / 2 : ℝ) : ℂ) := by simp [mid]
    rw [hsub, Complex.norm_real]
    show |x - (a + b) / 2| < (b - a) / 2
    rw [abs_lt]; constructor <;> linarith
  · -- F is holomorphic on the ball (by Morera)
    exact (isConservativeOn_and_continuousOn_iff_isDifferentiableOn Metric.isOpen_ball).mp
      ⟨hFcons, hFcont⟩
  · -- F agrees with f₊ on U ∩ upper half-plane
    intro z ⟨_, (hz : z.im > 0)⟩
    exact if_pos hz
  · -- F agrees with f₋ on U ∩ lower half-plane
    intro z ⟨_, (hz : z.im < 0)⟩
    show F z = f_minus z
    have h1 : ¬(z.im > 0) := by linarith
    simp only [F, h1, ite_false, hz, ite_true]

/-! ### Multi-dimensional edge-of-the-wedge via 1D slicing

The multi-dimensional edge-of-the-wedge theorem is proved by induction on dimension.
In each step, we fix all but one complex variable and apply the 1D result.

For the BHW application, we need the result for tube domains with the forward
light cone as the cone C. -/

/-- A tube domain in ℂⁿ: points whose imaginary part lies in an open cone C. -/
def TubeDomainSCV {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℂ) :=
  { z | (fun i => (z i).im) ∈ C }

/-- The opposite tube domain (cone -C). -/
theorem tubeDomain_neg {m : ℕ} (C : Set (Fin m → ℝ)) :
    TubeDomainSCV (Neg.neg '' C) =
    { z : Fin m → ℂ | (fun i => -(z i).im) ∈ C } := by
  ext z
  simp only [TubeDomainSCV, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    have : ∀ i, (z i).im = -y i := by
      intro i; have := congr_fun heq i; simp at this; linarith
    convert hy using 1; ext i; rw [this, neg_neg]
  · intro h
    exact ⟨fun i => -(z i).im, h, by ext i; simp⟩

/-- The identity theorem for holomorphic functions on a connected open set:
    if two holomorphic functions agree on a set with an accumulation point,
    they agree on the entire connected component.

    This is a direct consequence of the Mathlib identity theorem. -/
theorem identity_theorem_connected {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    (f g : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U)
    (hagree : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) :
    EqOn f g U := by
  have hfU : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have hgU : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hU
  exact hfU.eqOn_of_preconnected_of_frequently_eq hgU hconn.isPreconnected hz₀ hagree

/-- Translation invariance of holomorphic functions via the identity theorem.

    If `f` is holomorphic on a connected open set `U` that is translation-invariant
    (U + a ⊆ U), and `f(z + a) = f(z)` on a subset with a limit point, then
    `f(z + a) = f(z)` on all of `U`. -/
theorem holomorphic_translation_invariant {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (a : ℂ)
    (htransl : ∀ z ∈ U, z + a ∈ U)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U)
    (hagree : ∃ᶠ z in 𝓝[≠] z₀, f (z + a) = f z) :
    EqOn (fun z => f (z + a)) f U := by
  apply identity_theorem_connected hU hconn
  · exact (hf.comp (differentiable_id.add_const a).differentiableOn
      (fun z hz => htransl z hz))
  · exact hf
  · exact hz₀
  · exact hagree

end
