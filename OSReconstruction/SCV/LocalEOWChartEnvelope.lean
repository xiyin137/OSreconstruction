/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalEOWSideCone

/-!
# One-Chart Local EOW Envelope Geometry

This file starts the one-chart distributional EOW envelope layer with the
small chart-side geometry needed by the recovery theorem.  The strict side
balls are coordinate objects, but their images under `localEOWChart` have
original imaginary parts transported by `localEOWRealLinearPart ys`; this is
the chart-linear correction needed before the real-mollifier kernel route.
-/

noncomputable section

open Complex Metric Set

namespace SCV

variable {m : ℕ}

/-- Strict positive chart-side ball used by the local recovery theorem. -/
def StrictPositiveImagBall (R : ℝ) : Set (ComplexChartSpace m) :=
  Metric.ball 0 R ∩ {w | ∀ j, 0 < (w j).im}

/-- Strict negative chart-side ball used by the local recovery theorem. -/
def StrictNegativeImagBall (R : ℝ) : Set (ComplexChartSpace m) :=
  Metric.ball 0 R ∩ {w | ∀ j, (w j).im < 0}

theorem isOpen_StrictPositiveImagBall (R : ℝ) :
    IsOpen (StrictPositiveImagBall (m := m) R) := by
  dsimp [StrictPositiveImagBall]
  refine Metric.isOpen_ball.inter ?_
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const
      (Complex.continuous_im.comp (continuous_apply j))

theorem isOpen_StrictNegativeImagBall (R : ℝ) :
    IsOpen (StrictNegativeImagBall (m := m) R) := by
  dsimp [StrictNegativeImagBall]
  refine Metric.isOpen_ball.inter ?_
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (Complex.continuous_im.comp (continuous_apply j))
      continuous_const

/-- Coordinatewise imaginary part is norm-controlled by the complex chart
norm. -/
theorem norm_complexChart_im_le (w : ComplexChartSpace m) :
    ‖(fun j : Fin m => (w j).im)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro j
  rw [Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm (w j)).trans (norm_le_pi_norm w j)

/-- Coordinatewise real part is norm-controlled by the complex chart norm. -/
theorem norm_complexChart_re_le (w : ComplexChartSpace m) :
    ‖(fun j : Fin m => (w j).re)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro j
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm (w j)).trans (norm_le_pi_norm w j)

theorem norm_complexChart_im_lt_of_mem_ball {R : ℝ}
    {w : ComplexChartSpace m} (hw : w ∈ Metric.ball 0 R) :
    ‖(fun j : Fin m => (w j).im)‖ < R := by
  rw [Metric.mem_ball, dist_zero_right] at hw
  exact lt_of_le_of_lt (norm_complexChart_im_le w) hw

theorem norm_complexChart_re_lt_of_mem_ball {R : ℝ}
    {w : ComplexChartSpace m} (hw : w ∈ Metric.ball 0 R) :
    ‖(fun j : Fin m => (w j).re)‖ < R := by
  rw [Metric.mem_ball, dist_zero_right] at hw
  exact lt_of_le_of_lt (norm_complexChart_re_le w) hw

/-- The imaginary part of the affine local EOW chart is the real-linear chart
part applied to the coordinate imaginary vector. -/
theorem localEOWChart_im_eq_realLinearPart_im
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (w : ComplexChartSpace m) :
    (fun i => (localEOWChart x0 ys w i).im) =
      localEOWRealLinearPart ys (fun j => (w j).im) := by
  ext i
  simp [localEOWChart_im, localEOWRealLinearPart]

/-- Strict positive chart imaginary coordinates map to the local side cone
through the real-linear part of the EOW chart. -/
theorem localEOWRealLinearPart_im_mem_sideCone_of_strictPositive
    (hm : 0 < m)
    (ys : Fin m → Fin m → ℝ) {ε R : ℝ} (hε : 0 < ε)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    localEOWRealLinearPart ys (fun j => (w j).im) ∈
      localEOWSideCone ys ε := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have him_nonneg : ∀ j, 0 ≤ (w j).im := fun j => (hw.2 j).le
  have him_sum_pos : 0 < ∑ j, (w j).im :=
    Finset.sum_pos (fun j _ => hw.2 j) Finset.univ_nonempty
  exact localEOWRealLinearPart_mem_localEOWSideCone ys hε
    him_nonneg him_sum_pos

/-- Strict negative chart imaginary coordinates map to the negative image of
the local side cone. -/
theorem localEOWRealLinearPart_im_mem_neg_sideCone_of_strictNegative
    (hm : 0 < m)
    (ys : Fin m → Fin m → ℝ) {ε R : ℝ} (hε : 0 < ε)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    localEOWRealLinearPart ys (fun j => (w j).im) ∈
      Neg.neg '' localEOWSideCone ys ε := by
  let v : Fin m → ℝ := fun j => - (w j).im
  have hv_nonneg : ∀ j, 0 ≤ v j := fun j => by
    dsimp [v]
    exact (neg_pos.mpr (hw.2 j)).le
  have hv_sum_pos : 0 < ∑ j, v j := by
    haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    exact Finset.sum_pos (fun j _ => neg_pos.mpr (hw.2 j))
      Finset.univ_nonempty
  refine ⟨localEOWRealLinearPart ys v,
    localEOWRealLinearPart_mem_localEOWSideCone ys hε hv_nonneg
      hv_sum_pos, ?_⟩
  have hv_eq : v = -(fun j : Fin m => (w j).im) := by
    ext j
    rfl
  calc
    -localEOWRealLinearPart ys v =
        -localEOWRealLinearPart ys (-(fun j : Fin m => (w j).im)) := by
          rw [hv_eq]
    _ = localEOWRealLinearPart ys (fun j : Fin m => (w j).im) := by
          rw [localEOWRealLinearPart_neg]
          simp

/-- A strict positive chart-side ball small enough in coordinates maps into a
truncated local side cone. -/
theorem localEOWRealLinearPart_im_mem_truncatedSideCone_of_strictPositive
    (hm : 0 < m)
    (ys : Fin m → Fin m → ℝ) {ε R rside δside : ℝ}
    (hε : 0 < ε)
    (hδside :
      ∀ v : Fin m → ℝ, ‖v‖ < δside →
        ‖localEOWRealLinearPart ys v‖ < rside)
    (hRδ : R ≤ δside)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    localEOWRealLinearPart ys (fun j => (w j).im) ∈
      localEOWSideCone ys ε ∩ Metric.ball 0 rside := by
  constructor
  · exact localEOWRealLinearPart_im_mem_sideCone_of_strictPositive
      hm ys hε hw
  · rw [Metric.mem_ball, dist_zero_right]
    exact hδside (fun j => (w j).im)
      (lt_of_lt_of_le (norm_complexChart_im_lt_of_mem_ball hw.1) hRδ)

/-- A strict negative chart-side ball small enough in coordinates maps into the
negative image of a truncated local side cone. -/
theorem localEOWRealLinearPart_im_mem_neg_truncatedSideCone_of_strictNegative
    (hm : 0 < m)
    (ys : Fin m → Fin m → ℝ) {ε R rside δside : ℝ}
    (hε : 0 < ε)
    (hδside :
      ∀ v : Fin m → ℝ, ‖v‖ < δside →
        ‖localEOWRealLinearPart ys v‖ < rside)
    (hRδ : R ≤ δside)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    localEOWRealLinearPart ys (fun j => (w j).im) ∈
      Neg.neg '' (localEOWSideCone ys ε ∩ Metric.ball 0 rside) := by
  let v : Fin m → ℝ := fun j => - (w j).im
  have hv_nonneg : ∀ j, 0 ≤ v j := fun j => by
    dsimp [v]
    exact (neg_pos.mpr (hw.2 j)).le
  have hv_sum_pos : 0 < ∑ j, v j := by
    haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    exact Finset.sum_pos (fun j _ => neg_pos.mpr (hw.2 j))
      Finset.univ_nonempty
  have hv_norm_lt : ‖v‖ < δside := by
    have him_lt : ‖(fun j : Fin m => (w j).im)‖ < R :=
      norm_complexChart_im_lt_of_mem_ball hw.1
    calc
      ‖v‖ = ‖(fun j : Fin m => (w j).im)‖ := by
        dsimp [v]
        rw [show (fun j : Fin m => -(w j).im) =
            -(fun j : Fin m => (w j).im) by
          ext j
          rfl]
        exact norm_neg (fun j : Fin m => (w j).im)
      _ < δside := lt_of_lt_of_le him_lt hRδ
  refine ⟨localEOWRealLinearPart ys v, ?_, ?_⟩
  · constructor
    · exact localEOWRealLinearPart_mem_localEOWSideCone ys hε
        hv_nonneg hv_sum_pos
    · rw [Metric.mem_ball, dist_zero_right]
      exact hδside v hv_norm_lt
  · have hv_eq : v = -(fun j : Fin m => (w j).im) := by
      ext j
      rfl
    calc
      -localEOWRealLinearPart ys v =
          -localEOWRealLinearPart ys (-(fun j : Fin m => (w j).im)) := by
            rw [hv_eq]
      _ = localEOWRealLinearPart ys (fun j : Fin m => (w j).im) := by
            rw [localEOWRealLinearPart_neg]
            simp

/-- The local EOW chart sends a small strict positive coordinate side ball into
the tube over the truncated original side cone. -/
theorem localEOWChart_mem_TubeDomain_truncatedSideCone_of_strictPositive
    (hm : 0 < m)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ε R rside δside : ℝ}
    (hε : 0 < ε)
    (hδside :
      ∀ v : Fin m → ℝ, ‖v‖ < δside →
        ‖localEOWRealLinearPart ys v‖ < rside)
    (hRδ : R ≤ δside)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    localEOWChart x0 ys w ∈
      TubeDomain (localEOWSideCone ys ε ∩ Metric.ball 0 rside) := by
  change (fun i => (localEOWChart x0 ys w i).im) ∈
    localEOWSideCone ys ε ∩ Metric.ball 0 rside
  rw [localEOWChart_im_eq_realLinearPart_im]
  exact localEOWRealLinearPart_im_mem_truncatedSideCone_of_strictPositive
    hm ys hε hδside hRδ hw

/-- The local EOW chart sends a small strict negative coordinate side ball into
the tube over the negative truncated original side cone. -/
theorem localEOWChart_mem_TubeDomain_neg_truncatedSideCone_of_strictNegative
    (hm : 0 < m)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ε R rside δside : ℝ}
    (hε : 0 < ε)
    (hδside :
      ∀ v : Fin m → ℝ, ‖v‖ < δside →
        ‖localEOWRealLinearPart ys v‖ < rside)
    (hRδ : R ≤ δside)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    localEOWChart x0 ys w ∈
      TubeDomain (Neg.neg '' (localEOWSideCone ys ε ∩
        Metric.ball 0 rside)) := by
  change (fun i => (localEOWChart x0 ys w i).im) ∈
    Neg.neg '' (localEOWSideCone ys ε ∩ Metric.ball 0 rside)
  rw [localEOWChart_im_eq_realLinearPart_im]
  exact localEOWRealLinearPart_im_mem_neg_truncatedSideCone_of_strictNegative
    hm ys hε hδside hRδ hw

end SCV
