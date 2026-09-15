/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Real.Pi.Bounds
import OSReconstruction.SCV.StripCompactification










noncomputable section

open Complex Set Topology

namespace OSReconstruction.SCV

/-- The inverse target budget is strictly smaller than the compactification
radius. -/
theorem StripCompactificationParameters.targetBudget_lt_radius
    {S rho : Real}
    (P : StripCompactificationParameters S rho) :
    S < P.radius := by
  have hS :
      S < (Real.pi / 2) * P.slope :=
    (div_lt_iff₀ P.slope_pos).mp P.inverse_budget
  have hpi : Real.pi / 2 < 2 := by
    linarith [Real.pi_lt_four]
  have hmiddle :
      (Real.pi / 2) * P.slope <
        2 * P.slope :=
    mul_lt_mul_of_pos_right hpi P.slope_pos
  exact hS.trans (hmiddle.trans P.two_mul_slope_lt_radius)

/-- The principal complex arctangent is holomorphic on the open unit disc. -/
theorem differentiableOn_complex_arctan_unitBall :
    DifferentiableOn Complex Complex.arctan
      (Metric.ball (0 : Complex) 1) := by
  intro z hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  let A : Complex -> Complex :=
    fun w =>
      -I / 2 *
        (Complex.log (1 + w * I) -
          Complex.log (1 - w * I))
  have hplus_mem :
      1 + z * I ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one
      (z := z * I) (by simpa using hz_norm)
  have hminus_mem :
      1 - z * I ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one
      (z := -(z * I)) (by simpa using hz_norm)
  have hplus :
      DifferentiableAt Complex
        (fun w : Complex => Complex.log (1 + w * I)) z := by
    have hinner :
        DifferentiableAt Complex
          (fun w : Complex => 1 + w * I) z :=
      (differentiableAt_const 1).add
        (differentiableAt_id.mul
          (differentiableAt_const I))
    change DifferentiableAt Complex
      (Complex.log ∘ fun w : Complex => 1 + w * I) z
    exact DifferentiableAt.comp z
      (Complex.differentiableAt_log hplus_mem) hinner
  have hminus :
      DifferentiableAt Complex
        (fun w : Complex => Complex.log (1 - w * I)) z := by
    have hinner :
        DifferentiableAt Complex
          (fun w : Complex => 1 - w * I) z :=
      (differentiableAt_const 1).sub
        (differentiableAt_id.mul
          (differentiableAt_const I))
    change DifferentiableAt Complex
      (Complex.log ∘ fun w : Complex => 1 - w * I) z
    exact DifferentiableAt.comp z
      (Complex.differentiableAt_log hminus_mem) hinner
  have hA : DifferentiableAt Complex A z := by
    dsimp [A]
    exact
      (differentiableAt_const (-I / 2)).mul
        (hplus.sub hminus)
  have heq :
      ∀ w ∈ Metric.ball (0 : Complex) 1,
        Complex.arctan w = A w := by
    intro w hw
    have hw_norm : ‖w‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hw
    rw [Complex.arctan]
    rw [← Complex.hasSum_arctan_aux hw_norm]
    simp only [A]
    ring
  exact
    hA.differentiableWithinAt.congr
      (fun w hw => heq w hw)
      (heq z hz)

/-- On the imaginary diameter of the unit disc, complex arctangent is the
corresponding real `artanh`. -/
theorem complex_arctan_neg_I_mul_ofReal
    {x : Real}
    (hx : |x| < 1) :
    Complex.arctan ((-I) * (x : Complex)) =
      (-I) * (Real.artanh x : Complex) := by
  have hx_mem : x ∈ Set.Icc (-1 : Real) 1 := by
    exact ⟨(abs_lt.mp hx).1.le, (abs_lt.mp hx).2.le⟩
  have hratio_pos :
      0 < (1 + x) / (1 - x) := by
    exact div_pos (by linarith [abs_lt.mp hx]) (by linarith [abs_lt.mp hx])
  rw [Complex.arctan]
  have hplus :
      1 + ((-I) * (x : Complex)) * I =
        ((1 + x : Real) : Complex) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hminus :
      1 - ((-I) * (x : Complex)) * I =
        ((1 - x : Real) : Complex) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hplus, hminus]
  rw [← Complex.ofReal_div]
  rw [← Complex.ofReal_log hratio_pos.le]
  rw [Real.artanh_eq_half_log hx_mem]
  push_cast
  ring

/-- The holomorphic inverse of the scaled `tanh` compactification on its
central coefficient disc. -/
def stripCompactificationLocalInverse
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    (w : Complex) :
    Complex :=
  ((P.radius / P.slope : Real) : Complex) *
    Complex.arctan
      ((-I) * (w / (P.radius : Complex))) * I

theorem differentiableOn_stripCompactificationLocalInverse
    {S rho : Real}
    (P : StripCompactificationParameters S rho) :
    DifferentiableOn Complex
      (stripCompactificationLocalInverse P)
      (Metric.ball (0 : Complex) P.radius) := by
  intro w hw
  have hw_norm : ‖w‖ < P.radius := by
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have harg :
      (-I) * (w / (P.radius : Complex)) ∈
        Metric.ball (0 : Complex) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul,
      norm_neg, Complex.norm_I, one_mul, norm_div,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos P.radius_pos]
    exact (div_lt_one P.radius_pos).2 hw_norm
  have harctan :
      DifferentiableWithinAt Complex Complex.arctan
        (Metric.ball (0 : Complex) 1)
        ((-I) * (w / (P.radius : Complex))) :=
    differentiableOn_complex_arctan_unitBall _ harg
  have hinner :
      DifferentiableWithinAt Complex
        (fun z : Complex =>
          (-I) * (z / (P.radius : Complex)))
        (Metric.ball (0 : Complex) P.radius) w := by
    fun_prop
  have hcomp :
      DifferentiableWithinAt Complex
        (fun z : Complex =>
          Complex.arctan
            ((-I) * (z / (P.radius : Complex))))
        (Metric.ball (0 : Complex) P.radius) w := by
    change DifferentiableWithinAt Complex
      (Complex.arctan ∘ fun z : Complex => (-I) * (z / (P.radius : Complex)))
      (Metric.ball (0 : Complex) P.radius) w
    exact DifferentiableWithinAt.comp w harctan hinner
      (fun _ hz => by
        rw [Metric.mem_ball, dist_zero_right, norm_mul,
          norm_neg, Complex.norm_I, one_mul, norm_div,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos P.radius_pos]
        exact
          (div_lt_one P.radius_pos).2
            (by simpa [Metric.mem_ball, dist_zero_right] using hz))
  change
    DifferentiableWithinAt Complex
      (fun z : Complex =>
        ((P.radius / P.slope : Real) : Complex) *
          Complex.arctan
            ((-I) * (z / (P.radius : Complex))) * I)
      (Metric.ball (0 : Complex) P.radius) w
  exact
    ((differentiableWithinAt_const
      ((P.radius / P.slope : Real) : Complex)).mul hcomp).mul
        (differentiableWithinAt_const I)

/-- Compactification followed by its local inverse is the identity on the
central coefficient disc. -/
theorem stripCompactification_localInverse
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    {w : Complex}
    (hw : ‖w‖ < P.radius) :
    stripCompactification P.radius P.slope
        (stripCompactificationLocalInverse P w) =
      w := by
  let y : Complex :=
    (-I) * (w / (P.radius : Complex))
  have hy_norm : ‖y‖ < 1 := by
    dsimp [y]
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, norm_div,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos P.radius_pos]
    exact (div_lt_one P.radius_pos).2 hw
  have hy_ne_I : y ≠ I := by
    intro h
    rw [h, Complex.norm_I] at hy_norm
    linarith
  have hy_ne_neg_I : y ≠ -I := by
    intro h
    rw [h, norm_neg, Complex.norm_I] at hy_norm
    linarith
  have hscaled :
      (((P.slope / P.radius : Real) : Complex) *
          stripCompactificationLocalInverse P w) =
        Complex.arctan y * I := by
    dsimp [stripCompactificationLocalInverse, y]
    push_cast
    field_simp [P.slope_pos.ne', P.radius_pos.ne']
  rw [stripCompactification, hscaled, Complex.tanh_mul_I,
    Complex.tan_arctan hy_ne_I hy_ne_neg_I]
  dsimp [y]
  field_simp [P.radius_pos.ne']
  rw [show I ^ 2 = (-1 : Complex) by
    rw [pow_two, Complex.I_mul_I]]
  ring

/-- On pure-imaginary coefficients the local inverse is the existing
target-adapted real-arctangent preimage. -/
theorem stripCompactificationLocalInverse_pureImaginary
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    (w : Real) :
    stripCompactificationLocalInverse P ((w : Complex) * I) =
      P.preimage w := by
  dsimp [stripCompactificationLocalInverse,
    StripCompactificationParameters.preimage]
  rw [show
    (-I) * (((w : Complex) * I) / (P.radius : Complex)) =
      ((w / P.radius : Real) : Complex) by
        push_cast
        field_simp [P.radius_pos.ne']
        rw [Complex.I_sq]
        ring]
  rw [← Complex.ofReal_arctan]
  push_cast
  rfl

/-- On the real diameter of the coefficient disc, the local inverse is the
ordinary scaled real `artanh`. -/
theorem stripCompactificationLocalInverse_ofReal
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    {w : Real}
    (hw : |w| < P.radius) :
    stripCompactificationLocalInverse P (w : Complex) =
      ((P.radius / P.slope *
        Real.artanh (w / P.radius) : Real) : Complex) := by
  have hratio :
      |w / P.radius| < 1 := by
    rw [abs_div, abs_of_pos P.radius_pos]
    exact (div_lt_one P.radius_pos).2 hw
  dsimp [stripCompactificationLocalInverse]
  rw [show
    (-I) * ((w : Complex) / (P.radius : Complex)) =
      (-I) * ((w / P.radius : Real) : Complex) by
        push_cast
        rfl]
  rw [complex_arctan_neg_I_mul_ofReal hratio]
  ring_nf
  rw [Complex.I_sq]
  push_cast
  ring

@[simp]
theorem stripCompactificationLocalInverse_ofReal_im
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    {w : Real}
    (hw : |w| < P.radius) :
    (stripCompactificationLocalInverse P (w : Complex)).im = 0 := by
  rw [stripCompactificationLocalInverse_ofReal P hw]
  rfl

end OSReconstruction.SCV
