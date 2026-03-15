import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Wick Rotation Bridge

Small one-variable lemmas bridging the semigroup half-plane `{z : ℂ | 0 < z.re}`
and the Wick-rotated tube variable `{u : ℂ | 0 < u.im}` via `z = -I * u`.
-/

noncomputable section

open Complex

namespace OSReconstruction

/-- The Wick rotation `u ↦ -Iu` sends `{u : ℂ | 0 < u.im}` to
`{z : ℂ | 0 < z.re}` because `Re(-Iu) = Im(u)`. -/
theorem neg_I_mul_re_eq_im (u : ℂ) : (-I * u).re = u.im := by
  simp [neg_re, mul_re, I_re, I_im]

/-- The inverse Wick rotation `z ↦ Iz` sends `{z : ℂ | 0 < z.re}` to
`{u : ℂ | 0 < u.im}` because `Im(Iz) = Re(z)`. -/
theorem I_mul_im_eq_re (z : ℂ) : (I * z).im = z.re := by
  simp [mul_im, I_re, I_im]

/-- If `H` is holomorphic on the right half-plane, then composing with the Wick
rotation `u ↦ -Iu` gives a holomorphic function on the upper half-plane. -/
theorem differentiableOn_comp_neg_I_mul {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.re}) :
    DifferentiableOn ℂ (fun u => H (-I * u)) {u : ℂ | 0 < u.im} := by
  intro u hu
  simp only [Set.mem_setOf_eq] at hu
  have hmap : -I * u ∈ {z : ℂ | 0 < z.re} := by
    rw [Set.mem_setOf_eq, neg_I_mul_re_eq_im]
    exact hu
  have hH_diff : DifferentiableAt ℂ H (-I * u) :=
    hH.differentiableAt (IsOpen.mem_nhds (isOpen_lt continuous_const continuous_re) hmap)
  have hmul_diff : DifferentiableAt ℂ (fun v : ℂ => -I * v) u := by
    have hclm : (fun v : ℂ => -I * v) = ⇑((-I) • ContinuousLinearMap.id ℂ ℂ) := by
      ext v
      simp
    rw [hclm]
    exact ((-I) • ContinuousLinearMap.id ℂ ℂ).differentiableAt
  exact (hH_diff.comp u hmul_diff).differentiableWithinAt

/-- More generally, composing any holomorphic function with the Wick rotation
`u ↦ -Iu` preserves holomorphicity on the pullback of its domain. -/
theorem differentiableOn_wick_rotate {H : ℂ → ℂ} {S : Set ℂ}
    (hH : DifferentiableOn ℂ H S) (hS : IsOpen S) :
    DifferentiableOn ℂ (fun u => H (-I * u)) {u | -I * u ∈ S} := by
  intro u hu
  simp only [Set.mem_setOf_eq] at hu
  have hH_diff : DifferentiableAt ℂ H (-I * u) :=
    hH.differentiableAt (IsOpen.mem_nhds hS hu)
  have hmul_diff : DifferentiableAt ℂ (fun v : ℂ => -I * v) u := by
    have hclm : (fun v : ℂ => -I * v) = ⇑((-I) • ContinuousLinearMap.id ℂ ℂ) := by
      ext v
      simp
    rw [hclm]
    exact ((-I) • ContinuousLinearMap.id ℂ ℂ).differentiableAt
  exact (hH_diff.comp u hmul_diff).differentiableWithinAt

end OSReconstruction
