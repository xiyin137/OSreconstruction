/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.Prod
import OSReconstruction.SCV.Polydisc
import OSReconstruction.SCV.Osgood





























noncomputable section

open Complex MeasureTheory Topology Metric Set SCV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

namespace SCV









/-- The iterated circle integral over `m` circles.
    `iteratedCircleIntegral m f c r` computes
    `∮_{|w₁-c₁|=r₁} ⋯ ∮_{|wₘ-cₘ|=rₘ} f(w₁,...,wₘ) dwₘ⋯dw₁`. -/
def iteratedCircleIntegral :
    (m : ℕ) → ((Fin m → ℂ) → E) → (Fin m → ℂ) → (Fin m → ℝ) → E
  | 0, f, _, _ => f Fin.elim0
  | m + 1, f, c, r =>
      iteratedCircleIntegral m
        (fun z => ∮ w in C(c (Fin.last m), r (Fin.last m)), f (Fin.snoc z w))
        (c ∘ Fin.castSucc)
        (r ∘ Fin.castSucc)

omit [CompleteSpace E] in
/-- Unfolding lemma for the successor case of `iteratedCircleIntegral`. -/
theorem iteratedCircleIntegral_succ (m : ℕ) (f : (Fin (m + 1) → ℂ) → E)
    (c : Fin (m + 1) → ℂ) (r : Fin (m + 1) → ℝ) :
    iteratedCircleIntegral (m + 1) f c r =
    iteratedCircleIntegral m
      (fun z => ∮ w in C(c (Fin.last m), r (Fin.last m)), f (Fin.snoc z w))
      (c ∘ Fin.castSucc) (r ∘ Fin.castSucc) := rfl

omit [CompleteSpace E] in
/-- The iterated circle integral is linear (scalar multiplication). -/
theorem iteratedCircleIntegral_smul (m : ℕ) (a : ℂ) (f : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (r : Fin m → ℝ) :
    iteratedCircleIntegral m (fun z => a • f z) c r =
      a • iteratedCircleIntegral m f c r := by
  induction m with
  | zero => simp [iteratedCircleIntegral]
  | succ m ih =>
    simp only [iteratedCircleIntegral]
    rw [← ih]
    congr 1
    ext z
    rw [circleIntegral.integral_smul]



omit [CompleteSpace E] in
/-- Norm bound for the iterated circle integral.
    If `‖f(w)‖ ≤ C` for all `w` on the distinguished boundary, then
    `‖∮...∮ f‖ ≤ (2π)ᵐ · ∏ᵢ |rᵢ| · C`. -/
theorem norm_iteratedCircleIntegral_le (m : ℕ) (f : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (r : Fin m → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, 0 ≤ r i)
    (hf : ∀ w ∈ distinguishedBoundary c r, ‖f w‖ ≤ C) :
    ‖iteratedCircleIntegral m f c r‖ ≤
      (2 * Real.pi) ^ m * (∏ i : Fin m, |r i|) * C := by
  induction m generalizing C with
  | zero =>
    simp only [iteratedCircleIntegral, pow_zero, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact hf Fin.elim0 (fun i => i.elim0)
  | succ m ih =>
    simp only [iteratedCircleIntegral]
    set R := r (Fin.last m)
    set g := fun z => ∮ w in C(c (Fin.last m), R), f (Fin.snoc z w)
    set c' := c ∘ Fin.castSucc
    set r' := r ∘ Fin.castSucc
    have hr' : ∀ i, 0 ≤ r' i := fun i => hr (Fin.castSucc i)
    have hR : 0 ≤ R := hr (Fin.last m)
    -- Bound g on the inner distinguished boundary
    have hg : ∀ z ∈ distinguishedBoundary c' r',
        ‖g z‖ ≤ 2 * Real.pi * R * C := by
      intro z hz
      apply circleIntegral.norm_integral_le_of_norm_le_const hR
      intro w hw
      apply hf (Fin.snoc z w)
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact hw
      · intro j; simp only [Fin.snoc_castSucc]; exact hz j
    have hC' : 0 ≤ 2 * Real.pi * R * C := by positivity
    calc ‖iteratedCircleIntegral m g c' r'‖
        ≤ (2 * Real.pi) ^ m * (∏ i : Fin m, |r' i|) *
          (2 * Real.pi * R * C) := ih g c' r' (2 * Real.pi * R * C) hC' hr' hg
      _ = (2 * Real.pi) ^ (m + 1) * (∏ i : Fin (m + 1), |r i|) * C := by
          rw [Fin.prod_univ_castSucc (fun i => |r i|)]
          simp only [r', R, Function.comp_apply, abs_of_nonneg hR]
          ring
























end SCV
