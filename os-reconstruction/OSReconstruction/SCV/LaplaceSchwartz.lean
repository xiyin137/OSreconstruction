/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos












































noncomputable section

open Complex MeasureTheory Topology Metric Set

namespace SCV



/- The remaining missing theorem in this file should produce
    `HasFourierLaplaceReprRegular C F` from genuinely strong Fourier-Laplace input:
    an actual FL transform with the required dual-cone support, together with the
    corresponding growth and boundary-ray estimates.

    This upgrade is not yet formalized here. Downstream transport theorems therefore
    take `HasFourierLaplaceReprRegular` explicitly instead of claiming a weak-to-regular
    upgrade theorem that has not been proved. -/








/-- **Schwartz functions are integrable** (needed for dominated convergence applications).
    Schwartz functions decay rapidly, so they are in every Lp space. -/
theorem schwartzMap_integrable {m : ℕ} (f : SchwartzMap (Fin m → ℝ) ℂ) :
    MeasureTheory.Integrable (fun x => f x) := by
  have h := f.integrable_pow_mul MeasureTheory.MeasureSpace.volume 0
  simp only [pow_zero, one_mul] at h
  rw [← MeasureTheory.integrable_norm_iff (SchwartzMap.continuous f).aestronglyMeasurable]
  exact h

/-- **(1 + ‖x‖)^N * ‖f(x)‖ is integrable for Schwartz f.**
    This follows from Schwartz decay: ‖x‖^k * ‖f(x)‖ is integrable for all k,
    and (1 + ‖x‖)^N is bounded by a polynomial in ‖x‖. -/
theorem schwartzMap_polynomial_norm_integrable {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) (N : ℕ) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ => (1 + ‖x‖) ^ N * ‖f x‖) := by
  -- Use binomial expansion: (1 + ‖x‖)^N = ∑_{k=0}^{N} C(N,k) * ‖x‖^k
  -- So (1 + ‖x‖)^N * ‖f x‖ = ∑_{k} C(N,k) * (‖x‖^k * ‖f x‖)
  -- Each term is integrable by SchwartzMap.integrable_pow_mul.
  -- Strategy: show the function is dominated by a finite sum of integrable functions.
  -- Use Integrable.of_norm_le with bound being a finite sum.
  --
  -- Simpler approach: (1 + ‖x‖)^N ≤ 2^N * (1 + ‖x‖)^N doesn't help.
  -- Use: (1 + a)^N ≤ 2^N * max(1, a^N) ≤ 2^N * (1 + a^N) for a ≥ 0.
  -- Then (1 + ‖x‖)^N * ‖f x‖ ≤ 2^N * (‖f x‖ + ‖x‖^N * ‖f x‖).
  have h_norm_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => ‖f x‖) :=
    (schwartzMap_integrable f).norm
  have h_pow_int : MeasureTheory.Integrable
      (fun x : Fin m → ℝ => ‖x‖ ^ N * ‖f x‖) :=
    f.integrable_pow_mul MeasureTheory.MeasureSpace.volume N
  -- The sum 2^N * (‖f x‖ + ‖x‖^N * ‖f x‖) is integrable
  have h_sum : MeasureTheory.Integrable
      (fun x : Fin m → ℝ => (2 : ℝ) ^ N * (‖f x‖ + ‖x‖ ^ N * ‖f x‖)) :=
    (h_norm_int.add h_pow_int).const_mul _
  -- Bound: (1 + ‖x‖)^N ≤ 2^N * (1 + ‖x‖^N) for ‖x‖ ≥ 0
  have h_bound : ∀ x : Fin m → ℝ,
      ‖(1 + ‖x‖) ^ N * ‖f x‖‖ ≤ (2 : ℝ) ^ N * (‖f x‖ + ‖x‖ ^ N * ‖f x‖) := by
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by linarith [norm_nonneg x]) N) (norm_nonneg _))]
    have h1 : (1 + ‖x‖) ^ N ≤ (2 : ℝ) ^ N * (1 + ‖x‖ ^ N) := by
      have hx_nn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      calc (1 + ‖x‖) ^ N
          ≤ (2 * max 1 ‖x‖) ^ N := by
            apply pow_le_pow_left₀ (by linarith)
            calc 1 + ‖x‖ ≤ max 1 ‖x‖ + max 1 ‖x‖ :=
                  add_le_add (le_max_left 1 ‖x‖) (le_max_right 1 ‖x‖)
              _ = 2 * max 1 ‖x‖ := by ring
        _ = 2 ^ N * (max 1 ‖x‖) ^ N := by rw [mul_pow]
        _ ≤ 2 ^ N * (1 + ‖x‖ ^ N) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            by_cases h : (1 : ℝ) ≤ ‖x‖
            · simp [max_eq_right h]
            · push_neg at h
              simp [max_eq_left h.le]
    calc (1 + ‖x‖) ^ N * ‖f x‖
        ≤ (2 : ℝ) ^ N * (1 + ‖x‖ ^ N) * ‖f x‖ := by
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (2 : ℝ) ^ N * (‖f x‖ + ‖x‖ ^ N * ‖f x‖) := by ring
  exact h_sum.mono'
    ((continuous_const.add (continuous_norm)).pow N |>.mul
      (SchwartzMap.continuous f).norm |>.aestronglyMeasurable)
    (Filter.Eventually.of_forall h_bound)

/-- Polynomial weight integrability for Schwartz functions, restated with the
boundary-value naming used in the reconstruction files. -/
theorem integrable_poly_weight_schwartz {m : ℕ}
    (N : ℕ) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ => (1 + ‖x‖) ^ N * ‖f x‖) :=
  schwartzMap_polynomial_norm_integrable f N

/-- A measurable function with polynomial growth is integrable against any
Schwartz test function. This is the basic domination step used in
distributional boundary-value arguments. -/
theorem integrable_poly_growth_schwartz {m : ℕ}
    (G : (Fin m → ℝ) → ℂ)
    (hG_meas : MeasureTheory.AEStronglyMeasurable G MeasureTheory.MeasureSpace.volume)
    (C_bd : ℝ) (N : ℕ)
    (hG_bound : ∀ x : Fin m → ℝ, ‖G x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    MeasureTheory.Integrable (fun x => G x * f x) := by
  refine MeasureTheory.Integrable.mono'
    ((integrable_poly_weight_schwartz N f).const_mul C_bd)
    (hG_meas.mul f.continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc
    ‖G x‖ * ‖f x‖ ≤ C_bd * (1 + ‖x‖) ^ N * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (hG_bound x) (norm_nonneg _)
    _ = C_bd * ((1 + ‖x‖) ^ N * ‖f x‖) := by ring

/-- If an a.e. reflected kernel identity `conj(F x) = F (Ψ x)` holds for a
measure-preserving involution `Ψ`, then pairing against `f` is the conjugate of
pairing against `conj (f ∘ Ψ)`. This is the reality-pattern analogue of
`bv_integral_hermiticity_v2`. -/
theorem bv_reality_pattern {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α → ℂ) (f : α → ℂ)
    (Ψ : α ≃ᵐ α)
    (hΨ_mp : MeasurePreserving Ψ μ μ)
    (hΨ_inv : ∀ x, Ψ (Ψ x) = x)
    (hF_reflect : ∀ᵐ x ∂μ, starRingEnd ℂ (F x) = F (Ψ x)) :
    starRingEnd ℂ (∫ x, F x * f x ∂μ) =
      ∫ x, F x * starRingEnd ℂ (f (Ψ x)) ∂μ := by
  conv_lhs => rw [show starRingEnd ℂ (∫ x, F x * f x ∂μ) =
    ∫ x, starRingEnd ℂ (F x * f x) ∂μ from integral_conj.symm]
  have step1 : (fun x => starRingEnd ℂ (F x * f x)) =ᵐ[μ]
      fun x => F (Ψ x) * starRingEnd ℂ (f x) := by
    filter_upwards [hF_reflect] with x hx
    rw [map_mul, hx]
  rw [integral_congr_ae step1]
  symm
  rw [← hΨ_mp.integral_comp' (f := Ψ)
      (g := fun x => F x * starRingEnd ℂ (f (Ψ x)))]
  simp [hΨ_inv]










end SCV

end
