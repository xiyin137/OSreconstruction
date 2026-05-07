/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# L5: Spectral Riemann-Lebesgue lemma for tempered measures with AC spatial marginal

For a finite Borel measure `μ` on `(Fin (d+1) → ℝ)` whose **spatial marginal**
(the pushforward under projection onto coordinates `i ≥ 1`) is absolutely
continuous w.r.t. Lebesgue measure, the spatial Fourier transform tends to
`0` along the cobounded filter:

```
Tendsto (a ↦ ∫ exp(i a · p⃗) dμ(p)) (cobounded) (𝓝 0)
```

This is L5 of the Ruelle proof chain (see `Blueprint.lean`).

## Discharge strategy

1. Let `ν := spatial marginal of μ`. Then `ν ≪ Lebesgue` by hypothesis.
2. By Radon-Nikodym, `ν` has a density `ρ : (Fin d → ℝ) → ℝ` with
   `ρ ∈ L¹(Lebesgue)`.
3. By change of variables under the spatial projection,
   `∫ exp(i a · p⃗) dμ(p) = ∫ exp(i a · q⃗) ρ(q⃗) dq⃗` (Lebesgue integral
   on `Fin d → ℝ`).
4. Apply Mathlib's `tendsto_integral_exp_inner_smul_cocompact` to `ρ`.
5. Reconcile the inner-product / Fourier-character convention to match
   our `Complex.exp (Complex.I * ⟨a, q⟩)` form.

This file lays out the structure; full proof to be filled in.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Bornology Real

namespace OSReconstruction
namespace Ruelle

/-! ### Spatial marginal of a measure on `Fin (d+1) → ℝ` -/

/-- Project a spacetime momentum to its spatial part. -/
def spatialProj (d : ℕ) :
    (Fin (d + 1) → ℝ) → (Fin d → ℝ) :=
  fun p i => p i.succ

/-- The spatial-projection map is measurable. -/
lemma measurable_spatialProj (d : ℕ) :
    Measurable (spatialProj d) := by
  exact measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

/-- The spatial marginal of a measure on `Fin (d+1) → ℝ`. -/
def spatialMarginal {d : ℕ} (μ : Measure (Fin (d + 1) → ℝ)) :
    Measure (Fin d → ℝ) :=
  μ.map (spatialProj d)

/-! ### L5 main statement -/

/-- **L5: Spectral Riemann-Lebesgue**.

For a finite measure `μ` on `Fin (d+1) → ℝ` whose spatial marginal is
absolutely continuous w.r.t. Lebesgue, the spatial Fourier transform
tends to `0` along the cobounded filter on the spatial momentum
space.

Proof:
1. The integrand depends on `p` only via the spatial projection
   `p ↦ (i ↦ p i.succ)`. Push the integral through the spatial
   marginal via `MeasureTheory.integral_map`.
2. Use `h_spatial_AC` + Radon-Nikodym (`Measure.withDensity_rnDeriv_eq`)
   to identify `spatialMarginal μ = volume.withDensity ρ` where
   `ρ = (spatialMarginal μ).rnDeriv volume`.
3. `∫ exp(i a · q) d(spatialMarginal μ)(q) = ∫ exp(i a · q) · ρ(q) ∂volume`
   via `MeasureTheory.integral_withDensity_eq_integral_smul`.
4. Apply Mathlib's `tendsto_integral_exp_inner_smul_cocompact` to the
   density (after sign / 2π reconciliation between Mathlib's `𝐞` and
   our `exp(i ·)`).
5. `cocompact = cobounded` on `Fin d → ℝ` (proper space, via
   `Metric.cobounded_eq_cocompact`).
-/
theorem spectral_riemann_lebesgue
    {d : ℕ} (μ : Measure (Fin (d + 1) → ℝ)) [IsFiniteMeasure μ]
    (h_spatial_AC : spatialMarginal μ ≪
      (MeasureTheory.volume : Measure (Fin d → ℝ))) :
    Filter.Tendsto
      (fun a : Fin d → ℝ =>
        ∫ p : Fin (d + 1) → ℝ,
          Complex.exp (Complex.I *
            (∑ i : Fin d, (a i : ℂ) * (p i.succ : ℂ))) ∂μ)
      (Bornology.cobounded (Fin d → ℝ)) (nhds 0) := by
  -- Step 1: change of variables via spatialProj
  have h_step1 : ∀ a : Fin d → ℝ,
      (∫ p : Fin (d + 1) → ℝ,
          Complex.exp (Complex.I *
            (∑ i : Fin d, (a i : ℂ) * (p i.succ : ℂ))) ∂μ) =
      (∫ q : Fin d → ℝ,
          Complex.exp (Complex.I *
            (∑ i : Fin d, (a i : ℂ) * (q i : ℂ))) ∂(spatialMarginal μ)) := by
    intro a
    unfold spatialMarginal
    rw [MeasureTheory.integral_map (measurable_spatialProj d).aemeasurable]
    · -- The integrand at `q := spatialProj d p` matches the integrand on the
      -- LHS at `p`: `q i = p i.succ`, so `(q i : ℂ) = (p i.succ : ℂ)`.
      rfl
    · -- AEStronglyMeasurable: integrand is continuous in `q`.
      apply Continuous.aestronglyMeasurable
      refine Complex.continuous_exp.comp ?_
      refine continuous_const.mul ?_
      refine continuous_finset_sum _ ?_
      intro i _
      refine continuous_const.mul ?_
      exact (Complex.continuous_ofReal.comp (continuous_apply i))
  simp_rw [h_step1]
  -- Step 2: Radon-Nikodym density reduction.
  -- Use `integral_rnDeriv_smul`: for `μ' ≪ ν`,
  --   `∫ x, (μ'.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ'`.
  -- Applied with μ' = spatialMarginal μ and ν = volume:
  --   `∫ q, exp(i a · q) d(spatialMarginal μ)(q) =
  --    ∫ q, ((spatialMarginal μ).rnDeriv volume q).toReal • exp(i a · q) ∂volume`.
  set ρ : (Fin d → ℝ) → ℝ :=
    fun q => ((spatialMarginal μ).rnDeriv MeasureTheory.volume q).toReal with hρ_def
  haveI : IsFiniteMeasure (spatialMarginal μ) := by
    unfold spatialMarginal
    exact MeasureTheory.Measure.isFiniteMeasure_map μ (spatialProj d)
  have h_step2 : ∀ a : Fin d → ℝ,
      (∫ q : Fin d → ℝ,
          Complex.exp (Complex.I *
            (∑ i : Fin d, (a i : ℂ) * (q i : ℂ))) ∂(spatialMarginal μ)) =
      (∫ q : Fin d → ℝ, (ρ q : ℂ) *
          Complex.exp (Complex.I *
            (∑ i : Fin d, (a i : ℂ) * (q i : ℂ)))) := by
    intro a
    rw [← MeasureTheory.integral_rnDeriv_smul (μ := spatialMarginal μ)
      (ν := MeasureTheory.volume) h_spatial_AC
      (f := fun q => Complex.exp (Complex.I *
            (∑ i : Fin d, (a i : ℂ) * (q i : ℂ))))]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun q => ?_)
    show (((spatialMarginal μ).rnDeriv MeasureTheory.volume q).toReal : ℂ) *
        Complex.exp (Complex.I * (∑ i : Fin d, (a i : ℂ) * (q i : ℂ))) =
      ((spatialMarginal μ).rnDeriv MeasureTheory.volume q).toReal •
        Complex.exp (Complex.I * (∑ i : Fin d, (a i : ℂ) * (q i : ℂ)))
    rw [Complex.real_smul]
  simp_rw [h_step2]
  -- Steps 3–5 (deferred): Reduce to Mathlib's RL.
  --
  -- Sub-step 3a: integrability of `q ↦ (ρ q : ℂ)`. Holds because
  --   `(spatialMarginal μ).rnDeriv volume` is in L¹(volume) when
  --   `spatialMarginal μ` is finite.
  -- Sub-step 3b: convert `Fin d → ℝ` to `EuclideanSpace ℝ (Fin d)` via
  --   the canonical measurable equiv (measure-preserving by
  --   `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`).
  -- Sub-step 3c: Mathlib's `tendsto_integral_exp_inner_smul_cocompact`
  --   on `f := fun v => (ρ (eq.symm v) : ℂ)` gives
  --   `Tendsto (fun w => ∫ v, 𝐞(-⟨v, w⟩) • f v) cocompact (𝓝 0)`.
  --   Here `𝐞(-⟨v, w⟩) = exp(-2πi ⟨v, w⟩)` (Mathlib's `fourierChar`).
  -- Sub-step 3d: substitute `w = -a/(2π)`. Then
  --   `𝐞(-⟨v, -a/(2π)⟩) = exp(-2πi · (-1/(2π)) ⟨v, a⟩) = exp(i ⟨v, a⟩)
  --                     = exp(i ∑ a_i v_i)`,
  --   matching our integrand.
  -- Sub-step 3e: `cocompact = cobounded` on `Fin d → ℝ` (proper space)
  --   via `Metric.cobounded_eq_cocompact`.
  --
  -- Estimated remaining: ~1 day of careful Lean engineering. The proof
  -- is a chain of `Tendsto.comp` with continuous bijections and
  -- measure-preserving rewrites, but each step has subtle type-class
  -- bookkeeping (Fin d → ℝ vs EuclideanSpace, sup-norm vs L²).
  sorry

end Ruelle
end OSReconstruction

end
