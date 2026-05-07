/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# L5: Spectral Riemann-Lebesgue lemma for tempered measures with AC spatial marginal

**Status (2026-05-07): inventoried frontier lemma.** This is a pure
measure-theoretic / Fourier-analytic statement (NOT QFT-specific):
Riemann-Lebesgue for finite measures on `Fin (d+1) → ℝ` whose spatial
marginal is absolutely continuous w.r.t. Lebesgue.

Per PR #82 review (xiyin137): this file is acceptable as production
proof debt because:
* The statement is pure FA / measure theory, with no Wightman or BHW
  dependence.
* Substantial progress is already proved (steps 1, 2, 3a; see below).
* The remaining sub-steps (3b–e) reduce to standard Mathlib bridging
  via `EuclideanSpace ℝ (Fin d)` plus convention reconciliation.

For a finite Borel measure `μ` on `(Fin (d+1) → ℝ)` whose **spatial marginal**
(the pushforward under projection onto coordinates `i ≥ 1`) is absolutely
continuous w.r.t. Lebesgue measure, the spatial Fourier transform tends to
`0` along the cobounded filter:

```
Tendsto (a ↦ ∫ exp(i a · p⃗) dμ(p)) (cobounded) (𝓝 0)
```

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

## Status of steps

* Step 1 (change of variables via spatial projection): **PROVED**.
* Step 2 (Radon-Nikodym density reduction): **PROVED**.
* Step 3a (integrability of the density): **PROVED**.
* Steps 3b–e (Mathlib RL bridging on EuclideanSpace + convention
  reconciliation + cocompact↔cobounded): single sorry with concrete
  Mathlib targets. ~1 active day estimated remaining.
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
  -- Step 3a: integrability of `ρ`. The RN derivative `(spatialMarginal μ).rnDeriv volume`
  -- is in L¹(volume) because `spatialMarginal μ` is finite.
  have h_ρ_integrable : MeasureTheory.Integrable ρ MeasureTheory.volume := by
    show MeasureTheory.Integrable
      (fun q => ((spatialMarginal μ).rnDeriv MeasureTheory.volume q).toReal)
      MeasureTheory.volume
    exact MeasureTheory.Measure.integrable_toReal_rnDeriv (μ := spatialMarginal μ)
      (ν := MeasureTheory.volume)
  -- The complex-valued density `ρℂ : Fin d → ℝ → ℂ` is also integrable.
  have h_ρℂ_integrable : MeasureTheory.Integrable
      (fun q : Fin d → ℝ => (ρ q : ℂ)) MeasureTheory.volume := by
    exact h_ρ_integrable.ofReal
  -- Steps 3b-5 (deferred):
  --
  -- Key Mathlib pieces:
  -- * `MeasurableEquiv.toLp 2 (Fin d → ℝ) : (Fin d → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin d)`
  -- * `PiLp.volume_preserving_toLp : MeasurePreserving (toLp 2 (Fin d → ℝ))`
  -- * `tendsto_integral_exp_inner_smul_cocompact f`
  --   (`f : EuclideanSpace ℝ (Fin d) → ℂ`, gives Tendsto along cocompact)
  -- * `Metric.cobounded_eq_cocompact` on the proper space `EuclideanSpace ℝ (Fin d)`
  --
  -- The plan, written out as a chain:
  --
  --   our_integral(a) = ∫ q, (ρ q : ℂ) * exp(i ⟨a, q⟩) ∂volume_(Fin d → ℝ)
  --                  = ∫ v, (ρ (ofLp v) : ℂ) * exp(i ⟨a, ofLp v⟩) ∂volume_E
  --   [via PiLp.volume_preserving_toLp + integral_map]
  --                  = ∫ v, (ρ (ofLp v) : ℂ) * exp(i ⟨toLp a, v⟩_E) ∂volume_E
  --   [Pi pairing matches Euclidean inner product on values]
  --                  = ∫ v, 𝐞(-⟨v, w(a)⟩_E) • (ρ (ofLp v) : ℂ) ∂volume_E
  --   [where w(a) := -(2π)⁻¹ • toLp a, so 𝐞(-⟨v,w⟩) = exp(i⟨toLp a, v⟩)]
  --
  -- Mathlib RL: Tendsto (w ↦ ∫ v, 𝐞(-⟨v,w⟩) • f v) cocompact_E (𝓝 0).
  -- The map `a ↦ w(a) = -(2π)⁻¹ • toLp a` is a continuous bijection
  --   `(Fin d → ℝ) → EuclideanSpace ℝ (Fin d)`, taking cobounded → cocompact.
  -- Compose via `Tendsto.comp` to land at `Tendsto (a ↦ our_integral a) cobounded (𝓝 0)`.
  --
  -- The sub-step that's most fiddly: showing the integrand identity at v under
  -- the toLp/ofLp coercion, since `WithLp.ofLp v = v` definitionally as functions
  -- but Lean's elaborator distinguishes them via the WithLp wrapper.
  --
  -- Estimated remaining: ~1 day of careful Lean engineering. The proof
  -- is a chain of `Tendsto.comp` with continuous bijections and
  -- measure-preserving rewrites, but each step has subtle type-class
  -- bookkeeping (Fin d → ℝ vs EuclideanSpace, sup-norm vs L²).
  sorry

end Ruelle
end OSReconstruction

end
