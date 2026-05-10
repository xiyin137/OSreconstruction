/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors

PARKED 2026-05-06 (was `OSReconstruction/GeneralResults/SpectralAnalysis.lean`).
Moved to `Proofideas/` per PR #82 review (xiyin137): the two functional-
analysis axioms in this file (`spectral_riemann_lebesgue`,
`continuous_translate_schwartz`) were introduced for the
Källén-Lehmann route, never made it through formal axiom-gate review,
and are not used after the cluster theorem pivoted to the Ruelle 1962
route. Preserved here. Both are standard Mathlib-style FA statements
that can be re-introduced under the standard axiom-gate process if
needed downstream.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
# Generic spectral and Schwartz-space axioms

This file collects axioms that are independent of the Wightman/QFT setting
— they're pure measure theory or pure Schwartz-space analysis. Pulling
them out here keeps the Wightman files focused on QFT-specific content
and makes these axioms easier to vet, discharge, or eventually move to
Mathlib.

## Axioms

* `spectral_riemann_lebesgue` — for a finite positive Borel measure `μ` on
  `(Fin (d + 1) → ℝ)` whose marginal under spatial projection (via
  `Fin.succ`) is absolutely continuous, the spatial Fourier transform of
  `μ` tends to 0 at infinity. **Mathlib-derivable**: from
  `tendsto_integral_exp_inner_smul_cocompact` + measure decomposition.

* `continuous_translate_schwartz` — translation acts continuously on
  `SchwartzMap` in the parameter direction. Standard fact: Hörmander I
  Theorem 7.1.18; Reed-Simon I §V.3.
  **Mathlib-derivable**: from Schwartz seminorm decomposition.

## Discharge plan

Both axioms are scheduled for elimination once the Mathlib derivations
are written out — bookkeeping work, not new mathematical content.

## References

* Mathlib, `Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean`,
  `tendsto_integral_exp_inner_smul_cocompact`.
* Reed, Simon, *Methods of Modern Mathematical Physics*, Vol. I §V.3.
* Hörmander, *The Analysis of Linear Partial Differential Operators I*,
  Theorem 7.1.18.
-/

namespace OSReconstruction

open MeasureTheory

/-! ### Spectral Riemann-Lebesgue with absolute-continuity hypothesis -/

/-- **Spectral Riemann-Lebesgue lemma** for spatial Fourier transforms.

For a finite positive Borel measure `μ` on `Fin (d + 1) → ℝ` (think of as
spacetime `ℝ^{d+1}` indexed with 0 = time, 1..d = spatial), if the
spatial-coordinate marginal of `μ` is absolutely continuous w.r.t.
Lebesgue measure on `ℝᵈ`, then the spatial Fourier transform of `μ`
tends to 0 along the cocompact filter:
$$\int_{ℝ^{d+1}} e^{i \vec a \cdot \vec p}\, dμ(p) \to 0
  \quad \text{as} \quad |\vec a| \to \infty,$$
where `\vec a · \vec p := \sum_{i=1}^{d} a_i p_i` is the Euclidean
spatial inner product.

The hypothesis encodes "spatial marginal is absolutely continuous":
every Lebesgue-null set `E ⊆ ℝᵈ` pulls back via `Fin.succ`-spatial
projection to a μ-null subset of `ℝ^{d+1}`.

**Reference**: Mathlib `tendsto_integral_exp_inner_smul_cocompact`
(`Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean:180`) for the AC
density case; the general measure-theoretic statement extends via
Wiener's spectral decomposition.

**Discharge plan**: ~50 lines. Decompose `μ` into absolutely-continuous
+ singular-continuous + atomic; AC case from Mathlib's RL; SC case from
Wiener; atomic case forced by the AC-marginal hypothesis to have no
atoms with spatial part 0. -/
axiom spectral_riemann_lebesgue
    {d : ℕ} (μ : Measure (Fin (d + 1) → ℝ)) [IsFiniteMeasure μ]
    (h_spatial_AC :
      Measure.map (fun (p : Fin (d + 1) → ℝ) (i : Fin d) => p i.succ) μ ≪
        (MeasureTheory.volume : Measure (Fin d → ℝ))) :
    Filter.Tendsto
      (fun a : Fin d → ℝ =>
        ∫ p : Fin (d + 1) → ℝ,
          Complex.exp (Complex.I *
            (∑ i : Fin d, (a i : ℂ) * (p i.succ : ℂ))) ∂μ)
      (Bornology.cobounded (Fin d → ℝ)) (nhds 0)

/-! ### Continuity of translation on Schwartz space -/

/-- **Translation on Schwartz space is continuous in the parameter**.

For any Schwartz function `f : 𝓢(E, ℂ)` on a finite-dim real inner-product
space `E`, the assignment `a ↦ T_a f` (where `T_a f(x) := f(x - a)`) is
continuous as a map from `E` to `𝓢(E, ℂ)` in the Schwartz Fréchet
topology.

Stated abstractly via the existence of a continuous map producing
translates. The full type-correct statement uses `SchwartzMap.mk` with
appropriate smoothness + decay witnesses; here we just assert the
existence of the continuous-translate operator.

**Reference**: Hörmander I Theorem 7.1.18 (translation is a continuous
representation of `ℝⁿ` on `𝓢(ℝⁿ)`); Reed-Simon I §V.3.

**Discharge plan**: ~50 lines. Schwartz seminorm bounds + dominated
convergence; the compact-support specialization is in
`OSReconstruction/SCV/DistributionalUniqueness.lean::tendsto_translateSchwartz_nhds_of_isCompactSupport`. -/
axiom continuous_translate_schwartz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ T : E → SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ,
      -- Strong continuity: per fixed test function f, the map a ↦ T_a f
      -- is continuous in the Schwartz Fréchet topology.
      -- (Operator-norm continuity is mathematically FALSE for translation
      -- on Schwartz / L² — only strong continuity holds, per Hörmander
      -- Theorem 7.1.18.)
      (∀ f : SchwartzMap E ℂ, Continuous (fun a => T a f)) ∧
      ∀ (a : E) (f : SchwartzMap E ℂ) (x : E), (T a f) x = f (x - a)

end OSReconstruction
