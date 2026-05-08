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
  -- Step 3b: convert integral on `Fin d → ℝ` to integral on `EuclideanSpace ℝ (Fin d)`.
  -- Use `PiLp.volume_preserving_toLp.integral_comp_emb` (for the measurable embedding).
  -- The integrand pulled back through `WithLp.ofLp` yields an integrand on V.
  have h_step3b : ∀ a : Fin d → ℝ,
      (∫ q : Fin d → ℝ, (ρ q : ℂ) *
          Complex.exp (Complex.I *
            (∑ i : Fin d, (a i : ℂ) * (q i : ℂ)))) =
      (∫ v : EuclideanSpace ℝ (Fin d),
          (ρ (WithLp.ofLp v) : ℂ) *
          Complex.exp (Complex.I *
            (∑ i : Fin d, (a i : ℂ) * ((WithLp.ofLp v) i : ℂ)))) := by
    intro a
    -- `PiLp.volume_preserving_toLp` gives MeasurePreserving (toLp 2) volume volume
    -- for ι = Fin d (Fintype). Use `integral_comp_emb` via the measurable equiv.
    have hMP : MeasureTheory.MeasurePreserving
        (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
        MeasureTheory.volume MeasureTheory.volume :=
      PiLp.volume_preserving_toLp (Fin d)
    -- Apply integral_comp via the MeasurableEquiv.
    have hME : MeasureTheory.MeasurePreserving
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)) MeasureTheory.volume MeasureTheory.volume := hMP
    rw [← hME.integral_comp' (g := fun v : EuclideanSpace ℝ (Fin d) =>
        (ρ (WithLp.ofLp v) : ℂ) *
        Complex.exp (Complex.I *
          (∑ i : Fin d, (a i : ℂ) * ((WithLp.ofLp v) i : ℂ))))]
    rfl
  simp_rw [h_step3b]
  -- Step 3c: apply Mathlib's `tendsto_integral_exp_inner_smul_cocompact` to
  -- the function `f : EuclideanSpace ℝ (Fin d) → ℂ`,
  --   `f v := (ρ (WithLp.ofLp v) : ℂ)`.
  -- This gives `Tendsto (fun w => ∫ v, 𝐞(-⟪v, w⟫) • f v) cocompact (𝓝 0)`.
  set f_E : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun v => (ρ (WithLp.ofLp v) : ℂ) with hf_E_def
  have h_RL : Filter.Tendsto
      (fun w : EuclideanSpace ℝ (Fin d) =>
        ∫ v : EuclideanSpace ℝ (Fin d),
          Real.fourierChar (Multiplicative.ofAdd (-(@inner ℝ _ _ v w))) • f_E v)
      (Filter.cocompact (EuclideanSpace ℝ (Fin d)))
      (nhds 0) :=
    tendsto_integral_exp_inner_smul_cocompact f_E
  -- Step 3d-e: the affine map a ↦ -(2π)⁻¹ • toLp a, integrand identity, and
  -- Tendsto.comp.
  --
  -- Define the affine map.
  set aff_map : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) :=
    fun a => -((2 * Real.pi)⁻¹ : ℝ) • (WithLp.toLp 2 a) with haff_map_def
  -- aff_map is continuous (smul-by-const ∘ toLp, both continuous).
  have h_aff_cont : Continuous aff_map := by
    refine Continuous.const_smul ?_ _
    exact PiLp.continuous_toLp 2 (β := fun _ : Fin d => ℝ)
  -- aff_map maps cobounded → cobounded (it's a continuous bijection on
  -- finite-dim normed spaces; the inverse is a continuous bijection too).
  -- Therefore cobounded(Fin d → ℝ) → cobounded(EuclideanSpace) → cocompact.
  have h_aff_cobounded :
      Filter.Tendsto aff_map
        (Bornology.cobounded (Fin d → ℝ))
        (Filter.cocompact (EuclideanSpace ℝ (Fin d))) := by
    -- Strategy: aff_map is a linear bijection (smul by nonzero ∘ toLp 2).
    -- In finite dim, any linear equivalence becomes a homeomorphism via
    -- `LinearEquiv.toContinuousLinearEquiv`. A homeomorphism takes
    -- cocompact to cocompact, and on `Fin d → ℝ` cobounded = cocompact
    -- (proper space).
    have hpi_ne : -((2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by
      apply neg_ne_zero.mpr
      exact inv_ne_zero (by positivity)
    -- Build the linear equivalence (toLp first, then smul = aff_map).
    let aff_lin : (Fin d → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
      (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.trans
        (LinearEquiv.smulOfUnit
          (Units.mk0 (-((2 * Real.pi)⁻¹ : ℝ)) hpi_ne))
    -- The continuous linear equivalence (finite-dim).
    let aff_cle : (Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
      aff_lin.toContinuousLinearEquiv
    -- aff_cle is a homeomorphism.
    have h_aff_eq : ∀ a : Fin d → ℝ, aff_cle a = aff_map a := by
      intro a
      show (Units.mk0 (-((2 * Real.pi)⁻¹ : ℝ)) hpi_ne) • (WithLp.toLp 2 a) = aff_map a
      rfl
    -- Tendsto via Homeomorph.
    rw [show aff_map = aff_cle.toHomeomorph from
      funext (fun a => (h_aff_eq a).symm)]
    -- cocompact → cocompact via homeomorphism.
    have h_homeo_tendsto :
        Filter.Tendsto aff_cle.toHomeomorph
          (Filter.cocompact (Fin d → ℝ))
          (Filter.cocompact (EuclideanSpace ℝ (Fin d))) :=
      aff_cle.toHomeomorph.toCocompactMap.cocompact_tendsto'
    -- cobounded = cocompact on (Fin d → ℝ) (proper space).
    have h_cob_eq : Bornology.cobounded (Fin d → ℝ) =
        Filter.cocompact (Fin d → ℝ) :=
      Metric.cobounded_eq_cocompact
    rw [h_cob_eq]
    exact h_homeo_tendsto
  -- Apply Tendsto.comp.
  have h_comp := h_RL.comp h_aff_cobounded
  -- The composition has integrand `𝐞(-⟪v, aff_map a⟫_E) • f_E v`.
  -- Show this equals our integrand pointwise.
  refine h_comp.congr (fun a => ?_)
  -- Goal: integrand identity at `a`.
  -- LHS (from h_comp): ∫ v, 𝐞(-⟪v, aff_map a⟫) • f_E v ∂volume_E
  -- RHS (our goal at a): ∫ v, (ρ (ofLp v) : ℂ) * exp(I * ∑ a_i (ofLp v) i)
  --                       ∂volume_E
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun v => ?_)
  -- Pointwise: 𝐞(-⟪v, aff_map a⟫) • f_E v = (ρ (ofLp v) : ℂ) * exp(I * ∑ a_i v_i)
  show Real.fourierChar (Multiplicative.ofAdd (-(@inner ℝ _ _ v (aff_map a)))) • f_E v =
    (ρ (WithLp.ofLp v) : ℂ) *
      Complex.exp (Complex.I *
        (∑ i : Fin d, (a i : ℂ) * ((WithLp.ofLp v) i : ℂ)))
  -- Compute ⟪v, aff_map a⟫_E = -(2π)⁻¹ * ∑ i, v i * a i.
  have h_inner :
      (@inner ℝ _ _ v (aff_map a) : ℝ) =
        -((2 * Real.pi)⁻¹) * ∑ i : Fin d, v i * a i := by
    show (@inner ℝ _ _ v (-((2 * Real.pi)⁻¹ : ℝ) • (WithLp.toLp 2 a))) = _
    rw [inner_smul_right]
    show -((2 * Real.pi)⁻¹) * (@inner ℝ _ _ v (WithLp.toLp 2 a)) = _
    congr 1
    -- Inner product in EuclideanSpace = sum of products.
    show (@inner ℝ _ _ (v : EuclideanSpace ℝ (Fin d))
        (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin d)) : ℝ) =
      ∑ i : Fin d, v i * a i
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show (@inner ℝ ℝ _ (v i) ((WithLp.toLp 2 a) i)) = v i * a i
    -- For real inner product on ℝ: ⟨x, y⟩ = (conj y) * x = y * x = x * y.
    exact (RCLike.inner_apply (v i) ((WithLp.toLp 2 a) i)).trans (by simp [mul_comm])
  -- 𝐞(-⟪v, aff_map a⟫) = exp(I * ∑ a_i v_i).
  have h_circle :
      ((Real.fourierChar (Multiplicative.ofAdd (-(@inner ℝ _ _ v (aff_map a)))) :
          Circle) : ℂ) =
      Complex.exp (Complex.I * (∑ i : Fin d, (a i : ℂ) * (v i : ℂ))) := by
    rw [Real.fourierChar_apply]
    -- Multiplicative.ofAdd is just a type wrapper; the underlying ℝ value is the same.
    have hofadd : (Multiplicative.ofAdd (-(@inner ℝ _ _ v (aff_map a))) : ℝ) =
        -(@inner ℝ _ _ v (aff_map a) : ℝ) := rfl
    rw [show ((Multiplicative.ofAdd (-(@inner ℝ _ _ v (aff_map a)))) : ℝ) =
          (((2 * Real.pi)⁻¹) * ∑ i : Fin d, v i * a i : ℝ) from by rw [hofadd, h_inner]; ring]
    -- Now the goal has exp(↑(2 * π * (((2 * π)⁻¹) * ∑ v_i a_i)) * I)
    push_cast
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hpiC : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast hpi
    rw [show (2 * (Real.pi : ℂ)) * ((2 * (Real.pi : ℂ))⁻¹ *
          ∑ i : Fin d, ((v i : ℝ) : ℂ) * ((a i : ℝ) : ℂ)) =
        ∑ i : Fin d, ((v i : ℝ) : ℂ) * ((a i : ℝ) : ℂ) from by
      field_simp]
    congr 1
    rw [show ((∑ i : Fin d, ((v i : ℝ) : ℂ) * ((a i : ℝ) : ℂ)) : ℂ) * Complex.I =
        Complex.I * (∑ i : Fin d, (a i : ℂ) * (v i : ℂ)) from by
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring]
  -- Combine: smul = mul, then use h_circle.
  rw [Circle.smul_def, smul_eq_mul, h_circle]
  -- Goal: exp(I * ∑ a_i v_i) * f_E v = (ρ (ofLp v) : ℂ) * exp(I * ∑ a_i (ofLp v) i)
  -- f_E v = (ρ (ofLp v) : ℂ); (ofLp v) i = v i; final identity is mul_comm.
  show Complex.exp (Complex.I * ∑ i : Fin d, (a i : ℂ) * (v i : ℂ)) * f_E v =
    (ρ (WithLp.ofLp v) : ℂ) *
      Complex.exp (Complex.I *
        ∑ i : Fin d, (a i : ℂ) * ((WithLp.ofLp v) i : ℂ))
  show Complex.exp (Complex.I * ∑ i : Fin d, (a i : ℂ) * (v i : ℂ)) *
      (ρ (WithLp.ofLp v) : ℂ) =
    (ρ (WithLp.ofLp v) : ℂ) *
      Complex.exp (Complex.I *
        ∑ i : Fin d, (a i : ℂ) * ((WithLp.ofLp v) i : ℂ))
  ring

end Ruelle
end OSReconstruction

end
