/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Unbounded.Spectral
import OSReconstruction.vNA.Bochner.FunctionalCalculusLinearity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Convergence Theorems for Spectral Integrals

This file provides convergence theorems for the spectral functional calculus
`functionalCalculus P f` defined in `Unbounded/Spectral.lean`.

## Main Results

* `functionalCalculus_norm_sq`: The **norm-squared identity**:
    `‖f(T)x‖² = ∫ |f|² dμ_x` where `μ_x` is the diagonal spectral measure.
  This is the key bridge between operator norms and scalar integrals.

* `functionalCalculus_tendsto_SOT`: **Dominated convergence in SOT**:
    If `fₙ → f` pointwise and `|fₙ| ≤ g` with `g²` integrable,
    then `fₙ(T)x → f(T)x` for all x.

## Mathematical Background

The norm-squared identity is fundamental:
  `‖f(T)x‖² = ⟨f(T)x, f(T)x⟩ = ⟨x, f̄(T)f(T)x⟩ = ⟨x, |f|²(T)x⟩ = ∫ |f|² dμ_x`

This uses:
- `functionalCalculus_star`: `f(T)* = f̄(T)`
- `functionalCalculus_mul`: `f(T)g(T) = (fg)(T)`
- `functionalCalculus_inner_self`: `⟨x, f(T)x⟩ = ∫ f dμ_x`

The dominated convergence theorem then follows:
  `‖fₙ(T)x - f(T)x‖² = ‖(fₙ-f)(T)x‖² = ∫ |fₙ-f|² dμ_x → 0`
by the scalar dominated convergence theorem (Mathlib's
`tendsto_integral_of_dominated_convergence`).

## Coordination with existing infrastructure

- `vNA/Unbounded/Spectral.lean`: `SpectralMeasure`, `functionalCalculus`,
  `functionalCalculus_mul`, `functionalCalculus_star`, `diagonalMeasure`,
  `functionalCalculus_inner_self`
- `vNA/MeasureTheory/SpectralIntegral.lean`: `sesquilinearToOperator`
- `vNA/MeasureTheory/SpectralStieltjes.lean`: `ProjectionValuedMeasure`, `diagonalMeasure`

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VIII
-/

noncomputable section

open MeasureTheory Complex Filter Topology SpectralMeasure
open scoped InnerProduct ComplexConjugate

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Norm-squared identity -/

/-- The norm-squared identity for the spectral functional calculus:
    `‖f(T)x‖² = ∫ |f(t)|² dμ_x(t)`

    where `μ_x` is the diagonal spectral measure `μ_x(E) = ⟨x, P(E)x⟩`.

    **Proof:**
    ```
    ⟪f(T)x, f(T)x⟫ = (↑‖f(T)x‖)²       (inner_self_eq_norm_sq_to_K)
    ⟪f(T)x, f(T)x⟫ = ⟪x, f(T)*f(T)x⟫   (adjoint)
                     = ⟪x, (f̄·f)(T)x⟫    (star + mul)
                     = ∫ f̄·f dμ_x         (functionalCalculus_inner_self)
                     = ∫ ↑‖f‖² dμ_x       (f̄·f = ‖f‖²)
                     = ↑(∫ ‖f‖² dμ_x)     (integral_ofReal)
    ``` -/
theorem functionalCalculus_norm_sq (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    -- Integrability and boundedness of star f
    (hsf_int : ∀ z : H, Integrable (star ∘ f) (P.diagonalMeasure z))
    (hsf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(star ∘ f) t‖ ≤ M)
    -- Integrability and boundedness of |f|² = (star f) * f
    (hff_int : ∀ z : H, Integrable ((star ∘ f) * f) (P.diagonalMeasure z))
    (hff_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖((star ∘ f) * f) t‖ ≤ M)
    -- Measurability of f (for multiplicativity)
    (hf_meas : Measurable f)
    (x : H) :
    (‖functionalCalculus P f hf_int hf_bdd x‖ : ℝ)^2 =
    ∫ t, ‖f t‖^2 ∂(P.diagonalMeasure x) := by
  -- Step 1: ‖v‖² = re⟨v,v⟩
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  -- Step 2: ⟨f(T)x, f(T)x⟩ = ⟨x, f(T)*f(T)x⟩
  have h2 : @inner ℂ H _ (functionalCalculus P f hf_int hf_bdd x)
      (functionalCalculus P f hf_int hf_bdd x) =
      @inner ℂ H _ x ((functionalCalculus P f hf_int hf_bdd).adjoint
        (functionalCalculus P f hf_int hf_bdd x)) := by
    rw [ContinuousLinearMap.adjoint_inner_right]
  -- Step 3: f(T)* = f̄(T)
  have h3 : (functionalCalculus P f hf_int hf_bdd).adjoint =
      functionalCalculus P (star ∘ f) hsf_int hsf_bdd :=
    functionalCalculus_star P f hf_int hf_bdd hsf_int hsf_bdd
  -- Step 4: f̄(T)·f(T) = (f̄·f)(T)
  have h4 : functionalCalculus P (star ∘ f) hsf_int hsf_bdd ∘L
      functionalCalculus P f hf_int hf_bdd =
      functionalCalculus P ((star ∘ f) * f) hff_int hff_bdd := by
    rw [← functionalCalculus_mul P (star ∘ f) f hsf_int hsf_bdd hf_int hf_bdd
      hff_int hff_bdd hf_meas]
  -- Combine steps 2-4: ⟨f(T)x, f(T)x⟩ = ⟨x, (f̄f)(T)x⟩
  have h234 : @inner ℂ H _ (functionalCalculus P f hf_int hf_bdd x)
      (functionalCalculus P f hf_int hf_bdd x) =
      @inner ℂ H _ x (functionalCalculus P ((star ∘ f) * f) hff_int hff_bdd x) := by
    rw [h2, h3]
    congr 1
    have := congrFun (congrArg DFunLike.coe h4) x
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this
  -- Step 5: ⟨x, (f̄f)(T)x⟩ = ∫ (f̄f) dμ_x  (via functionalCalculus_inner_self)
  have h5 : @inner ℂ H _ x (functionalCalculus P ((star ∘ f) * f) hff_int hff_bdd x) =
      ∫ t, ((star ∘ f) * f) t ∂(P.diagonalMeasure x) :=
    functionalCalculus_inner_self P ((star ∘ f) * f) hff_int hff_bdd x
  -- Step 6: (f̄·f)(t) = ↑‖f(t)‖² (as ℂ)
  -- Uses: starRingEnd ℂ (f t) * f t = ⟪f t, f t⟫_ℂ = (↑‖f t‖)² = ↑(‖f t‖²)
  have h6 : ∀ t, ((star ∘ f) * f) t = (↑(‖f t‖^2) : ℂ) := by
    intro t
    show starRingEnd ℂ (f t) * f t = ↑(‖f t‖ ^ 2)
    rw [mul_comm, ← @RCLike.inner_apply ℂ, inner_self_eq_norm_sq_to_K]; norm_cast
  -- Combine: re⟨f(T)x, f(T)x⟩ = re(∫ ↑‖f‖² dμ_x) = ∫ ‖f‖² dμ_x
  rw [h234, h5]
  simp_rw [h6]
  -- Goal: re(∫ t, ↑(‖f t‖²) dμ_x) = ∫ t, ‖f t‖² dμ_x
  -- Pull re inside the integral, then re(↑r) = r
  have hint : Integrable (fun t => (↑(‖f t‖ ^ 2) : ℂ)) (P.diagonalMeasure x) :=
    (hff_int x).congr (Eventually.of_forall h6)
  conv_lhs => rw [show RCLike.re (∫ t, (↑(‖f t‖ ^ 2) : ℂ) ∂P.diagonalMeasure x) =
    ∫ t, RCLike.re (↑(‖f t‖ ^ 2) : ℂ) ∂P.diagonalMeasure x from (integral_re hint).symm]
  congr 1

/-! ### Simplified norm-squared identity -/

/-- Simplified norm-squared identity that automatically derives the auxiliary
    hypotheses (star, product) from basic integrability and measurability. -/
theorem functionalCalculus_norm_sq' (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hf_meas : Measurable f)
    (x : H) :
    (‖functionalCalculus P f hf_int hf_bdd x‖ : ℝ)^2 =
    ∫ t, ‖f t‖^2 ∂(P.diagonalMeasure x) := by
  -- Derive star hypotheses: star preserves norm and measurability
  have hf_meas_star : Measurable (star ∘ f) := continuous_star.measurable.comp hf_meas
  have hsf_int : ∀ z : H, Integrable (star ∘ f) (P.diagonalMeasure z) := by
    intro z
    exact (hf_int z).mono (hf_meas_star.aestronglyMeasurable)
      (Eventually.of_forall fun t => by simp [Function.comp_apply])
  have hsf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(star ∘ f) t‖ ≤ M := by
    obtain ⟨M, hM_nn, hM⟩ := hf_bdd
    exact ⟨M, hM_nn, fun t => by rw [Function.comp_apply, norm_star]; exact hM t⟩
  -- Derive |f|² = (star f) * f hypotheses
  have h_norm_sq_eq : ∀ t, ‖((star ∘ f) * f) t‖ = ‖f t‖ ^ 2 := by
    intro t; show ‖star (f t) * f t‖ = ‖f t‖ ^ 2
    rw [norm_mul, norm_star, sq]
  have hf_bdd' := hf_bdd
  obtain ⟨M, hM_nn, hM⟩ := hf_bdd'
  have hff_int : ∀ z : H, Integrable ((star ∘ f) * f) (P.diagonalMeasure z) := by
    intro z
    exact ((hf_int z).norm.const_mul M).mono'
      ((hf_meas_star.mul hf_meas).aestronglyMeasurable)
      (Eventually.of_forall fun t => by
        rw [h_norm_sq_eq]
        calc ‖f t‖ ^ 2 = ‖f t‖ * ‖f t‖ := sq (‖f t‖)
          _ ≤ M * ‖f t‖ := mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _))
  have hff_bdd : ∃ M', 0 ≤ M' ∧ ∀ t, ‖((star ∘ f) * f) t‖ ≤ M' :=
    ⟨M ^ 2, sq_nonneg _, fun t => by
      rw [h_norm_sq_eq]
      calc ‖f t‖ ^ 2 = ‖f t‖ * ‖f t‖ := sq (‖f t‖)
        _ ≤ M * M := mul_le_mul (hM t) (hM t) (norm_nonneg _) (le_trans (norm_nonneg _) (hM t))
        _ = M ^ 2 := (sq M).symm⟩
  exact functionalCalculus_norm_sq P f hf_int hf_bdd hsf_int hsf_bdd hff_int hff_bdd hf_meas x

/-- Diagonal spectral measure of `f(T)x`, tested against `g`, is obtained by
weighting the diagonal measure of `x` by `|f|^2`.

This is the generic spectral identity behind the fixed-measure / varying-weight
route: once a family of vectors is realized as `f_n(T)x` over a fixed spectral
measure, all pairings against another bounded Borel symbol `g` become scalar
integrals against the fixed diagonal measure with weights `‖f_n‖^2`. -/
theorem diagonalMeasure_functionalCalculus_weighted_integral
    (P : SpectralMeasure H)
    (f g : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hsf_int : ∀ z : H, Integrable (star ∘ f) (P.diagonalMeasure z))
    (hsf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(star ∘ f) t‖ ≤ M)
    (hg_int : ∀ z : H, Integrable g (P.diagonalMeasure z))
    (hg_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖g t‖ ≤ M)
    (hgf_int : ∀ z : H, Integrable (g * f) (P.diagonalMeasure z))
    (hgf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(g * f) t‖ ≤ M)
    (hsgff_int : ∀ z : H, Integrable ((star ∘ f) * (g * f)) (P.diagonalMeasure z))
    (hsgff_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖((star ∘ f) * (g * f)) t‖ ≤ M)
    (hf_meas : Measurable f)
    (hg_meas : Measurable g)
    (x : H) :
    ∫ t, g t ∂(P.diagonalMeasure (functionalCalculus P f hf_int hf_bdd x)) =
      ∫ t, g t * (↑(‖f t‖ ^ 2) : ℂ) ∂(P.diagonalMeasure x) := by
  let fT := functionalCalculus P f hf_int hf_bdd
  let gT := functionalCalculus P g hg_int hg_bdd
  let fx := fT x
  have hmul_gf :
      functionalCalculus P (g * f) hgf_int hgf_bdd = gT ∘L fT := by
    simpa [fT, gT] using
      (functionalCalculus_mul P g f hg_int hg_bdd hf_int hf_bdd hgf_int hgf_bdd hf_meas)
  have hstar :
      ContinuousLinearMap.adjoint fT = functionalCalculus P (star ∘ f) hsf_int hsf_bdd := by
    simpa [fT] using
      (functionalCalculus_star P f hf_int hf_bdd hsf_int hsf_bdd)
  have hmul_sgff :
      functionalCalculus P ((star ∘ f) * (g * f)) hsgff_int hsgff_bdd =
        (functionalCalculus P (star ∘ f) hsf_int hsf_bdd) ∘L
          (functionalCalculus P (g * f) hgf_int hgf_bdd) := by
    have hgf_meas : Measurable (g * f) := hg_meas.mul hf_meas
    simpa using
      (functionalCalculus_mul P (star ∘ f) (g * f)
        hsf_int hsf_bdd hgf_int hgf_bdd hsgff_int hsgff_bdd hgf_meas)
  calc
    ∫ t, g t ∂(P.diagonalMeasure fx)
      = @inner ℂ H _ fx (gT fx) := by
          symm
          exact functionalCalculus_inner_self P g hg_int hg_bdd fx
    _ = @inner ℂ H _ x (ContinuousLinearMap.adjoint fT (gT (fT x))) := by
          exact (ContinuousLinearMap.adjoint_inner_right fT x (gT (fT x))).symm
    _ = @inner ℂ H _ x
          ((functionalCalculus P (star ∘ f) hsf_int hsf_bdd) (gT (fT x))) := by
          rw [hstar]
    _ = @inner ℂ H _ x
          (((functionalCalculus P (star ∘ f) hsf_int hsf_bdd) ∘L
              (functionalCalculus P (g * f) hgf_int hgf_bdd)) x) := by
          rw [hmul_gf]
          simp [ContinuousLinearMap.comp_apply, fT, gT]
    _ = @inner ℂ H _ x
          (functionalCalculus P ((star ∘ f) * (g * f)) hsgff_int hsgff_bdd x) := by
          rw [← hmul_sgff]
    _ = ∫ t, ((star ∘ f) * (g * f)) t ∂(P.diagonalMeasure x) := by
          exact functionalCalculus_inner_self P ((star ∘ f) * (g * f)) hsgff_int hsgff_bdd x
    _ = ∫ t, g t * (↑(‖f t‖ ^ 2) : ℂ) ∂(P.diagonalMeasure x) := by
          refine integral_congr_ae ?_
          filter_upwards with t
          have hnorm_sq : starRingEnd ℂ (f t) * f t = (↑(‖f t‖ ^ 2) : ℂ) := by
            rw [mul_comm, ← @RCLike.inner_apply ℂ, inner_self_eq_norm_sq_to_K]
            norm_cast
          simpa [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using
            congrArg (fun z : ℂ => g t * z) hnorm_sq

/-! ### Dominated convergence for spectral integrals -/

/-- Dominated convergence in the strong operator topology for spectral integrals:
    If `fₙ → f` pointwise and `‖fₙ(t)‖ ≤ g(t)` with `g²` integrable w.r.t. all
    diagonal spectral measures, then `fₙ(T)x → f(T)x` for all x.

    **Proof:** Using the norm-squared identity and linearity:
    `‖fₙ(T)x - f(T)x‖² = ‖(fₙ-f)(T)x‖² = ∫ |fₙ-f|² dμ_x → 0`
    by the scalar dominated convergence theorem, since `|fₙ-f|² ≤ 4g²` and
    `|fₙ(t)-f(t)|² → 0` pointwise. -/
theorem functionalCalculus_tendsto_SOT (P : SpectralMeasure H)
    (f : ℕ → ℝ → ℂ) (flim : ℝ → ℂ)
    -- Pointwise convergence
    (hf_tend : ∀ t, Tendsto (fun n => f n t) atTop (nhds (flim t)))
    -- Uniform bound
    (g : ℝ → ℝ) (hg_nonneg : ∀ t, 0 ≤ g t)
    (hf_bound : ∀ n t, ‖f n t‖ ≤ g t)
    (hflim_bound : ∀ t, ‖flim t‖ ≤ g t)
    -- g is bounded (for operator norm bounds)
    (hg_bdd : ∃ M, ∀ t, g t ≤ M)
    -- g² is integrable w.r.t. all diagonal spectral measures
    (hg2_int : ∀ z : H, Integrable (fun t => (g t)^2) (P.diagonalMeasure z))
    -- Integrability hypotheses for each fₙ and flim
    (hf_int : ∀ n z, Integrable (f n) (P.diagonalMeasure z))
    (hf_bdd : ∀ n, ∃ M, 0 ≤ M ∧ ∀ t, ‖f n t‖ ≤ M)
    (hflim_int : ∀ z, Integrable flim (P.diagonalMeasure z))
    (hflim_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖flim t‖ ≤ M)
    -- Measurability hypotheses (needed for norm-squared identity)
    (hf_meas : ∀ n, Measurable (f n))
    (hflim_meas : Measurable flim)
    (x : H) :
    Tendsto (fun n => functionalCalculus P (f n) (hf_int n) (hf_bdd n) x)
      atTop (nhds (functionalCalculus P flim hflim_int hflim_bdd x)) := by
  -- === Hypotheses for the difference function d n = f n - flim ===
  obtain ⟨Mg, hMg⟩ := hg_bdd
  have hMg_nn : 0 ≤ Mg := le_trans (hg_nonneg 0) (hMg 0)
  -- Integrability of d n
  have hd_int : ∀ n z, Integrable (f n - flim) (P.diagonalMeasure z) :=
    fun n z => (hf_int n z).sub (hflim_int z)
  -- Norm bound: ‖d n t‖ ≤ 2g(t) ≤ 2Mg
  have hd_bound : ∀ n t, ‖(f n - flim) t‖ ≤ 2 * g t := by
    intro n t; show ‖f n t - flim t‖ ≤ 2 * g t
    calc ‖f n t - flim t‖ ≤ ‖f n t‖ + ‖flim t‖ := norm_sub_le _ _
      _ ≤ g t + g t := add_le_add (hf_bound n t) (hflim_bound t)
      _ = 2 * g t := by ring
  have hd_bdd : ∀ n, ∃ M, 0 ≤ M ∧ ∀ t, ‖(f n - flim) t‖ ≤ M := by
    intro n; exact ⟨2 * Mg, by linarith, fun t =>
      le_trans (hd_bound n t) (by nlinarith [hMg t])⟩
  -- Measurability of d n
  have hd_meas : ∀ n, Measurable (f n - flim) := fun n => (hf_meas n).sub hflim_meas
  -- === Key identity: fₙ(T) - flim(T) = (fₙ - flim)(T) ===
  have hsub : ∀ n, functionalCalculus P (f n) (hf_int n) (hf_bdd n) -
      functionalCalculus P flim hflim_int hflim_bdd =
      functionalCalculus P (f n - flim) (hd_int n) (hd_bdd n) :=
    fun n => (P.functionalCalculus_sub (f n) flim (hf_int n) (hf_bdd n)
      hflim_int hflim_bdd (hd_int n) (hd_bdd n)).symm
  -- === Norm-squared identity for d n ===
  have hnorm_sq : ∀ n, (‖functionalCalculus P (f n - flim) (hd_int n) (hd_bdd n) x‖ : ℝ)^2 =
      ∫ t, ‖(f n - flim) t‖^2 ∂(P.diagonalMeasure x) :=
    fun n => functionalCalculus_norm_sq' P (f n - flim) (hd_int n) (hd_bdd n) (hd_meas n) x
  -- === Scalar DCT: ∫ ‖dₙ‖² dμ_x → 0 ===
  have hint_tend : Tendsto (fun n => ∫ t, ‖(f n - flim) t‖^2 ∂(P.diagonalMeasure x))
      atTop (nhds 0) := by
    -- Apply scalar DCT with dominating function 4g²
    -- The limit function is the zero function (since |fₙ(t) - f(t)|² → 0)
    have h_lim : ∀ᵐ t ∂(P.diagonalMeasure x),
        Tendsto (fun n => ‖(f n - flim) t‖ ^ 2) atTop (nhds 0) := by
      apply Eventually.of_forall; intro t
      have : Tendsto (fun n => f n t - flim t) atTop (nhds 0) := by
        rw [show (0 : ℂ) = flim t - flim t from (sub_self _).symm]
        exact (hf_tend t).sub tendsto_const_nhds
      have : Tendsto (fun n => ‖f n t - flim t‖) atTop (nhds 0) := by
        rw [show (0 : ℝ) = ‖(0 : ℂ)‖ from norm_zero.symm]
        exact continuous_norm.continuousAt.tendsto.comp this
      rw [show (0 : ℝ) = 0 ^ 2 from (zero_pow two_ne_zero).symm]
      exact this.pow 2
    have h_bound : ∀ n, ∀ᵐ t ∂(P.diagonalMeasure x),
        ‖‖(f n - flim) t‖ ^ 2‖ ≤ 4 * (g t) ^ 2 := by
      intro n; apply Eventually.of_forall; intro t
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      show ‖f n t - flim t‖ ^ 2 ≤ 4 * (g t) ^ 2
      calc ‖f n t - flim t‖ ^ 2 ≤ (2 * g t) ^ 2 :=
            sq_le_sq' (by linarith [norm_nonneg (f n t - flim t), hg_nonneg t]) (hd_bound n t)
        _ = 4 * (g t) ^ 2 := by ring
    have h_meas : ∀ n, AEStronglyMeasurable (fun t => ‖(f n - flim) t‖ ^ 2)
        (P.diagonalMeasure x) :=
      fun n => ((hd_meas n).norm.pow_const 2).aestronglyMeasurable
    have h_dom_int : Integrable (fun t => 4 * (g t) ^ 2) (P.diagonalMeasure x) := by
      have : (fun t => 4 * (g t) ^ 2) = (fun t => (4 : ℝ) • (g t) ^ 2) := by
        ext t; exact (smul_eq_mul _ _).symm
      rw [this]; exact (hg2_int x).smul (4 : ℝ)
    have := tendsto_integral_of_dominated_convergence _ h_meas h_dom_int h_bound h_lim
    simp only [integral_zero] at this
    exact this
  -- === Conclude: ‖fₙ(T)x - f(T)x‖ → 0 ===
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hint_tend) (ε ^ 2) (by positivity)
  exact ⟨N, fun n hn => by
    rw [dist_eq_norm]
    -- ‖fₙ(T)x - f(T)x‖ = ‖(fₙ-f)(T)x‖
    have h_eq : functionalCalculus P (f n) (hf_int n) (hf_bdd n) x -
        functionalCalculus P flim hflim_int hflim_bdd x =
        functionalCalculus P (f n - flim) (hd_int n) (hd_bdd n) x := by
      rw [← ContinuousLinearMap.sub_apply]; congr 1; exact hsub n
    rw [h_eq]
    -- From ‖v‖² < ε², conclude ‖v‖ < ε (using nlinarith)
    by_contra h_not
    push_neg at h_not -- ε ≤ ‖v‖
    have h_sq_ge : ε ^ 2 ≤ (‖functionalCalculus P (f n - flim) (hd_int n) (hd_bdd n) x‖ : ℝ) ^ 2 :=
      sq_le_sq' (by linarith) h_not
    have h_int_lt : ∫ t, ‖(f n - flim) t‖ ^ 2 ∂(P.diagonalMeasure x) < ε ^ 2 := by
      have := hN n hn
      rw [dist_zero_right, Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at this
      exact this
    linarith [hnorm_sq n]⟩

end
