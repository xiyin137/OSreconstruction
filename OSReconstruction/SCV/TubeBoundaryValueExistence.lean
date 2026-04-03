/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.VladimirovTillmann
import OSReconstruction.GeneralResults.DistributionalLimit
import OSReconstruction.GeneralResults.DiffUnderIntegralSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Tube-Domain Boundary Value Existence from Polynomial Growth

The converse direction of the Vladimirov-Tillmann theorem:
a holomorphic function on a tube domain T(C) with the global Vladimirov
growth bound has tempered distributional boundary values.

This is the **critical SCV theorem** needed for OS reconstruction:
it takes the analytically continued Schwinger functions (which have
polynomial growth from the semigroup contraction) and produces the
Wightman distributions as tempered boundary values.

## Strategy (1D ray integration, avoiding Poincaré lemma)

Fix η ∈ C and approach the boundary along the ray y = tη for t > 0.

1. The Vladimirov bound along the ray: |F(x+itη)| ≤ C(1+|x|)^N · t^{-q}
2. Define the k-th iterated integral using Cauchy's repeated integration formula:
   `G_k(x,t) = (i^k / (k-1)!) ∫_{t₀}^{t} (t-τ)^{k-1} F(x+iτη) dτ`
   This is ONE integral (not k nested integrals), avoiding Fubini boilerplate.
3. For k > q, the t^{-q} singularity is integrable: (t-τ)^{k-1} · τ^{-q} ∈ L¹
4. G_k(x,t) extends continuously to t = 0 as a function H(x)
5. H(x) has polynomial growth (inherited from F)
6. Define the boundary value W as a distributional derivative by duality:
   `⟨W, φ⟩ = (-1)^k ∫ H(x) · ((η·∇_x)^k φ(x)) dx + ⟨correction terms, φ⟩`
   Since φ is Schwartz, (η·∇)^k φ is Schwartz, and the integral converges.

This constructs W ∈ S'(ℝ^m) using only 1D real integrals — no Poincaré lemma,
no Fourier multiplier traps, no Fréchet-valued integration.

## References

- Vladimirov, "Methods of Generalized Functions", §25
- See docs/vladimirov_tillmann_proof_plan.md (Phase 4)
- See docs/vladimirov_tillmann_gemini_reviews.md (ray integration trick)
-/

open scoped Classical ComplexConjugate BigOperators NNReal
open MeasureTheory Complex Filter
noncomputable section

variable {m : ℕ}

/-! ### General-purpose distribution theory axioms -/

/-- A continuous function with polynomial growth defines a tempered distribution
    via integration against Schwartz test functions.

    This is a standard functional analysis fact: if |F(x)| ≤ C(1+‖x‖)^N,
    then φ ↦ ∫ F(x)φ(x) dx is continuous on Schwartz space (because
    polynomial times Schwartz is integrable, and the Schwartz seminorm
    bound gives |∫ Fφ| ≤ C · ‖φ‖_{N+dim+1, 0}).

    Ref: Hörmander, "The Analysis of Linear PDOs I", Theorem 7.1.5 -/
theorem polyGrowth_temperedDistribution {m : ℕ}
    (F : (Fin m → ℝ) → ℂ) (hF_cont : Continuous F)
    (C_bd : ℝ) (N : ℕ) (hC_bd : 0 < C_bd)
    (hF_growth : ∀ x : Fin m → ℝ, ‖F x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    ∃ (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        T φ = ∫ x : Fin m → ℝ, F x * φ x := by
  let n : ℕ := (volume : Measure (Fin m → ℝ)).integrablePower
  let s : Finset (ℕ × ℕ) := Finset.Iic (N + n, 0)
  let A : SchwartzMap (Fin m → ℝ) ℂ → ℂ := fun φ => ∫ x : Fin m → ℝ, F x * φ x
  have hpointwise_decay :
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ) (x : Fin m → ℝ),
        ‖F x * φ x‖ ≤
          (1 + ‖x‖) ^ (- (n : ℝ)) *
            (C_bd * (2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ)) := by
    intro φ x
    have hsch :
        (1 + ‖x‖) ^ (N + n) * ‖φ x‖ ≤
          2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ := by
      simpa [s] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℂ) (m := (N + n, 0)) (k := N + n) (n := 0)
          le_rfl le_rfl φ x)
    have hdecay :
        (1 + ‖x‖) ^ N * ‖φ x‖ ≤
          (1 + ‖x‖) ^ (- (n : ℝ)) *
            (2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ) := by
      rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul, le_div_iff₀' (by positivity),
        Real.rpow_natCast]
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hsch
    rw [Complex.norm_mul]
    calc
      ‖F x‖ * ‖φ x‖ ≤ (C_bd * (1 + ‖x‖) ^ N) * ‖φ x‖ := by
        gcongr
        exact hF_growth x
      _ = C_bd * ((1 + ‖x‖) ^ N * ‖φ x‖) := by ring
      _ ≤ C_bd * ((1 + ‖x‖) ^ (- (n : ℝ)) *
            (2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ)) := by
        gcongr
      _ = (1 + ‖x‖) ^ (- (n : ℝ)) *
            (C_bd * (2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ)) := by
        ring
  have hdom_integrable :
      Integrable (fun x : Fin m → ℝ => (1 + ‖x‖) ^ (- (n : ℝ))) := by
    simpa [n] using
      (MeasureTheory.Measure.integrable_pow_neg_integrablePower
        (μ := (volume : Measure (Fin m → ℝ))))
  have hA_integrable :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ, Integrable (fun x : Fin m → ℝ => F x * φ x) := by
    intro φ
    have hdom_mul_integrable :
        Integrable (fun x : Fin m → ℝ =>
          (1 + ‖x‖) ^ (- (n : ℝ)) *
            (C_bd * (2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ))) := by
      exact hdom_integrable.mul_const _
    refine Integrable.mono' hdom_mul_integrable
      (hF_cont.aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable)
      (Eventually.of_forall (hpointwise_decay φ))
  have hbound :
      ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
        ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
          ‖A φ‖ ≤ C * (s'.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ := by
    refine ⟨s, C_bd * (2 ^ (N + n) * ∫ x : Fin m → ℝ, (1 + ‖x‖) ^ (- (n : ℝ))), ?_, ?_⟩
    · positivity
    · intro φ
      calc
        ‖A φ‖ = ‖∫ x : Fin m → ℝ, F x * φ x‖ := rfl
        _ ≤ ∫ x : Fin m → ℝ,
            (1 + ‖x‖) ^ (- (n : ℝ)) *
              (C_bd * (2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ)) := by
            exact MeasureTheory.norm_integral_le_of_norm_le
              ((hdom_integrable.mul_const
                (C_bd * (2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ))))
              (Eventually.of_forall (hpointwise_decay φ))
        _ = C_bd * (2 ^ (N + n) * ∫ x : Fin m → ℝ, (1 + ‖x‖) ^ (- (n : ℝ))) *
              (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ := by
            rw [integral_mul_const]
            ring
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (D := Fin m → ℝ) (E := ℂ) (G := ℂ)
    A
    (fun φ ψ => by
      simp [A, mul_add, integral_add, hA_integrable φ, hA_integrable ψ])
    (fun a φ => by
      simp [A, smul_eq_mul, mul_left_comm, integral_const_mul])
    hbound, ?_⟩
  intro φ
  rfl

/-! ### The directional derivative operator -/

/-- The directional derivative as a continuous linear operator on Schwartz space.
    `(η · ∇) φ (x) = ∑_j η_j · (∂φ/∂x_j)(x)`

    This is `lineDerivOpCLM` from Mathlib's `SchwartzMap.Deriv`, which is
    `evalCLM m ∘L fderivCLM` — the composition of the Fréchet derivative
    (a CLM 𝓢(E,F) →L 𝓢(E, E →L F)) with evaluation at direction η. -/
def directionalDerivSchwartz {m : ℕ} (η : Fin m → ℝ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (Fin m → ℝ) ℂ) η

/-- The distributional directional derivative of a tempered distribution.
    Defined by duality: ⟨(η·∇)T, φ⟩ = -⟨T, (η·∇)φ⟩.

    This is NOT an axiom — it's just `-(T.comp (directionalDerivSchwartz η))`,
    which is automatically a CLM by `ContinuousLinearMap.comp` + `Neg`. -/
def distribDirectionalDeriv {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) (η : Fin m → ℝ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
  -(T.comp (directionalDerivSchwartz η))

theorem distribDirectionalDeriv_apply {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) (η : Fin m → ℝ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    distribDirectionalDeriv T η φ = -(T (directionalDerivSchwartz η φ)) := by
  simp [distribDirectionalDeriv]

/-- The k-th iterated distributional directional derivative. -/
def iteratedDistribDirectionalDeriv {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) (η : Fin m → ℝ) (k : ℕ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
  ((-1 : ℂ) ^ k) • (T.comp ((directionalDerivSchwartz η) ^ k))

/-- The k-th iterated directional derivative. -/
def iteratedDirectionalDerivSchwartz (η : Fin m → ℝ) (k : ℕ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
  (directionalDerivSchwartz η) ^ k

/-! ### The slice functional -/

/-- Integration of F(x+iy) against a test function, for y in the tube. -/
def tubeSlice
    (F : (Fin m → ℂ) → ℂ) (y : Fin m → ℝ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) : ℂ :=
  ∫ x : Fin m → ℝ, F (fun i => (x i : ℂ) + (y i : ℂ) * I) * φ x

/-! ### Cauchy's repeated integration formula -/

/-- The k-th iterated integral of the slice functional along a ray η ∈ C.
    Using Cauchy's formula for repeated integration:

    `G_k(φ, t) = (1/(k-1)!) ∫_{t₀}^{t} (t-τ)^{k-1} · tubeSlice F (τ•η) φ dτ`

    This is a single 1D integral, avoiding recursive definition + Fubini. -/
def cauchyRepeatedIntegral
    (F : (Fin m → ℂ) → ℂ) (η : Fin m → ℝ) (t₀ : ℝ)
    (k : ℕ) (φ : SchwartzMap (Fin m → ℝ) ℂ) (t : ℝ) : ℂ :=
  (((k - 1).factorial : ℝ)⁻¹ : ℂ) *
    ∫ τ in Set.Icc t₀ t,
      ((t - τ) ^ (k - 1) : ℝ) * tubeSlice F (τ • η) φ

/-! ### Sub-lemmas for the boundary value construction -/

/-- For each ε > 0 and η ∈ C, the slice functional defines a tempered distribution.
    This is because F(x+iεη) has polynomial growth in x (from the Vladimirov bound
    with y = εη fixed), so `polyGrowth_temperedDistribution` applies. -/
theorem tubeSlice_temperedDistribution
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_cone : IsCone C)
    {F : (Fin m → ℂ) → ℂ}
    (hF_cont : ContinuousOn F (SCV.TubeDomain C))
    {C_bd : ℝ} {N M : ℕ} (hC_bd : 0 < C_bd)
    (hF_growth : ∀ z ∈ SCV.TubeDomain C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N *
        (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M)
    (η : Fin m → ℝ) (hη : η ∈ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T_ε : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      ∀ φ, T_ε φ = tubeSlice F (ε • η) φ := by
  -- F_ε(x) := F(x + iεη) is continuous with polynomial growth in x:
  -- |F(x+iεη)| ≤ C_bd (1+‖(x,εη)‖)^N · (dist(εη,∂C)⁻¹ + 1)^M
  -- The dist factor is a constant D_ε for fixed ε,η.
  -- So |F_ε(x)| ≤ C_bd · D_ε^M · (1+‖x‖+ε‖η‖)^N ≤ C' · (1+‖x‖)^N
  -- Then polyGrowth_temperedDistribution gives the result.
  --
  -- Step 1: εη ∈ C (cone scaling)
  have hεη : ε • η ∈ C := hC_cone η hη ε hε
  -- Step 2: x+iεη ∈ TubeDomain C for all x
  have hmem : ∀ x : Fin m → ℝ,
      (fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I) ∈ SCV.TubeDomain C := by
    intro x
    show (fun i => ((fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I) i).im) ∈ C
    convert hεη using 1
    ext i; simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
  -- Step 3: F_ε(x) = F(x+iεη) has polynomial growth
  -- |F_ε(x)| ≤ C_bd · (1+‖z‖)^N · D^M where D = (1+dist(εη,∂C)⁻¹)
  -- Since ‖z‖ ≤ ‖x‖ + ε‖η‖ and D is constant, this is ≤ C'(1+‖x‖)^N
  let Fε : (Fin m → ℝ) → ℂ := fun x =>
    F (fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I)
  have hslice_cont : Continuous (fun x : Fin m → ℝ =>
      fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I) := by
    fun_prop
  have hFε_cont : Continuous Fε := by
    simpa [Fε] using hF_cont.comp_continuous hslice_cont hmem
  let Cε : ℝ :=
    C_bd * (1 + ‖ε • η‖) ^ N *
      (1 + (Metric.infDist (ε • η) Cᶜ)⁻¹) ^ M
  have hCε_pos : 0 < Cε := by
    dsimp [Cε]
    have hnorm_pos : 0 < 1 + ‖ε • η‖ := by positivity
    have hdist_pos : 0 < 1 + (Metric.infDist (ε • η) Cᶜ)⁻¹ := by
      have hdist_nonneg : 0 ≤ (Metric.infDist (ε • η) Cᶜ)⁻¹ :=
        inv_nonneg.mpr Metric.infDist_nonneg
      linarith
    exact mul_pos (mul_pos hC_bd (pow_pos hnorm_pos _)) (pow_pos hdist_pos _)
  have hFε_growth : ∀ x : Fin m → ℝ, ‖Fε x‖ ≤ Cε * (1 + ‖x‖) ^ N := by
    intro x
    have hgrowth :=
      hF_growth (fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I) (hmem x)
    have hreal_le : ‖fun i => (x i : ℂ)‖ ≤ ‖x‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
      intro i
      simpa using (norm_le_pi_norm x i)
    have himag_le : ‖fun i => (((ε • η) i : ℝ) * I : ℂ)‖ ≤ ‖ε • η‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg (ε • η))]
      intro i
      simpa [Complex.norm_mul, Complex.norm_I] using (norm_le_pi_norm (ε • η) i)
    have hnorm_le : ‖(fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I)‖ ≤ ‖x‖ + ‖ε • η‖ := by
      calc
        ‖(fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I)‖
            ≤ ‖fun i => (x i : ℂ)‖ + ‖fun i => (((ε • η) i : ℝ) * I : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖x‖ + ‖ε • η‖ := add_le_add hreal_le himag_le
    have hbase_le : 1 + ‖(fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I)‖ ≤
        (1 + ‖ε • η‖) * (1 + ‖x‖) := by
      nlinarith [hnorm_le, norm_nonneg x, norm_nonneg (ε • η)]
    have hpow_le :
        (1 + ‖(fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I)‖) ^ N ≤
          ((1 + ‖ε • η‖) * (1 + ‖x‖)) ^ N := by
      exact pow_le_pow_left₀ (by positivity) hbase_le N
    have hdist_nonneg : 0 ≤ (Metric.infDist (ε • η) Cᶜ)⁻¹ :=
      inv_nonneg.mpr Metric.infDist_nonneg
    calc
      ‖Fε x‖
          ≤ C_bd * (1 + ‖(fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I)‖) ^ N *
              (1 + (Metric.infDist (ε • η) Cᶜ)⁻¹) ^ M := by
            simpa [Fε] using hgrowth
      _ ≤ C_bd * (((1 + ‖ε • η‖) * (1 + ‖x‖)) ^ N) *
            (1 + (Metric.infDist (ε • η) Cᶜ)⁻¹) ^ M := by
            gcongr
      _ = Cε * (1 + ‖x‖) ^ N := by
            dsimp [Cε]
            rw [mul_pow]
            ring
  obtain ⟨T_ε, hT_ε⟩ :=
    polyGrowth_temperedDistribution Fε hFε_cont Cε N hCε_pos hFε_growth
  refine ⟨T_ε, ?_⟩
  intro φ
  simpa [Fε, tubeSlice] using hT_ε φ

/-- **Derivative of the tube slice along a positive ray.**

    This is the analytic heart of the ray-integration argument. A complete proof
    needs three ingredients that are not yet fully packaged in this file:

    1. A positive-time extension of `τ ↦ F(x + iτη)` compatible with
       `hasDerivAt_schwartz_integral`, whose hypotheses are global in `τ` while
       the tube slice is only naturally controlled for `τ > 0`.
    2. The Cauchy-Riemann chain-rule computation
       `d/dτ F(x + iτη) = i Σ_j η_j ∂_{x_j} F(x + iτη)`.
    3. The integration-by-parts identity against Schwartz test functions.

    We keep the resulting derivative formula as an interface theorem. -/
axiom hasDerivAt_tubeSlice_ray
    {C : Set (Fin m → ℝ)}
    {F : (Fin m → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (hF_cont : ContinuousOn F (SCV.TubeDomain C))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (hC_cone : IsCone C) (hC_open : IsOpen C)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    HasDerivAt
      (fun τ => tubeSlice F (τ • η) φ)
      (-I * tubeSlice F (τ₀ • η) (directionalDerivSchwartz η φ))
      τ₀

/-- Continuity of the tube-slice derivative along a ray, restricted to τ > 0.

    Needs polynomial growth of F to ensure the integral is well-defined and
    dominated convergence applies for parameter continuity.

    **Previous version was underassumed**: ContinuousOn alone doesn't guarantee
    integrability of F(x+iτη)ψ(x) — e.g., F(z) = exp(z²) is entire but
    |F(x+iτη)| = exp(x²-τ²) grows too fast for Schwartz test functions. -/
axiom continuous_tubeSlice_ray_deriv
    {C : Set (Fin m → ℝ)}
    {F : (Fin m → ℂ) → ℂ}
    (hF_cont : ContinuousOn F (SCV.TubeDomain C))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (hC_cone : IsCone C) (hC_open : IsOpen C)
    -- Polynomial growth needed for integrability + dominated convergence
    {C_bd : ℝ} {N : ℕ} (hC_bd : 0 < C_bd)
    (hF_growth : ∀ z ∈ SCV.TubeDomain C, ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    ContinuousOn (fun (τ : ℝ) => -I * tubeSlice F (τ • η) (directionalDerivSchwartz η φ))
      (Set.Ioi 0)

/-- The Cauchy-Riemann ray-integration identity (1D FTC along a ray in the cone).

    For F holomorphic on T(C) and η ∈ C, the function
    `g(τ) = tubeSlice F (τ • η) φ` satisfies
    `g'(τ) = -i · tubeSlice F (τ • η) (directionalDerivSchwartz η φ)`
    (CR equations + integration by parts).

    Integrating from t₀ to t gives the FTC identity:
    `g(t) - g(t₀) = -i ∫_{t₀}^{t} tubeSlice F (τ•η) (η·∇φ) dτ`

    Proof needs: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` to push
    d/dτ inside the integral, CR equations, integration by parts. -/
theorem cr_integration_identity
    {C : Set (Fin m → ℝ)}
    {F : (Fin m → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (hF_cont : ContinuousOn F (SCV.TubeDomain C))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (hC_cone : IsCone C) (hC_open : IsOpen C)
    {C_bd : ℝ} {N : ℕ} (hC_bd : 0 < C_bd)
    (hF_growth : ∀ z ∈ SCV.TubeDomain C, ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (t₀ t : ℝ) (ht₀ : 0 < t₀) (ht : 0 < t) (ht₀_le_t : t₀ ≤ t)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    tubeSlice F (t • η) φ - tubeSlice F (t₀ • η) φ =
      -I * ∫ τ in Set.Icc t₀ t,
        tubeSlice F (τ • η) (directionalDerivSchwartz η φ) := by
  /-
    Proof:
    1. Define g(τ) = tubeSlice F (τ•η) φ = ∫ F(x+iτη)φ(x) dx
    2. Show g'(τ) = -I · tubeSlice F (τ•η) (directionalDerivSchwartz η φ)
       via hasDerivAt_tubeSlice_ray (CR + IBP + diff under integral)
    3. Apply FTC: g(t) - g(t₀) = ∫_{t₀}^{t} g'(τ) dτ
    4. Convert the interval integral to a set integral on Icc (using t₀ ≤ t)
  -/
  -- Step 1: Define the slice function g and its derivative g'
  let g : ℝ → ℂ := fun τ => tubeSlice F (τ • η) φ
  let g' : ℝ → ℂ := fun τ => -I * tubeSlice F (τ • η) (directionalDerivSchwartz η φ)
  -- Step 2: g has derivative g' at every τ > 0
  have hderiv : ∀ τ₀ : ℝ, 0 < τ₀ → HasDerivAt g (g' τ₀) τ₀ := by
    intro τ₀ hτ₀
    exact hasDerivAt_tubeSlice_ray hF_hol hF_cont η hη hC_cone hC_open τ₀ hτ₀ φ
  -- Step 3: g' is continuous (hence interval integrable)
  have hg'_cont : ContinuousOn g' (Set.Ioi 0) :=
    continuous_tubeSlice_ray_deriv hF_cont η hη hC_cone hC_open hC_bd hF_growth φ
  have hg'_int : IntervalIntegrable g' volume t₀ t :=
    (hg'_cont.mono (by
      intro τ hτ
      exact Set.mem_Ioi.mpr (by rcases Set.mem_uIcc.mp hτ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)
    )).intervalIntegrable
  -- Step 4: HasDerivAt on the full uIcc (both t₀ ≤ τ ≤ t and t ≤ τ ≤ t₀ cases)
  have hderiv_uIcc : ∀ τ ∈ Set.uIcc t₀ t, HasDerivAt g (g' τ) τ := by
    intro τ hτ
    apply hderiv
    rcases Set.mem_uIcc.mp hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  -- Step 5: FTC gives g(t) - g(t₀) = ∫ τ in t₀..t, g'(τ)
  have hFTC : ∫ τ in t₀..t, g' τ = g t - g t₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_uIcc hg'_int
  -- Step 6: Pull out -I from the interval integral
  have key : g t - g t₀ = -I * ∫ τ in t₀..t,
      tubeSlice F (τ • η) (directionalDerivSchwartz η φ) := by
    rw [← hFTC]
    show ∫ τ in t₀..t, g' τ =
      -I * ∫ τ in t₀..t, tubeSlice F (τ • η) (directionalDerivSchwartz η φ)
    simp only [g', intervalIntegral.integral_const_mul]
  -- Step 7: Convert interval integral to set integral on Icc (using t₀ ≤ t)
  rw [key]
  congr 1
  -- Goal: ∫ τ in t₀..t, f τ = ∫ τ in Set.Icc t₀ t, f τ
  -- For Lebesgue measure with t₀ ≤ t:
  --   ∫ τ in t₀..t, f τ = ∫ τ in Ioc t₀ t, f τ    (by integral_of_le)
  --   ∫ τ in Icc t₀ t, f τ = ∫ τ in Ioc t₀ t, f τ  (by integral_Icc_eq_integral_Ioc)
  rw [intervalIntegral.integral_of_le ht₀_le_t, ← integral_Icc_eq_integral_Ioc]


/-! ### The boundary value construction -/

/-- **Main converse theorem**: Vladimirov growth on a tube implies existence of
    tempered distributional boundary values.

    The full proof uses Cauchy regularization, repeated ray integration, and
    the distributional-limit construction. Those steps are not yet fully
    formalized here, so this result remains an explicit interface theorem. -/
axiom tube_boundaryValue_of_vladimirov_growth
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_ne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (SCV.TubeDomain C))
    {C_bd : ℝ} {N M : ℕ} (hC_bd : 0 < C_bd)
    (hF_growth : ∀ (z : Fin m → ℂ), z ∈ SCV.TubeDomain C →
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N *
        (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M) :
    ∃ (W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ)
        (η : Fin m → ℝ), η ∈ C →
        Tendsto
          (fun ε : ℝ => tubeSlice F (ε • η) φ)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W φ))

/-- **Boundary value existence for pure polynomial growth.**

    This is the `M = 0` specialization of the full converse theorem. The proof
    still needs the tube-domain type conversion and the equicontinuous/Cauchy
    limit packaging, so we keep it as an explicit interface theorem for now. -/
axiom tube_boundaryValueData_of_polyGrowth'
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_ne : C.Nonempty)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)
        (η : Fin n → Fin (d + 1) → ℝ),
        η ∈ C →
        Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W φ))

end
