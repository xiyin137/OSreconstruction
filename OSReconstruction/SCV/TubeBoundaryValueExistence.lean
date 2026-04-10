/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.VladimirovTillmann
import OSReconstruction.GeneralResults.DistributionalLimit
import OSReconstruction.GeneralResults.DiffUnderIntegralSchwartz
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Complex.Schwarz
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

set_option maxHeartbeats 400000 in
/-- **Derivative of the tube slice along a positive ray.**

    The slice map is differentiated by applying
    `hasDerivAt_schwartz_integral` to the parameter family
    `τ ↦ (x ↦ F(x + iτη))`.

    The remaining gaps are exactly the analytic pieces that are not yet packaged
    elsewhere in the repo:

    1. the Cauchy-Riemann chain rule for the `τ`-derivative of the slice;
    2. a local polynomial growth bound for that derivative (from Cauchy
       estimates);
    3. the integration-by-parts identity moving the `x`-derivative onto the
       Schwartz test function. -/
theorem hasDerivAt_tubeSlice_ray
    {C : Set (Fin m → ℝ)}
    {F : (Fin m → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (hF_cont : ContinuousOn F (SCV.TubeDomain C))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (hC_cone : IsCone C) (hC_open : IsOpen C)
    {C_bd : ℝ} {N : ℕ} (hC_bd : 0 < C_bd)
    (hF_growth : ∀ z ∈ SCV.TubeDomain C, ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    HasDerivAt
      (fun τ => tubeSlice F (τ • η) φ)
      (-I * tubeSlice F (τ₀ • η) (directionalDerivSchwartz η φ))
      τ₀ := by
  let δ : ℝ := τ₀ / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let slice : ℝ → (Fin m → ℝ) → (Fin m → ℂ) :=
    fun τ x i => (x i : ℂ) + ((τ • η) i : ℝ) * I
  let vη : Fin m → ℂ := fun i => (η i : ℂ) * I
  let Fparam : ℝ → (Fin m → ℝ) → ℂ := fun τ x =>
    if hτ : |τ - τ₀| < δ then F (slice τ x) else 0
  let Fparam' : ℝ → (Fin m → ℝ) → ℂ :=
    fun τ x => if hτ : |τ - τ₀| < δ then (fderiv ℂ F (slice τ x)) (vη) else 0
  have hslice_mem :
      ∀ {τ : ℝ}, |τ - τ₀| < δ → ∀ x : Fin m → ℝ, slice τ x ∈ SCV.TubeDomain C := by
    intro τ hτ x
    rcases abs_lt.mp hτ with ⟨hτ_lo, hτ_hi⟩
    have hτ_pos : 0 < τ := by
      dsimp [δ] at hτ_lo
      linarith
    have hτη : τ • η ∈ C := hC_cone η hη τ hτ_pos
    show (fun i => (slice τ x i).im) ∈ C
    convert hτη using 1
    ext i
    simp [slice, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Pi.smul_apply, smul_eq_mul]
  have hFparam_meas : ∀ τ, AEStronglyMeasurable (Fparam τ) volume := by
    intro τ
    by_cases hτ : |τ - τ₀| < δ
    · have hslice_cont : Continuous (slice τ) := by
        fun_prop
      have hcont : Continuous (Fparam τ) := by
        simpa [Fparam, slice, hτ] using hF_cont.comp_continuous hslice_cont (hslice_mem hτ)
      exact hcont.aestronglyMeasurable
    · simpa [Fparam, hτ] using (continuous_const : Continuous fun _ : Fin m → ℝ => (0 : ℂ)).aestronglyMeasurable
  let Kτ : ℝ := (3 * τ₀ / 2) * ‖η‖
  have hτ_bound : ∀ {τ : ℝ}, |τ - τ₀| < δ → ‖τ • η‖ ≤ Kτ := by
    intro τ hτ
    rcases abs_lt.mp hτ with ⟨hτ_lo, hτ_hi⟩
    have hτ_nonneg : 0 ≤ τ := by
      dsimp [δ] at hτ_lo
      linarith
    have hτ_le : τ ≤ 3 * τ₀ / 2 := by
      dsimp [δ] at hτ_hi
      linarith
    calc
      ‖τ • η‖ = ‖τ‖ * ‖η‖ := by rw [norm_smul]
      _ = τ * ‖η‖ := by simp [abs_of_nonneg hτ_nonneg]
      _ ≤ ((3 * τ₀ / 2) : ℝ) * ‖η‖ := by gcongr
  have hFparam_growth :
      ∀ τ, |τ - τ₀| < δ → ∀ x : Fin m → ℝ,
        ‖Fparam τ x‖ ≤ (C_bd * (1 + Kτ) ^ N) * (1 + ‖x‖) ^ N := by
    intro τ hτ x
    have hgrowth := hF_growth (slice τ x) (hslice_mem hτ x)
    have hreal_le : ‖fun i => (x i : ℂ)‖ ≤ ‖x‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
      intro i
      simpa using (norm_le_pi_norm x i)
    have himag_le : ‖fun i => (((τ • η) i : ℝ) * I : ℂ)‖ ≤ ‖τ • η‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg (τ • η))]
      intro i
      simpa [Complex.norm_mul, Complex.norm_I] using (norm_le_pi_norm (τ • η) i)
    have hnorm_le : ‖slice τ x‖ ≤ ‖x‖ + ‖τ • η‖ := by
      calc
        ‖slice τ x‖
            ≤ ‖fun i => (x i : ℂ)‖ + ‖fun i => (((τ • η) i : ℝ) * I : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖x‖ + ‖τ • η‖ := add_le_add hreal_le himag_le
    have hbase_le : 1 + ‖slice τ x‖ ≤ (1 + Kτ) * (1 + ‖x‖) := by
      have hKτ_nonneg : 0 ≤ Kτ := by
        dsimp [Kτ]
        positivity
      have htauK : ‖τ • η‖ ≤ Kτ := hτ_bound hτ
      nlinarith [hnorm_le, htauK, norm_nonneg x, hKτ_nonneg]
    have hpow_le :
        (1 + ‖slice τ x‖) ^ N ≤ ((1 + Kτ) * (1 + ‖x‖)) ^ N := by
      exact pow_le_pow_left₀ (by positivity) hbase_le N
    calc
      ‖Fparam τ x‖ ≤ C_bd * (1 + ‖slice τ x‖) ^ N := by
        simpa [Fparam, hτ] using hgrowth
      _ ≤ C_bd * (((1 + Kτ) * (1 + ‖x‖)) ^ N) := by
        gcongr
      _ = (C_bd * (1 + Kτ) ^ N) * (1 + ‖x‖) ^ N := by
        rw [mul_pow]
        ring
  have hFparam_deriv :
      ∀ τ, |τ - τ₀| < δ → ∀ x : Fin m → ℝ,
        HasDerivAt (fun s => Fparam s x) (Fparam' τ x) τ := by
    intro τ hτ x
    have hEq :
        (fun s => Fparam s x) =ᶠ[nhds τ] (fun s => F (slice s x)) := by
      have hopen : IsOpen {s : ℝ | |s - τ₀| < δ} := by
        simpa using isOpen_lt (by fun_prop) continuous_const
      filter_upwards [hopen.mem_nhds hτ] with s hs
      simp [Fparam, hs]
    have hslice_deriv : HasDerivAt (fun s => slice s x) vη τ := by
      refine hasDerivAt_pi.2 ?_
      intro i
      have hmul : HasDerivAt (fun s : ℝ => s * η i) (η i) τ := by
        simpa [one_mul] using (hasDerivAt_id τ).mul_const (η i)
      have hofReal : HasDerivAt (fun s : ℝ => ((s * η i : ℝ) : ℂ)) (η i) τ :=
        hmul.ofReal_comp
      have hI : HasDerivAt (fun s : ℝ => (((s * η i : ℝ) : ℂ) * I)) ((η i : ℂ) * I) τ :=
        hofReal.mul_const I
      simpa [slice, vη, Pi.smul_apply, smul_eq_mul] using hI.const_add (x i : ℂ)
    have hF_at : DifferentiableAt ℂ F (slice τ x) := by
      exact (hF_hol _ (hslice_mem hτ x)).differentiableAt
        ((SCV.tubeDomain_isOpen hC_open).mem_nhds (hslice_mem hτ x))
    have hcomp :
        HasDerivAt (fun s => F (slice s x)) (((fderiv ℂ F (slice τ x)).restrictScalars ℝ) vη) τ := by
      simpa using
        (hF_at.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt τ hslice_deriv
    have hderiv :
        HasDerivAt (fun s => Fparam s x) (((fderiv ℂ F (slice τ x)).restrictScalars ℝ) vη) τ :=
      hcomp.congr_of_eventuallyEq hEq
    simpa [Fparam', hτ] using hderiv
  have hFparam'_meas : AEStronglyMeasurable (Fparam' τ₀) volume := by
    have hslice0_meas : Measurable (slice τ₀) := by
      exact (by fun_prop : Continuous (slice τ₀)).measurable
    have hmeas :
        Measurable fun x : Fin m → ℝ => (fderiv ℂ F (slice τ₀ x)) vη :=
      (ContinuousLinearMap.measurable_apply vη).comp ((measurable_fderiv ℂ F).comp hslice0_meas)
    simpa [Fparam', hδ] using hmeas.aestronglyMeasurable
  obtain ⟨C_bd', N', hC_bd', hFparam'_growth⟩ :
      ∃ (C_bd' : ℝ) (N' : ℕ), 0 < C_bd' ∧
        ∀ τ, |τ - τ₀| < δ → ∀ x : Fin m → ℝ,
          ‖Fparam' τ x‖ ≤ C_bd' * (1 + ‖x‖) ^ N' := by
    let r : ℝ := τ₀ / 4
    have hr : 0 < r := by
      dsimp [r]
      positivity
    let Kc : ℝ := (2 * τ₀) * ‖η‖
    let A0 : ℝ := (2 / r) * (C_bd * (1 + Kc) ^ N)
    refine ⟨A0, N, ?_, ?_⟩
    · dsimp [A0, r, Kc]
      positivity
    · intro τ hτ x
      rcases abs_lt.mp hτ with ⟨hτ_lo, hτ_hi⟩
      have hτ_pos : 0 < τ := by
        dsimp [δ] at hτ_lo
        linarith
      have hτ_nonneg : 0 ≤ τ := hτ_pos.le
      have hτ_le : τ ≤ 3 * τ₀ / 2 := by
        dsimp [δ] at hτ_hi
        linarith
      let sliceC : ℂ → (Fin m → ℂ) := fun w i => (x i : ℂ) + w * (η i : ℂ) * I
      let g : ℂ → ℂ := fun w => F (sliceC w)
      have hsliceC_tau : sliceC (τ : ℂ) = slice τ x := by
        ext i
        simp [sliceC, slice, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      have hsliceC_hasDerivAt : ∀ w : ℂ, HasDerivAt sliceC vη w := by
        intro w
        refine hasDerivAt_pi.2 ?_
        intro i
        simpa [sliceC, vη, mul_assoc, mul_left_comm, mul_comm] using
          ((((hasDerivAt_id w).mul_const ((η i : ℂ))).mul_const I).const_add (x i : ℂ))
      have hsliceC_mem_ball :
          ∀ {w : ℂ}, w ∈ Metric.ball (τ : ℂ) r → sliceC w ∈ SCV.TubeDomain C := by
        intro w hw
        have hdist : ‖w - (τ : ℂ)‖ < r := by
          simpa [Metric.mem_ball, dist_eq_norm] using hw
        have hre_abs : |w.re - τ| ≤ ‖w - (τ : ℂ)‖ := by
          simpa [Complex.sub_re] using (Complex.abs_re_le_norm (w - (τ : ℂ)))
        have hre : |w.re - τ| < r := lt_of_le_of_lt hre_abs hdist
        have hrew_pos : 0 < w.re := by
          have hrew_lo : τ - r < w.re := by
            linarith [(abs_lt.mp hre).1]
          have hτ_gt_half : τ₀ / 2 < τ := by
            dsimp [δ] at hτ_lo
            linarith
          have hτr_pos : 0 < τ - r := by
            dsimp [r] at *
            linarith
          linarith
        have hwη : w.re • η ∈ C := hC_cone η hη w.re hrew_pos
        show (fun i => (sliceC w i).im) ∈ C
        · convert hwη using 1
          ext i
          simp [sliceC, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
            Complex.I_re, Complex.I_im, mul_assoc, mul_left_comm, mul_comm]
      have hsliceC_mem_tau : sliceC (τ : ℂ) ∈ SCV.TubeDomain C := by
        simpa [hsliceC_tau] using hslice_mem hτ x
      have hg_diff : DifferentiableOn ℂ g (Metric.ball (τ : ℂ) r) := by
        intro w hw
        have hF_at : DifferentiableAt ℂ F (sliceC w) := by
          exact (hF_hol _ (hsliceC_mem_ball hw)).differentiableAt
            ((SCV.tubeDomain_isOpen hC_open).mem_nhds (hsliceC_mem_ball hw))
        exact (hF_at.comp w (hsliceC_hasDerivAt w).differentiableAt).differentiableWithinAt
      have hsliceC_norm_bound :
          ∀ {w : ℂ}, w ∈ Metric.ball (τ : ℂ) r → ‖sliceC w‖ ≤ ‖x‖ + Kc := by
        intro w hw
        have hdist : ‖w - (τ : ℂ)‖ < r := by
          simpa [Metric.mem_ball, dist_eq_norm] using hw
        have hw_norm : ‖w‖ ≤ 2 * τ₀ := by
          have hdist_le : ‖w - (τ : ℂ)‖ ≤ r := le_of_lt hdist
          have hτ_norm : ‖(τ : ℂ)‖ = τ := by
            simp [Complex.norm_real, abs_of_nonneg hτ_nonneg]
          calc
            ‖w‖ = ‖(w - (τ : ℂ)) + (τ : ℂ)‖ := by ring_nf
            _ ≤ ‖w - (τ : ℂ)‖ + ‖(τ : ℂ)‖ := norm_add_le _ _
            _ ≤ r + τ := by
              rw [hτ_norm]
              gcongr
            _ ≤ 2 * τ₀ := by
              dsimp [r]
              linarith
        have hreal_le : ‖fun i => (x i : ℂ)‖ ≤ ‖x‖ := by
          rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
          intro i
          simpa using (norm_le_pi_norm x i)
        have himag_le : ‖fun i => (w * (η i : ℂ) * I : ℂ)‖ ≤ ‖w‖ * ‖η‖ := by
          rw [pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg w) (norm_nonneg η))]
          intro i
          calc
            ‖(w * (η i : ℂ) * I : ℂ)‖ = ‖w‖ * ‖η i‖ := by
              simp [Complex.norm_mul, mul_assoc]
            _ ≤ ‖w‖ * ‖η‖ := by
              gcongr
              simpa using (norm_le_pi_norm η i)
        have hnorm_le : ‖sliceC w‖ ≤ ‖x‖ + ‖w‖ * ‖η‖ := by
          simpa [sliceC] using
            (norm_add_le (fun i => (x i : ℂ)) (fun i => (w * (η i : ℂ) * I : ℂ)))
              |>.trans (add_le_add hreal_le himag_le)
        calc
          ‖sliceC w‖ ≤ ‖x‖ + ‖w‖ * ‖η‖ := hnorm_le
          _ ≤ ‖x‖ + Kc := by
            dsimp [Kc]
            gcongr
      have hsliceC_tau_norm : ‖sliceC (τ : ℂ)‖ ≤ ‖x‖ + Kc := by
        have hreal_le : ‖fun i => (x i : ℂ)‖ ≤ ‖x‖ := by
          rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
          intro i
          simpa using (norm_le_pi_norm x i)
        have himag_le : ‖fun i => ((τ : ℂ) * (η i : ℂ) * I : ℂ)‖ ≤ ‖(τ : ℂ)‖ * ‖η‖ := by
          rw [pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg (τ : ℂ)) (norm_nonneg η))]
          intro i
          calc
            ‖((τ : ℂ) * (η i : ℂ) * I : ℂ)‖ = ‖(τ : ℂ)‖ * ‖η i‖ := by
              simp [Complex.norm_mul, mul_assoc]
            _ ≤ ‖(τ : ℂ)‖ * ‖η‖ := by
              gcongr
              simpa using (norm_le_pi_norm η i)
        have hnorm_le : ‖sliceC (τ : ℂ)‖ ≤ ‖x‖ + ‖(τ : ℂ)‖ * ‖η‖ := by
          simpa [sliceC] using
            (norm_add_le (fun i => (x i : ℂ)) (fun i => (((τ : ℂ) * (η i : ℂ) * I : ℂ))))
              |>.trans (add_le_add hreal_le himag_le)
        calc
          ‖sliceC (τ : ℂ)‖ ≤ ‖x‖ + ‖(τ : ℂ)‖ * ‖η‖ := hnorm_le
          _ ≤ ‖x‖ + Kc := by
            dsimp [Kc]
            have hτ_norm : ‖(τ : ℂ)‖ = τ := by
              simp [Complex.norm_real, abs_of_nonneg hτ_nonneg]
            rw [hτ_norm]
            gcongr
            linarith
      have hbound_ball :
          ∀ {w : ℂ}, w ∈ Metric.ball (τ : ℂ) r →
            ‖g w‖ ≤ (C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N := by
        intro w hw
        have hgrowth := hF_growth (sliceC w) (hsliceC_mem_ball hw)
        have hbase_le : 1 + ‖sliceC w‖ ≤ (1 + Kc) * (1 + ‖x‖) := by
          have hKc_nonneg : 0 ≤ Kc := by
            dsimp [Kc]
            positivity
          nlinarith [hsliceC_norm_bound hw, norm_nonneg x, hKc_nonneg]
        have hpow_le :
            (1 + ‖sliceC w‖) ^ N ≤ ((1 + Kc) * (1 + ‖x‖)) ^ N := by
          exact pow_le_pow_left₀ (by positivity) hbase_le N
        calc
          ‖g w‖ ≤ C_bd * (1 + ‖sliceC w‖) ^ N := by simpa [g] using hgrowth
          _ ≤ C_bd * (((1 + Kc) * (1 + ‖x‖)) ^ N) := by gcongr
          _ = (C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N := by
            rw [mul_pow]
            ring
      have hbound_tau : ‖g (τ : ℂ)‖ ≤ (C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N := by
        have hgrowth := hF_growth (sliceC (τ : ℂ)) hsliceC_mem_tau
        have hbase_le : 1 + ‖sliceC (τ : ℂ)‖ ≤ (1 + Kc) * (1 + ‖x‖) := by
          have hKc_nonneg : 0 ≤ Kc := by
            dsimp [Kc]
            positivity
          nlinarith [hsliceC_tau_norm, norm_nonneg x, hKc_nonneg]
        have hpow_le :
            (1 + ‖sliceC (τ : ℂ)‖) ^ N ≤ ((1 + Kc) * (1 + ‖x‖)) ^ N := by
          exact pow_le_pow_left₀ (by positivity) hbase_le N
        calc
          ‖g (τ : ℂ)‖ ≤ C_bd * (1 + ‖sliceC (τ : ℂ)‖) ^ N := by simpa [g] using hgrowth
          _ ≤ C_bd * (((1 + Kc) * (1 + ‖x‖)) ^ N) := by gcongr
          _ = (C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N := by
            rw [mul_pow]
            ring
      have hmaps :
          Set.MapsTo g (Metric.ball (τ : ℂ) r)
            (Metric.closedBall (g (τ : ℂ))
              (2 * ((C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N))) := by
        intro w hw
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc
          ‖g w - g (τ : ℂ)‖ ≤ ‖g w‖ + ‖g (τ : ℂ)‖ := norm_sub_le _ _
          _ ≤ ((C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N) +
                ((C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N) := by
                  exact add_le_add (hbound_ball hw) hbound_tau
          _ = 2 * ((C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N) := by ring
      have hderivCauchy :
          ‖deriv g (τ : ℂ)‖ ≤
            (2 * ((C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N)) / r := by
        exact norm_deriv_le_div_of_mapsTo_ball hg_diff hmaps hr
      have hg_deriv :
          HasDerivAt g (Fparam' τ x) (τ : ℂ) := by
        have hF_at : DifferentiableAt ℂ F (sliceC (τ : ℂ)) := by
          simpa [hsliceC_tau] using
            (hF_hol _ (hslice_mem hτ x)).differentiableAt
              ((SCV.tubeDomain_isOpen hC_open).mem_nhds (hslice_mem hτ x))
        simpa [g, sliceC, Fparam', hτ, hsliceC_tau] using
          hF_at.hasFDerivAt.comp_hasDerivAt (τ : ℂ) (hsliceC_hasDerivAt (τ : ℂ))
      have hderiv_eq : deriv g (τ : ℂ) = Fparam' τ x := hg_deriv.deriv
      calc
        ‖Fparam' τ x‖ = ‖deriv g (τ : ℂ)‖ := by rw [hderiv_eq]
        _ ≤ (2 * ((C_bd * (1 + Kc) ^ N) * (1 + ‖x‖) ^ N)) / r := hderivCauchy
        _ = ((2 / r) * (C_bd * (1 + Kc) ^ N)) * (1 + ‖x‖) ^ N := by
          field_simp [hr.ne']
        _ = A0 * (1 + ‖x‖) ^ N := by
          simp [A0, mul_assoc, mul_left_comm, mul_comm]
  have hmain :
      HasDerivAt
        (fun τ => ∫ x : Fin m → ℝ, Fparam τ x * φ x)
        (∫ x : Fin m → ℝ, Fparam' τ₀ x * φ x)
        τ₀ := by
    exact hasDerivAt_schwartz_integral
      Fparam τ₀ δ hδ
      hFparam_meas
      (C_bd * (1 + Kτ) ^ N) N
      (by
        have hKτ_pos : 0 < 1 + Kτ := by
          dsimp [Kτ]
          positivity
        exact mul_pos hC_bd (pow_pos hKτ_pos _))
      hFparam_growth
      Fparam'
      hFparam_deriv
      hFparam'_meas
      C_bd' N' hC_bd'
      hFparam'_growth
      φ
  have htarget :
      ∫ x : Fin m → ℝ, Fparam' τ₀ x * φ x =
        -I * tubeSlice F (τ₀ • η) (directionalDerivSchwartz η φ) := by
    have hτ0 : |τ₀ - τ₀| < δ := by
      simpa [δ] using hδ
    let uη : Fin m → ℂ := fun i => (η i : ℂ)
    let G : (Fin m → ℝ) → ℂ := fun x => F (slice τ₀ x)
    let G' : (Fin m → ℝ) → ℂ := fun x => (fderiv ℂ F (slice τ₀ x)) (uη)
    let A : (Fin m → ℝ) →L[ℝ] (Fin m → ℂ) :=
      ContinuousLinearMap.pi fun i =>
        Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)
    have hA_apply : A η = uη := by
      ext i
      simp [A, uη]
    have hG_line : ∀ x : Fin m → ℝ, HasLineDerivAt ℝ G (G' x) x η := by
      intro x
      have hsliceX :
          HasFDerivAt (fun y : Fin m → ℝ => slice τ₀ y) A x := by
        refine hasFDerivAt_pi.2 ?_
        intro i
        simpa [slice, A] using
          (Complex.ofRealCLM.hasFDerivAt.comp x (ContinuousLinearMap.proj i).hasFDerivAt).const_add
            (((τ₀ • η) i : ℝ) * I)
      have hF_at : DifferentiableAt ℂ F (slice τ₀ x) := by
        exact (hF_hol _ (hslice_mem hτ0 x)).differentiableAt
          ((SCV.tubeDomain_isOpen hC_open).mem_nhds (hslice_mem hτ0 x))
      have hG_fderiv :
          HasFDerivAt G (((fderiv ℂ F (slice τ₀ x)).restrictScalars ℝ).comp A) x := by
        simpa [G] using (hF_at.hasFDerivAt.restrictScalars ℝ).comp x hsliceX
      have hderiv_vec :
          (((fderiv ℂ F (slice τ₀ x)).restrictScalars ℝ).comp A) η = G' x := by
        simp [G', hA_apply]
      exact (hG_fderiv.hasLineDerivAt η).congr_deriv hderiv_vec
    have hφ_line : ∀ x : Fin m → ℝ,
        HasLineDerivAt ℝ (fun y : Fin m → ℝ => φ y)
          (directionalDerivSchwartz η φ x) x η := by
      intro x
      have hφdiff : DifferentiableAt ℝ φ x := φ.differentiableAt
      rcases hφdiff with ⟨f', hf'⟩
      have hderiv_eq : f' = fderiv ℝ (fun y : Fin m → ℝ => φ y) x := hf'.fderiv.symm
      simpa [directionalDerivSchwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
        (hf'.hasLineDerivAt η).congr_deriv (by simpa using congrArg (fun L => L η) hderiv_eq)
    have hG_meas : AEStronglyMeasurable G volume := by
      simpa [G, Fparam, hδ] using hFparam_meas τ₀
    have hG_growth : ∀ x : Fin m → ℝ, ‖G x‖ ≤ (C_bd * (1 + Kτ) ^ N) * (1 + ‖x‖) ^ N := by
      intro x
      simpa [G, Fparam, hδ] using hFparam_growth τ₀ hτ0 x
    have hG'_meas : AEStronglyMeasurable G' volume := by
      have hslice0_meas : Measurable (slice τ₀) := by
        exact (by fun_prop : Continuous (slice τ₀)).measurable
      have hmeas : Measurable G' :=
        (ContinuousLinearMap.measurable_apply uη).comp ((measurable_fderiv ℂ F).comp hslice0_meas)
      exact hmeas.aestronglyMeasurable
    have hG'_growth : ∀ x : Fin m → ℝ, ‖G' x‖ ≤ C_bd' * (1 + ‖x‖) ^ N' := by
      intro x
      have hx := hFparam'_growth τ₀ hτ0 x
      have hvη : vη = I • uη := by
        ext i
        simp [vη, uη, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      have hcr : Fparam' τ₀ x = I * G' x := by
        calc
          Fparam' τ₀ x = (fderiv ℂ F (slice τ₀ x)) (vη) := by
            simp [Fparam', hδ]
          _ = (fderiv ℂ F (slice τ₀ x)) (I • uη) := by simpa [hvη]
          _ = I * G' x := by
            simp [G', map_smul, smul_eq_mul]
      rw [hcr, norm_mul, Complex.norm_I, one_mul] at hx
      simpa using hx
    have h_int_Gφ : Integrable (fun x : Fin m → ℝ => G x * φ x) := by
      exact integrable_polyGrowth_mul_schwartz G hG_meas
        ((C_bd * (1 + Kτ) ^ N)) N
        (by
          have hKτ_pos : 0 < 1 + Kτ := by
            dsimp [Kτ]
            positivity
          exact mul_pos hC_bd (pow_pos hKτ_pos _))
        hG_growth φ
    have h_int_Gdφ : Integrable (fun x : Fin m → ℝ => G x * directionalDerivSchwartz η φ x) := by
      exact integrable_polyGrowth_mul_schwartz G hG_meas
        ((C_bd * (1 + Kτ) ^ N)) N
        (by
          have hKτ_pos : 0 < 1 + Kτ := by
            dsimp [Kτ]
            positivity
          exact mul_pos hC_bd (pow_pos hKτ_pos _))
        hG_growth (directionalDerivSchwartz η φ)
    have h_int_G'φ : Integrable (fun x : Fin m → ℝ => G' x * φ x) := by
      exact integrable_polyGrowth_mul_schwartz G' hG'_meas C_bd' N' hC_bd' hG'_growth φ
    have hibp :
        ∫ x : Fin m → ℝ, G x * directionalDerivSchwartz η φ x =
          - ∫ x : Fin m → ℝ, G' x * φ x := by
      exact integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
        (μ := (volume : Measure (Fin m → ℝ))) (B := ContinuousLinearMap.mul ℝ ℂ)
        h_int_G'φ h_int_Gdφ h_int_Gφ hG_line hφ_line
    have hibp' :
        ∫ x : Fin m → ℝ, G' x * φ x =
          - ∫ x : Fin m → ℝ, G x * directionalDerivSchwartz η φ x := by
      have := congrArg Neg.neg hibp
      simpa using this.symm
    have hcr_int :
        ∫ x : Fin m → ℝ, Fparam' τ₀ x * φ x = I * ∫ x : Fin m → ℝ, G' x * φ x := by
      calc
        ∫ x : Fin m → ℝ, Fparam' τ₀ x * φ x
            = ∫ x : Fin m → ℝ, (I * G' x) * φ x := by
                apply integral_congr_ae
                filter_upwards with x
                have hvη : vη = I • uη := by
                  ext i
                  simp [vη, uη, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
                have hcr : Fparam' τ₀ x = I * G' x := by
                  calc
                    Fparam' τ₀ x = (fderiv ℂ F (slice τ₀ x)) (vη) := by
                      simp [Fparam', hδ]
                    _ = (fderiv ℂ F (slice τ₀ x)) (I • uη) := by simpa [hvη]
                    _ = I * G' x := by
                      simp [G', map_smul, smul_eq_mul]
                simp [hcr]
        _ = I * ∫ x : Fin m → ℝ, G' x * φ x := by
            rw [show (fun x : Fin m → ℝ => (I * G' x) * φ x) =
                fun x : Fin m → ℝ => I * (G' x * φ x) by
                  funext x; ring, integral_const_mul]
    calc
      ∫ x : Fin m → ℝ, Fparam' τ₀ x * φ x
          = I * ∫ x : Fin m → ℝ, G' x * φ x := hcr_int
      _ = -I * ∫ x : Fin m → ℝ, G x * directionalDerivSchwartz η φ x := by
          rw [hibp']
          ring
      _ = -I * tubeSlice F (τ₀ • η) (directionalDerivSchwartz η φ) := by
          simp [tubeSlice, G, slice, Pi.smul_apply, smul_eq_mul]
  have hEq :
      (fun τ => ∫ x : Fin m → ℝ, Fparam τ x * φ x) =ᶠ[nhds τ₀]
        (fun τ => tubeSlice F (τ • η) φ) := by
    filter_upwards [Metric.ball_mem_nhds τ₀ hδ] with τ hτ
    have hτ' : |τ - τ₀| < δ := Metric.mem_ball.mp hτ
    simp [Fparam, tubeSlice, hτ', slice]
  exact (hmain.congr_of_eventuallyEq hEq.symm).congr_deriv htarget

/-- Continuity of the tube-slice derivative along a ray, restricted to τ > 0.

    Needs polynomial growth of F to ensure the integral is well-defined and
    dominated convergence applies for parameter continuity.

    **Previous version was underassumed**: ContinuousOn alone doesn't guarantee
    integrability of F(x+iτη)ψ(x) — e.g., F(z) = exp(z²) is entire but
    |F(x+iτη)| = exp(x²-τ²) grows too fast for Schwartz test functions. -/
theorem continuous_tubeSlice_ray_deriv
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
      (Set.Ioi 0) := by
  let ψ : SchwartzMap (Fin m → ℝ) ℂ := directionalDerivSchwartz η φ
  have hcont_slice : ContinuousOn (fun τ : ℝ => tubeSlice F (τ • η) ψ) (Set.Ioi 0) := by
    refine (isOpen_Ioi.continuousOn_iff).2 ?_
    intro τ₀ hτ₀
    let δ : ℝ := τ₀ / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      exact half_pos (Set.mem_Ioi.mp hτ₀)
    let slice : ℝ → (Fin m → ℝ) → (Fin m → ℂ) :=
      fun τ x i => (x i : ℂ) + ((τ • η) i : ℝ) * I
    have hslice_mem :
        ∀ {τ : ℝ}, |τ - τ₀| < δ → ∀ x : Fin m → ℝ, slice τ x ∈ SCV.TubeDomain C := by
      intro τ hτ x
      rcases abs_lt.mp hτ with ⟨hτ_lo, _⟩
      have hτ_pos : 0 < τ := by
        have hτ₀_pos : 0 < τ₀ := Set.mem_Ioi.mp hτ₀
        dsimp [δ] at hτ_lo
        linarith
      have hτη : τ • η ∈ C := hC_cone η hη τ hτ_pos
      show (fun i => (slice τ x i).im) ∈ C
      convert hτη using 1
      ext i
      simp [slice, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Pi.smul_apply, smul_eq_mul]
    let Kτ : ℝ := (3 * τ₀ / 2) * ‖η‖
    have hτ_bound : ∀ {τ : ℝ}, |τ - τ₀| < δ → ‖τ • η‖ ≤ Kτ := by
      intro τ hτ
      rcases abs_lt.mp hτ with ⟨hτ_lo, hτ_hi⟩
      have hτ_nonneg : 0 ≤ τ := by
        have hτ₀_pos : 0 < τ₀ := Set.mem_Ioi.mp hτ₀
        dsimp [δ] at hτ_lo
        linarith
      have hτ_le : τ ≤ 3 * τ₀ / 2 := by
        dsimp [δ] at hτ_hi
        linarith
      calc
        ‖τ • η‖ = ‖τ‖ * ‖η‖ := by rw [norm_smul]
        _ = τ * ‖η‖ := by simp [abs_of_nonneg hτ_nonneg]
        _ ≤ (3 * τ₀ / 2) * ‖η‖ := by gcongr
    let gB : (Fin m → ℝ) → ℂ :=
      fun x => (((C_bd * (1 + Kτ) ^ N) * (1 + ‖x‖) ^ N : ℝ) : ℂ)
    let B : (Fin m → ℝ) → ℝ := fun x => ‖gB x * ψ x‖
    have hpoint_cont :
        ∀ x : Fin m → ℝ, ContinuousAt (fun τ : ℝ => F (slice τ x) * ψ x) τ₀ := by
      intro x
      have hτ0 : |τ₀ - τ₀| < δ := by
        simpa [δ] using hδ
      have hF_at : ContinuousAt F (slice τ₀ x) := by
        exact hF_cont.continuousAt
          ((SCV.tubeDomain_isOpen hC_open).mem_nhds (hslice_mem hτ0 x))
      have hslice_at : ContinuousAt (fun τ : ℝ => slice τ x) τ₀ := by
        exact (by fun_prop : Continuous fun τ : ℝ => slice τ x).continuousAt
      have hcomp : ContinuousAt (fun τ : ℝ => F (slice τ x)) τ₀ := by
        simpa [Function.comp] using (ContinuousAt.comp (f := fun τ : ℝ => slice τ x) (x := τ₀) hF_at hslice_at :
          ContinuousAt (F ∘ fun τ : ℝ => slice τ x) τ₀)
      exact hcomp.mul_const (ψ x)
    have hmeas :
        ∀ᶠ τ in nhds τ₀,
          AEStronglyMeasurable (fun x : Fin m → ℝ => F (slice τ x) * ψ x) volume := by
      filter_upwards [Metric.ball_mem_nhds τ₀ hδ] with τ hτ
      have hτ' : |τ - τ₀| < δ := Metric.mem_ball.mp hτ
      have hcontF : Continuous fun x : Fin m → ℝ => F (slice τ x) := by
        exact hF_cont.comp_continuous (by fun_prop) (hslice_mem hτ')
      exact (hcontF.mul ψ.continuous).aestronglyMeasurable
    have hgB_meas : AEStronglyMeasurable gB volume := by
      exact (by fun_prop : Continuous gB).aestronglyMeasurable
    have hKτ_pos : 0 < 1 + Kτ := by
      have hτ₀_pos : 0 < τ₀ := Set.mem_Ioi.mp hτ₀
      dsimp [Kτ]
      nlinarith [norm_nonneg η]
    have hgB_norm : ∀ x : Fin m → ℝ,
        ‖gB x‖ = (C_bd * (1 + Kτ) ^ N) * (1 + ‖x‖) ^ N := by
      intro x
      have hcoeff_nonneg : 0 ≤ (C_bd * (1 + Kτ) ^ N) * (1 + ‖x‖) ^ N := by
        positivity
      unfold gB
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoeff_nonneg]
    have hgB_growth : ∀ x : Fin m → ℝ, ‖gB x‖ ≤ (C_bd * (1 + Kτ) ^ N) * (1 + ‖x‖) ^ N := by
      intro x
      rw [hgB_norm]
    have hB_int_complex : Integrable (fun x : Fin m → ℝ => gB x * ψ x) := by
      exact integrable_polyGrowth_mul_schwartz gB hgB_meas
        (C_bd * (1 + Kτ) ^ N) N
        (mul_pos hC_bd (pow_pos hKτ_pos _))
        hgB_growth ψ
    have hB_int : Integrable B := by
      simpa [B] using hB_int_complex.norm
    have hbound_event :
        ∀ᶠ τ in nhds τ₀,
          ∀ x : Fin m → ℝ, ‖F (slice τ x) * ψ x‖ ≤ B x := by
      filter_upwards [Metric.ball_mem_nhds τ₀ hδ] with τ hτ x
      have hτ' : |τ - τ₀| < δ := Metric.mem_ball.mp hτ
      have hgrowth := hF_growth (slice τ x) (hslice_mem hτ' x)
      have hreal_le : ‖fun i => (x i : ℂ)‖ ≤ ‖x‖ := by
        rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
        intro i
        simpa using (norm_le_pi_norm x i)
      have himag_le : ‖fun i => (((τ • η) i : ℝ) * I : ℂ)‖ ≤ ‖τ • η‖ := by
        rw [pi_norm_le_iff_of_nonneg (norm_nonneg (τ • η))]
        intro i
        simpa [Complex.norm_mul, Complex.norm_I] using (norm_le_pi_norm (τ • η) i)
      have hnorm_le : ‖slice τ x‖ ≤ ‖x‖ + ‖τ • η‖ := by
        calc
          ‖slice τ x‖
              ≤ ‖fun i => (x i : ℂ)‖ + ‖fun i => (((τ • η) i : ℝ) * I : ℂ)‖ := norm_add_le _ _
          _ ≤ ‖x‖ + ‖τ • η‖ := add_le_add hreal_le himag_le
      have hbase_le : 1 + ‖slice τ x‖ ≤ (1 + Kτ) * (1 + ‖x‖) := by
        have hKτ_nonneg : 0 ≤ Kτ := by
          have hτ₀_pos : 0 < τ₀ := Set.mem_Ioi.mp hτ₀
          dsimp [Kτ]
          nlinarith [norm_nonneg η]
        have htauK : ‖τ • η‖ ≤ Kτ := hτ_bound hτ'
        nlinarith [hnorm_le, htauK, norm_nonneg x, hKτ_nonneg]
      have hpow_le :
          (1 + ‖slice τ x‖) ^ N ≤ ((1 + Kτ) * (1 + ‖x‖)) ^ N := by
        exact pow_le_pow_left₀ (by positivity) hbase_le N
      rw [norm_mul]
      calc
        ‖F (slice τ x)‖ * ‖ψ x‖ ≤ (C_bd * (1 + ‖slice τ x‖) ^ N) * ‖ψ x‖ := by
          exact mul_le_mul_of_nonneg_right hgrowth (norm_nonneg _)
        _ ≤ (C_bd * (((1 + Kτ) * (1 + ‖x‖)) ^ N)) * ‖ψ x‖ := by
          gcongr
        _ = ((C_bd * (1 + Kτ) ^ N) * (1 + ‖x‖) ^ N) * ‖ψ x‖ := by
          rw [mul_pow]
          ring
        _ = ‖gB x‖ * ‖ψ x‖ := by rw [hgB_norm]
        _ = ‖gB x * ψ x‖ := by rw [norm_mul]
        _ = B x := rfl
    have hlim :
        ∀ᵐ x : Fin m → ℝ ∂volume,
          Tendsto (fun τ : ℝ => F (slice τ x) * ψ x) (nhds τ₀) (nhds (F (slice τ₀ x) * ψ x)) := by
      exact Filter.Eventually.of_forall fun x => (hpoint_cont x).tendsto
    have hbound_event_ae :
        ∀ᶠ τ in nhds τ₀, ∀ᵐ x : Fin m → ℝ ∂volume, ‖F (slice τ x) * ψ x‖ ≤ B x := by
      filter_upwards [hbound_event] with τ hτ
      exact Filter.Eventually.of_forall hτ
    have htend :
        Tendsto (fun τ : ℝ => ∫ x : Fin m → ℝ, F (slice τ x) * ψ x)
          (nhds τ₀) (nhds (∫ x : Fin m → ℝ, F (slice τ₀ x) * ψ x)) := by
      exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        B hmeas hbound_event_ae hB_int hlim
    simpa [tubeSlice, slice, Pi.smul_apply, smul_eq_mul] using htend
  exact continuousOn_const.mul hcont_slice

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
    exact hasDerivAt_tubeSlice_ray hF_hol hF_cont η hη hC_cone hC_open hC_bd hF_growth τ₀ hτ₀ φ
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

/-- **Main converse theorem (Cauchy regularization)**: Vladimirov growth on a tube
    implies existence of tempered distributional boundary values.

    Proof sketch:
    - Define H(x) = i^k / (k-1)! ∫₀^{t₀} (t₀-τ)^{k-1} F(x+iτη) dτ with k = M+2.
    - The singularity τ^{-M} from Vladimirov growth integrates against the
      τ^{M+1} factor from (t₀-τ)^{k-1}, making H well-defined and continuous.
    - H has polynomial growth in x, hence defines a tempered distribution.
    - The boundary value W is recovered as the k-th iterated distributional
      directional derivative of H plus a polynomial correction term.
    - Uses `cr_integration_identity` (proved) applied k times together with DCT
      to pass ε→0⁺ inside the integral. -/
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
    is obtained by flattening `Fin n → Fin (d + 1)` to `Fin (n * (d + 1))`,
    applying the flat-space theorem `tube_boundaryValue_of_vladimirov_growth`,
    and transporting the resulting boundary functional back to the product
    Schwartz space. -/
private theorem flattenCLEquiv_norm_eq (n d : ℕ) (z : Fin n → Fin d → ℂ) :
    ‖flattenCLEquiv n d z‖ = ‖z‖ := by
  simp only [Pi.norm_def]
  congr 1
  simp only [Pi.nnnorm_def, flattenCLEquiv_apply]
  apply le_antisymm
  · apply Finset.sup_le
    intro b _
    exact Finset.le_sup_of_le (Finset.mem_univ (finProdFinEquiv.symm b).1)
      (Finset.le_sup_of_le (Finset.mem_univ (finProdFinEquiv.symm b).2) (by simp))
  · apply Finset.sup_le
    intro i _
    apply Finset.sup_le
    intro j _
    exact Finset.le_sup_of_le (Finset.mem_univ (finProdFinEquiv (i, j))) (by simp)

theorem tube_boundaryValueData_of_polyGrowth'
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
          (nhds (W φ)) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let Cflat : Set (Fin (n * (d + 1)) → ℝ) := eR '' C
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  have hCflat_open : IsOpen Cflat := by
    exact eR.toHomeomorph.isOpenMap _ hC_open
  have hCflat_conv : Convex ℝ Cflat := by
    exact hC_conv.linear_image eR.toLinearEquiv.toLinearMap
  have hCflat_cone : IsCone Cflat := by
    intro y hy t ht
    rcases hy with ⟨y', hy', rfl⟩
    refine ⟨t • y', hC_cone y' hy' t ht, ?_⟩
    simpa using eR.map_smul t y'
  have hCflat_ne : Cflat.Nonempty := by
    rcases hC_ne with ⟨y, hy⟩
    exact ⟨eR y, ⟨y, hy, rfl⟩⟩
  have hmem_flat : ∀ z : Fin (n * (d + 1)) → ℂ,
      z ∈ SCV.TubeDomain Cflat → e.symm z ∈ TubeDomainSetPi C := by
    intro z hz
    change (fun i => (z i).im) ∈ Cflat at hz
    dsimp [Cflat] at hz
    change (fun k μ => ((e.symm z) k μ).im) ∈ C
    rcases hz with ⟨y, hy, hyw⟩
    convert hy using 1
    ext k μ
    have hcomp := congr_fun hyw (finProdFinEquiv (k, μ))
    simpa [e, eR, flattenCLEquiv_symm_apply, flattenCLEquivReal_apply] using hcomp.symm
  have hG_hol : DifferentiableOn ℂ G (SCV.TubeDomain Cflat) := by
    refine hF_hol.comp e.symm.differentiableOn ?_
    intro z hz
    exact hmem_flat z hz
  have hG_growth : ∀ z ∈ SCV.TubeDomain Cflat,
      ‖G z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    intro z hz
    have hz' : e.symm z ∈ TubeDomainSetPi C := hmem_flat z hz
    have hflat := hF_growth (e.symm z) hz'
    have hnorm : ‖e.symm z‖ = ‖z‖ := by
      simpa [e] using (flattenCLEquiv_norm_eq n (d + 1) (e.symm z)).symm
    simpa [G, hnorm] using hflat
  obtain ⟨Tflat, hBVflat⟩ :=
    tube_boundaryValue_of_vladimirov_growth
      hCflat_open hCflat_conv hCflat_cone hCflat_ne hG_hol
      (M := 0) hC
      (fun z hz => by
        simpa using hG_growth z hz)
  let pushforward : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR.symm
  let W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    Tflat.comp pushforward
  refine ⟨W, ?_⟩
  intro φ η hη
  have hηflat : eR η ∈ Cflat := ⟨η, hη, rfl⟩
  have hflat :
      Tendsto
        (fun ε : ℝ =>
          ∫ x : Fin (n * (d + 1)) → ℝ,
            G (fun i => ↑(x i) + (ε : ℂ) * ↑(eR η i) * I) * (pushforward φ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Tflat (pushforward φ))) := by
    simpa [tubeSlice, G] using hBVflat (pushforward φ) (eR η) hηflat
  have hEq :
      (fun ε : ℝ =>
        ∫ x : Fin (n * (d + 1)) → ℝ,
          G (fun i => ↑(x i) + (ε : ℂ) * ↑(eR η i) * I) * (pushforward φ x))
      =
      (fun ε : ℝ =>
        ∫ y : Fin n → Fin (d + 1) → ℝ,
          F (fun k μ => ↑(y k μ) + (ε : ℂ) * ↑(η k μ) * I) * φ y) := by
    funext ε
    rw [integral_flatten_change_of_variables n (d + 1)
      (fun x : Fin (n * (d + 1)) → ℝ =>
        G (fun i => ↑(x i) + (ε : ℂ) * ↑(eR η i) * I) * (pushforward φ x))]
    congr 1
    ext y
    have hFarg :
        G (fun i => ↑(eR y i) + (ε : ℂ) * ↑(eR η i) * I) =
          F (fun k μ => ↑(y k μ) + (ε : ℂ) * ↑(η k μ) * I) := by
      change F (e.symm (fun i => ↑(eR y i) + (ε : ℂ) * ↑(eR η i) * I)) =
        F (fun k μ => ↑(y k μ) + (ε : ℂ) * ↑(η k μ) * I)
      congr 1
      ext k μ
      have hyk : eR y (finProdFinEquiv (k, μ)) = y k μ := by
        simp [eR, flattenCLEquivReal_apply]
      have hηk : eR η (finProdFinEquiv (k, μ)) = η k μ := by
        simp [eR, flattenCLEquivReal_apply]
      rw [show (e.symm (fun i => ↑(eR y i) + (ε : ℂ) * ↑(eR η i) * I)) k μ =
          (fun i => ↑(eR y i) + (ε : ℂ) * ↑(eR η i) * I) (finProdFinEquiv (k, μ)) by
            simp [e, flattenCLEquiv_symm_apply]]
      simp [hyk, hηk]
    have hφarg : pushforward φ (eR y) = φ y := by
      simp [pushforward, eR]
    rw [hFarg, hφarg]
  rw [hEq] at hflat
  simpa [W, pushforward] using hflat

end
