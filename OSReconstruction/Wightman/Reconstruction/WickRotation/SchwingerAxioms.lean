/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation
import OSReconstruction.ComplexLieGroups.D1OrbitSet
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.JostWitnessGeneralSigma
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Schwinger Axioms from Wightman Functions

Verification that the Schwinger functions constructed via Wick rotation
satisfy the Osterwalder-Schrader axioms on the current corrected surface.

- E0 (temperedness on `ZeroDiagonalSchwartz`): corrected OS-I zero-diagonal surface
- E1a (translation invariance): BHW translation invariance
- E1b (rotation invariance): complex Lorentz invariance restricted to SO(d+1)
- E2 (reflection positivity): Wick rotation of time-reflection = conjugation + R2
- E3 (permutation symmetry): BHW permutation invariance
- E4 (cluster): Wightman cluster axiom via analytic continuation
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-- Wick rotation of a single point preserves each component norm:
    `‖wickRotatePoint x i‖ = ‖x i‖` for each i.
    - i = 0: `‖I * ↑(x 0)‖ = |x 0|` since `‖I‖ = 1`
    - i > 0: `‖↑(x i)‖ = |x i|` since `Complex.norm_real` -/
theorem wickRotatePoint_component_norm_eq {d : ℕ}
    (x : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    ‖wickRotatePoint x i‖ = ‖x i‖ := by
  simp only [wickRotatePoint]; split_ifs with h
  · subst h; rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
  · rw [Complex.norm_real]

/-- The norm of a Wick-rotated Euclidean configuration is at most the original norm.

    Since `‖wickRotatePoint(x k) i‖ = ‖x k i‖` componentwise, and the Pi norm
    is the sup over all components, the Wick-rotated norm equals the original.
    We prove ≤ which suffices for the polynomial growth argument. -/
theorem wickRotate_norm_le {d n : ℕ}
    (x : Fin n → Fin (d + 1) → ℝ) :
    ‖fun k => wickRotatePoint (x k)‖ ≤ ‖x‖ := by
  -- Both norms are Pi sup norms. We bound each component.
  -- Step 1: ∀ k i, ‖wickRotatePoint(x k) i‖ ≤ ‖x‖
  have hcomp : ∀ (k : Fin n) (i : Fin (d + 1)),
      ‖wickRotatePoint (x k) i‖ ≤ ‖x‖ := by
    intro k i
    rw [wickRotatePoint_component_norm_eq]
    exact (norm_le_pi_norm (x k) i).trans (norm_le_pi_norm x k)
  -- Step 2: ∀ k, ‖wickRotatePoint(x k)‖ ≤ ‖x‖
  have hk : ∀ k : Fin n, ‖wickRotatePoint (x k)‖ ≤ ‖x‖ := by
    intro k
    -- Component bound → pi norm bound (manual, to avoid norm instance issues)
    simp only [Pi.norm_def, Pi.nnnorm_def]
    rw [NNReal.coe_le_coe]
    apply Finset.sup_le
    intro i _
    have := hcomp k i
    -- ‖wickRotatePoint(x k) i‖ ≤ ‖x‖ is in terms of ℂ norm and ℝ nested pi norm
    -- We need: ‖wickRotatePoint(x k) i‖₊ ≤ sup_j sup_μ ‖x j μ‖₊
    simp only [Pi.norm_def, Pi.nnnorm_def] at this
    exact_mod_cast this
  -- Step 3: ‖fun k => wickRotatePoint(x k)‖ ≤ ‖x‖
  simp only [Pi.norm_def, Pi.nnnorm_def]
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro k _
  have := hk k
  simp only [Pi.norm_def, Pi.nnnorm_def] at this
  exact_mod_cast this

/-- **Integrability of the Wick-rotated BHW kernel on the zero-diagonal test space.**

    This is the genuine analytic input behind the literal pointwise definition
    of `constructSchwingerFunctions`. A global polynomial bound on
    `W_analytic_BHW(Wick(x))` is overstrong in general: Euclidean Schwinger kernels
    can have genuine coincidence singularities, so one must combine growth control
    at spatial infinity with local Euclidean singularity analysis near the PET
    boundary/diagonal strata.

    On the corrected OS-I surface, the only honest general pairing statement is
    for `f ∈ ZeroDiagonalSchwartz`: those test functions kill the coincidence
    singularities, so the remaining content is decay at infinity.

    Blocked by: honest Euclidean singularity control for the BHW extension near
    coincidence configurations, together with the existing forward-tube boundary-value
    input. The previous intermediate theorems
    `polynomial_growth_forwardTube_full`, `polynomial_growth_on_PET`, and
    `bhw_euclidean_polynomial_bound` were overstrong and have been removed. -/
theorem wick_rotated_kernel_mul_zeroDiagonal_integrable {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ f : ZeroDiagonalSchwartz d n,
      MeasureTheory.Integrable
        (fun x : NPointDomain d n =>
          (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * f.1 x)
        MeasureTheory.volume := by
  sorry

/-- Helper: the integral of a polynomial-growth kernel against a Schwartz function defines
    a continuous linear functional on Schwartz space.

    The mathematical content is standard (Reed-Simon I, Theorem V.10):
    |∫ K(x)f(x)dx| ≤ C_bd · I_dim · 2^(N+dim+1) · seminorm_{N+dim+1,0}(f)
    where I_dim = ∫ (1+|x|)^{-(dim+1)} dx is finite (dim = n*(d+1)).

    The proof requires:
    - `SchwartzMap.one_add_le_sup_seminorm_apply` for decay of Schwartz functions
    - `integrable_one_add_norm` for integrability of (1+|x|)^{-r} when r > dim
    - `SchwartzMap.mkCLMtoNormedSpace` to assemble the CLM from the seminorm bound
    - `HasTemperateGrowth` instance for `volume` on `NPointDomain d n`

    Currently blocked by: `IsAddHaarMeasure` for `volume` on `Fin n → Fin (d+1) → ℝ`
    (nested Pi type). Mathlib provides the instance for single-level Pi types
    (`Fin n → ℝ`) but not for nested Pi types. The mathematical content is
    unambiguous — this is a standard functional analysis result. -/
theorem schwartz_polynomial_kernel_continuous {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    Continuous (fun f : SchwartzNPoint d n => ∫ x, K x * f x) := by
  -- Provide the IsAddHaarMeasure instance for the nested pi type (not found by inferInstance)
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  -- Strategy: construct a CLM via mkCLMtoNormedSpace and extract continuity
  suffices h : ∃ (A : SchwartzNPoint d n →L[ℂ] ℂ), ∀ f, A f = ∫ x, K x * f x by
    obtain ⟨A, hA⟩ := h; simp_rw [← hA]; exact A.continuous
  -- Key: (1+t)^N ≤ 2^N * (1 + t^N) for t ≥ 0
  have h_binom_ineq : ∀ (t : ℝ), 0 ≤ t → (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
    intro t ht
    have h2t : 1 + t ≤ 2 * max 1 t :=
      calc 1 + t ≤ max 1 t + max 1 t := add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * max 1 t := by ring
    calc (1 + t) ^ N
        ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by positivity) h2t N
      _ = 2 ^ N * (max 1 t) ^ N := by rw [mul_pow]
      _ ≤ 2 ^ N * (1 + t ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total t 1 with h | h
          · rw [max_eq_left h]; simp [one_pow]; linarith [pow_nonneg ht N]
          · rw [max_eq_right h]; linarith [show (1 : ℝ) ^ N = 1 from one_pow N]
  -- Helper: K*f is integrable for any Schwartz f
  have hKf_int : ∀ f : SchwartzNPoint d n,
      MeasureTheory.Integrable (fun x => K x * f x) MeasureTheory.volume := by
    intro f
    have hf_int := f.integrable (μ := MeasureTheory.volume)
    have hf_pow_int := f.integrable_pow_mul MeasureTheory.volume N
    -- Majorant: g(x) = C_bd * 2^N * (‖f(x)‖ + ‖x‖^N * ‖f(x)‖) is integrable
    have hg_int : MeasureTheory.Integrable
        (fun x => C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
          ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖)) MeasureTheory.volume :=
      (hf_int.norm.add hf_pow_int).const_mul (C_bd * 2 ^ N)
    apply hg_int.mono' (hK_meas.mul f.integrable.aestronglyMeasurable)
    filter_upwards [hK_bound] with x hx
    simp only [Pi.mul_apply, norm_mul]
    calc ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖
        ≤ C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ ≤ C_bd * (2 ^ N * (1 + ‖x‖ ^ N)) * ‖(f : NPointDomain d n → ℂ) x‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (h_binom_ineq ‖x‖ (norm_nonneg _)) (le_of_lt hC)
      _ = C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
            ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖) := by ring
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (fun f => ∫ x, K x * f x) ?_ ?_ ?_,
    fun f => rfl⟩
  · -- Additivity: ∫ K*(f+g) = ∫ K*f + ∫ K*g
    intro f g; simp only [SchwartzMap.add_apply, mul_add]
    exact MeasureTheory.integral_add (hKf_int f) (hKf_int g)
  · -- Scalar: ∫ K*(a•f) = a • ∫ K*f
    intro a f; simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ x : NPointDomain d n, K x * (a * f x) = a * (K x * f x) from
      fun x => by ring]
    exact MeasureTheory.integral_const_mul a _
  · -- Seminorm bound: ∃ s C, 0 ≤ C ∧ ∀ f, ‖∫ K*f‖ ≤ C * (s.sup seminormFamily) f
    -- Let D = finrank, M = N + D + 1
    set D := Module.finrank ℝ (NPointDomain d n)
    set M := N + D + 1
    -- I_D = ∫ (1+‖x‖)^(-(D+1)) < ∞
    have hD_lt : (D : ℝ) < ↑(D + 1) := by push_cast; linarith
    have hI_int : MeasureTheory.Integrable
        (fun x : NPointDomain d n => (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)))
        MeasureTheory.volume :=
      integrable_one_add_norm hD_lt
    set I_D := ∫ x : NPointDomain d n, (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ))
    -- The constant
    set C_sem := C_bd * 2 ^ M * I_D
    refine ⟨Finset.Iic (M, 0), C_sem, ?_, ?_⟩
    · -- 0 ≤ C_sem
      apply mul_nonneg (mul_nonneg (le_of_lt hC) (by positivity))
      apply MeasureTheory.integral_nonneg
      intro x; apply Real.rpow_nonneg; linarith [norm_nonneg x]
    · -- The bound: ‖∫ K*f‖ ≤ C_sem * (s.sup seminormFamily) f
      intro f
      -- Abbreviate the seminorm
      set sem := (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)
      -- From one_add_le_sup_seminorm_apply: (1+‖x‖)^M * ‖f(x)‖ ≤ 2^M * sem(f)
      have hsem_bound : ∀ x : NPointDomain d n,
          (1 + ‖x‖) ^ M * ‖(f : NPointDomain d n → ℂ) x‖ ≤ 2 ^ M * sem f := by
        intro x
        have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, 0))
          (le_refl M) (le_refl 0) f x
        rwa [norm_iteratedFDeriv_zero] at h
      -- Pointwise bound: ‖K x * f x‖ ≤ C_bd * 2^M * sem(f) * (1+‖x‖)^(-(D+1))
      have hpointwise : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
          ‖K x * (f : NPointDomain d n → ℂ) x‖ ≤
            C_bd * 2 ^ M * sem f * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
        filter_upwards [hK_bound] with x hx
        have h1x_pos : (0 : ℝ) < 1 + ‖x‖ := by linarith [norm_nonneg x]
        have h1xD1_pos : (0 : ℝ) < (1 + ‖x‖) ^ (D + 1) := pow_pos h1x_pos _
        -- Rewrite rpow as inverse of natural power
        rw [Real.rpow_neg (le_of_lt h1x_pos), Real.rpow_natCast]
        rw [norm_mul]
        -- ‖K x‖ * ‖f x‖ ≤ C_bd * (1+‖x‖)^N * ‖f x‖
        have step1 : ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖ ≤
            C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        -- (1+‖x‖)^N * ‖f x‖ ≤ 2^M * sem(f) / (1+‖x‖)^(D+1)
        -- From: (1+‖x‖)^M * ‖f x‖ ≤ 2^M * sem(f) and M = N + D + 1
        have step2 : (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ ≤
            2 ^ M * sem f * ((1 + ‖x‖) ^ (D + 1))⁻¹ := by
          rw [le_mul_inv_iff₀ h1xD1_pos]
          calc (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ * (1 + ‖x‖) ^ (D + 1)
              = (1 + ‖x‖) ^ (N + (D + 1)) * ‖(f : NPointDomain d n → ℂ) x‖ := by
                rw [pow_add]; ring
            _ = (1 + ‖x‖) ^ M * ‖(f : NPointDomain d n → ℂ) x‖ := by
                congr 1
            _ ≤ 2 ^ M * sem f := hsem_bound x
        calc ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖
            ≤ C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ := step1
          _ = C_bd * ((1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖) := by ring
          _ ≤ C_bd * (2 ^ M * sem f * ((1 + ‖x‖) ^ (D + 1))⁻¹) :=
              mul_le_mul_of_nonneg_left step2 (le_of_lt hC)
          _ = C_bd * 2 ^ M * sem f * ((1 + ‖x‖) ^ (D + 1))⁻¹ := by ring
      -- Integrate the pointwise bound
      calc ‖(fun f => ∫ x, K x * f x) f‖
          = ‖∫ x, K x * (f : NPointDomain d n → ℂ) x‖ := by rfl
        _ ≤ ∫ x, ‖K x * (f : NPointDomain d n → ℂ) x‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ x, C_bd * 2 ^ M * sem f * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) :=
            MeasureTheory.integral_mono_ae (hKf_int f).norm
              (hI_int.const_mul (C_bd * 2 ^ M * sem f)) hpointwise
        _ = C_bd * 2 ^ M * sem f * I_D := by
            rw [MeasureTheory.integral_const_mul]
        _ = C_bd * 2 ^ M * I_D * sem f := by ring
        _ = C_sem * sem f := by rfl

/-- A polynomial-growth kernel is integrable against every Schwartz function. -/
theorem schwartz_polynomial_kernel_integrable {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    ∀ f : SchwartzNPoint d n,
      MeasureTheory.Integrable (fun x => K x * f x) MeasureTheory.volume := by
  -- This is the `hKf_int` argument from `schwartz_polynomial_kernel_continuous`.
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have h_binom_ineq : ∀ (t : ℝ), 0 ≤ t → (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
    intro t ht
    have h2t : 1 + t ≤ 2 * max 1 t :=
      calc 1 + t ≤ max 1 t + max 1 t := add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * max 1 t := by ring
    calc (1 + t) ^ N
        ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by positivity) h2t N
      _ = 2 ^ N * (max 1 t) ^ N := by rw [mul_pow]
      _ ≤ 2 ^ N * (1 + t ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total t 1 with h | h
          · rw [max_eq_left h]; simp [one_pow]; linarith [pow_nonneg ht N]
          · rw [max_eq_right h]; linarith [show (1 : ℝ) ^ N = 1 from one_pow N]
  intro f
  have hf_int := f.integrable (μ := MeasureTheory.volume)
  have hf_pow_int := f.integrable_pow_mul MeasureTheory.volume N
  have hg_int : MeasureTheory.Integrable
      (fun x => C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
        ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖)) MeasureTheory.volume :=
    (hf_int.norm.add hf_pow_int).const_mul (C_bd * 2 ^ N)
  apply hg_int.mono' (hK_meas.mul f.integrable.aestronglyMeasurable)
  filter_upwards [hK_bound] with x hx
  simp only [Pi.mul_apply, norm_mul]
  calc ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖
      ≤ C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ :=
        mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ ≤ C_bd * (2 ^ N * (1 + ‖x‖ ^ N)) * ‖(f : NPointDomain d n → ℂ) x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (h_binom_ineq ‖x‖ (norm_nonneg _)) (le_of_lt hC)
    _ = C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
          ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖) := by ring

/-- **Continuity of Schwartz integration against a polynomially bounded kernel.**

    If K : D → ℂ is measurable and satisfies the a.e. polynomial bound
    ‖K(x)‖ ≤ C · (1 + ‖x‖)^N, then the linear functional f ↦ ∫ K(x)·f(x) dx
    is continuous on Schwartz space.

    Ref: Reed-Simon I, Theorem V.10; Hormander, Theorem 7.1.18 -/
theorem schwartz_continuous_of_polynomial_bound {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    Continuous (fun f : SchwartzNPoint d n => ∫ x, K x * f x) :=
  schwartz_polynomial_kernel_continuous K hK_meas C_bd N hC hK_bound

/-- **The Wick-rotated BHW kernel is a.e. strongly measurable.**

    The function x ↦ F_ext(Wick(x)) is a.e. strongly measurable on NPointDomain.
    This follows from the fact that F_ext is holomorphic (hence continuous) on the
    permuted extended tube, Wick rotation is continuous, and a.e. Euclidean points
    lie in PET (by `ae_euclidean_points_in_permutedTube`). -/
theorem bhw_euclidean_kernel_measurable {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)))
      MeasureTheory.volume := by
  -- Strategy: F_ext is continuous on PET (holomorphic ⇒ continuous). Wick is continuous.
  -- The composition is ContinuousOn on S = Wick⁻¹(PET), which is open and has full measure.
  -- ContinuousOn.aestronglyMeasurable gives AEStronglyMeasurable on μ.restrict S.
  -- Since μ(Sᶜ) = 0, piecewise with 0 on Sᶜ gives the result.
  set F_ext := (W_analytic_BHW Wfn n).val
  set wick : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ) :=
    fun x k => wickRotatePoint (x k)
  set S := wick ⁻¹' (PermutedExtendedTube d n)
  -- F_ext is continuous on PET
  have hF_cont : ContinuousOn F_ext (PermutedExtendedTube d n) :=
    (W_analytic_BHW Wfn n).property.1.continuousOn
  -- wickRotatePoint is continuous as a function Fin (d+1) → ℝ → Fin (d+1) → ℂ
  have hwickpt_cont : Continuous (wickRotatePoint (d := d)) := by
    apply continuous_pi; intro μ
    simp only [wickRotatePoint]
    split_ifs
    · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
    · exact Complex.continuous_ofReal.comp (continuous_apply μ)
  -- wick : NPointDomain d n → Fin n → Fin (d+1) → ℂ is continuous
  have hwick_cont : Continuous wick := by
    apply continuous_pi; intro k
    exact hwickpt_cont.comp (continuous_apply k)
  -- PET is open, so S is open and measurable
  have hPET_open : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  have hS_open : IsOpen S := hPET_open.preimage hwick_cont
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  -- F_ext ∘ wick is ContinuousOn S
  have hcomp_cont : ContinuousOn (fun x => F_ext (wick x)) S :=
    hF_cont.comp hwick_cont.continuousOn (Set.mapsTo_preimage wick _)
  -- Sᶜ has measure zero (ae_euclidean_points_in_permutedTube)
  have hSc_null : MeasureTheory.volume Sᶜ = 0 :=
    MeasureTheory.mem_ae_iff.mp ae_euclidean_points_in_permutedTube
  -- AEStronglyMeasurable on μ.restrict S
  have h_on_S : MeasureTheory.AEStronglyMeasurable
      (fun x => F_ext (wick x)) (MeasureTheory.volume.restrict S) :=
    hcomp_cont.aestronglyMeasurable hS_meas
  -- Since Sᶜ has measure zero, volume.restrict S = volume
  have hrestr : MeasureTheory.volume.restrict S = MeasureTheory.volume :=
    MeasureTheory.Measure.restrict_eq_self_of_ae_mem
      (MeasureTheory.mem_ae_iff.mpr hSc_null)
  change MeasureTheory.AEStronglyMeasurable (fun x => F_ext (wick x))
    MeasureTheory.volume
  rw [← hrestr]
  exact h_on_S

/-- On compact Euclidean regions whose Wick images stay inside PET,
    the BHW Euclidean kernel is uniformly bounded.

    This is the genuine local regularity statement available from the current
    analytic continuation infrastructure: away from the PET boundary, the kernel
    is just the restriction of a holomorphic function and therefore locally
    bounded. The remaining E0 difficulty is to control what happens near the
    Euclidean singular locus where the Wick image approaches the PET boundary,
    together with the behavior at spatial infinity. -/
private theorem bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (hPET : ∀ x ∈ K, (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    ∃ C : ℝ, ∀ x ∈ K,
      ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤ C := by
  set F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ := (W_analytic_BHW Wfn n).val
  set wick : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ) :=
    fun x k => wickRotatePoint (x k)
  have hF_cont : ContinuousOn F_ext (PermutedExtendedTube d n) :=
    (W_analytic_BHW Wfn n).property.1.continuousOn
  have hwickpt_cont : Continuous (wickRotatePoint (d := d)) := by
    apply continuous_pi
    intro μ
    simp only [wickRotatePoint]
    split_ifs
    · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
    · exact Complex.continuous_ofReal.comp (continuous_apply μ)
  have hwick_cont : Continuous wick := by
    apply continuous_pi
    intro k
    exact hwickpt_cont.comp (continuous_apply k)
  have hkernel_cont : ContinuousOn (fun x : NPointDomain d n => ‖F_ext (wick x)‖) K := by
    refine (hF_cont.comp hwick_cont.continuousOn ?_).norm
    intro x hx
    simpa [wick] using hPET x hx
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn (f := fun x : NPointDomain d n => ‖F_ext (wick x)‖)
      hkernel_cont
  refine ⟨C, ?_⟩
  intro x hx
  simpa [F_ext, wick] using hC x hx

/-- Corollary of local PET boundedness on compact Euclidean regions with strictly
    increasing positive time coordinates. -/
private theorem bhw_euclidean_kernel_bounded_on_compact_positiveOrdered
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (hord : ∀ x ∈ K, ∀ k j : Fin n, k < j → x k 0 < x j 0)
    (hpos : ∀ x ∈ K, ∀ k : Fin n, 0 < x k 0) :
    ∃ C : ℝ, ∀ x ∈ K,
      ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤ C := by
  refine bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
    (Wfn := Wfn) hK ?_
  intro x hx
  have hFT : (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n :=
      euclidean_ordered_in_forwardTube x (hord x hx) (hpos x hx)
  have hFT_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hFT
  have hPET_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.PermutedExtendedTube d n :=
    BHW.forwardTube_subset_permutedExtendedTube hFT_BHW
  simpa [BHW_permutedExtendedTube_eq (d := d) (n := n)] using hPET_BHW

/-- The constructed Schwinger functional is continuous on the OS-I
    zero-diagonal test space.

    This is the honest E0 surface currently needed in `OsterwalderSchraderAxioms`.
    Unlike the deleted full-Schwartz theorem fronts, this matches the corrected
    OS-I axiom surface after the zero-diagonal repair. -/
theorem constructedSchwinger_tempered_zeroDiagonal (Wfn : WightmanFunctions d) (n : ℕ) :
    Continuous (fun f : ZeroDiagonalSchwartz d n => constructSchwingerFunctions Wfn n f.1) := by
  sorry

/-- The Schwinger functionals constructed from Wightman functions are linear in
    the test function argument.

    After the zero-diagonal repair, this is no longer justified by the deleted
    full-Schwartz integrability theorem. The remaining honest proof has to treat
    the total extension of `constructSchwingerFunctions` separately from the
    OS-I zero-diagonal pairing. -/
theorem constructedSchwinger_linear (Wfn : WightmanFunctions d) (n : ℕ) :
    IsLinearMap ℂ (constructSchwingerFunctions Wfn n) := by
  sorry

/-- The BHW extension F_ext inherits translation invariance from the Wightman
    distribution W_n.

    Both z ↦ F_ext(z) and z ↦ F_ext(z + c) (for real c) are holomorphic on the
    permuted extended tube with the same distributional boundary values (by
    translation invariance of W_n). By uniqueness of analytic continuation on the
    connected permuted extended tube, they agree.

    Requires: identity theorem for holomorphic functions on tube domains in ℂⁿ.
    The multi-dimensional identity theorem is proved in `SCV/IdentityTheorem.lean`
    (modulo Hartogs analyticity).

    This pointwise form requires both Euclidean configurations
    `wick(x)` and `wick(x + a)` to lie in PET.

    Ref: Streater-Wightman, Theorem 2.8 (uniqueness of holomorphic extension to tubes) -/
theorem F_ext_translation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (a : SpacetimeDim d) (x : NPointDomain d n)
    (htube : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n)
    (htube_shift : (fun k => wickRotatePoint (fun μ => x k μ + a μ)) ∈
      PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
    (W_analytic_BHW Wfn n).val
      (fun k => wickRotatePoint (fun μ => x k μ + a μ)) := by
  -- wickRotatePoint is additive: wick(x + a) = wick(x) + wick(a)
  have hwick_add : (fun k => wickRotatePoint (fun μ => x k μ + a μ)) =
      (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a μ) := by
    ext k μ
    simp only [wickRotatePoint]
    split_ifs <;> push_cast <;> ring
  rw [hwick_add]
  exact (bhw_translation_invariant Wfn (wickRotatePoint a)
    (fun k => wickRotatePoint (x k)) htube (by
      simpa [hwick_add] using htube_shift)).symm

theorem constructedSchwinger_translation_invariant (Wfn : WightmanFunctions d)
    (n : ℕ) (a : SpacetimeDim d) (f g : SchwartzNPoint d n)
    (hfg : ∀ x, g.toFun x = f.toFun (fun i => x i + a)) :
    constructSchwingerFunctions Wfn n f = constructSchwingerFunctions Wfn n g := by
  simp only [constructSchwingerFunctions]
  have hfg' : ∀ x : NPointDomain d n,
      (g : NPointDomain d n → ℂ) x = (f : NPointDomain d n → ℂ) (fun i => x i + a) := hfg
  simp_rw [hfg']
  set a' : NPointDomain d n := fun _ => a
  set K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))
  let P : NPointDomain d n → Prop :=
    fun x => (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n
  have hP_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume, P x :=
    ae_euclidean_points_in_permutedTube
  have hP_shift_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume, P (x + a') := by
    exact (MeasureTheory.eventually_add_right_iff
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)))
      (t := a') (p := P)).2 hP_ae
  -- K is translation-invariant a.e.: K(x) = K(x + a') for a.e. x with wick(x) ∈ PET
  have hK_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      K x = K (x + a') := by
    filter_upwards [hP_ae, hP_shift_ae] with x hx hx_shift
    exact F_ext_translation_invariant Wfn n a x hx (by
      simpa [P] using hx_shift)
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (x + a')
      = ∫ x : NPointDomain d n, K (x + a') * (f : NPointDomain d n → ℂ) (x + a') := by
        exact MeasureTheory.integral_congr_ae (hK_ae.mono fun x hx => by simp only; rw [hx])
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        MeasureTheory.integral_add_right_eq_self
          (fun x => K x * (f : NPointDomain d n → ℂ) x) a'

/-- F_ext is invariant under proper Euclidean rotations (SO(d+1)) at all Euclidean points.

    For Euclidean points with distinct positive times, this follows from
    `schwinger_euclidean_invariant` (AnalyticContinuation.lean) + BHW complex
    Lorentz invariance. For general configurations, it extends by analyticity
    of F_ext ∘ Wick (or by the distribution-level argument).

    Restricted to det R = 1 (proper rotations). Full O(d+1) invariance (det=-1)
    would require parity invariance, which is not implied by Wightman axioms.

    Ref: Streater-Wightman, Theorem 3.6 (BHW); Jost, §IV.5 -/
theorem F_ext_rotation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hR : R.transpose * R = 1)
    (hdet : R.det = 1) (x : NPointDomain d n)
    (htube : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
    (W_analytic_BHW Wfn n).val
      (fun k => wickRotatePoint (R.mulVec (x k))) := by
  have := schwinger_euclidean_invariant
    (fun n => (W_analytic_BHW Wfn n).val)
    (fun n Λ z hz => (W_analytic_BHW Wfn n).property.2.2.1 Λ z hz)
    n R hdet hR x htube
  simp only [SchwingerFromWightman] at this
  exact this.symm

omit [NeZero d] in
/-- Orthogonal transformations preserve volume: the map x ↦ R·x on ℝ^(d+1)
    has |det R| = 1, so the product map on NPointDomain preserves Lebesgue measure. -/
theorem integral_orthogonal_eq_self (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => R.mulVec (x i)) =
    ∫ x : NPointDomain d n, h x := by
  -- det R ≠ 0 and |det R| = 1 from orthogonality
  have hdet : R.det ≠ 0 := by
    intro h; have := congr_arg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, h, mul_zero] at this
    exact zero_ne_one this
  have habs : |R.det| = 1 := by
    have h1 : R.det * R.det = 1 := by
      have := congr_arg Matrix.det hR
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rcases mul_self_eq_one_iff.mp h1 with h | h <;> simp [h]
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  -- R.mulVec preserves volume on each factor
  have hmv : (fun v => R.mulVec v) = Matrix.toLin' R := by
    ext v; simp [Matrix.toLin'_apply]
  have hcont_R : Continuous (Matrix.toLin' R) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcont_Rt : Continuous (Matrix.toLin' R.transpose) :=
    LinearMap.continuous_of_finiteDimensional _
  have hmp_factor : MeasureTheory.MeasurePreserving
      (fun v : Fin (d+1) → ℝ => R.mulVec v)
      MeasureTheory.volume MeasureTheory.volume := by
    rw [hmv]; constructor
    · exact hcont_R.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
      simp [abs_inv, habs]
  -- Construct MeasurableEquiv for the componentwise map
  let e : (Fin n → Fin (d+1) → ℝ) ≃ᵐ (Fin n → Fin (d+1) → ℝ) :=
    { toEquiv := {
        toFun := fun a i => R.mulVec (a i)
        invFun := fun a i => R.transpose.mulVec (a i)
        left_inv := fun a => by ext i j; simp [Matrix.mulVec_mulVec, hR]
        right_inv := fun a => by ext i j; simp [Matrix.mulVec_mulVec, hR'] }
      measurable_toFun :=
        measurable_pi_lambda _ fun i => hcont_R.measurable.comp (measurable_pi_apply i)
      measurable_invFun :=
        measurable_pi_lambda _ fun i => hcont_Rt.measurable.comp (measurable_pi_apply i) }
  -- Lift volume preservation to product, then get integral equality
  have hmp : MeasureTheory.MeasurePreserving (⇑e)
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_pi (fun (_ : Fin n) => hmp_factor)
  exact hmp.integral_comp' h

omit [NeZero d] in
private theorem measurePreserving_timeReflectionN :
    MeasureTheory.MeasurePreserving (timeReflectionN d : NPointDomain d n → NPointDomain d n)
      MeasureTheory.volume MeasureTheory.volume := by
  let R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Matrix.diagonal (Function.update (fun _ : Fin (d + 1) => (1 : ℝ)) 0 (-1))
  have hR : R.transpose * R = 1 := by
    have hdiag :
        R.transpose * R =
          Matrix.diagonal (fun i =>
            (Function.update (fun _ : Fin (d + 1) => (1 : ℝ)) 0 (-1) i) ^ 2) := by
      simp [R, Matrix.diagonal_mul_diagonal, pow_two]
    refine hdiag.trans ?_
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i = 0
      · subst hi0
        simp [Function.update]
      · simp [Matrix.diagonal, Function.update]
    · simp [Matrix.diagonal, hij]
  have hTR : (fun x : NPointDomain d n => timeReflectionN d x) =
      (fun x : NPointDomain d n => fun i => R.mulVec (x i)) := by
    funext x
    ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [R, timeReflectionN, timeReflection, Matrix.mulVec_diagonal, Function.update]
    · simp [R, timeReflectionN, timeReflection, Matrix.mulVec_diagonal, Function.update, hμ]
  have hdet : R.det ≠ 0 := by
    intro h
    have := congr_arg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, h, mul_zero] at this
    exact zero_ne_one this
  have habs : |R.det| = 1 := by
    have h1 : R.det * R.det = 1 := by
      have := congr_arg Matrix.det hR
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rcases mul_self_eq_one_iff.mp h1 with h | h <;> simp [h]
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  have hmv : (fun v => R.mulVec v) = Matrix.toLin' R := by
    ext v
    simp [Matrix.toLin'_apply]
  have hcont_R : Continuous (Matrix.toLin' R) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcont_Rt : Continuous (Matrix.toLin' R.transpose) :=
    LinearMap.continuous_of_finiteDimensional _
  have hmp_factor : MeasureTheory.MeasurePreserving
      (fun v : Fin (d + 1) → ℝ => R.mulVec v)
      MeasureTheory.volume MeasureTheory.volume := by
    rw [hmv]
    constructor
    · exact hcont_R.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
      simp [abs_inv, habs]
  let e : (Fin n → Fin (d + 1) → ℝ) ≃ᵐ (Fin n → Fin (d + 1) → ℝ) :=
    { toEquiv := {
        toFun := fun a i => R.mulVec (a i)
        invFun := fun a i => R.transpose.mulVec (a i)
        left_inv := fun a => by ext i j; simp [Matrix.mulVec_mulVec, hR]
        right_inv := fun a => by ext i j; simp [Matrix.mulVec_mulVec, hR'] }
      measurable_toFun :=
        measurable_pi_lambda _ fun i => hcont_R.measurable.comp (measurable_pi_apply i)
      measurable_invFun :=
        measurable_pi_lambda _ fun i => hcont_Rt.measurable.comp (measurable_pi_apply i) }
  have hmp : MeasureTheory.MeasurePreserving (⇑e)
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_pi (fun (_ : Fin n) => hmp_factor)
  simpa [hTR] using hmp

omit [NeZero d] in
/-- Time reflection preserves Lebesgue measure on Euclidean `n`-point configurations. -/
private theorem integral_timeReflection_eq_self (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (timeReflectionN d x) =
    ∫ x : NPointDomain d n, h x := by
  have hTR_meas : Measurable (timeReflectionN d : NPointDomain d n → NPointDomain d n) := by
    apply Continuous.measurable
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      have hi0 : Continuous (fun a : NPointDomain d n => a i 0) :=
        (continuous_apply (0 : Fin (d + 1))).comp (continuous_apply i)
      simpa [timeReflectionN, timeReflection] using hi0.neg
    · have hiμ : Continuous (fun a : NPointDomain d n => a i μ) :=
        (continuous_apply μ).comp (continuous_apply i)
      simpa [timeReflectionN, timeReflection, hμ] using hiμ
  let e : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv := {
        toFun := timeReflectionN d
        invFun := timeReflectionN d
        left_inv := by
          intro x
          ext i μ
          by_cases hμ : μ = 0
          · subst hμ
            simp [timeReflectionN, timeReflection]
          · simp [timeReflectionN, timeReflection, hμ]
        right_inv := by
          intro x
          ext i μ
          by_cases hμ : μ = 0
          · subst hμ
            simp [timeReflectionN, timeReflection]
          · simp [timeReflectionN, timeReflection, hμ] }
      measurable_toFun := hTR_meas
      measurable_invFun := hTR_meas }
  exact (measurePreserving_timeReflectionN (d := d) (n := n)).integral_comp' (f := e) h

omit [NeZero d] in
private theorem measurePreserving_revPerm :
    MeasureTheory.MeasurePreserving
      (fun x : NPointDomain d n => fun i => x (Fin.rev i))
      MeasureTheory.volume MeasureTheory.volume := by
  simpa [Fin.revPerm] using
    (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin n => Fin (d + 1) → ℝ) Fin.revPerm).symm

/-- Reflected-reversed Euclidean configurations also lie in PET a.e.

    This closes the geometric side of Euclidean BHW reality: the target point
    `wick(timeReflection(x ∘ rev))` is defined on the same full-measure PET set
    as `wick(x)`. The remaining gap in `bhw_euclidean_reality_ae` is therefore
    purely the analytic Schwarz-reflection argument. -/
theorem ae_reflected_reversed_euclidean_points_in_permutedTube {d n : ℕ} [NeZero d] :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (timeReflection d (x (Fin.rev k)))) ∈
        PermutedExtendedTube d n := by
  let T : NPointDomain d n → NPointDomain d n :=
    fun x => timeReflectionN d (fun i => x (Fin.rev i))
  have hT :
      MeasureTheory.MeasurePreserving T MeasureTheory.volume MeasureTheory.volume :=
    (measurePreserving_timeReflectionN (d := d) (n := n)).comp
      (measurePreserving_revPerm (d := d) (n := n))
  rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
  let s : Set (NPointDomain d n) :=
    {x | (fun k => wickRotatePoint (x k)) ∉ PermutedExtendedTube d n}
  have hs_null : MeasureTheory.volume s = 0 := by
    simpa [s] using
      (MeasureTheory.mem_ae_iff.mp (ae_euclidean_points_in_permutedTube (d := d) (n := n)))
  simpa [T, s, timeReflectionN] using hT.preimage_null hs_null

/-- Original and reflected-reversed Euclidean configurations lie in PET simultaneously a.e. -/
theorem ae_euclidean_points_in_permutedTube_overlap {d n : ℕ} [NeZero d] :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n ∧
      (fun k => wickRotatePoint (timeReflection d (x (Fin.rev k)))) ∈
        PermutedExtendedTube d n := by
  filter_upwards [ae_euclidean_points_in_permutedTube (d := d) (n := n),
    ae_reflected_reversed_euclidean_points_in_permutedTube (d := d) (n := n)] with x hx hx'
  exact ⟨hx, hx'⟩

/-- The Schwinger functions satisfy rotation invariance (E1b).

    Proof: Complex Lorentz invariance of W_analytic on the permuted extended tube,
    together with the fact that SO(d+1) ⊂ L₊(ℂ) preserves Euclidean points.
    The rotation R ∈ SO(d+1) acts on the forward tube via its embedding in L₊(ℂ). -/
theorem constructedSchwinger_rotation_invariant (Wfn : WightmanFunctions d)
    (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1) (hdet : R.det = 1)
    (f g : SchwartzNPoint d n)
    (hfg : ∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) :
    constructSchwingerFunctions Wfn n f = constructSchwingerFunctions Wfn n g := by
  simp only [constructSchwingerFunctions]
  have hfg' : ∀ x : NPointDomain d n,
      (g : NPointDomain d n → ℂ) x =
      (f : NPointDomain d n → ℂ) (fun i => R.mulVec (x i)) := hfg
  simp_rw [hfg']
  set K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))
  -- K is rotation-invariant a.e.: K(x) = K(Rx) for a.e. x with wick(x) ∈ PET
  have hK_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      K x = K (fun i => R.mulVec (x i)) := by
    filter_upwards [ae_euclidean_points_in_permutedTube] with x hx
    exact F_ext_rotation_invariant Wfn n R hR hdet x hx
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (fun i => R.mulVec (x i))
      = ∫ x : NPointDomain d n,
          K (fun i => R.mulVec (x i)) *
          (f : NPointDomain d n → ℂ) (fun i => R.mulVec (x i)) := by
        exact MeasureTheory.integral_congr_ae (hK_ae.mono fun x hx => by simp only; rw [hx])
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        integral_orthogonal_eq_self R hR
          (fun x => K x * (f : NPointDomain d n → ℂ) x)

omit [NeZero d] in
/-- Wick rotation of a time-reflected point equals componentwise conjugation
    of the Wick-rotated point: Wick(θ(τ,x⃗)) = conj(Wick(τ,x⃗)).

    This is because: θ(τ,x⃗) = (-τ,x⃗), and Wick(-τ,x⃗) = (-iτ,x⃗),
    while conj(Wick(τ,x⃗)) = conj(iτ, x⃗) = (-iτ, x⃗) (spatial coords are real).

    This identity connects the OS time-reflection involution to complex conjugation
    in the tube domain, which is the bridge between the Euclidean and Minkowski
    inner products. -/
theorem wickRotatePoint_timeReflection (x : Fin (d + 1) → ℝ) (μ : Fin (d + 1)) :
    wickRotatePoint (timeReflection d x) μ = starRingEnd ℂ (wickRotatePoint x μ) := by
  simp only [wickRotatePoint, timeReflection]
  by_cases hμ : μ = 0
  · subst hμ; simp [Complex.conj_ofReal]
  · simp [hμ, Complex.conj_ofReal]

/-- Reverse the point order and conjugate each complex coordinate. This is the
    complex-geometric involution underlying Wightman Hermiticity on Euclidean
    Wick points. -/
private def hermitianReverse {d n : ℕ} :
    (Fin n → Fin (d + 1) → ℂ) → (Fin n → Fin (d + 1) → ℂ) :=
  fun z k μ => starRingEnd ℂ (z (Fin.rev k) μ)

private def oneFin (d : ℕ) [NeZero d] : Fin (d + 1) :=
  ⟨1, Nat.succ_lt_succ (NeZero.pos d)⟩

private theorem zero_ne_oneFin (d : ℕ) [NeZero d] :
    (0 : Fin (d + 1)) ≠ oneFin d := by
  intro h
  have := congrArg Fin.val h
  simp [oneFin] at this

private def hermitianTwistMatrix (d : ℕ) [NeZero d] :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (fun μ => if μ = (0 : Fin (d + 1)) ∨ μ = oneFin d then (-1 : ℝ) else 1)

private theorem hermitianTwistMatrix_orthogonal (d : ℕ) [NeZero d] :
    (hermitianTwistMatrix d).transpose * hermitianTwistMatrix d = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi0 : i = 0
    · subst hi0
      simp [hermitianTwistMatrix, oneFin]
    · by_cases hi1 : i = oneFin d
      · subst hi1
        simp [hermitianTwistMatrix, oneFin]
      · simp [hermitianTwistMatrix, hi0, hi1]
  · simp [hermitianTwistMatrix, hij]

private theorem hermitianTwistMatrix_det (d : ℕ) [NeZero d] :
    (hermitianTwistMatrix d).det = 1 := by
  classical
  let e1 : Fin (d + 1) := oneFin d
  have h0 : (0 : Fin (d + 1)) ∈ (Finset.univ : Finset (Fin (d + 1))) := Finset.mem_univ _
  have h1 : e1 ∈ (Finset.univ : Finset (Fin (d + 1))) := Finset.mem_univ _
  have h01 : (0 : Fin (d + 1)) ≠ e1 := zero_ne_oneFin d
  unfold hermitianTwistMatrix
  rw [Matrix.det_diagonal]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 1)))
    (fun μ => if μ = 0 ∨ μ = e1 then (-1 : ℝ) else 1) h0]
  rw [← Finset.mul_prod_erase ((Finset.univ : Finset (Fin (d + 1))).erase 0)
    (fun μ => if μ = 0 ∨ μ = e1 then (-1 : ℝ) else 1)
    (a := e1) (Finset.mem_erase.mpr ⟨h01.symm, h1⟩)]
  have hrest :
      ∀ x ∈ ((Finset.univ : Finset (Fin (d + 1))).erase 0).erase e1,
        (if x = 0 ∨ x = e1 then (-1 : ℝ) else 1) = 1 := by
    intro x hx
    have hx1 : x ≠ e1 := (Finset.mem_erase.mp hx).1
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    simp [hx0, hx1]
  have hprod :
      ∏ x ∈ ((Finset.univ : Finset (Fin (d + 1))).erase 0).erase e1,
        (if x = 0 ∨ x = e1 then (-1 : ℝ) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    exact hrest x hx
  have hneg0 : (if (0 : Fin (d + 1)) = 0 ∨ (0 : Fin (d + 1)) = e1 then (-1 : ℝ) else 1) = -1 := by
    simp
  have hnege1 : (if e1 = 0 ∨ e1 = e1 then (-1 : ℝ) else 1) = -1 := by
    simp
  rw [hneg0, hnege1, hprod]
  ring

private noncomputable def hermitianTwistCLG (d : ℕ) [NeZero d] : ComplexLorentzGroup d :=
  ComplexLorentzGroup.ofEuclidean (hermitianTwistMatrix d)
    (hermitianTwistMatrix_det d) (hermitianTwistMatrix_orthogonal d)

private theorem hermitianTwistCLG_val {d : ℕ} [NeZero d] (μ ν : Fin (d + 1)) :
    (hermitianTwistCLG d).val μ ν =
      if μ = ν then (if μ = 0 ∨ μ = oneFin d then (-1 : ℂ) else 1) else 0 := by
  by_cases hμν : μ = ν
  · subst hμν
    by_cases hμ0 : μ = 0
    · subst hμ0
      simp [hermitianTwistCLG, ComplexLorentzGroup.ofEuclidean, hermitianTwistMatrix, oneFin]
    · by_cases hμ1 : μ = oneFin d
      · subst hμ1
        simp [hermitianTwistCLG, ComplexLorentzGroup.ofEuclidean, hermitianTwistMatrix, oneFin]
      · have hcast :
            ((if μ = oneFin d then (-1 : ℝ) else 1 : ℝ) : ℂ) =
              (if μ = oneFin d then (-1 : ℂ) else 1) := by
            split_ifs; norm_num
        have hgoal :
            (hermitianTwistCLG d).val μ μ =
              ((if μ = oneFin d then (-1 : ℝ) else 1 : ℝ) : ℂ) := by
          simp [hermitianTwistCLG, ComplexLorentzGroup.ofEuclidean, hermitianTwistMatrix,
            oneFin, hμ0]
        simpa using show
          (hermitianTwistCLG d).val μ μ =
            (if μ = 0 ∨ μ = oneFin d then (-1 : ℂ) else 1) from
          calc
            (hermitianTwistCLG d).val μ μ =
                ((if μ = oneFin d then (-1 : ℝ) else 1 : ℝ) : ℂ) :=
              hgoal
            _ = (if μ = 0 ∨ μ = oneFin d then (-1 : ℂ) else 1) := by
              simpa [hμ0] using hcast
  · by_cases hν0 : ν = 0
    · subst hν0
      simp [hermitianTwistCLG, ComplexLorentzGroup.ofEuclidean, hermitianTwistMatrix,
        oneFin, hμν]
    · by_cases hμ0 : μ = 0
      · subst hμ0
        simp [hermitianTwistCLG, ComplexLorentzGroup.ofEuclidean, hermitianTwistMatrix,
          oneFin, hμν, hν0]
      · simp [hermitianTwistCLG, ComplexLorentzGroup.ofEuclidean, hermitianTwistMatrix,
        oneFin, hμν, hμ0, hν0]

private theorem complexLorentzAction_hermitianTwistCLG {d n : ℕ} [NeZero d]
    (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) (μ : Fin (d + 1)) :
    BHW.complexLorentzAction (hermitianTwistCLG d) z k μ =
      (if μ = 0 ∨ μ = oneFin d then (-1 : ℂ) else 1) * z k μ := by
  simp [BHW.complexLorentzAction, hermitianTwistCLG_val]

private def spatialFlipOne {d : ℕ} [NeZero d]
    (x : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun μ => if μ = oneFin d then -x μ else x μ

private def spatialFlipOneN {d n : ℕ} [NeZero d]
    (x : NPointDomain d n) : NPointDomain d n :=
  fun k => spatialFlipOne (x k)

private def hermitianTwistReal {d : ℕ} [NeZero d]
    (x : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  timeReflection d (spatialFlipOne x)

private def hermitianTwistRealN {d n : ℕ} [NeZero d]
    (x : NPointDomain d n) : NPointDomain d n :=
  fun k => hermitianTwistReal (x k)

/-- The honest PET overlap for Euclidean Hermiticity: points whose conjugate-reverse
    image also lies in the permuted extended tube. -/
private def hermitianReverseOverlap {d n : ℕ} [NeZero d] :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | z ∈ PermutedExtendedTube d n ∧ hermitianReverse z ∈ PermutedExtendedTube d n }

private theorem hermitianReverse_involutive {d n : ℕ}
    (z : Fin n → Fin (d + 1) → ℂ) :
    hermitianReverse (hermitianReverse z) = z := by
  ext k μ
  simp [hermitianReverse, Fin.rev_rev]

private theorem continuous_hermitianReverse {d n : ℕ} :
    Continuous (hermitianReverse (d := d) (n := n)) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  have hcoord : Continuous fun z : Fin n → Fin (d + 1) → ℂ => z (Fin.rev k) μ :=
    (continuous_apply μ).comp ((continuous_apply (Fin.rev k)).comp continuous_id)
  simpa [hermitianReverse] using hcoord.star

private theorem isOpen_hermitianReverseOverlap {d n : ℕ} [NeZero d] :
    IsOpen (hermitianReverseOverlap (d := d) (n := n)) := by
  have hPET_open : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  exact hPET_open.inter (hPET_open.preimage (continuous_hermitianReverse (d := d) (n := n)))

private theorem hermitianReverse_wickRotate {d n : ℕ}
    (x : NPointDomain d n) :
    hermitianReverse (fun k => wickRotatePoint (x k)) =
      (fun k => wickRotatePoint (timeReflection d (x (Fin.rev k)))) := by
  ext k μ
  simp [hermitianReverse, wickRotatePoint_timeReflection]

/-- In `d = 1`, the mixed slice with real time and imaginary space coordinates.
    It interacts cleanly with `hermitianReverse`, but is later shown not to lie
    in the permuted extended tube for any nonempty configuration. -/
private def mixedWickPoint (x : SpacetimeDim 1) : Fin (1 + 1) → ℂ :=
  fun μ => if μ = 0 then (x 0 : ℂ) else (x 1 : ℂ) * Complex.I

private def mixedWick {n : ℕ} (x : NPointDomain 1 n) : Fin n → Fin (1 + 1) → ℂ :=
  fun k => mixedWickPoint (x k)

private theorem hermitianReverse_mixedWick {n : ℕ}
    (x : NPointDomain 1 n) :
    hermitianReverse (mixedWick x) =
      mixedWick (fun k => spatialFlipOne (x (Fin.rev k))) := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [hermitianReverse, mixedWick, mixedWickPoint, spatialFlipOne, zero_ne_oneFin]
  · have hμ1 : μ = (1 : Fin (1 + 1)) := by
      fin_cases μ
      · contradiction
      · rfl
    subst hμ1
    simp [hermitianReverse, mixedWick, mixedWickPoint, spatialFlipOne, oneFin]

private theorem bhw_inOpenForwardCone_one_iff_pm
    (η : Fin (1 + 1) → ℝ) :
    BHW.InOpenForwardCone 1 η ↔ (η 0 + η 1 > 0 ∧ η 0 - η 1 > 0) := by
  rw [BHW.inOpenForwardCone_iff_timePos_gapPos]
  constructor
  · rintro ⟨h0, hgap⟩
    have hgap' : 0 < η 0 ^ 2 - η 1 ^ 2 := by
      simpa using hgap
    constructor <;> nlinarith
  · rintro ⟨hplus, hminus⟩
    refine ⟨by linarith, ?_⟩
    have hgap : 0 < η 0 ^ 2 - η 1 ^ 2 := by
      nlinarith [hplus, hminus]
    simpa using hgap

private theorem rapidityElementD1_val_zero_zero (θ : ℂ) :
    (BHW.rapidityElementD1 θ).val 0 0 = Complex.cosh θ := by
  rfl

private theorem rapidityElementD1_val_zero_one (θ : ℂ) :
    (BHW.rapidityElementD1 θ).val 0 1 = Complex.sinh θ := by
  rfl

private theorem rapidityElementD1_val_one_zero (θ : ℂ) :
    (BHW.rapidityElementD1 θ).val 1 0 = Complex.sinh θ := by
  rfl

private theorem rapidityElementD1_val_one_one (θ : ℂ) :
    (BHW.rapidityElementD1 θ).val 1 1 = Complex.cosh θ := by
  rfl

private theorem hermitianReverse_complexLorentzAction_pureImag_rapidity
    {n : ℕ} (b : ℝ) (z : Fin n → Fin (1 + 1) → ℂ) :
    hermitianReverse
        (BHW.complexLorentzAction (BHW.rapidityElementD1 ((b : ℂ) * Complex.I)) z) =
      BHW.complexLorentzAction
        (BHW.rapidityElementD1 (-((b : ℂ) * Complex.I)))
        (hermitianReverse z) := by
  have hcosh :
      starRingEnd ℂ (Complex.cosh ((b : ℂ) * Complex.I)) =
        Complex.cosh ((b : ℂ) * Complex.I) := by
    rw [Complex.cosh_mul_I]
    apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im]
  have hsinh :
      starRingEnd ℂ (Complex.sinh ((b : ℂ) * Complex.I)) =
        -Complex.sinh ((b : ℂ) * Complex.I) := by
    rw [Complex.sinh_mul_I]
    apply Complex.ext <;> simp [Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ext k μ
  fin_cases μ
  · simp [hermitianReverse, BHW.complexLorentzAction,
      rapidityElementD1_val_zero_zero, rapidityElementD1_val_zero_one, hcosh, hsinh]
  · simp [hermitianReverse, BHW.complexLorentzAction,
      rapidityElementD1_val_one_zero, rapidityElementD1_val_one_one, hcosh, hsinh]

private theorem hermitianReverseOverlap_pureImag_rapidity_invariant
    {n : ℕ} (b : ℝ) {z : Fin n → Fin (1 + 1) → ℂ}
    (hz : z ∈ hermitianReverseOverlap (d := 1) (n := n)) :
    BHW.complexLorentzAction (BHW.rapidityElementD1 ((b : ℂ) * Complex.I)) z ∈
      hermitianReverseOverlap (d := 1) (n := n) := by
  refine ⟨?_, ?_⟩
  · have hzPET : z ∈ BHW.PermutedExtendedTube 1 n := by
      simpa [BHW_permutedExtendedTube_eq (d := 1) (n := n)] using hz.1
    have hrotPET :
        BHW.complexLorentzAction (BHW.rapidityElementD1 ((b : ℂ) * Complex.I)) z ∈
          BHW.PermutedExtendedTube 1 n :=
      BHW.complexLorentzAction_mem_permutedExtendedTube hzPET
        (BHW.rapidityElementD1 ((b : ℂ) * Complex.I))
    simpa [BHW_permutedExtendedTube_eq (d := 1) (n := n)] using hrotPET
  · have hzhrPET : hermitianReverse z ∈ BHW.PermutedExtendedTube 1 n := by
      simpa [BHW_permutedExtendedTube_eq (d := 1) (n := n)] using hz.2
    rw [hermitianReverse_complexLorentzAction_pureImag_rapidity]
    have hrotPET :
        BHW.complexLorentzAction (BHW.rapidityElementD1 (-((b : ℂ) * Complex.I)))
          (hermitianReverse z) ∈ BHW.PermutedExtendedTube 1 n :=
      BHW.complexLorentzAction_mem_permutedExtendedTube hzhrPET
        (BHW.rapidityElementD1 (-((b : ℂ) * Complex.I)))
    simpa [BHW_permutedExtendedTube_eq (d := 1) (n := n)] using hrotPET

private theorem mixedWickPoint_rapidity_plus_im
    (x : SpacetimeDim 1) (a b : ℝ) :
    (BHW.complexLorentzAction
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I))
        (fun _ : Fin 1 => mixedWickPoint x) 0 0).im +
      (BHW.complexLorentzAction
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I))
        (fun _ : Fin 1 => mixedWickPoint x) 0 1).im =
      Real.exp a * (x 0 * Real.sin b + x 1 * Real.cos b) := by
  let θ : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have hsum :
      BHW.complexLorentzAction
          (BHW.rapidityElementD1 θ)
          (fun _ : Fin 1 => mixedWickPoint x) 0 0 +
        BHW.complexLorentzAction
          (BHW.rapidityElementD1 θ)
          (fun _ : Fin 1 => mixedWickPoint x) 0 1 =
        Complex.exp θ * ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) := by
    simp [BHW.complexLorentzAction, mixedWickPoint, θ,
      rapidityElementD1_val_zero_zero, rapidityElementD1_val_zero_one,
      rapidityElementD1_val_one_zero, rapidityElementD1_val_one_one]
    change
      Complex.cosh θ * ↑(x 0) + Complex.sinh θ * (↑(x 1) * Complex.I) +
          (Complex.sinh θ * ↑(x 0) + Complex.cosh θ * (↑(x 1) * Complex.I)) =
        Complex.exp θ * ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I)
    calc
      Complex.cosh θ * ↑(x 0) + Complex.sinh θ * (↑(x 1) * Complex.I) +
            (Complex.sinh θ * ↑(x 0) + Complex.cosh θ * (↑(x 1) * Complex.I))
          = (Complex.cosh θ + Complex.sinh θ) *
              ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) := by ring
      _ = Complex.exp θ * ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) := by
            rw [Complex.cosh_add_sinh]
  have him := congrArg Complex.im hsum
  simp [θ, Complex.add_im, Complex.mul_im, Complex.exp_re, Complex.exp_im] at him
  ring_nf at him ⊢
  exact him

private theorem mixedWickPoint_rapidity_minus_im
    (x : SpacetimeDim 1) (a b : ℝ) :
    (BHW.complexLorentzAction
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I))
        (fun _ : Fin 1 => mixedWickPoint x) 0 0).im -
      (BHW.complexLorentzAction
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I))
        (fun _ : Fin 1 => mixedWickPoint x) 0 1).im =
      Real.exp (-a) * (-(x 0 * Real.sin b + x 1 * Real.cos b)) := by
  let θ : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have hdiff :
      BHW.complexLorentzAction
          (BHW.rapidityElementD1 θ)
          (fun _ : Fin 1 => mixedWickPoint x) 0 0 -
        BHW.complexLorentzAction
          (BHW.rapidityElementD1 θ)
          (fun _ : Fin 1 => mixedWickPoint x) 0 1 =
        Complex.exp (-θ) * ((x 0 : ℂ) - (x 1 : ℂ) * Complex.I) := by
    simp [BHW.complexLorentzAction, mixedWickPoint, θ,
      rapidityElementD1_val_zero_zero, rapidityElementD1_val_zero_one,
      rapidityElementD1_val_one_zero, rapidityElementD1_val_one_one]
    change
      (Complex.cosh θ * ↑(x 0) + Complex.sinh θ * (↑(x 1) * Complex.I)) -
          (Complex.sinh θ * ↑(x 0) + Complex.cosh θ * (↑(x 1) * Complex.I)) =
        Complex.exp (-(↑b * Complex.I) + -↑a) * ((x 0 : ℂ) - (x 1 : ℂ) * Complex.I)
    calc
      (Complex.cosh θ * ↑(x 0) + Complex.sinh θ * (↑(x 1) * Complex.I)) -
            (Complex.sinh θ * ↑(x 0) + Complex.cosh θ * (↑(x 1) * Complex.I))
          = (Complex.cosh θ - Complex.sinh θ) *
              ((x 0 : ℂ) - (x 1 : ℂ) * Complex.I) := by ring
      _ = Complex.exp (-(↑b * Complex.I) + -↑a) * ((x 0 : ℂ) - (x 1 : ℂ) * Complex.I) := by
            have hsub : Complex.cosh θ - Complex.sinh θ =
                Complex.exp (-(↑b * Complex.I) + -↑a) := by
              calc
                Complex.cosh θ - Complex.sinh θ = Complex.exp (-θ) := by
                  rw [Complex.cosh_sub_sinh]
                _ = Complex.exp (-(↑b * Complex.I) + -↑a) := by
                  congr 1
                  simp [θ]
            rw [hsub]
  have him := congrArg Complex.im hdiff
  simp [θ, Complex.sub_im, Complex.mul_im, Complex.exp_re, Complex.exp_im] at him
  ring_nf at him ⊢
  exact him

private theorem rapidity_mixedWickPoint_not_mem_BHW_forwardTube
    (x : SpacetimeDim 1) (a b : ℝ) :
    BHW.complexLorentzAction
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I))
        (fun _ : Fin 1 => mixedWickPoint x) ∉
      BHW.ForwardTube 1 1 := by
  intro hz
  let z : Fin 1 → Fin (1 + 1) → ℂ :=
    BHW.complexLorentzAction
      (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I))
      (fun _ : Fin 1 => mixedWickPoint x)
  have hcone : BHW.InOpenForwardCone 1 (fun μ => (z 0 μ).im) := by
    simpa [z] using hz (0 : Fin 1)
  rcases (bhw_inOpenForwardCone_one_iff_pm (fun μ => (z 0 μ).im)).1 hcone with
    ⟨hplus, hminus⟩
  have hplus_formula :
      (z 0 0).im + (z 0 1).im =
        Real.exp a * (x 0 * Real.sin b + x 1 * Real.cos b) := by
    simpa [z] using mixedWickPoint_rapidity_plus_im x a b
  have hminus_formula :
      (z 0 0).im - (z 0 1).im =
        Real.exp (-a) * (-(x 0 * Real.sin b + x 1 * Real.cos b)) := by
    simpa [z] using mixedWickPoint_rapidity_minus_im x a b
  have hS :
      0 < x 0 * Real.sin b + x 1 * Real.cos b := by
    nlinarith [hplus, hplus_formula, Real.exp_pos a]
  have hnegS :
      0 < -(x 0 * Real.sin b + x 1 * Real.cos b) := by
    nlinarith [hminus, hminus_formula, Real.exp_pos (-a)]
  linarith

private theorem single_mixedWickPoint_not_mem_BHW_extendedTube
    (x : SpacetimeDim 1) :
    (fun _ : Fin 1 => mixedWickPoint x) ∉ BHW.ExtendedTube 1 1 := by
  intro hz
  rcases Set.mem_iUnion.mp hz with ⟨Λ, w, hwFT, hEq⟩
  have hback :
      BHW.complexLorentzAction Λ⁻¹ (fun _ : Fin 1 => mixedWickPoint x) ∈
        BHW.ForwardTube 1 1 := by
    have hback' :
        BHW.complexLorentzAction Λ⁻¹ (BHW.complexLorentzAction Λ w) ∈
          BHW.ForwardTube 1 1 := by
      simpa [BHW.complexLorentzAction_inv] using hwFT
    simpa [hEq] using hback'
  rcases BHW.d1_exists_rapidityElement_principal_im_repr Λ⁻¹ with ⟨a, b, _, hrepr⟩
  rw [hrepr] at hback
  exact rapidity_mixedWickPoint_not_mem_BHW_forwardTube x a b hback

private theorem firstPoint_mem_BHW_forwardTube_of_mem_BHW_forwardTube
    {n : ℕ} [NeZero n]
    {z : Fin n → Fin (1 + 1) → ℂ} (hz : z ∈ BHW.ForwardTube 1 n) :
    (fun _ : Fin 1 => z 0) ∈ BHW.ForwardTube 1 1 := by
  intro k
  fin_cases k
  simpa [BHW.ForwardTube] using hz (0 : Fin n)

private theorem mixedWick_not_mem_BHW_permutedExtendedTube
    {n : ℕ} [NeZero n] (x : NPointDomain 1 n) :
    mixedWick x ∉ BHW.PermutedExtendedTube 1 n := by
  intro hz
  rcases Set.mem_iUnion.mp hz with ⟨π, Λ, w, hwπ, hEq⟩
  let y : Fin n → Fin (1 + 1) → ℂ := fun k => w (π k)
  have hyFT : y ∈ BHW.ForwardTube 1 n := by
    simpa [y, BHW.PermutedForwardTube] using hwπ
  have hy0FT : (fun _ : Fin 1 => y 0) ∈ BHW.ForwardTube 1 1 :=
    firstPoint_mem_BHW_forwardTube_of_mem_BHW_forwardTube hyFT
  have hy0Eq :
      (fun _ : Fin 1 => mixedWickPoint (x (π 0))) =
        BHW.complexLorentzAction Λ (fun _ : Fin 1 => y 0) := by
    ext j μ
    fin_cases j
    have hEq0 :
        mixedWick x (π 0) μ = (BHW.complexLorentzAction Λ w) (π 0) μ := by
      exact congrArg (fun cfg : Fin n → Fin (1 + 1) → ℂ => cfg (π 0) μ) hEq
    simpa [mixedWick, y] using hEq0
  have hsingleET : (fun _ : Fin 1 => mixedWickPoint (x (π 0))) ∈ BHW.ExtendedTube 1 1 := by
    exact Set.mem_iUnion.mpr ⟨Λ, (fun _ : Fin 1 => y 0), hy0FT, hy0Eq⟩
  exact single_mixedWickPoint_not_mem_BHW_extendedTube (x (π 0)) hsingleET

private theorem mixedWick_not_mem_permutedExtendedTube
    {n : ℕ} [NeZero n] (x : NPointDomain 1 n) :
    mixedWick x ∉ PermutedExtendedTube 1 n := by
  rw [← BHW_permutedExtendedTube_eq (d := 1) (n := n)]
  exact mixedWick_not_mem_BHW_permutedExtendedTube x

private def complexLorentzActionVec
    (Λ : ComplexLorentzGroup 1) (ξ : Fin (1 + 1) → ℂ) : Fin (1 + 1) → ℂ :=
  fun μ => ∑ ν, Λ.val μ ν * ξ ν

private def lightConePlus (ξ : Fin (1 + 1) → ℂ) : ℂ :=
  ξ 0 + ξ 1

private def lightConeMinus (ξ : Fin (1 + 1) → ℂ) : ℂ :=
  ξ 0 - ξ 1

private theorem diffCoordFun_complexLorentzAction
    {n : ℕ} (Λ : ComplexLorentzGroup 1)
    (z : Fin n → Fin (1 + 1) → ℂ) :
    BHW.diffCoordFun n 1 (BHW.complexLorentzAction Λ z) =
      BHW.complexLorentzAction Λ (BHW.diffCoordFun n 1 z) := by
  ext k μ
  by_cases hk : k.val = 0
  · simp [BHW.diffCoordFun, BHW.complexLorentzAction, hk]
  · simp [BHW.diffCoordFun, BHW.complexLorentzAction, hk]
    ring_nf

private theorem diffCoordFun_realEmbed_im_zero
    {n : ℕ} (x : NPointDomain 1 n) (k : Fin n) (μ : Fin (1 + 1)) :
    (BHW.diffCoordFun n 1 (BHW.realEmbed x) k μ).im = 0 := by
  by_cases hk : k.val = 0
  · simp [BHW.diffCoordFun, BHW.realEmbed, hk]
  · simp [BHW.diffCoordFun, BHW.realEmbed, hk]

private theorem diffCoordFun_realEmbed_re_eq_consecutiveDiff
    {n : ℕ} (x : NPointDomain 1 n) (k : Fin n) (μ : Fin (1 + 1)) :
    (BHW.diffCoordFun n 1 (BHW.realEmbed x) k μ).re = BHW.consecutiveDiff x k μ := by
  by_cases hk : k.val = 0
  · simp [BHW.diffCoordFun, BHW.realEmbed, BHW.consecutiveDiff, hk]
  · simp [BHW.diffCoordFun, BHW.realEmbed, BHW.consecutiveDiff, hk]

private theorem lightConePlus_rapidity
    (θ : ℂ) (ξ : Fin (1 + 1) → ℂ) :
    lightConePlus (complexLorentzActionVec (BHW.rapidityElementD1 θ) ξ) =
      Complex.exp θ * lightConePlus ξ := by
  simp [lightConePlus, complexLorentzActionVec, rapidityElementD1_val_zero_zero,
    rapidityElementD1_val_zero_one, rapidityElementD1_val_one_zero,
    rapidityElementD1_val_one_one]
  calc
    Complex.cosh θ * ξ 0 + Complex.sinh θ * ξ 1 +
        (Complex.sinh θ * ξ 0 + Complex.cosh θ * ξ 1)
        = (Complex.cosh θ + Complex.sinh θ) * (ξ 0 + ξ 1) := by ring
    _ = Complex.exp θ * (ξ 0 + ξ 1) := by rw [Complex.cosh_add_sinh]

private theorem lightConeMinus_rapidity
    (θ : ℂ) (ξ : Fin (1 + 1) → ℂ) :
    lightConeMinus (complexLorentzActionVec (BHW.rapidityElementD1 θ) ξ) =
      Complex.exp (-θ) * lightConeMinus ξ := by
  simp [lightConeMinus, complexLorentzActionVec, rapidityElementD1_val_zero_zero,
    rapidityElementD1_val_zero_one, rapidityElementD1_val_one_zero,
    rapidityElementD1_val_one_one]
  calc
    Complex.cosh θ * ξ 0 + Complex.sinh θ * ξ 1 -
        (Complex.sinh θ * ξ 0 + Complex.cosh θ * ξ 1)
        = (Complex.cosh θ - Complex.sinh θ) * (ξ 0 - ξ 1) := by ring
    _ = Complex.exp (-θ) * (ξ 0 - ξ 1) := by rw [Complex.cosh_sub_sinh]

private theorem lightConePlus_real_mul_sin_of_real_output
    (ξ : Fin (1 + 1) → ℂ) (a b : ℝ)
    (hreal0 :
      (complexLorentzActionVec
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ 0).im = 0)
    (hreal1 :
      (complexLorentzActionVec
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ 1).im = 0) :
    (lightConePlus
        (complexLorentzActionVec
          (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ)).re *
        Real.sin b =
      -Real.exp a * (lightConePlus ξ).im := by
  let θ : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  let y := complexLorentzActionVec (BHW.rapidityElementD1 θ) ξ
  have hplus_eq : lightConePlus y = Complex.exp θ * lightConePlus ξ := by
    simpa [y, θ] using lightConePlus_rapidity θ ξ
  have hy_im : (lightConePlus y).im = 0 := by
    rw [show lightConePlus y = y 0 + y 1 by rfl, Complex.add_im, hreal0, hreal1]
    ring
  have hIm :
      (lightConePlus y).im =
        Real.exp a * Real.cos b * (lightConePlus ξ).im +
          Real.exp a * Real.sin b * (lightConePlus ξ).re := by
    have hIm0 := congrArg Complex.im hplus_eq
    simpa [θ, Complex.mul_im, Complex.exp_re, Complex.exp_im] using hIm0
  have hRe :
      (lightConePlus y).re =
        Real.exp a * Real.cos b * (lightConePlus ξ).re -
          Real.exp a * Real.sin b * (lightConePlus ξ).im := by
    have hRe0 := congrArg Complex.re hplus_eq
    simpa [θ, Complex.mul_re, Complex.exp_re, Complex.exp_im] using hRe0
  have hIm' :
      (lightConePlus ξ).re * Real.sin b = -(lightConePlus ξ).im * Real.cos b := by
    nlinarith [hy_im, hIm, Real.exp_pos a]
  have hSin :
      (lightConePlus y).re * Real.sin b =
        Real.exp a * (((lightConePlus ξ).re * Real.cos b -
          (lightConePlus ξ).im * Real.sin b) * Real.sin b) := by
    rw [hRe]
    ring
  have hStep :
      Real.exp a * (((lightConePlus ξ).re * Real.cos b -
          (lightConePlus ξ).im * Real.sin b) * Real.sin b) =
        -Real.exp a * (lightConePlus ξ).im *
          (Real.cos b ^ 2 + Real.sin b ^ 2) := by
    calc
      Real.exp a * (((lightConePlus ξ).re * Real.cos b -
          (lightConePlus ξ).im * Real.sin b) * Real.sin b)
          = Real.exp a * (((lightConePlus ξ).re * Real.sin b) * Real.cos b -
              (lightConePlus ξ).im * Real.sin b * Real.sin b) := by ring
      _ = Real.exp a * ((-(lightConePlus ξ).im * Real.cos b) * Real.cos b -
            (lightConePlus ξ).im * Real.sin b * Real.sin b) := by rw [hIm']
      _ = -Real.exp a * (lightConePlus ξ).im *
            (Real.cos b ^ 2 + Real.sin b ^ 2) := by ring
  have hsq : Real.cos b ^ 2 + Real.sin b ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq b]
  calc
    (lightConePlus y).re * Real.sin b =
        Real.exp a * (((lightConePlus ξ).re * Real.cos b -
          (lightConePlus ξ).im * Real.sin b) * Real.sin b) := hSin
    _ = -Real.exp a * (lightConePlus ξ).im *
          (Real.cos b ^ 2 + Real.sin b ^ 2) := hStep
    _ = -Real.exp a * (lightConePlus ξ).im := by rw [hsq]; ring

private theorem lightConeMinus_real_mul_sin_of_real_output
    (ξ : Fin (1 + 1) → ℂ) (a b : ℝ)
    (hreal0 :
      (complexLorentzActionVec
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ 0).im = 0)
    (hreal1 :
      (complexLorentzActionVec
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ 1).im = 0) :
    (lightConeMinus
        (complexLorentzActionVec
          (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ)).re *
        Real.sin b =
      Real.exp (-a) * (lightConeMinus ξ).im := by
  let θ : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  let y := complexLorentzActionVec (BHW.rapidityElementD1 θ) ξ
  have hminus_eq : lightConeMinus y = Complex.exp (-θ) * lightConeMinus ξ := by
    simpa [y, θ] using lightConeMinus_rapidity θ ξ
  have hy_im : (lightConeMinus y).im = 0 := by
    rw [show lightConeMinus y = y 0 - y 1 by rfl, Complex.sub_im, hreal0, hreal1]
    ring
  have hIm :
      (lightConeMinus y).im =
        Real.exp (-a) * Real.cos b * (lightConeMinus ξ).im -
          Real.exp (-a) * Real.sin b * (lightConeMinus ξ).re := by
    have hIm0 := congrArg Complex.im hminus_eq
    simpa [θ, Complex.mul_im, Complex.exp_re, Complex.exp_im] using hIm0
  have hRe :
      (lightConeMinus y).re =
        Real.exp (-a) * Real.cos b * (lightConeMinus ξ).re +
          Real.exp (-a) * Real.sin b * (lightConeMinus ξ).im := by
    have hRe0 := congrArg Complex.re hminus_eq
    simpa [θ, Complex.mul_re, Complex.exp_re, Complex.exp_im] using hRe0
  have hIm' :
      (lightConeMinus ξ).re * Real.sin b = (lightConeMinus ξ).im * Real.cos b := by
    nlinarith [hy_im, hIm, Real.exp_pos (-a)]
  have hSin :
      (lightConeMinus y).re * Real.sin b =
        Real.exp (-a) * (((lightConeMinus ξ).re * Real.cos b +
          (lightConeMinus ξ).im * Real.sin b) * Real.sin b) := by
    rw [hRe]
    ring
  have hStep :
      Real.exp (-a) * (((lightConeMinus ξ).re * Real.cos b +
          (lightConeMinus ξ).im * Real.sin b) * Real.sin b) =
        Real.exp (-a) * (lightConeMinus ξ).im *
          (Real.cos b ^ 2 + Real.sin b ^ 2) := by
    calc
      Real.exp (-a) * (((lightConeMinus ξ).re * Real.cos b +
          (lightConeMinus ξ).im * Real.sin b) * Real.sin b)
          = Real.exp (-a) * (((lightConeMinus ξ).re * Real.sin b) * Real.cos b +
              (lightConeMinus ξ).im * Real.sin b * Real.sin b) := by ring
      _ = Real.exp (-a) * (((lightConeMinus ξ).im * Real.cos b) * Real.cos b +
            (lightConeMinus ξ).im * Real.sin b * Real.sin b) := by rw [hIm']
      _ = Real.exp (-a) * (lightConeMinus ξ).im *
            (Real.cos b ^ 2 + Real.sin b ^ 2) := by ring
  have hsq : Real.cos b ^ 2 + Real.sin b ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq b]
  calc
    (lightConeMinus y).re * Real.sin b =
        Real.exp (-a) * (((lightConeMinus ξ).re * Real.cos b +
          (lightConeMinus ξ).im * Real.sin b) * Real.sin b) := hSin
    _ = Real.exp (-a) * (lightConeMinus ξ).im *
          (Real.cos b ^ 2 + Real.sin b ^ 2) := hStep
    _ = Real.exp (-a) * (lightConeMinus ξ).im := by rw [hsq]; ring

private theorem extendedTube_d1_common_lightCone_phase
    {n : ℕ} {z : Fin n → Fin (1 + 1) → ℂ}
    :
    z ∈ BHW.ExtendedTube 1 n ↔
      ∃ b : ℝ, ∀ k : Fin n,
        0 < (Complex.exp ((b : ℂ) * Complex.I) *
          lightConePlus (BHW.diffCoordFun n 1 z k)).im ∧
        0 < (Complex.exp (-(b : ℂ) * Complex.I) *
          lightConeMinus (BHW.diffCoordFun n 1 z k)).im := by
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨Λ, w, hwFT, hEq⟩
    rcases BHW.d1_exists_rapidityElement_principal_im_repr Λ with ⟨a, b0, _, hrepr⟩
    refine ⟨-b0, ?_⟩
    intro k
    let ξ : Fin (1 + 1) → ℂ := BHW.diffCoordFun n 1 w k
    have hξ_cone : BHW.InOpenForwardCone 1 (fun μ => (ξ μ).im) := by
      by_cases hk : k.val = 0
      · simpa [ξ, BHW.ForwardTube, BHW.diffCoordFun, hk] using hwFT k
      · simpa [ξ, BHW.ForwardTube, BHW.diffCoordFun, hk] using hwFT k
    rcases (bhw_inOpenForwardCone_one_iff_pm (fun μ => (ξ μ).im)).1 hξ_cone with
      ⟨hξ_plus, hξ_minus⟩
    have hξ_plus_im : 0 < (lightConePlus ξ).im := by
      simpa [lightConePlus, Complex.add_im] using hξ_plus
    have hξ_minus_im : 0 < (lightConeMinus ξ).im := by
      simpa [lightConeMinus, Complex.sub_im] using hξ_minus
    have hdiff_eq :
        BHW.diffCoordFun n 1 z =
          BHW.complexLorentzAction
            (BHW.rapidityElementD1 ((a : ℂ) + (b0 : ℂ) * Complex.I))
            (BHW.diffCoordFun n 1 w) := by
      calc
        BHW.diffCoordFun n 1 z = BHW.diffCoordFun n 1 (BHW.complexLorentzAction Λ w) := by
          rw [hEq]
        _ = BHW.complexLorentzAction Λ (BHW.diffCoordFun n 1 w) :=
          diffCoordFun_complexLorentzAction Λ w
        _ = BHW.complexLorentzAction
              (BHW.rapidityElementD1 ((a : ℂ) + (b0 : ℂ) * Complex.I))
              (BHW.diffCoordFun n 1 w) := by
            rw [hrepr]
    have hact :
        BHW.diffCoordFun n 1 z k =
          complexLorentzActionVec
            (BHW.rapidityElementD1 ((a : ℂ) + (b0 : ℂ) * Complex.I)) ξ := by
      ext μ
      simpa [ξ, BHW.complexLorentzAction, complexLorentzActionVec] using
        (congrArg (fun t : Fin n → Fin (1 + 1) → ℂ => t k μ) hdiff_eq)
    have hplus_eq :
        lightConePlus (BHW.diffCoordFun n 1 z k) =
          Complex.exp ((a : ℂ) + (b0 : ℂ) * Complex.I) * lightConePlus ξ := by
      rw [hact]
      simpa using lightConePlus_rapidity ((a : ℂ) + (b0 : ℂ) * Complex.I) ξ
    have hminus_eq :
        lightConeMinus (BHW.diffCoordFun n 1 z k) =
          Complex.exp (-((a : ℂ) + (b0 : ℂ) * Complex.I)) * lightConeMinus ξ := by
      rw [hact]
      simpa using lightConeMinus_rapidity ((a : ℂ) + (b0 : ℂ) * Complex.I) ξ
    have hplus_phase :
        Complex.exp (((-b0 : ℂ)) * Complex.I) *
            lightConePlus (BHW.diffCoordFun n 1 z k) =
          Complex.exp (a : ℂ) * lightConePlus ξ := by
      rw [hplus_eq]
      calc
        Complex.exp ((-((b0 : ℂ))) * Complex.I) *
            (Complex.exp ((a : ℂ) + (b0 : ℂ) * Complex.I) * lightConePlus ξ)
            =
          (Complex.exp ((-((b0 : ℂ))) * Complex.I) *
              Complex.exp ((a : ℂ) + (b0 : ℂ) * Complex.I)) * lightConePlus ξ := by
                ring
        _ = Complex.exp (((-((b0 : ℂ))) * Complex.I) +
              ((a : ℂ) + (b0 : ℂ) * Complex.I)) * lightConePlus ξ := by
                rw [← Complex.exp_add]
        _ = Complex.exp (a : ℂ) * lightConePlus ξ := by
              congr 1
              ring
    have hminus_phase :
        Complex.exp (-((-b0 : ℂ) * Complex.I)) *
            lightConeMinus (BHW.diffCoordFun n 1 z k) =
          Complex.exp (-((a : ℂ))) * lightConeMinus ξ := by
      rw [hminus_eq]
      calc
        Complex.exp (-((-((b0 : ℂ))) * Complex.I)) *
            (Complex.exp (-((a : ℂ) + (b0 : ℂ) * Complex.I)) * lightConeMinus ξ)
            =
          (Complex.exp (-((-((b0 : ℂ))) * Complex.I)) *
              Complex.exp (-((a : ℂ) + (b0 : ℂ) * Complex.I))) * lightConeMinus ξ := by
                ring
        _ = Complex.exp ((-((-((b0 : ℂ))) * Complex.I)) +
              (-((a : ℂ) + (b0 : ℂ) * Complex.I))) * lightConeMinus ξ := by
                rw [← Complex.exp_add]
        _ = Complex.exp (-((a : ℂ))) * lightConeMinus ξ := by
              congr 1
              ring
    constructor
    · have him :
          (Complex.exp (a : ℂ) * lightConePlus ξ).im =
            Real.exp a * (lightConePlus ξ).im := by
          simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]
      have hplus_im :
          (Complex.exp (((-b0 : ℂ)) * Complex.I) *
              lightConePlus (BHW.diffCoordFun n 1 z k)).im =
            Real.exp a * (lightConePlus ξ).im := by
        rw [hplus_phase]
        exact him
      have hplus_pos :
          0 < (Complex.exp (((-b0 : ℂ)) * Complex.I) *
              lightConePlus (BHW.diffCoordFun n 1 z k)).im := by
        rw [hplus_im]
        exact mul_pos (Real.exp_pos a) hξ_plus_im
      simpa using hplus_pos
    · have him :
          (Complex.exp (-((a : ℂ))) * lightConeMinus ξ).im =
            Real.exp (-a) * (lightConeMinus ξ).im := by
          simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]
      have hminus_im :
          (Complex.exp (-((-b0 : ℂ) * Complex.I)) *
              lightConeMinus (BHW.diffCoordFun n 1 z k)).im =
            Real.exp (-a) * (lightConeMinus ξ).im := by
        rw [hminus_phase]
        exact him
      have hminus_pos :
          0 < (Complex.exp (-((-b0 : ℂ) * Complex.I)) *
              lightConeMinus (BHW.diffCoordFun n 1 z k)).im := by
        rw [hminus_im]
        exact mul_pos (Real.exp_pos (-a)) hξ_minus_im
      simpa using hminus_pos
  · rintro ⟨b, hb⟩
    let Λ : ComplexLorentzGroup 1 := BHW.rapidityElementD1 ((b : ℂ) * Complex.I)
    let w : Fin n → Fin (1 + 1) → ℂ := BHW.complexLorentzAction Λ z
    have hwFT : w ∈ BHW.ForwardTube 1 n := by
      intro k
      let ξ : Fin (1 + 1) → ℂ := BHW.diffCoordFun n 1 z k
      have hdiff_eq :
          BHW.diffCoordFun n 1 w =
            BHW.complexLorentzAction Λ (BHW.diffCoordFun n 1 z) := by
        simpa [w] using diffCoordFun_complexLorentzAction Λ z
      have hact :
          BHW.diffCoordFun n 1 w k = complexLorentzActionVec Λ ξ := by
        ext μ
        simpa [ξ, BHW.complexLorentzAction, complexLorentzActionVec] using
          (congrArg (fun t : Fin n → Fin (1 + 1) → ℂ => t k μ) hdiff_eq)
      have hplus_eq :
          lightConePlus (BHW.diffCoordFun n 1 w k) =
            Complex.exp ((b : ℂ) * Complex.I) * lightConePlus ξ := by
        rw [hact]
        simpa [Λ] using lightConePlus_rapidity ((b : ℂ) * Complex.I) ξ
      have hminus_eq :
          lightConeMinus (BHW.diffCoordFun n 1 w k) =
            Complex.exp (-((b : ℂ) * Complex.I)) * lightConeMinus ξ := by
        rw [hact]
        simpa [Λ] using lightConeMinus_rapidity ((b : ℂ) * Complex.I) ξ
      have hplus_im :
          0 < (lightConePlus (BHW.diffCoordFun n 1 w k)).im := by
        rw [hplus_eq]
        simpa [ξ] using (hb k).1
      have hminus_im :
          0 < (lightConeMinus (BHW.diffCoordFun n 1 w k)).im := by
        rw [hminus_eq]
        simpa [ξ] using (hb k).2
      have hpm :
          0 < ((BHW.diffCoordFun n 1 w k) 0).im + ((BHW.diffCoordFun n 1 w k) 1).im ∧
          0 < ((BHW.diffCoordFun n 1 w k) 0).im - ((BHW.diffCoordFun n 1 w k) 1).im := by
        constructor
        · simpa [lightConePlus, Complex.add_im] using hplus_im
        · simpa [lightConeMinus, Complex.sub_im] using hminus_im
      have hcone :
          BHW.InOpenForwardCone 1 (fun μ => (BHW.diffCoordFun n 1 w k μ).im) :=
        (bhw_inOpenForwardCone_one_iff_pm
          (fun μ => (BHW.diffCoordFun n 1 w k μ).im)).2 hpm
      by_cases hk : k.val = 0
      · simpa [w, BHW.ForwardTube, BHW.diffCoordFun, hk] using hcone
      · simpa [w, BHW.ForwardTube, BHW.diffCoordFun, hk] using hcone
    refine Set.mem_iUnion.mpr ⟨Λ⁻¹, w, hwFT, ?_⟩
    simp [w, BHW.complexLorentzAction_inv]

private theorem realExtendedTube_d1_consecutiveDiff_mul_sin_sign
    {n : ℕ} {x : NPointDomain 1 n}
    (hx : BHW.realEmbed x ∈ BHW.ExtendedTube 1 n) :
    ∃ b : ℝ, ∀ k : Fin n,
      (BHW.consecutiveDiff x k 0 + BHW.consecutiveDiff x k 1) * Real.sin b < 0 ∧
      0 < (BHW.consecutiveDiff x k 0 - BHW.consecutiveDiff x k 1) * Real.sin b := by
  rcases Set.mem_iUnion.mp hx with ⟨Λ, w, hwFT, hEq⟩
  rcases BHW.d1_exists_rapidityElement_principal_im_repr Λ with ⟨a, b, _, hrepr⟩
  refine ⟨b, ?_⟩
  intro k
  let ξ : Fin (1 + 1) → ℂ := BHW.diffCoordFun n 1 w k
  have hξ_cone : BHW.InOpenForwardCone 1 (fun μ => (ξ μ).im) := by
    by_cases hk : k.val = 0
    · simpa [ξ, BHW.ForwardTube, BHW.diffCoordFun, hk] using hwFT k
    · simpa [ξ, BHW.ForwardTube, BHW.diffCoordFun, hk] using hwFT k
  rcases (bhw_inOpenForwardCone_one_iff_pm (fun μ => (ξ μ).im)).1 hξ_cone with
    ⟨hξ_plus, hξ_minus⟩
  have hdiff_eq :
      BHW.diffCoordFun n 1 (BHW.realEmbed x) =
        BHW.complexLorentzAction (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I))
          (BHW.diffCoordFun n 1 w) := by
    calc
      BHW.diffCoordFun n 1 (BHW.realEmbed x)
          = BHW.diffCoordFun n 1 (BHW.complexLorentzAction Λ w) := by
              rw [hEq]
      _ = BHW.complexLorentzAction Λ (BHW.diffCoordFun n 1 w) :=
            diffCoordFun_complexLorentzAction Λ w
      _ = BHW.complexLorentzAction
            (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I))
            (BHW.diffCoordFun n 1 w) := by rw [hrepr]
  have hact0 :
      complexLorentzActionVec
          (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ 0 =
        BHW.diffCoordFun n 1 (BHW.realEmbed x) k 0 := by
    simpa [ξ, BHW.complexLorentzAction, complexLorentzActionVec] using
      (congrArg (fun z : Fin n → Fin (1 + 1) → ℂ => z k 0) hdiff_eq).symm
  have hact1 :
      complexLorentzActionVec
          (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ 1 =
        BHW.diffCoordFun n 1 (BHW.realEmbed x) k 1 := by
    simpa [ξ, BHW.complexLorentzAction, complexLorentzActionVec] using
      (congrArg (fun z : Fin n → Fin (1 + 1) → ℂ => z k 1) hdiff_eq).symm
  have hreal0 :
      (complexLorentzActionVec
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ 0).im = 0 := by
    rw [hact0]
    exact diffCoordFun_realEmbed_im_zero x k 0
  have hreal1 :
      (complexLorentzActionVec
        (BHW.rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I)) ξ 1).im = 0 := by
    rw [hact1]
    exact diffCoordFun_realEmbed_im_zero x k 1
  have hplus_mul0 :
      (((BHW.diffCoordFun n 1 (BHW.realEmbed x) k 0) +
          (BHW.diffCoordFun n 1 (BHW.realEmbed x) k 1)).re) * Real.sin b =
        -Real.exp a * ((ξ 0).im + (ξ 1).im) := by
    have := lightConePlus_real_mul_sin_of_real_output ξ a b hreal0 hreal1
    simpa [lightConePlus, hact0, hact1] using this
  have hminus_mul0 :
      (((BHW.diffCoordFun n 1 (BHW.realEmbed x) k 0) -
          (BHW.diffCoordFun n 1 (BHW.realEmbed x) k 1)).re) * Real.sin b =
        Real.exp (-a) * ((ξ 0).im - (ξ 1).im) := by
    have := lightConeMinus_real_mul_sin_of_real_output ξ a b hreal0 hreal1
    simpa [lightConeMinus, hact0, hact1] using this
  have hplus_mul :
      (BHW.consecutiveDiff x k 0 + BHW.consecutiveDiff x k 1) * Real.sin b =
        -Real.exp a * ((ξ 0).im + (ξ 1).im) := by
    simpa [Complex.add_re,
      diffCoordFun_realEmbed_re_eq_consecutiveDiff x k 0,
      diffCoordFun_realEmbed_re_eq_consecutiveDiff x k 1] using hplus_mul0
  have hminus_mul :
      (BHW.consecutiveDiff x k 0 - BHW.consecutiveDiff x k 1) * Real.sin b =
        Real.exp (-a) * ((ξ 0).im - (ξ 1).im) := by
    simpa [Complex.sub_re,
      diffCoordFun_realEmbed_re_eq_consecutiveDiff x k 0,
      diffCoordFun_realEmbed_re_eq_consecutiveDiff x k 1] using hminus_mul0
  constructor
  · nlinarith [hplus_mul, hξ_plus, Real.exp_pos a]
  · nlinarith [hminus_mul, hξ_minus, Real.exp_pos (-a)]

private theorem realExtendedTube_d1_point_mul_sin_sign_of_consecutive
    {n : ℕ} {x : NPointDomain 1 n} {b : ℝ}
    (hb : ∀ k : Fin n,
      (BHW.consecutiveDiff x k 0 + BHW.consecutiveDiff x k 1) * Real.sin b < 0 ∧
      0 < (BHW.consecutiveDiff x k 0 - BHW.consecutiveDiff x k 1) * Real.sin b) :
    ∀ k : Fin n,
      (x k 0 + x k 1) * Real.sin b < 0 ∧
      0 < (x k 0 - x k 1) * Real.sin b := by
  intro k
  have hpoint :
      ∀ m (hm : m < n),
        (x ⟨m, hm⟩ 0 + x ⟨m, hm⟩ 1) * Real.sin b < 0 ∧
        0 < (x ⟨m, hm⟩ 0 - x ⟨m, hm⟩ 1) * Real.sin b := by
    intro m hm
    induction m with
    | zero =>
        let k0 : Fin n := ⟨0, hm⟩
        simpa [k0, BHW.consecutiveDiff] using hb k0
    | succ m ih =>
        have hm' : m < n := by omega
        let i : Fin n := ⟨m, hm'⟩
        let j : Fin n := ⟨m + 1, hm⟩
        have hprev := ih hm'
        have hdiff := hb j
        have hplus_eq :
            (x j 0 + x j 1) * Real.sin b =
              (x i 0 + x i 1) * Real.sin b +
                (BHW.consecutiveDiff x j 0 + BHW.consecutiveDiff x j 1) * Real.sin b := by
          simp [BHW.consecutiveDiff, i, j]
          ring
        have hminus_eq :
            (x j 0 - x j 1) * Real.sin b =
              (x i 0 - x i 1) * Real.sin b +
                (BHW.consecutiveDiff x j 0 - BHW.consecutiveDiff x j 1) * Real.sin b := by
          simp [BHW.consecutiveDiff, i, j]
          ring
        constructor
        · nlinarith [hprev.1, hdiff.1, hplus_eq]
        · nlinarith [hprev.2, hdiff.2, hminus_eq]
  exact hpoint k.val k.isLt

private theorem positive_mul_of_two_negative_products
    {u s t : ℝ} (hs : u * s < 0) (ht : u * t < 0) :
    0 < s * t := by
  by_cases hu : 0 < u
  · have hs' : s < 0 := by nlinarith
    have ht' : t < 0 := by nlinarith
    nlinarith
  · have hu' : u < 0 := by
      have hne : u ≠ 0 := by
        intro hu0
        simp [hu0] at hs
      exact lt_of_le_of_ne (le_of_not_gt hu) hne
    have hs' : 0 < s := by nlinarith
    have ht' : 0 < t := by nlinarith
    nlinarith

private theorem negative_mul_of_negative_and_positive_products
    {u s t : ℝ} (hs : u * s < 0) (ht : 0 < u * t) :
    s * t < 0 := by
  by_cases hu : 0 < u
  · have hs' : s < 0 := by nlinarith
    have ht' : 0 < t := by nlinarith
    nlinarith
  · have hu' : u < 0 := by
      have hne : u ≠ 0 := by
        intro hu0
        simp [hu0] at hs
      exact lt_of_le_of_ne (le_of_not_gt hu) hne
    have hs' : 0 < s := by nlinarith
    have ht' : t < 0 := by nlinarith
    nlinarith

private theorem consecutiveDiff_rev_one_eq_neg_last
    {n : ℕ} (hn : 2 ≤ n) (x : NPointDomain 1 n) (μ : Fin (1 + 1)) :
    BHW.consecutiveDiff (fun k => x (Fin.rev k)) ⟨1, by omega⟩ μ =
      -BHW.consecutiveDiff x ⟨n - 1, by omega⟩ μ := by
  haveI : NeZero n := ⟨by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  have hrev0 : Fin.rev (0 : Fin n) = last := by
    ext
    simp [last, Fin.rev]
  have hrev1 : Fin.rev one = ⟨n - 2, by omega⟩ := by
    ext
    simp [one, Fin.rev]
  have hn1 : n - 1 ≠ 0 := by omega
  have hidx : (⟨n - 1 - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := by
    apply Fin.ext
    show n - 1 - 1 = n - 2
    omega
  calc
    BHW.consecutiveDiff (fun k => x (Fin.rev k)) one μ
        = x ⟨n - 2, by omega⟩ μ - x last μ := by
            simp [BHW.consecutiveDiff, one, hrev0, hrev1, last]
    _ = -BHW.consecutiveDiff x last μ := by
          calc
            x ⟨n - 2, by omega⟩ μ - x last μ = -(x last μ - x ⟨n - 2, by omega⟩ μ) := by ring
            _ = -BHW.consecutiveDiff x last μ := by
                  simp [BHW.consecutiveDiff, last, hn1, hidx]

private theorem hermitianReverse_realEmbed {d n : ℕ}
    (x : NPointDomain d n) :
    hermitianReverse (BHW.realEmbed x) =
      BHW.realEmbed (fun k => x (Fin.rev k)) := by
  ext k μ
  simp [hermitianReverse, BHW.realEmbed]

private theorem hermitianTwistCLG_realEmbed {d n : ℕ} [NeZero d]
    (x : NPointDomain d n) :
    BHW.complexLorentzAction (hermitianTwistCLG d) (BHW.realEmbed x) =
      BHW.realEmbed (hermitianTwistRealN x) := by
  ext k μ
  rw [complexLorentzAction_hermitianTwistCLG]
  by_cases hμ0 : μ = 0
  · subst hμ0
    simp [BHW.realEmbed, hermitianTwistRealN, hermitianTwistReal, spatialFlipOne, oneFin,
      timeReflection]
  · by_cases hμ1 : μ = oneFin d
    · subst hμ1
      simp [BHW.realEmbed, hermitianTwistRealN, hermitianTwistReal, spatialFlipOne, oneFin,
        timeReflection]
    · have hcast :
          ((if μ = oneFin d then -x k μ else x k μ : ℝ) : ℂ) =
            (if μ = oneFin d then -((x k μ : ℂ)) else (x k μ : ℂ)) := by
          split_ifs; simp
      simpa [BHW.realEmbed, hermitianTwistRealN, hermitianTwistReal, spatialFlipOne, oneFin,
        timeReflection, hμ0] using hcast.symm

private theorem hermitianTwistCLG_hermitianReverse_wickRotate {d n : ℕ} [NeZero d]
    (x : NPointDomain d n) :
    BHW.complexLorentzAction (hermitianTwistCLG d)
        (hermitianReverse (fun k => wickRotatePoint (x k))) =
      (fun k => wickRotatePoint (spatialFlipOne (x (Fin.rev k)))) := by
  ext k μ
  rw [hermitianReverse_wickRotate, complexLorentzAction_hermitianTwistCLG]
  by_cases hμ0 : μ = 0
  · subst hμ0
    simp [wickRotatePoint, timeReflection, spatialFlipOne, oneFin]
  · by_cases hμ1 : μ = oneFin d
    · subst hμ1
      simp [wickRotatePoint, timeReflection, spatialFlipOne, oneFin]
    · have hcast :
          ((if μ = oneFin d then -((x (Fin.rev k)) μ) else (x (Fin.rev k)) μ : ℝ) : ℂ) =
            (if μ = oneFin d then -((x (Fin.rev k)) μ : ℂ) else ((x (Fin.rev k)) μ : ℂ)) := by
          split_ifs; simp
      simpa [wickRotatePoint, timeReflection, spatialFlipOne, oneFin, hμ0] using hcast.symm

/-- If `F` is holomorphic on PET, then its conjugate-reverse partner
    `z ↦ conj(F(conj-rev z))` is holomorphic on the reflected overlap domain. -/
private theorem differentiableOn_hermitianReverse_partner {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (PermutedExtendedTube d n)) :
    DifferentiableOn ℂ (fun z => starRingEnd ℂ (F (hermitianReverse z)))
      {z | hermitianReverse z ∈ PermutedExtendedTube d n} := by
  let ρ : (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ (Fin (d + 1) → ℂ) Fin.revPerm).toContinuousLinearEquiv
  have hρ_apply :
      ∀ z : Fin n → Fin (d + 1) → ℂ, ρ z = fun k => z (Fin.rev k) := by
    intro z
    ext k μ
    simp [ρ, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Fin.revPerm]
  have hFρ :
      DifferentiableOn ℂ (F ∘ ρ) (ρ ⁻¹' PermutedExtendedTube d n) := by
    refine hF.comp (fun z _ => ρ.differentiableAt.differentiableWithinAt) ?_
    intro z hz
    exact hz
  have hPET_open : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  have hρ_open : IsOpen (ρ ⁻¹' PermutedExtendedTube d n) :=
    hPET_open.preimage ρ.continuous
  intro z hz
  have hz' : star z ∈ ρ ⁻¹' PermutedExtendedTube d n := by
    simpa [Set.preimage, hermitianReverse, hρ_apply] using hz
  have hdiffAt : DifferentiableAt ℂ (F ∘ ρ) (star z) :=
    (hFρ (star z) hz').differentiableAt (hρ_open.mem_nhds hz')
  have hstarstar : DifferentiableAt ℂ (star ∘ (F ∘ ρ) ∘ star) z := by
    simpa [Function.comp] using hdiffAt.star_star
  simpa [Function.comp, hermitianReverse, hρ_apply] using hstarstar.differentiableWithinAt

/-- Euclidean Wick points lie in the Hermiticity overlap a.e. -/
private theorem ae_euclidean_points_in_hermitianReverseOverlap {d n : ℕ} [NeZero d] :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ hermitianReverseOverlap (d := d) (n := n) := by
  filter_upwards [ae_euclidean_points_in_permutedTube_overlap (d := d) (n := n)] with x hx
  refine ⟨hx.1, ?_⟩
  simpa [hermitianReverse_wickRotate] using hx.2

private theorem measure_timeEq_zero {d n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MeasureTheory.volume {x : NPointDomain d n | x i 0 = x j 0} = 0 := by
  let L : NPointDomain d n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x i 0 - x j 0
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro a x
        simp
        ring }
  have hset :
      {x : NPointDomain d n | x i 0 = x j 0} = (LinearMap.ker L : Set (NPointDomain d n)) := by
    ext x
    simp [L, LinearMap.mem_ker, sub_eq_zero]
  have hker_ne_top : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
    have hval : L (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0) = 0 := by
      simpa using congrArg
        (fun f => f (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0)) hzero
    have hji : j ≠ i := by
      intro h
      exact hij h.symm
    have : (1 : ℝ) = 0 := by
      simp [L, hji] at hval
    norm_num at this
  rw [hset]
  exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume (LinearMap.ker L) hker_ne_top

private theorem ae_pairwise_distinct_timeCoords {d n : ℕ} :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0 := by
  have hall : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ p : {p : Fin n × Fin n // p.1 ≠ p.2}, x p.1.1 0 ≠ x p.1.2 0 := by
    simpa using
      ((Set.toFinite (Set.univ : Set {p : Fin n × Fin n // p.1 ≠ p.2})).eventually_all
        (l := MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)))
        (p := fun p => fun x : NPointDomain d n => x p.1.1 0 ≠ x p.1.2 0)).2
        (fun p _ => by
          let s : Set (NPointDomain d n) := {x | x p.1.1 0 = x p.1.2 0}
          have hs0 : MeasureTheory.volume s = 0 := by
            simpa [s] using measure_timeEq_zero (d := d) p.1.1 p.1.2 p.2
          have hsae :
              sᶜ ∈ MeasureTheory.ae
                (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
            MeasureTheory.compl_mem_ae_iff.mpr hs0
          simpa [s, Set.compl_setOf] using hsae)
  filter_upwards [hall] with x hx i j hij
  exact hx ⟨⟨i, j⟩, hij⟩

private theorem euclidean_distinct_in_BHW_permutedForwardTube {d n : ℕ} [NeZero d]
    (xs : NPointDomain d n)
    (hdistinct : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0)
    (hpos : ∀ i : Fin n, xs i 0 > 0) :
    ∃ π : Equiv.Perm (Fin n),
      (fun k => wickRotatePoint (xs k)) ∈ BHW.PermutedForwardTube d n π := by
  let π := Tuple.sort (fun k => xs k 0)
  have hmono := Tuple.monotone_sort (fun k => xs k 0)
  have hinj : Function.Injective (fun k => xs k 0) := by
    intro i j h
    by_contra hij
    exact hdistinct i j hij h
  have hstrict : StrictMono ((fun k => xs k 0) ∘ π) :=
    hmono.strictMono_of_injective (hinj.comp π.injective)
  have hord : ∀ k j : Fin n, k < j → xs (π k) 0 < xs (π j) 0 :=
    fun k j hkj => hstrict hkj
  have hpos' : ∀ k : Fin n, xs (π k) 0 > 0 :=
    fun k => hpos (π k)
  have hfwd : (fun k => wickRotatePoint (xs (π k))) ∈ ForwardTube d n :=
    euclidean_ordered_in_forwardTube (fun k => xs (π k)) hord hpos'
  refine ⟨π, ?_⟩
  simpa [BHW_permutedForwardTube_eq (d := d) (n := n) π] using hfwd

private theorem euclidean_distinct_twisted_reverse_in_BHW_permutedForwardTube {d n : ℕ}
    [NeZero d] (xs : NPointDomain d n)
    (hdistinct : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0)
    (hpos : ∀ i : Fin n, xs i 0 > 0) :
    ∃ σ : Equiv.Perm (Fin n),
      BHW.complexLorentzAction (hermitianTwistCLG d)
        (hermitianReverse (fun k => wickRotatePoint (xs k))) ∈
          BHW.PermutedForwardTube d n σ := by
  let ys : NPointDomain d n := fun k => spatialFlipOne (xs (Fin.rev k))
  have hdistinct_y : ∀ i j : Fin n, i ≠ j → ys i 0 ≠ ys j 0 := by
    intro i j hij
    have hij_rev : Fin.rev i ≠ Fin.rev j := by
      simpa using hij
    simpa [ys, spatialFlipOne, oneFin, zero_ne_oneFin] using
      hdistinct (Fin.rev i) (Fin.rev j) hij_rev
  have hpos_y : ∀ i : Fin n, ys i 0 > 0 := by
    intro i
    simpa [ys, spatialFlipOne, oneFin, zero_ne_oneFin] using hpos (Fin.rev i)
  obtain ⟨σ, hσ⟩ :=
    euclidean_distinct_in_BHW_permutedForwardTube (d := d) ys hdistinct_y hpos_y
  refine ⟨σ, ?_⟩
  simpa [ys, hermitianTwistCLG_hermitianReverse_wickRotate] using hσ

/-- The real ET-overlap relevant for Hermiticity: both `x` and its reversed
    configuration lie in the ordinary extended tube. -/
private def hermitianRealOverlap {d n : ℕ} [NeZero d] :
    Set (NPointDomain d n) :=
  { x | BHW.realEmbed x ∈ BHW.ExtendedTube d n ∧
      BHW.realEmbed (fun k => x (Fin.rev k)) ∈ BHW.ExtendedTube d n }

private theorem continuous_realEmbed {d n : ℕ} :
    Continuous (BHW.realEmbed : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ)) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply k))

private theorem continuous_realEmbed_rev {d n : ℕ} :
    Continuous
      (fun x : NPointDomain d n => BHW.realEmbed (fun k => x (Fin.rev k))) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply (Fin.rev k)))

private theorem isOpen_hermitianRealOverlap {d n : ℕ} [NeZero d] :
    IsOpen (hermitianRealOverlap (d := d) (n := n)) := by
  have h1 : IsOpen {x : NPointDomain d n | BHW.realEmbed x ∈ BHW.ExtendedTube d n} :=
    BHW.isOpen_extendedTube.preimage (continuous_realEmbed (d := d) (n := n))
  have h2 : IsOpen
      {x : NPointDomain d n | BHW.realEmbed (fun k => x (Fin.rev k)) ∈ BHW.ExtendedTube d n} :=
    BHW.isOpen_extendedTube.preimage (continuous_realEmbed_rev (d := d) (n := n))
  simpa [hermitianRealOverlap] using h1.inter h2

private theorem mem_hermitianRealOverlap_rev {d n : ℕ} [NeZero d]
    {x : NPointDomain d n} (hx : x ∈ hermitianRealOverlap (d := d) (n := n)) :
    (fun k => x (Fin.rev k)) ∈ hermitianRealOverlap (d := d) (n := n) := by
  refine ⟨hx.2, ?_⟩
  simpa [hermitianRealOverlap, BHW.realEmbed, Fin.rev_rev] using hx.1

private theorem hermitianRealOverlap_eq_empty_d1_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    hermitianRealOverlap (d := 1) (n := n) = ∅ := by
  haveI : NeZero n := ⟨by omega⟩
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  let last : Fin n := ⟨n - 1, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  have hrev0 : Fin.rev (0 : Fin n) = last := by
    ext
    simp [last, Fin.rev]
  rcases realExtendedTube_d1_consecutiveDiff_mul_sin_sign hx.1 with ⟨b, hbDiff⟩
  rcases realExtendedTube_d1_consecutiveDiff_mul_sin_sign hx.2 with ⟨c, hcDiff⟩
  have hbPoint := realExtendedTube_d1_point_mul_sin_sign_of_consecutive (x := x) hbDiff
  have hcPoint :=
    realExtendedTube_d1_point_mul_sin_sign_of_consecutive (x := fun k => x (Fin.rev k)) hcDiff
  have hlast_b :
      (x last 0 + x last 1) * Real.sin b < 0 ∧
      0 < (x last 0 - x last 1) * Real.sin b := by
    exact hbPoint last
  have hlast_c :
      (x last 0 + x last 1) * Real.sin c < 0 ∧
      0 < (x last 0 - x last 1) * Real.sin c := by
    simpa [last, hrev0] using hcPoint (0 : Fin n)
  have hsame : 0 < Real.sin b * Real.sin c := by
    exact positive_mul_of_two_negative_products hlast_b.1 hlast_c.1
  have hlastDiff_c :
      0 <
        (BHW.consecutiveDiff x last 0 + BHW.consecutiveDiff x last 1) * Real.sin c := by
    have hrev_one := (hcDiff one).1
    have hcd0 := consecutiveDiff_rev_one_eq_neg_last hn x 0
    have hcd1 := consecutiveDiff_rev_one_eq_neg_last hn x 1
    have hneg :
        ((-BHW.consecutiveDiff x last 0) + (-BHW.consecutiveDiff x last 1)) * Real.sin c < 0 := by
      simpa [one, hcd0, hcd1] using hrev_one
    nlinarith
  have hopposite : Real.sin b * Real.sin c < 0 := by
    exact negative_mul_of_negative_and_positive_products (hbDiff last).1 hlastDiff_c
  nlinarith

private theorem realEmbed_hermitianTwistRev_mem_extendedTube_iff_d1
    {n : ℕ} (x : NPointDomain 1 n) :
    BHW.realEmbed (hermitianTwistRealN (fun k => x (Fin.rev k))) ∈ BHW.ExtendedTube 1 n ↔
      BHW.realEmbed (fun k => x (Fin.rev k)) ∈ BHW.ExtendedTube 1 n := by
  constructor
  · intro hx
    have hx' :
        BHW.complexLorentzAction (hermitianTwistCLG 1)
          (BHW.realEmbed (hermitianTwistRealN (fun k => x (Fin.rev k)))) ∈
            BHW.ExtendedTube 1 n :=
      BHW.complexLorentzAction_mem_extendedTube n (hermitianTwistCLG 1) hx
    have htwice :
        hermitianTwistRealN (d := 1) (n := n)
            (hermitianTwistRealN (fun k => x (Fin.rev k))) =
          fun k => x (Fin.rev k) := by
      ext k μ
      fin_cases μ
      · simp [hermitianTwistRealN, hermitianTwistReal, spatialFlipOne, oneFin, timeReflection]
      · simp [hermitianTwistRealN, hermitianTwistReal, spatialFlipOne, oneFin, timeReflection]
    simpa [hermitianTwistCLG_realEmbed, htwice] using hx'
  · intro hx
    have hx' :
        BHW.complexLorentzAction (hermitianTwistCLG 1)
          (BHW.realEmbed (fun k => x (Fin.rev k))) ∈
            BHW.ExtendedTube 1 n :=
      BHW.complexLorentzAction_mem_extendedTube n (hermitianTwistCLG 1) hx
    simpa [hermitianTwistCLG_realEmbed] using hx'

private theorem hermitianTwistRevRealOverlap_eq_empty_d1_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    {x : NPointDomain 1 n |
      BHW.realEmbed x ∈ BHW.ExtendedTube 1 n ∧
        BHW.realEmbed (hermitianTwistRealN (fun k => x (Fin.rev k))) ∈
          BHW.ExtendedTube 1 n} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  have hx' : x ∈ hermitianRealOverlap (d := 1) (n := n) := by
    refine ⟨hx.1, ?_⟩
    exact (realEmbed_hermitianTwistRev_mem_extendedTube_iff_d1 x).1 hx.2
  have hempty := hermitianRealOverlap_eq_empty_d1_of_two_le (n := n) hn
  rw [hempty] at hx'
  exact hx'

private theorem realEmbed_mem_hermitianReverseOverlap_of_mem_hermitianRealOverlap
    {d n : ℕ} [NeZero d] {x : NPointDomain d n}
    (hx : x ∈ hermitianRealOverlap (d := d) (n := n)) :
    BHW.realEmbed x ∈ hermitianReverseOverlap (d := d) (n := n) := by
  refine ⟨?_, ?_⟩
  · simpa [hermitianReverseOverlap, BHW_permutedExtendedTube_eq (d := d) (n := n)] using
      BHW.extendedTube_subset_permutedExtendedTube hx.1
  · simpa [hermitianReverse_realEmbed, hermitianReverseOverlap,
      BHW_permutedExtendedTube_eq (d := d) (n := n)] using
      BHW.extendedTube_subset_permutedExtendedTube hx.2

private theorem imDiff_realEmbed_eq_zero {d n : ℕ}
    (x : NPointDomain d n) (k : Fin n) :
    BHW.imDiff (BHW.realEmbed x) k = 0 := by
  ext μ
  by_cases hk : (k : ℕ) = 0
  · simp [BHW.imDiff, BHW.realEmbed, hk]
  · simp [BHW.imDiff, BHW.realEmbed, hk]

private theorem permutedForwardTube_subset_permutedExtendedTube_BHW
    {d n : ℕ} (π : Equiv.Perm (Fin n)) :
    BHW.PermutedForwardTube d n π ⊆ BHW.PermutedExtendedTube d n := by
  intro z hz
  refine Set.mem_iUnion.mpr ⟨π, ?_⟩
  exact ⟨1, z, hz, (BHW.complexLorentzAction_one z).symm⟩

private theorem smul_add_realEmbed_mem_permutedForwardTube_BHW
    {d n : ℕ} {π : Equiv.Perm (Fin n)}
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ BHW.PermutedForwardTube d n π)
    (x : NPointDomain d n) {t : ℝ} (ht : 0 < t) :
    t • z + (1 - t) • BHW.realEmbed x ∈ BHW.PermutedForwardTube d n π := by
  let zπ : Fin n → Fin (d + 1) → ℂ := fun k => z (π k)
  let xπ : NPointDomain d n := fun k => x (π k)
  have hzπ : zπ ∈ BHW.ForwardTube d n := by
    simpa [zπ, BHW.PermutedForwardTube] using hz
  change (fun k => (t • z + (1 - t) • BHW.realEmbed x) (π k)) ∈ BHW.ForwardTube d n
  have hcomb :
      (fun k => (t • z + (1 - t) • BHW.realEmbed x) (π k))
        = t • zπ + (1 - t) • BHW.realEmbed xπ := by
    ext k μ
    simp [zπ, xπ, BHW.realEmbed]
  rw [hcomb]
  intro k
  change BHW.InOpenForwardCone d (BHW.imDiff (t • zπ + (1 - t) • BHW.realEmbed xπ) k)
  have hzero : BHW.imDiff (BHW.realEmbed xπ) k = 0 :=
    imDiff_realEmbed_eq_zero xπ k
  rw [BHW.imDiff_linear zπ (BHW.realEmbed xπ) t (1 - t) k, hzero, smul_zero, add_zero]
  exact BHW.inOpenForwardCone_smul_pos (hη := hzπ k) ht

private theorem hermitianReverse_smul_add_realEmbed {d n : ℕ}
    (x : NPointDomain d n) (z : Fin n → Fin (d + 1) → ℂ) (t : ℝ) :
    hermitianReverse (t • z + (1 - t) • BHW.realEmbed x) =
      t • hermitianReverse z + (1 - t) • BHW.realEmbed (fun k => x (Fin.rev k)) := by
  ext k μ
  simp [hermitianReverse, BHW.realEmbed]

private theorem hermitianTwistCLG_hermitianReverse_smul_add_realEmbed {d n : ℕ} [NeZero d]
    (x : NPointDomain d n) (z : Fin n → Fin (d + 1) → ℂ) (t : ℝ) :
    BHW.complexLorentzAction (hermitianTwistCLG d)
        (hermitianReverse (t • z + (1 - t) • BHW.realEmbed x)) =
      t • BHW.complexLorentzAction (hermitianTwistCLG d) (hermitianReverse z) +
        (1 - t) • BHW.realEmbed (hermitianTwistRealN (fun k => x (Fin.rev k))) := by
  rw [hermitianReverse_smul_add_realEmbed (d := d) (n := n) x z t]
  ext k μ
  by_cases hμ0 : μ = 0
  · subst hμ0
    simp [complexLorentzAction_hermitianTwistCLG, BHW.realEmbed, hermitianTwistRealN,
      hermitianTwistReal, spatialFlipOne, oneFin, timeReflection]
    ring
  · by_cases hμ1 : μ = oneFin d
    · subst hμ1
      simp [complexLorentzAction_hermitianTwistCLG, BHW.realEmbed, hermitianTwistRealN,
        hermitianTwistReal, spatialFlipOne, oneFin, timeReflection]
      ring
    · have hμ1' : μ ≠ ⟨1, Nat.succ_lt_succ (NeZero.pos d)⟩ := by
        simpa [oneFin] using hμ1
      simp [complexLorentzAction_hermitianTwistCLG, BHW.realEmbed, hermitianTwistRealN,
        hermitianTwistReal, spatialFlipOne, oneFin, timeReflection, hμ0, hμ1']

private theorem joinedIn_hermitianReverseOverlap_of_dual_permutedForwardTube
    {d n : ℕ} [NeZero d] {π σ : Equiv.Perm (Fin n)}
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzπ : z ∈ BHW.PermutedForwardTube d n π)
    (hzσ : hermitianReverse z ∈ BHW.PermutedForwardTube d n σ)
    {x : NPointDomain d n}
    (hx : x ∈ hermitianRealOverlap (d := d) (n := n)) :
    JoinedIn (hermitianReverseOverlap (d := d) (n := n)) (BHW.realEmbed x) z := by
  let γ : ℝ → (Fin n → Fin (d + 1) → ℂ) :=
    fun t => t • z + (1 - t) • BHW.realEmbed x
  refine JoinedIn.ofLine (f := γ) ?_ ?_ ?_ ?_
  · have htz : Continuous fun t : ℝ => t • z :=
      continuous_id.smul continuous_const
    have htx : Continuous fun t : ℝ => (1 - t) • BHW.realEmbed x := by
      exact (continuous_const.sub continuous_id).smul continuous_const
    exact (htz.add htx).continuousOn
  · simp [γ]
  · simp [γ]
  · intro w hw
    rcases hw with ⟨t, htI, rfl⟩
    by_cases ht0 : t = 0
    · subst ht0
      simpa [γ] using realEmbed_mem_hermitianReverseOverlap_of_mem_hermitianRealOverlap hx
    · have htpos : 0 < t := by
        exact lt_of_le_of_ne htI.1 (Ne.symm ht0)
      refine ⟨?_, ?_⟩
      · have hγπ :
          γ t ∈ BHW.PermutedForwardTube d n π :=
            smul_add_realEmbed_mem_permutedForwardTube_BHW hzπ x htpos
        have hγPET : γ t ∈ BHW.PermutedExtendedTube d n :=
          permutedForwardTube_subset_permutedExtendedTube_BHW π hγπ
        simpa [γ, BHW_permutedExtendedTube_eq (d := d) (n := n)] using hγPET
      · have hγσ :
          hermitianReverse (γ t) ∈ BHW.PermutedForwardTube d n σ := by
            rw [hermitianReverse_smul_add_realEmbed (d := d) (n := n) x z t]
            exact smul_add_realEmbed_mem_permutedForwardTube_BHW hzσ
              (fun k => x (Fin.rev k)) htpos
        have hγPET : hermitianReverse (γ t) ∈ BHW.PermutedExtendedTube d n :=
          permutedForwardTube_subset_permutedExtendedTube_BHW σ hγσ
        simpa [γ, BHW_permutedExtendedTube_eq (d := d) (n := n)] using hγPET

private theorem eq_zero_on_hermitianReverseOverlap_of_dual_permutedForwardTube
    {d n : ℕ} [NeZero d]
    {H : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hH_holo : DifferentiableOn ℂ H (hermitianReverseOverlap (d := d) (n := n)))
    (hH_real :
      ∀ x ∈ hermitianRealOverlap (d := d) (n := n), H (BHW.realEmbed x) = 0)
    {π σ : Equiv.Perm (Fin n)} {z : Fin n → Fin (d + 1) → ℂ}
    (hzπ : z ∈ BHW.PermutedForwardTube d n π)
    (hzσ : hermitianReverse z ∈ BHW.PermutedForwardTube d n σ)
    {x : NPointDomain d n}
    (hx : x ∈ hermitianRealOverlap (d := d) (n := n)) :
    H z = 0 := by
  let D : Set (Fin n → Fin (d + 1) → ℂ) := hermitianReverseOverlap (d := d) (n := n)
  let C : Set (Fin n → Fin (d + 1) → ℂ) := connectedComponentIn D z
  let V : Set (NPointDomain d n) := hermitianRealOverlap (d := d) (n := n)
  have hzD : z ∈ D := by
    refine ⟨?_, ?_⟩
    · have hzPET : z ∈ BHW.PermutedExtendedTube d n :=
        permutedForwardTube_subset_permutedExtendedTube_BHW π hzπ
      simpa [D, BHW_permutedExtendedTube_eq (d := d) (n := n)] using hzPET
    · have hzPET : hermitianReverse z ∈ BHW.PermutedExtendedTube d n :=
        permutedForwardTube_subset_permutedExtendedTube_BHW σ hzσ
      simpa [D, BHW_permutedExtendedTube_eq (d := d) (n := n)] using hzPET
  have hC_open : IsOpen C :=
    (isOpen_hermitianReverseOverlap (d := d) (n := n)).connectedComponentIn
  have hC_conn : IsConnected C :=
    isConnected_connectedComponentIn_iff.mpr hzD
  have hH_holo_C : DifferentiableOn ℂ H C := by
    refine hH_holo.mono ?_
    exact connectedComponentIn_subset D z
  have hjoin : JoinedIn D (BHW.realEmbed x) z :=
    joinedIn_hermitianReverseOverlap_of_dual_permutedForwardTube hzπ hzσ hx
  have hrange_sub_C : Set.range hjoin.somePath ⊆ C := by
    apply (isPreconnected_range hjoin.somePath.continuous).subset_connectedComponentIn
    · refine ⟨1, ?_⟩
      exact hjoin.somePath.target
    · intro y hy
      rcases hy with ⟨t, rfl⟩
      exact hjoin.somePath_mem t
  have hxC : BHW.realEmbed x ∈ C := by
    apply hrange_sub_C
    refine ⟨0, ?_⟩
    exact hjoin.somePath.source
  let V' : Set (NPointDomain d n) := {y | y ∈ V ∧ BHW.realEmbed y ∈ C}
  have hV'_open : IsOpen V' := by
    refine (isOpen_hermitianRealOverlap (d := d) (n := n)).inter ?_
    exact hC_open.preimage (continuous_realEmbed (d := d) (n := n))
  have hV'_ne : V'.Nonempty := ⟨x, hx, hxC⟩
  have hV'_sub : ∀ y ∈ V', BHW.realEmbed y ∈ C := by
    intro y hy
    exact hy.2
  have hH_real' : ∀ y ∈ V', H (BHW.realEmbed y) = 0 := by
    intro y hy
    exact hH_real y hy.1
  exact BHW.identity_theorem_totally_real_product
    hC_open hC_conn hH_holo_C hV'_open hV'_ne hV'_sub hH_real' z
      (mem_connectedComponentIn hzD)

private theorem joinedIn_hermitianReverseOverlap_of_dual_permutedForwardTube_twist
    {d n : ℕ} [NeZero d] {π σ : Equiv.Perm (Fin n)}
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzπ : z ∈ BHW.PermutedForwardTube d n π)
    (hzσ :
      BHW.complexLorentzAction (hermitianTwistCLG d) (hermitianReverse z) ∈
        BHW.PermutedForwardTube d n σ)
    {x : NPointDomain d n}
    (hx : x ∈ hermitianRealOverlap (d := d) (n := n)) :
    JoinedIn (hermitianReverseOverlap (d := d) (n := n)) (BHW.realEmbed x) z := by
  let γ : ℝ → (Fin n → Fin (d + 1) → ℂ) :=
    fun t => t • z + (1 - t) • BHW.realEmbed x
  refine JoinedIn.ofLine (f := γ) ?_ ?_ ?_ ?_
  · have htz : Continuous fun t : ℝ => t • z :=
      continuous_id.smul continuous_const
    have htx : Continuous fun t : ℝ => (1 - t) • BHW.realEmbed x := by
      exact (continuous_const.sub continuous_id).smul continuous_const
    exact (htz.add htx).continuousOn
  · simp [γ]
  · simp [γ]
  · intro w hw
    rcases hw with ⟨t, htI, rfl⟩
    by_cases ht0 : t = 0
    · subst ht0
      simpa [γ] using realEmbed_mem_hermitianReverseOverlap_of_mem_hermitianRealOverlap hx
    · have htpos : 0 < t := lt_of_le_of_ne htI.1 (Ne.symm ht0)
      refine ⟨?_, ?_⟩
      · have hγπ :
          γ t ∈ BHW.PermutedForwardTube d n π :=
            smul_add_realEmbed_mem_permutedForwardTube_BHW hzπ x htpos
        have hγPET : γ t ∈ BHW.PermutedExtendedTube d n :=
          permutedForwardTube_subset_permutedExtendedTube_BHW π hγπ
        simpa [γ, BHW_permutedExtendedTube_eq (d := d) (n := n)] using hγPET
      · have hγσ_twist :
          BHW.complexLorentzAction (hermitianTwistCLG d) (hermitianReverse (γ t)) ∈
            BHW.PermutedForwardTube d n σ := by
          rw [hermitianTwistCLG_hermitianReverse_smul_add_realEmbed (d := d) (n := n) x z t]
          exact smul_add_realEmbed_mem_permutedForwardTube_BHW hzσ
            (hermitianTwistRealN (fun k => x (Fin.rev k))) htpos
        have hγPET_twist :
            BHW.complexLorentzAction (hermitianTwistCLG d) (hermitianReverse (γ t)) ∈
              BHW.PermutedExtendedTube d n :=
          permutedForwardTube_subset_permutedExtendedTube_BHW σ hγσ_twist
        have hγPET :
            hermitianReverse (γ t) ∈ BHW.PermutedExtendedTube d n := by
          have :=
            BHW.complexLorentzAction_mem_permutedExtendedTube hγPET_twist (hermitianTwistCLG d)⁻¹
          simpa [BHW.complexLorentzAction_inv] using this
        simpa [γ, BHW_permutedExtendedTube_eq (d := d) (n := n)] using hγPET

private theorem eq_zero_on_hermitianReverseOverlap_of_dual_permutedForwardTube_twist
    {d n : ℕ} [NeZero d]
    {H : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hH_holo : DifferentiableOn ℂ H (hermitianReverseOverlap (d := d) (n := n)))
    (hH_real :
      ∀ x ∈ hermitianRealOverlap (d := d) (n := n), H (BHW.realEmbed x) = 0)
    {π σ : Equiv.Perm (Fin n)} {z : Fin n → Fin (d + 1) → ℂ}
    (hzπ : z ∈ BHW.PermutedForwardTube d n π)
    (hzσ :
      BHW.complexLorentzAction (hermitianTwistCLG d) (hermitianReverse z) ∈
        BHW.PermutedForwardTube d n σ)
    {x : NPointDomain d n}
    (hx : x ∈ hermitianRealOverlap (d := d) (n := n)) :
    H z = 0 := by
  let D : Set (Fin n → Fin (d + 1) → ℂ) := hermitianReverseOverlap (d := d) (n := n)
  let C : Set (Fin n → Fin (d + 1) → ℂ) := connectedComponentIn D z
  let V : Set (NPointDomain d n) := hermitianRealOverlap (d := d) (n := n)
  have hzD : z ∈ D := by
    refine ⟨?_, ?_⟩
    · have hzPET : z ∈ BHW.PermutedExtendedTube d n :=
        permutedForwardTube_subset_permutedExtendedTube_BHW π hzπ
      simpa [D, BHW_permutedExtendedTube_eq (d := d) (n := n)] using hzPET
    · have hzPET_twist :
          BHW.complexLorentzAction (hermitianTwistCLG d) (hermitianReverse z) ∈
            BHW.PermutedExtendedTube d n :=
        permutedForwardTube_subset_permutedExtendedTube_BHW σ hzσ
      have hzPET :
          hermitianReverse z ∈ BHW.PermutedExtendedTube d n := by
        have :=
          BHW.complexLorentzAction_mem_permutedExtendedTube hzPET_twist (hermitianTwistCLG d)⁻¹
        simpa [BHW.complexLorentzAction_inv] using this
      simpa [D, BHW_permutedExtendedTube_eq (d := d) (n := n)] using hzPET
  have hC_open : IsOpen C :=
    (isOpen_hermitianReverseOverlap (d := d) (n := n)).connectedComponentIn
  have hC_conn : IsConnected C :=
    isConnected_connectedComponentIn_iff.mpr hzD
  have hH_holo_C : DifferentiableOn ℂ H C := by
    refine hH_holo.mono ?_
    exact connectedComponentIn_subset D z
  have hjoin : JoinedIn D (BHW.realEmbed x) z :=
    joinedIn_hermitianReverseOverlap_of_dual_permutedForwardTube_twist hzπ hzσ hx
  have hrange_sub_C : Set.range hjoin.somePath ⊆ C := by
    apply (isPreconnected_range hjoin.somePath.continuous).subset_connectedComponentIn
    · refine ⟨1, ?_⟩
      exact hjoin.somePath.target
    · intro y hy
      rcases hy with ⟨t, rfl⟩
      exact hjoin.somePath_mem t
  have hxC : BHW.realEmbed x ∈ C := by
    apply hrange_sub_C
    refine ⟨0, ?_⟩
    exact hjoin.somePath.source
  let V' : Set (NPointDomain d n) := {y | y ∈ V ∧ BHW.realEmbed y ∈ C}
  have hV'_open : IsOpen V' := by
    refine (isOpen_hermitianRealOverlap (d := d) (n := n)).inter ?_
    exact hC_open.preimage (continuous_realEmbed (d := d) (n := n))
  have hV'_ne : V'.Nonempty := ⟨x, hx, hxC⟩
  have hV'_sub : ∀ y ∈ V', BHW.realEmbed y ∈ C := by
    intro y hy
    exact hy.2
  have hH_real' : ∀ y ∈ V', H (BHW.realEmbed y) = 0 := by
    intro y hy
    exact hH_real y hy.1
  exact BHW.identity_theorem_totally_real_product
    hC_open hC_conn hH_holo_C hV'_open hV'_ne hV'_sub hH_real' z
      (mem_connectedComponentIn hzD)

private theorem bhw_inOpenForwardCone_iff_wightman {d : ℕ} [NeZero d]
    (η : Fin (d + 1) → ℝ) :
    BHW.InOpenForwardCone d η ↔ _root_.InOpenForwardCone d η := by
  unfold BHW.InOpenForwardCone _root_.InOpenForwardCone
  unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩
  · convert h.2 using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = 0
    · subst hi
      simp [LorentzLieGroup.minkowskiSignature, MinkowskiSpace.metricSignature, sq]
    · simp [LorentzLieGroup.minkowskiSignature, MinkowskiSpace.metricSignature, hi, sq]
  · convert h.2 using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = 0
    · subst hi
      simp [LorentzLieGroup.minkowskiSignature, MinkowskiSpace.metricSignature, sq]
    · simp [LorentzLieGroup.minkowskiSignature, MinkowskiSpace.metricSignature, hi, sq]

/-- The chosen BHW extension restricts on the ordinary extended tube to the
    canonical `extendF` extension from the forward tube. -/
private theorem W_analytic_BHW_eq_extendF_on_extendedTube
    (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ z ∈ BHW.ExtendedTube d n,
      (W_analytic_BHW Wfn n).val z =
        BHW.extendF (Wfn.spectrum_condition n).choose z := by
  let F : (Fin n → Fin (d + 1) → ℂ) → ℂ := (Wfn.spectrum_condition n).choose
  have hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      (Wfn.spectrum_condition n).choose_spec.1
  have hF_real_inv :
      ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z := by
    intro Λ z hz
    exact W_analytic_lorentz_on_tube Wfn n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        F (BHW.complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact BHW.complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  have hExtend_holo :
      DifferentiableOn ℂ (BHW.extendF F) (BHW.ExtendedTube d n) :=
    BHW.extendF_holomorphicOn n F hF_holo hF_cinv
  have hBHW_holo_ET :
      DifferentiableOn ℂ (W_analytic_BHW Wfn n).val (BHW.ExtendedTube d n) := by
    refine (W_analytic_BHW Wfn n).property.1.mono ?_
    intro z hz
    simpa [BHW_permutedExtendedTube_eq (d := d) (n := n)] using
      BHW.extendedTube_subset_permutedExtendedTube hz
  obtain ⟨z0, hz0FT⟩ := BHW.forwardTube_nonempty (d := d) (n := n)
  have hz0ET : z0 ∈ BHW.ExtendedTube d n := BHW.forwardTube_subset_extendedTube hz0FT
  have hagree :
      (W_analytic_BHW Wfn n).val =ᶠ[nhds z0] BHW.extendF F := by
    filter_upwards [BHW.isOpen_forwardTube.mem_nhds hz0FT] with z hz
    rw [(W_analytic_BHW Wfn n).property.2.1 z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)]
    exact (BHW.extendF_eq_on_forwardTube n F hF_holo hF_real_inv z hz).symm
  have hEqOn :=
    identity_theorem_product BHW.isOpen_extendedTube
      (BHW.isConnected_extendedTube (d := d) (n := n))
      hBHW_holo_ET hExtend_holo hz0ET hagree
  intro z hz
  exact hEqOn hz

private theorem bhw_real_hermitian_on_edge
    (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ x ∈ hermitianRealOverlap (d := d) (n := n),
      starRingEnd ℂ ((W_analytic_BHW Wfn n).val
        (BHW.realEmbed (fun k => x (Fin.rev k)))) =
      (W_analytic_BHW Wfn n).val (BHW.realEmbed x) := by
  let F : (Fin n → Fin (d + 1) → ℂ) → ℂ := (Wfn.spectrum_condition n).choose
  let V : Set (NPointDomain d n) := hermitianRealOverlap (d := d) (n := n)
  let gV : NPointDomain d n → ℂ :=
    fun x => starRingEnd ℂ (BHW.extendF F (BHW.realEmbed (fun k => x (Fin.rev k))))
  let hVf : NPointDomain d n → ℂ := fun x => BHW.extendF F (BHW.realEmbed x)
  have hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      (Wfn.spectrum_condition n).choose_spec.1
  have hF_real_inv :
      ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z := by
    intro Λ z hz
    exact W_analytic_lorentz_on_tube Wfn n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        F (BHW.complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact BHW.complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  have hExtend_cont : ContinuousOn (BHW.extendF F) (BHW.ExtendedTube d n) :=
    (BHW.extendF_holomorphicOn n F hF_holo hF_cinv).continuousOn
  have hgV_cont : ContinuousOn gV V := by
    have hbase : ContinuousOn
        (fun x : NPointDomain d n =>
          BHW.extendF F (BHW.realEmbed (fun k => x (Fin.rev k)))) V := by
      refine hExtend_cont.comp (continuous_realEmbed_rev (d := d) (n := n)).continuousOn ?_
      intro x hx
      exact hx.2
    simpa [gV] using hbase.star
  have hhVf_cont : ContinuousOn hVf V := by
    refine hExtend_cont.comp (continuous_realEmbed (d := d) (n := n)).continuousOn ?_
    intro x hx
    exact hx.1
  have hV_open : IsOpen V := isOpen_hermitianRealOverlap (d := d) (n := n)
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η := (inForwardCone_iff_mem_forwardConeAbs η).2 hη_abs
  have hη_FT :
      ∀ (x : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) ∈ BHW.ForwardTube d n := by
    intro x ε hε k
    show BHW.InOpenForwardCone d _
    have him :
        (fun μ =>
          ((fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) k μ -
            (if h : k.val = 0 then 0 else
              fun μ =>
                (x ⟨k.val - 1, by omega⟩ μ : ℂ) +
                  ε * (η ⟨k.val - 1, by omega⟩ μ : ℂ) * Complex.I) μ).im) =
          ε • (fun μ => η k μ - (if h : k.val = 0 then 0 else η ⟨k.val - 1, by omega⟩) μ) := by
      ext μ
      by_cases hk : (k : ℕ) = 0
      · simp [hk, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
      · simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
        ring
    rw [him]
    exact (bhw_inOpenForwardCone_iff_wightman _).2
      (inOpenForwardCone_smul d ε hε _ (hη k))
  have hEqOn : Set.EqOn gV hVf V := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hV_open hgV_cont hhVf_cont ?_
    intro φ hφ_compact hφ_tsupport
    let σ : Equiv.Perm (Fin n) := Fin.revPerm
    let eσ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      (LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) σ).toContinuousLinearEquiv
    let φHC : SchwartzNPoint d n := φ.borchersConj
    have hφRev_compact :
        HasCompactSupport ((φ.reverse : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
      simpa [σ, eσ, SchwartzMap.reverse,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        hφ_compact.comp_homeomorph eσ.toHomeomorph
    have hφHC_support :
        Function.support (φHC : NPointDomain d n → ℂ) =
          Function.support ((φ.reverse : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
      ext x
      simp [φHC, Function.mem_support]
    have hφHC_compact : HasCompactSupport (φHC : NPointDomain d n → ℂ) := by
      simpa [φHC, SchwartzMap.borchersConj, SchwartzMap.conj]
        using hφRev_compact.comp_left (g := starRingEnd ℂ) (map_zero _)
    have hφRev_tsupport :
        tsupport ((φ.reverse : SchwartzNPoint d n) : NPointDomain d n → ℂ) =
          eσ.toHomeomorph ⁻¹' tsupport (φ : NPointDomain d n → ℂ) := by
      simpa [σ, eσ, SchwartzMap.reverse,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        (tsupport_comp_eq_preimage (g := (φ : NPointDomain d n → ℂ)) eσ.toHomeomorph)
    have hφHC_tsupport :
        tsupport (φHC : NPointDomain d n → ℂ) =
          tsupport ((φ.reverse : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
      simp [tsupport, hφHC_support]
    have hφ_ET :
        ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ),
          BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
      intro x hx
      exact (hφ_tsupport hx).1
    have hφHC_ET :
        ∀ x ∈ tsupport (φHC : NPointDomain d n → ℂ),
          BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
      intro x hx
      have hxrev : (fun k => x (Fin.rev k)) ∈ tsupport (φ : NPointDomain d n → ℂ) := by
        simpa [hφHC_tsupport, hφRev_tsupport, σ, eσ] using hx
      have hxrevV : (fun k => x (Fin.rev k)) ∈ V := hφ_tsupport hxrev
      have hxV : x ∈ V := by
        simpa [V, Fin.rev_rev] using
          (mem_hermitianRealOverlap_rev (d := d) (n := n)
            (x := fun k => x (Fin.rev k)) hxrevV)
      exact hxV.1
    haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := by infer_instance
    have hpair_φ :
        (∫ x : NPointDomain d n, hVf x * φ x) = Wfn.W n φ := by
      exact tendsto_nhds_unique
        (BHW.tendsto_extendF_boundary_integral_of_hasCompactSupport_ET
          n F hF_holo hF_cinv φ hφ_compact η hη_FT hφ_ET)
        ((Wfn.spectrum_condition n).choose_spec.2 φ η hη)
    have hpair_HC :
        (∫ x : NPointDomain d n, hVf x * φHC x) = Wfn.W n φHC := by
      exact tendsto_nhds_unique
        (BHW.tendsto_extendF_boundary_integral_of_hasCompactSupport_ET
          n F hF_holo hF_cinv φHC hφHC_compact η hη_FT hφHC_ET)
        ((Wfn.spectrum_condition n).choose_spec.2 φHC η hη)
    have hW_herm : Wfn.W n φHC = starRingEnd ℂ (Wfn.W n φ) := by
      refine Wfn.hermitian n φ φHC ?_
      intro x
      change φ.borchersConj x = starRingEnd ℂ (φ (fun i => x (Fin.rev i)))
      exact SchwartzMap.borchersConj_apply φ x
    let erev : NPointDomain d n ≃ᵐ NPointDomain d n :=
      { toEquiv := {
          toFun := fun x i => x (Fin.rev i)
          invFun := fun x i => x (Fin.rev i)
          left_inv := by
            intro x
            ext i μ
            simp [Fin.rev_rev]
          right_inv := by
            intro x
            ext i μ
            simp [Fin.rev_rev] }
        measurable_toFun := by
          apply measurable_pi_lambda
          intro i
          exact measurable_pi_apply (Fin.rev i)
        measurable_invFun := by
          apply measurable_pi_lambda
          intro i
          exact measurable_pi_apply (Fin.rev i) }
    calc
      ∫ x : NPointDomain d n, gV x * φ x
          = ∫ x : NPointDomain d n,
              starRingEnd ℂ (hVf x) * φ (fun i => x (Fin.rev i)) := by
              symm
              rw [← (measurePreserving_revPerm (d := d) (n := n)).integral_comp' (f := erev)]
              simp [erev, gV, hVf, Fin.rev_rev]
      _ = ∫ x : NPointDomain d n, starRingEnd ℂ (hVf x * φHC x) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            simp [φHC, map_mul, mul_comm]
      _ = starRingEnd ℂ (∫ x : NPointDomain d n, hVf x * φHC x) := by
            rw [← _root_.integral_conj]
      _ = starRingEnd ℂ (Wfn.W n φHC) := by rw [hpair_HC]
      _ = Wfn.W n φ := by rw [hW_herm]; simp
      _ = ∫ x : NPointDomain d n, hVf x * φ x := by rw [hpair_φ.symm]
  intro x hx
  have hEq := hEqOn hx
  have hx_rev_ET : BHW.realEmbed (fun k => x (Fin.rev k)) ∈ BHW.ExtendedTube d n := hx.2
  have hx_ET : BHW.realEmbed x ∈ BHW.ExtendedTube d n := hx.1
  calc
    starRingEnd ℂ ((W_analytic_BHW Wfn n).val (BHW.realEmbed (fun k => x (Fin.rev k))))
        = starRingEnd ℂ (BHW.extendF F (BHW.realEmbed (fun k => x (Fin.rev k)))) := by
            rw [W_analytic_BHW_eq_extendF_on_extendedTube (Wfn := Wfn) (n := n)
              (BHW.realEmbed (fun k => x (Fin.rev k))) hx_rev_ET]
    _ = BHW.extendF F (BHW.realEmbed x) := hEq
    _ = (W_analytic_BHW Wfn n).val (BHW.realEmbed x) := by
          symm
          exact W_analytic_BHW_eq_extendF_on_extendedTube (Wfn := Wfn) (n := n)
            (BHW.realEmbed x) hx_ET

private theorem hermitianRealOverlap_nonempty_of_two_le
    {d n : ℕ} [NeZero d] (hd : 2 ≤ d) :
    (hermitianRealOverlap (d := d) (n := n)).Nonempty := by
  rcases JostWitnessGeneralSigma.jostWitness_exists (d := d) (n := n) hd Fin.revPerm with
    ⟨x, _, hxET, hrevET⟩
  exact ⟨x, hxET, by simpa [BHW.realEmbed] using hrevET⟩

/-- Each (n,m)-term of the OS inner product with the constructed Schwinger functions
    equals the corresponding term of the Wightman inner product.

    The proof uses three key ingredients:
    1. **Change of variables** (time reflection θ in first n coordinates):
       converts osConj(f_n) = conj(f_n(θ·)) to conj(f_n(·)), and changes
       F_ext evaluation from forward-tube to backward-tube for first n args.

    2. **F_ext permutation invariance** (BHW property 4): allows reordering
       the first n arguments, converting conj(f_n(y₁,...,yₙ)) to
       conj(f_n(yₙ,...,y₁)) = borchersConj(f_n)(y₁,...,yₙ).

    3. **Boundary value identity**: the integral of F_ext at mixed
       backward/forward Euclidean points against a test function equals
       the Wightman distributional pairing W(n+m)(·).

    Steps 1-2 are provable from existing infrastructure. Step 3 is the
    deep analytic content requiring the distributional boundary value theory
    (Fourier-Laplace representation + Paley-Wiener).

    Blocked by: `boundary_values_tempered` and distributional BV infrastructure.

    Ref: OS I, Section 5; Streater-Wightman §3.4 -/
theorem schwinger_os_term_eq_wightman_term (Wfn : WightmanFunctions d)
    (n m : ℕ) (f_n : SchwartzNPoint d n) (f_m : SchwartzNPoint d m)
    (hsupp_n : ∀ x, f_n.toFun x ≠ 0 → x ∈ OrderedPositiveTimeRegion d n)
    (hsupp_m : ∀ x, f_m.toFun x ≠ 0 → x ∈ OrderedPositiveTimeRegion d m) :
    constructSchwingerFunctions Wfn (n + m) (f_n.osConjTensorProduct f_m) =
    Wfn.W (n + m) (f_n.conjTensorProduct f_m) := by
  sorry

/-- The OS inner product for Wick-rotated Schwinger functions equals the
    Wightman inner product for test functions supported at positive times.

    This is the key identity: ⟨F,F⟩_OS = ⟨F,F⟩_W when F is supported at τ > 0.
    Combined with Wightman positive definiteness (R2), this gives E2.

    Proof: each (n,m)-term of the OS sum equals the (n,m)-term of the Wightman sum
    (by `schwinger_os_term_eq_wightman_term`), so the sums are equal.

    Ref: OS I, Section 5 -/
theorem os_inner_product_eq_wightman (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
      x ∈ OrderedPositiveTimeRegion d n) :
    OSInnerProduct d (constructSchwingerFunctions Wfn) F F =
    WightmanInnerProduct d Wfn.W F F := by
  simp only [OSInnerProduct, WightmanInnerProduct]
  congr 1
  ext n
  congr 1
  ext m
  exact schwinger_os_term_eq_wightman_term Wfn n m (F.funcs n) (F.funcs m)
    (hsupp n) (hsupp m)

/-- The OS inner product for Wick-rotated Schwinger functions reduces to
    the Wightman positivity form after the rotation.

    For test functions F supported in τ > 0, the OS inner product equals
    the Wightman inner product (by `os_inner_product_eq_wightman`), which
    is non-negative by R2 (positive definiteness).

    Ref: OS I, Section 5 (proof that E2 follows from R2); Glimm-Jaffe Ch. 19 -/
theorem os_inner_product_eq_wightman_positivity (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
      x ∈ OrderedPositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 := by
  rw [os_inner_product_eq_wightman Wfn F hsupp]
  exact Wfn.positive_definite F

theorem constructedSchwinger_reflection_positive (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
      x ∈ OrderedPositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 :=
  os_inner_product_eq_wightman_positivity Wfn F hsupp

/-- F_ext is invariant under permutations of arguments at all Euclidean points.

    For Euclidean points with distinct positive times, this follows directly from
    BHW permutation symmetry (`schwinger_permutation_symmetric` in
    AnalyticContinuation.lean) + `euclidean_distinct_in_permutedTube`. For general
    configurations, it extends by analyticity of F_ext ∘ Wick.

    Ref: Jost, §IV.5; Streater-Wightman, Theorem 3.6 -/
theorem F_ext_permutation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : NPointDomain d n)
    (htube : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
    (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x (σ k))) := by
  -- BHW permutation invariance: F_ext(z ∘ σ) = F_ext(z) for z ∈ PET
  exact ((W_analytic_BHW Wfn n).property.2.2.2 σ
    (fun k => wickRotatePoint (x k)) htube).symm

omit [NeZero d] in
/-- Permutations preserve volume: the map x ↦ x ∘ σ on (ℝ^{d+1})^n is
    a rearrangement of factors, preserving Lebesgue measure. -/
theorem integral_perm_eq_self (σ : Equiv.Perm (Fin n))
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => x (σ i)) =
    ∫ x : NPointDomain d n, h x :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp' h

/-- The Schwinger functions satisfy permutation symmetry (E3).

    Proof: BHW permutation invariance on the permuted extended tube,
    restricted to Euclidean points. -/
theorem constructedSchwinger_symmetric (Wfn : WightmanFunctions d)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint d n)
    (hfg : ∀ x, g.toFun x = f.toFun (fun i => x (σ i))) :
    constructSchwingerFunctions Wfn n f = constructSchwingerFunctions Wfn n g := by
  simp only [constructSchwingerFunctions]
  have hfg' : ∀ x : NPointDomain d n,
      (g : NPointDomain d n → ℂ) x =
      (f : NPointDomain d n → ℂ) (fun i => x (σ i)) := hfg
  simp_rw [hfg']
  set K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))
  -- K is permutation-invariant a.e.: K(x) = K(x ∘ σ) for a.e. x with wick(x) ∈ PET
  have hK_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      K x = K (fun i => x (σ i)) := by
    filter_upwards [ae_euclidean_points_in_permutedTube] with x hx
    exact F_ext_permutation_invariant Wfn n σ x hx
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (fun i => x (σ i))
      = ∫ x : NPointDomain d n,
          K (fun i => x (σ i)) *
          (f : NPointDomain d n → ℂ) (fun i => x (σ i)) := by
        exact MeasureTheory.integral_congr_ae (hK_ae.mono fun x hx => by simp only; rw [hx])
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        integral_perm_eq_self σ
          (fun x => K x * (f : NPointDomain d n → ℂ) x)

private abbrev permuteSchwartz (σ : Equiv.Perm (Fin n)) (f : SchwartzNPoint d n) :
    SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) σ).toContinuousLinearEquiv) f

omit [NeZero d] in
@[simp] private theorem permuteSchwartz_apply (σ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    permuteSchwartz σ f x = f (fun i => x (σ i)) := by
  rfl

omit [NeZero d] in
@[simp] private theorem permuteSchwartz_one (f : SchwartzNPoint d n) :
    permuteSchwartz (1 : Equiv.Perm (Fin n)) f = f := by
  ext x
  simp [permuteSchwartz]

omit [NeZero d] in
@[simp] private theorem permuteSchwartz_mul (σ τ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n) :
    permuteSchwartz (σ * τ) f = permuteSchwartz σ (permuteSchwartz τ f) := by
  ext x
  simp [permuteSchwartz]

omit [NeZero d] in
private theorem permute_support_jost (σ : Equiv.Perm (Fin n)) (f : SchwartzNPoint d n)
    (hf : ∀ x : NPointDomain d n, f x ≠ 0 → x ∈ BHW.JostSet d n) :
    ∀ x : NPointDomain d n, permuteSchwartz σ f x ≠ 0 → x ∈ BHW.JostSet d n := by
  intro x hx
  have hy : (fun i => x (σ i)) ∈ BHW.JostSet d n := hf _ hx
  simpa using (BHW.jostSet_permutation_invariant (d := d) (n := n) σ.symm hy)

omit [NeZero d] in
private theorem areSpacelikeSeparated_of_jost_pair (x y : SpacetimeDim d)
    (h : BHW.IsSpacelike d (fun μ => x μ - y μ)) :
    MinkowskiSpace.AreSpacelikeSeparated d x y := by
  unfold MinkowskiSpace.AreSpacelikeSeparated MinkowskiSpace.IsSpacelike
  have hs :
      MinkowskiSpace.minkowskiNormSq d (x - y)
        =
      (∑ μ, if μ = 0 then (y μ - x μ) * (x μ - y μ)
             else (x μ - y μ) * (x μ - y μ)) := by
    unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    refine Finset.sum_congr rfl ?_
    intro μ _
    by_cases h0 : μ = 0
    · subst h0
      simp [MinkowskiSpace.metricSignature]
    · simp [MinkowskiSpace.metricSignature, h0]
  have ht :
      (∑ μ, if μ = 0 then (y μ - x μ) * (x μ - y μ)
             else (x μ - y μ) * (x μ - y μ))
        =
      (∑ μ, if μ = 0 then -((x μ - y μ) * (x μ - y μ))
             else (x μ - y μ) * (x μ - y μ)) := by
    refine Finset.sum_congr rfl ?_
    intro μ _
    by_cases h0 : μ = 0
    · subst h0
      ring_nf
    · simp [h0]
  rw [hs, ht]
  simpa [BHW.IsSpacelike, LorentzLieGroup.minkowskiSignature, sq] using h

private theorem wightman_perm_invariant_on_jost_support (Wfn : WightmanFunctions d)
    (n : ℕ) (f : SchwartzNPoint d n)
    (hf : ∀ x : NPointDomain d n, f x ≠ 0 → x ∈ BHW.JostSet d n)
    (σ : Equiv.Perm (Fin n)) :
    Wfn.W n (permuteSchwartz σ f) = Wfn.W n f := by
  refine BHW.Fin.Perm.adjSwap_induction (n := n)
    (motive := fun τ => Wfn.W n (permuteSchwartz τ f) = Wfn.W n f) ?_ ?_ σ
  · simp [permuteSchwartz]
  · intro τ i hi hτ
    let gτ : SchwartzNPoint d n := permuteSchwartz τ f
    have hsupp : ∀ x : NPointDomain d n, gτ x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩) := by
      intro x hx
      have hxJ : x ∈ BHW.JostSet d n :=
        permute_support_jost (d := d) (n := n) τ f hf x hx
      have hij : i ≠ ⟨i.val + 1, hi⟩ := by
        intro hEq
        have : i.val = i.val + 1 := by simpa using congrArg Fin.val hEq
        omega
      exact areSpacelikeSeparated_of_jost_pair (d := d) (x i) (x ⟨i.val + 1, hi⟩)
        (hxJ.2 i ⟨i.val + 1, hi⟩ hij)
    have hswap0 :
        Wfn.W n gτ = Wfn.W n (permuteSchwartz (Equiv.swap i ⟨i.val + 1, hi⟩) gτ) := by
      refine Wfn.locally_commutative n i ⟨i.val + 1, hi⟩ gτ
        (permuteSchwartz (Equiv.swap i ⟨i.val + 1, hi⟩) gτ) hsupp ?_
      intro x
      change permuteSchwartz (Equiv.swap i ⟨i.val + 1, hi⟩) gτ x =
        gτ (fun k => x ((Equiv.swap i ⟨i.val + 1, hi⟩) k))
      rw [permuteSchwartz_apply]
    calc
      Wfn.W n (permuteSchwartz (Equiv.swap i ⟨i.val + 1, hi⟩ * τ) f)
          = Wfn.W n (permuteSchwartz (Equiv.swap i ⟨i.val + 1, hi⟩) gτ) := by
            simp [gτ]
      _ = Wfn.W n gτ := hswap0.symm
      _ = Wfn.W n f := hτ

private theorem wightman_reverse_invariant_on_jost_support (Wfn : WightmanFunctions d)
    (n : ℕ) (f : SchwartzNPoint d n)
    (hf : ∀ x : NPointDomain d n, f x ≠ 0 → x ∈ BHW.JostSet d n) :
    Wfn.W n f.reverse = Wfn.W n f := by
  simpa [SchwartzMap.reverse, permuteSchwartz]
    using wightman_perm_invariant_on_jost_support (d := d) Wfn n f hf Fin.revPerm

/-- On real-valued Schwartz functions supported in the Jost set, the Wightman
    pairing is real.

    This is the distributional boundary counterpart of Euclidean BHW reality:
    Jost-support reversal invariance plus Wightman Hermiticity force
    `W_n(f) = conj(W_n(f))`. The remaining gap in `bhw_euclidean_reality_ae`
    is to transfer this real-boundary statement to the Euclidean analytic
    continuation. -/
private theorem wightman_real_on_jost_support (Wfn : WightmanFunctions d)
    (n : ℕ) (f : SchwartzNPoint d n)
    (hf : ∀ x : NPointDomain d n, f x ≠ 0 → x ∈ BHW.JostSet d n)
    (hreal : ∀ x : NPointDomain d n, starRingEnd ℂ (f x) = f x) :
    starRingEnd ℂ (Wfn.W n f) = Wfn.W n f := by
  have hherm :
      Wfn.W n f.reverse = starRingEnd ℂ (Wfn.W n f) := by
    refine Wfn.hermitian n f f.reverse ?_
    intro x
    rw [SchwartzMap.reverse]
    symm
    exact hreal (fun i => x i.rev)
  calc
    starRingEnd ℂ (Wfn.W n f) = Wfn.W n f.reverse := hherm.symm
    _ = Wfn.W n f := wightman_reverse_invariant_on_jost_support (d := d) Wfn n f hf

/-- Euclidean-point Hermiticity of the BHW extension.

    For Euclidean configurations, the BHW extension at `wick(x)` is related by
    complex conjugation to the value at the time-reflected, reversed
    configuration. This is the analytic Euclidean counterpart of the Wightman
    Hermiticity axiom and is the genuine remaining input in
    `constructedSchwinger_reality`. -/
theorem bhw_euclidean_reality_ae (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      starRingEnd ℂ ((W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))) =
        (W_analytic_BHW Wfn n).val
          (fun k => wickRotatePoint (timeReflection d (x (Fin.rev k)))) := by
  let F : (Fin n → Fin (d + 1) → ℂ) → ℂ := (W_analytic_BHW Wfn n).val
  let G : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => starRingEnd ℂ (F (hermitianReverse z))
  let H : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z => G z - F z
  let D : Set (Fin n → Fin (d + 1) → ℂ) := hermitianReverseOverlap (d := d) (n := n)
  let V : Set (NPointDomain d n) := hermitianRealOverlap (d := d) (n := n)
  have hF_holo : DifferentiableOn ℂ F (PermutedExtendedTube d n) :=
    (W_analytic_BHW Wfn n).property.1
  have hG_holo : DifferentiableOn ℂ G D := by
    refine (differentiableOn_hermitianReverse_partner (d := d) (n := n) hF_holo).mono ?_
    intro z hz
    exact hz.2
  have hD_open : IsOpen D := isOpen_hermitianReverseOverlap (d := d) (n := n)
  have hF_holo_D : DifferentiableOn ℂ F D := by
    refine hF_holo.mono ?_
    intro z hz
    exact hz.1
  have hH_holo : DifferentiableOn ℂ H D := by
    exact hG_holo.sub hF_holo_D
  have hV_open : IsOpen V := isOpen_hermitianRealOverlap (d := d) (n := n)
  have hV_sub_D : ∀ x ∈ V, BHW.realEmbed x ∈ D := by
    intro x hx
    refine ⟨?_, ?_⟩
    · simpa [V, hermitianRealOverlap, D, hermitianReverseOverlap,
        BHW_permutedExtendedTube_eq (d := d) (n := n)] using
        BHW.extendedTube_subset_permutedExtendedTube hx.1
    · simpa [hermitianReverse_realEmbed, V, hermitianRealOverlap, D, hermitianReverseOverlap,
        BHW_permutedExtendedTube_eq (d := d) (n := n)] using
        BHW.extendedTube_subset_permutedExtendedTube hx.2
  have hwick_mem : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ D :=
    ae_euclidean_points_in_hermitianReverseOverlap (d := d) (n := n)
  have hH_real :
      ∀ x ∈ V, H (BHW.realEmbed x) = 0 := by
    intro x hx
    have hedge := bhw_real_hermitian_on_edge (Wfn := Wfn) (n := n) x hx
    simpa [H, G, F, hermitianReverse_realEmbed, sub_eq_zero] using hedge
  have hmain_of_V_nonempty :
      V.Nonempty →
      ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
        starRingEnd ℂ ((W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))) =
          (W_analytic_BHW Wfn n).val
            (fun k => wickRotatePoint (timeReflection d (x (Fin.rev k)))) := by
    intro hV_ne
    rcases hV_ne with ⟨x0, hx0⟩
    filter_upwards [hwick_mem, ae_pairwise_distinct_timeCoords (d := d) (n := n)]
      with x hxD hdistinct
    let A : ℝ := 1 + ∑ i : Fin n, |x i 0|
    let a : SpacetimeDim d := fun μ => if μ = 0 then A else 0
    let xs : NPointDomain d n := fun k μ => x k μ + a μ
    let z : Fin n → Fin (d + 1) → ℂ := fun k => wickRotatePoint (x k)
    let zShift : Fin n → Fin (d + 1) → ℂ := fun k => wickRotatePoint (xs k)
    let zRev : Fin n → Fin (d + 1) → ℂ :=
      fun k => wickRotatePoint (timeReflection d (x (Fin.rev k)))
    let zShiftRev : Fin n → Fin (d + 1) → ℂ :=
      fun k => wickRotatePoint (timeReflection d (xs (Fin.rev k)))
    have hpos_shift : ∀ i : Fin n, xs i 0 > 0 := by
      intro i
      have hi_le :
          |x i 0| ≤ ∑ j : Fin n, |x j 0| := by
        simpa using
          Finset.single_le_sum (fun j _ => abs_nonneg (x j 0)) (Finset.mem_univ i)
      have hx_lower : -|x i 0| ≤ x i 0 := neg_abs_le (x i 0)
      have hpos : 0 < x i 0 + A := by
        dsimp [A]
        linarith
      simpa [xs, a] using hpos
    have hdistinct_shift : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0 := by
      intro i j hij
      simpa [xs, a] using hdistinct i j hij
    obtain ⟨π, hzπ⟩ :=
      euclidean_distinct_in_BHW_permutedForwardTube (d := d) xs hdistinct_shift hpos_shift
    obtain ⟨σ, hzσ⟩ :=
      euclidean_distinct_twisted_reverse_in_BHW_permutedForwardTube
        (d := d) xs hdistinct_shift hpos_shift
    have hzShift_mem : zShift ∈ PermutedExtendedTube d n := by
      simpa [BHW_permutedExtendedTube_eq (d := d) (n := n)] using
        permutedForwardTube_subset_permutedExtendedTube_BHW π hzπ
    have hzRev_mem : zRev ∈ PermutedExtendedTube d n := by
      simpa [D, z, zRev, hermitianReverse_wickRotate] using hxD.2
    have hzShiftRev_mem : zShiftRev ∈ PermutedExtendedTube d n := by
      have hzσPET :
          BHW.complexLorentzAction (hermitianTwistCLG d) (hermitianReverse zShift) ∈
            BHW.PermutedExtendedTube d n :=
        permutedForwardTube_subset_permutedExtendedTube_BHW σ hzσ
      have hzhrPET : hermitianReverse zShift ∈ BHW.PermutedExtendedTube d n := by
        have :=
          BHW.complexLorentzAction_mem_permutedExtendedTube hzσPET (hermitianTwistCLG d)⁻¹
        simpa [BHW.complexLorentzAction_inv] using this
      simpa [zShift, zShiftRev, hermitianReverse_wickRotate,
        BHW_permutedExtendedTube_eq (d := d) (n := n)] using hzhrPET
    have hzero_shift : H zShift = 0 := by
      exact eq_zero_on_hermitianReverseOverlap_of_dual_permutedForwardTube_twist
        (d := d) (n := n) hH_holo hH_real hzπ hzσ hx0
    have hHerm_shift₀ : starRingEnd ℂ (F zShiftRev) = F zShift := by
      simpa [H, G, F, zShift, zShiftRev, sub_eq_zero, hermitianReverse_wickRotate]
        using hzero_shift
    have hHerm_shift : starRingEnd ℂ (F zShift) = F zShiftRev := by
      have hstar := congrArg (starRingEnd ℂ) hHerm_shift₀
      simpa using hstar.symm
    have hF_shift : F z = F zShift := by
      exact F_ext_translation_invariant Wfn n a x hxD.1 hzShift_mem
    have hF_shift_rev : F zRev = F zShiftRev := by
      have hxRevShift_cfg_eq :
          (fun k μ => timeReflection d (x (Fin.rev k)) μ + timeReflection d a μ) =
            fun k μ => timeReflection d (xs (Fin.rev k)) μ := by
        ext k μ
        by_cases hμ : μ = 0
        · subst hμ
          simp [xs, a, timeReflection]
          ring
        · simp [xs, a, timeReflection, hμ]
      let zRevShift : Fin n → Fin (d + 1) → ℂ :=
        fun k => wickRotatePoint (fun μ =>
          timeReflection d (x (Fin.rev k)) μ + timeReflection d a μ)
      have hzRevShift_eq : zRevShift = zShiftRev := by
        simpa [zRevShift, zShiftRev] using
          congrArg (fun cfg : NPointDomain d n => fun k => wickRotatePoint (cfg k))
            hxRevShift_cfg_eq
      have hzRevShift_mem : zRevShift ∈ PermutedExtendedTube d n := by
        simpa [hzRevShift_eq] using hzShiftRev_mem
      have hF_shift_rev' : F zRev = F zRevShift := by
        exact F_ext_translation_invariant Wfn n (timeReflection d a)
          (fun k => timeReflection d (x (Fin.rev k))) hzRev_mem hzRevShift_mem
      simpa [hzRevShift_eq] using hF_shift_rev'
    calc
      starRingEnd ℂ (F z) = starRingEnd ℂ (F zShift) := by rw [hF_shift]
      _ = F zShiftRev := hHerm_shift
      _ = F zRev := by rw [← hF_shift_rev]
  by_cases h2 : 2 ≤ d
  · exact hmain_of_V_nonempty
      (hermitianRealOverlap_nonempty_of_two_le (d := d) (n := n) h2)
  · have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hd1 : d = 1 := by omega
    subst hd1
    by_cases hn2 : 2 ≤ n
    · have hV_empty : V = ∅ := by
        simpa [V] using hermitianRealOverlap_eq_empty_d1_of_two_le (n := n) hn2
      -- Remaining low-dimensional gap: the old untwisted real-edge strategy is
      -- now provably impossible for `d = 1`, `n ≥ 2`, because the anchor set
      -- `hermitianRealOverlap` is empty. The mixed candidate slice `(t, i x)`
      -- also cannot work here: `mixedWick_not_mem_permutedExtendedTube` shows
      -- it never meets PET for nonempty configurations. So the live problem is
      -- to find a different honest overlap/anchor geometry for the comparison
      -- function, not just to extract one more witness on the existing surfaces.
      let _ := hV_empty
      let _ := hH_holo
      let _ := hD_open
      let _ := hV_sub_D
      let _ := hV_open
      let _ := hH_real
      let _ := hwick_mem
      sorry
    · have hV_nonempty : V.Nonempty := by
        by_cases hn0 : n = 0
        · subst hn0
          let x0 : NPointDomain 1 0 := fun k => Fin.elim0 k
          have hx0FT : BHW.realEmbed x0 ∈ BHW.ForwardTube 1 0 := by
            intro k
            exact Fin.elim0 k
          refine ⟨x0, ?_⟩
          constructor
          · exact BHW.forwardTube_subset_extendedTube hx0FT
          · simpa [BHW.realEmbed] using BHW.forwardTube_subset_extendedTube hx0FT
        · have hn1 : n = 1 := by omega
          subst hn1
          rcases BHW.forwardJostSet_nonempty (d := 1) (n := 1) (by omega) (by omega) with
            ⟨x0, hx0FJ⟩
          have hx0ET : BHW.realEmbed x0 ∈ BHW.ExtendedTube 1 1 :=
            BHW.forwardJostSet_subset_extendedTube (d := 1) (n := 1) (by omega) x0 hx0FJ
          have hx0rev_eq : (fun k => x0 (Fin.rev k)) = x0 := by
            ext k μ
            fin_cases k
            rfl
          refine ⟨x0, ?_⟩
          constructor
          · exact hx0ET
          · simpa [BHW.realEmbed, hx0rev_eq] using hx0ET
      exact hmain_of_V_nonempty hV_nonempty

/-- The Schwinger functions constructed from Wightman functions satisfy the
    standard reality condition `conj(S_n(f)) = S_n(conj f)`.

    This is the Euclidean counterpart of Wightman Hermiticity together with the
    BHW symmetry of the analytic continuation on Euclidean points. It is the
    missing input needed for Hermiticity of the abstract OS form and for the
    standard Laplace/spectral semigroup argument.

    After the zero-diagonal repair, the old proof route through the deleted
    full-Schwartz integrability theorem is no longer available. The remaining
    proof has to combine the Euclidean Hermiticity identity with a separate
    justification of the total-extension pairing. -/
theorem constructedSchwinger_reality (Wfn : WightmanFunctions d) (n : ℕ)
    (f : SchwartzNPoint d n) :
    starRingEnd ℂ (constructSchwingerFunctions Wfn n f) =
      constructSchwingerFunctions Wfn n f.osConj := by
  sorry

/-- Pointwise cluster property of BHW extension at Euclidean points.

    For Euclidean points z = (iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) with strictly increasing τ,
    the BHW extension satisfies the cluster decomposition: as the spatial separation
    between the first n and last m points grows, the (n+m)-point function factorizes.

    This follows from the Wightman cluster property (axiom R4) via analytic continuation:
    the cluster property holds as a distributional identity, and by uniqueness of analytic
    continuation it lifts to the holomorphic extension.

    Blocked by: the Wightman cluster property at the analytic level (requires BHW
    multiplicativity for product configurations) and the dominated convergence argument
    (requires polynomial growth bounds on the BHW extension). -/
theorem bhw_pointwise_cluster_euclidean (Wfn : WightmanFunctions d) (n m : ℕ)
    (z_n : Fin n → Fin (d + 1) → ℂ) (z_m : Fin m → Fin (d + 1) → ℂ)
    (hz_n : IsEuclidean z_n) (hz_m : IsEuclidean z_m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ‖(W_analytic_BHW Wfn (n + m)).val
            (Fin.append z_n (fun k μ => z_m k μ + ↑(a μ) * Complex.I)) -
          (W_analytic_BHW Wfn n).val z_n *
          (W_analytic_BHW Wfn m).val z_m‖ < ε := by
  sorry

/-- Cluster property of W_analytic at the integral level: when the (n+m)-point
    analytic Wightman function is integrated against a tensor product f ⊗ g_a
    where g_a is g translated by a large purely spatial vector a (a 0 = 0),
    the result approaches the product S_n(f) * S_m(g).

    This is the analytic continuation of the Wightman cluster decomposition
    property, which follows from uniqueness of the vacuum (the mass gap
    ensures exponential decay of the truncated correlation functions).
    The Schwartz decay of f and g provides the domination needed for
    dominated convergence.

    Ref: Streater-Wightman, Theorem 3.5 (cluster decomposition);
    Glimm-Jaffe, Chapter 19 -/
theorem W_analytic_cluster_integral (Wfn : WightmanFunctions d) (n m : ℕ)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ∀ (g_a : SchwartzNPoint d m),
          (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
          ‖(∫ x : NPointDomain d (n + m),
              (W_analytic_BHW Wfn (n + m)).val
                (fun k => wickRotatePoint (x k)) *
              (f.tensorProduct g_a) x) -
            (∫ x : NPointDomain d n,
              (W_analytic_BHW Wfn n).val
                (fun k => wickRotatePoint (x k)) * f x) *
            (∫ x : NPointDomain d m,
              (W_analytic_BHW Wfn m).val
                (fun k => wickRotatePoint (x k)) * g x)‖ < ε := by
  -- The proof combines the pointwise cluster property with dominated convergence.
  -- Step 1: Use bhw_pointwise_cluster_euclidean for the pointwise estimate
  -- Step 2: Use Schwartz decay of f, g to dominate the integrand
  -- Step 3: Apply dominated convergence
  sorry

/-- The Schwinger functions satisfy clustering (E4).

    Proof: Follows from cluster decomposition of Wightman functions (R4)
    via the analytic continuation. The key input is `W_analytic_cluster_integral`,
    which combines the pointwise cluster property of W_analytic with
    dominated convergence using Schwartz function decay. -/
theorem constructedSchwinger_cluster (Wfn : WightmanFunctions d)
    (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ∀ (g_a : SchwartzNPoint d m),
          (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
          ‖constructSchwingerFunctions Wfn (n + m) (f.tensorProduct g_a) -
            constructSchwingerFunctions Wfn n f *
            constructSchwingerFunctions Wfn m g‖ < ε := by
  -- Unfold constructSchwingerFunctions to expose the integrals
  simp only [constructSchwingerFunctions]
  exact W_analytic_cluster_integral Wfn n m f g ε hε


end
