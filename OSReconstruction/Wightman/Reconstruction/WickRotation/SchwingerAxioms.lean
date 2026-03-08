/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation

/-!
# Schwinger Axioms from Wightman Functions

Verification that the Schwinger functions constructed via Wick rotation
satisfy all Osterwalder-Schrader axioms E0-E4.

- E0 (temperedness): polynomial growth bounds + Schwartz integration
- E1a (translation invariance): now taken as an explicit exported input
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
    permuted extended tube, Wick rotation is continuous, and the caller supplies
    the a.e.-PET hypothesis for Wick-rotated Euclidean points. -/
theorem bhw_euclidean_kernel_measurable {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ m : ℕ,
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) m σ))
    (hExtPerm_d1 : ∀ m : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 →
        ∀ (z : Fin m → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d m →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d m →
          BHW.extendF ((Wfn.spectrum_condition m).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition m).choose) z)
    (hPET_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k)))
      MeasureTheory.volume := by
  -- Strategy: F_ext is continuous on PET (holomorphic ⇒ continuous). Wick is continuous.
  -- The composition is ContinuousOn on S = Wick⁻¹(PET), which is open and has full measure.
  -- ContinuousOn.aestronglyMeasurable gives AEStronglyMeasurable on μ.restrict S.
  -- Since μ(Sᶜ) = 0, piecewise with 0 on Sᶜ gives the result.
  set F_ext := (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val
  set wick : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ) :=
    fun x k => wickRotatePoint (x k)
  set S := wick ⁻¹' (PermutedExtendedTube d n)
  -- F_ext is continuous on PET
  have hF_cont : ContinuousOn F_ext (PermutedExtendedTube d n) :=
    (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).property.1.continuousOn
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
  -- Sᶜ has measure zero by the explicit a.e.-PET hypothesis
  have hSc_null : MeasureTheory.volume Sᶜ = 0 :=
    MeasureTheory.mem_ae_iff.mp hPET_ae
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

/-- Schwinger functions constructed via Wick rotation are tempered (E0).

    The integral S_n(f) = ∫ F_ext(Wick(x)) f(x) dx defines a continuous linear
    functional on the Schwartz space. The proof combines:

    1. an explicit a.e. polynomial bound on the Wick-rotated BHW kernel
       (supplied as the `hPoly` hypothesis below),
    2. `bhw_euclidean_kernel_measurable`: The kernel is a.e. strongly measurable.
    3. `schwartz_continuous_of_polynomial_bound`: A polynomially bounded measurable kernel
       defines a continuous functional on Schwartz space via integration.

    Ref: OS I (1973) Proposition 5.1 -/
theorem wick_rotated_schwinger_tempered {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ m : ℕ,
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) m σ))
    (hExtPerm_d1 : ∀ m : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 →
        ∀ (z : Fin m → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d m →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d m →
          BHW.extendF ((Wfn.spectrum_condition m).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition m).choose) z)
    (n : ℕ)
    (hPET_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n)
    (hPoly :
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
          ‖(W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k))‖ ≤
            C_bd * (1 + ‖x‖) ^ N) :
    Continuous (constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n) := by
  -- The goal is: Continuous (fun f => ∫ x, F_ext(Wick(x)) * f(x) dx)
  -- Obtain the polynomial bound on the BHW kernel at Euclidean points
  obtain ⟨C_bd, N, hC, hbound⟩ := hPoly
  -- Obtain measurability of the kernel
  have hmeas :=
    bhw_euclidean_kernel_measurable (n := n) Wfn hRegular hSeedConn_hd2 hExtPerm_d1 hPET_ae
  -- The function constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n is definitionally equal to
  -- fun f => ∫ x, K(x) * f(x) where K(x) = F_ext(Wick(x))
  show Continuous (fun f : SchwartzNPoint d n =>
    ∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k)) * (f x))
  exact schwartz_continuous_of_polynomial_bound
    (fun x => (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k)))
    hmeas C_bd N hC hbound

/-- The Schwinger functions constructed from Wightman functions satisfy temperedness (E0).

    This follows from the temperedness of Wightman functions (R0) and the
    geometric estimates in OS I, Proposition 5.1: the Wick-rotated kernel
    composed with f is integrable and the integral depends continuously on f. -/
theorem constructedSchwinger_tempered (Wfn : WightmanFunctions d)
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ m : ℕ,
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) m σ))
    (hExtPerm_d1 : ∀ m : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 →
        ∀ (z : Fin m → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d m →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d m →
          BHW.extendF ((Wfn.spectrum_condition m).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition m).choose) z)
    (n : ℕ)
    (hPET_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n)
    (hPoly :
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
          ‖(W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k))‖ ≤
            C_bd * (1 + ‖x‖) ^ N) :
    Continuous (constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n) := by
  exact wick_rotated_schwinger_tempered Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n hPET_ae hPoly

/-- F_ext is invariant under proper Euclidean rotations (SO(d+1)) at all Euclidean points.

    For Euclidean points with distinct positive times, this follows from
    `schwinger_euclidean_invariant` (AnalyticContinuation.lean) + BHW complex
    Lorentz invariance. For general configurations, it extends by analyticity
    of F_ext ∘ Wick (or by the distribution-level argument).

    Restricted to det R = 1 (proper rotations). Full O(d+1) invariance (det=-1)
    would require parity invariance, which is not implied by Wightman axioms.

    Ref: Streater-Wightman, Theorem 3.6 (BHW); Jost, §IV.5 -/
theorem F_ext_rotation_invariant (Wfn : WightmanFunctions d)
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ m : ℕ,
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) m σ))
    (hExtPerm_d1 : ∀ m : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 →
        ∀ (z : Fin m → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d m →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d m →
          BHW.extendF ((Wfn.spectrum_condition m).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition m).choose) z)
    (n : ℕ)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hR : R.transpose * R = 1)
    (hdet : R.det = 1) (x : NPointDomain d n)
    (htube : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k)) =
    (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val
      (fun k => wickRotatePoint (R.mulVec (x k))) := by
  have := schwinger_euclidean_invariant
    (fun n => (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val)
    (fun n Λ z hz => (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).property.2.2.1 Λ z hz)
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

/-- The Schwinger functions satisfy rotation invariance (E1b).

    Proof: Complex Lorentz invariance of W_analytic on the permuted extended tube,
    together with the fact that SO(d+1) ⊂ L₊(ℂ) preserves Euclidean points.
    The rotation R ∈ SO(d+1) acts on the forward tube via its embedding in L₊(ℂ). -/
theorem constructedSchwinger_rotation_invariant (Wfn : WightmanFunctions d)
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ m : ℕ,
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) m σ))
    (hExtPerm_d1 : ∀ m : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 →
        ∀ (z : Fin m → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d m →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d m →
          BHW.extendF ((Wfn.spectrum_condition m).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition m).choose) z)
    (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hPET_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n)
    (hR : R.transpose * R = 1) (hdet : R.det = 1)
    (f g : SchwartzNPoint d n)
    (hfg : ∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) :
    constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n f = constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n g := by
  simp only [constructSchwingerFunctions]
  have hfg' : ∀ x : NPointDomain d n,
      (g : NPointDomain d n → ℂ) x =
      (f : NPointDomain d n → ℂ) (fun i => R.mulVec (x i)) := hfg
  simp_rw [hfg']
  set K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k))
  -- K is rotation-invariant a.e.: K(x) = K(Rx) for a.e. x with wick(x) ∈ PET
  have hK_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      K x = K (fun i => R.mulVec (x i)) := by
    filter_upwards [hPET_ae] with x hx
    exact F_ext_rotation_invariant Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n R hR hdet x hx
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

/-- F_ext is invariant under permutations of arguments at all Euclidean points.

    For Euclidean points with distinct positive times, this follows directly from
    BHW permutation symmetry (`schwinger_permutation_symmetric` in
    AnalyticContinuation.lean) + `euclidean_distinct_in_permutedTube`. For general
    configurations, it extends by analyticity of F_ext ∘ Wick.

    Ref: Jost, §IV.5; Streater-Wightman, Theorem 3.6 -/
theorem F_ext_permutation_invariant (Wfn : WightmanFunctions d)
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ m : ℕ,
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) m σ))
    (hExtPerm_d1 : ∀ m : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 →
        ∀ (z : Fin m → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d m →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d m →
          BHW.extendF ((Wfn.spectrum_condition m).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition m).choose) z)
    (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : NPointDomain d n)
    (htube : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k)) =
    (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x (σ k))) := by
  -- BHW permutation invariance: F_ext(z ∘ σ) = F_ext(z) for z ∈ PET
  exact ((W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).property.2.2.2 σ
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
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ m : ℕ,
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) m σ))
    (hExtPerm_d1 : ∀ m : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin m)), σ ≠ 1 → ¬ m ≤ 1 →
        ∀ (z : Fin m → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d m →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d m →
          BHW.extendF ((Wfn.spectrum_condition m).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition m).choose) z)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint d n)
    (hPET_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n)
    (hfg : ∀ x, g.toFun x = f.toFun (fun i => x (σ i))) :
    constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n f = constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n g := by
  simp only [constructSchwingerFunctions]
  have hfg' : ∀ x : NPointDomain d n,
      (g : NPointDomain d n → ℂ) x =
      (f : NPointDomain d n → ℂ) (fun i => x (σ i)) := hfg
  simp_rw [hfg']
  set K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k))
  -- K is permutation-invariant a.e.: K(x) = K(x ∘ σ) for a.e. x with wick(x) ∈ PET
  have hK_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      K x = K (fun i => x (σ i)) := by
    filter_upwards [hPET_ae] with x hx
    exact F_ext_permutation_invariant Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n σ x hx
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (fun i => x (σ i))
      = ∫ x : NPointDomain d n,
          K (fun i => x (σ i)) *
          (f : NPointDomain d n → ℂ) (fun i => x (σ i)) := by
        exact MeasureTheory.integral_congr_ae (hK_ae.mono fun x hx => by simp only; rw [hx])
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        integral_perm_eq_self σ
          (fun x => K x * (f : NPointDomain d n → ℂ) x)

end
