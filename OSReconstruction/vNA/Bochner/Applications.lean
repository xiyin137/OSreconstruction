/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Bochner.Convergence
import OSReconstruction.vNA.Bochner.FunctionalCalculusLinearity

/-!
# Applications of the Spectral Functional Calculus

This file provides useful corollaries of the spectral functional calculus
infrastructure built in `Convergence.lean` and `FunctionalCalculusLinearity.lean`.

## Main Results

* `functionalCalculus_congr`: Proof irrelevance — if `f = g` pointwise then
  `f(T) = g(T)` regardless of integrability/boundedness proofs.

* `functionalCalculus_opNorm_le`: Tight operator norm bound `‖f(T)‖ ≤ M`.

* `functionalCalculus_isSelfAdjoint`: If `f` is real-valued then `f(T)` is self-adjoint.

* `functionalCalculus_inner_self_nonneg`: If `f ≥ 0` then `f(T)` is positive.

* `functionalCalculus_smul`: Scalar multiplication `(c • f)(T) = c • f(T)`.
-/

noncomputable section

open MeasureTheory Complex Filter Topology SpectralMeasure
open scoped InnerProduct ComplexConjugate

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Proof irrelevance (congr) -/

/-- The functional calculus depends only on `f`, not on the proofs of integrability
    and boundedness. If `f = g` pointwise, then `f(T) = g(T)`.

    Proof: By polarization, it suffices to show `⟨f(T)x, x⟩ = ⟨g(T)x, x⟩`.
    Using `functionalCalculus_inner_self_flip`:
    `⟨f(T)x, x⟩ = conj(∫ f dμ_x) = conj(∫ g dμ_x) = ⟨g(T)x, x⟩`. -/
theorem functionalCalculus_congr (P : SpectralMeasure H) (f g : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hg_int : ∀ z : H, Integrable g (P.diagonalMeasure z))
    (hg_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖g t‖ ≤ M)
    (hfg : ∀ t, f t = g t) :
    functionalCalculus P f hf_int hf_bdd = functionalCalculus P g hg_int hg_bdd := by
  apply ContinuousLinearMap.ext_inner_self
  intro x
  rw [functionalCalculus_inner_self_flip P f hf_int hf_bdd x,
      functionalCalculus_inner_self_flip P g hg_int hg_bdd x]
  congr 1
  exact integral_congr_ae (Eventually.of_forall hfg)

/-- Support-aware congruence: if every diagonal measure is supported in `E`, then
two bounded measurable functions that agree on `E` have the same functional calculus. -/
theorem functionalCalculus_congr_on_support (P : SpectralMeasure H)
    (E : Set ℝ)
    (hsupport : ∀ z : H, P.diagonalMeasure z Eᶜ = 0)
    (f g : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hg_int : ∀ z : H, Integrable g (P.diagonalMeasure z))
    (hg_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖g t‖ ≤ M)
    (hfg : ∀ t ∈ E, f t = g t) :
    functionalCalculus P f hf_int hf_bdd = functionalCalculus P g hg_int hg_bdd := by
  apply ContinuousLinearMap.ext_inner_self
  intro z
  rw [functionalCalculus_inner_self_flip P f hf_int hf_bdd z,
      functionalCalculus_inner_self_flip P g hg_int hg_bdd z]
  congr 1
  apply integral_congr_ae
  have hmemE : ∀ᵐ t ∂(P.diagonalMeasure z), t ∈ E := by
    rw [ae_iff]
    simpa [Set.compl_setOf, Set.setOf_mem_eq] using hsupport z
  filter_upwards [hmemE] with t ht
  exact hfg t ht

/-! ### Operator norm bound -/

/-- Tight operator norm bound: `‖f(T)‖ ≤ M` where `∀ t, ‖f t‖ ≤ M`.

    This is tighter than the `2M` bound from the sesquilinear form construction.
    Proof: `‖f(T)x‖² = ∫ |f|² dμ_x ≤ M² · μ_x(ℝ) = M² ‖x‖²`. -/
theorem functionalCalculus_opNorm_le (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hf_meas : Measurable f) (M : ℝ) (hM_nn : 0 ≤ M) (hM : ∀ t, ‖f t‖ ≤ M) :
    ‖functionalCalculus P f hf_int hf_bdd‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM_nn
  intro x
  by_cases hx : x = 0
  · simp [hx]
  -- ‖f(T)x‖² = ∫ |f|² dμ_x ≤ M² · ‖x‖²
  have hnorm_sq := functionalCalculus_norm_sq' P f hf_int hf_bdd hf_meas x
  -- ∫ |f|² dμ_x ≤ M² · ‖x‖²
  have h_int_le : ∫ t, ‖f t‖ ^ 2 ∂(P.diagonalMeasure x) ≤ M ^ 2 * ‖x‖ ^ 2 := by
    calc ∫ t, ‖f t‖ ^ 2 ∂(P.diagonalMeasure x)
        ≤ ∫ _, M ^ 2 ∂(P.diagonalMeasure x) := by
          apply integral_mono_of_nonneg
          · exact Eventually.of_forall fun _ => sq_nonneg _
          · exact integrable_const _
          · exact Eventually.of_forall fun t =>
              sq_le_sq' (by linarith [norm_nonneg (f t)]) (hM t)
      _ = (P.diagonalMeasure x).real Set.univ * M ^ 2 := by
          rw [integral_const, smul_eq_mul]
      _ ≤ ‖x‖ ^ 2 * M ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          rw [P.diagonalMeasure_real_univ]
      _ = M ^ 2 * ‖x‖ ^ 2 := by ring
  -- ‖f(T)x‖² ≤ (M ‖x‖)² implies ‖f(T)x‖ ≤ M ‖x‖
  have h_sq : ‖functionalCalculus P f hf_int hf_bdd x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [mul_pow]; linarith
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _),
       Real.sqrt_sq (mul_nonneg hM_nn (norm_nonneg x))] at h_sqrt

/-! ### Self-adjointness -/

/-- If `f` is real-valued (i.e., `star ∘ f = f`), then `f(T)` is self-adjoint.

    Proof: By `functionalCalculus_star`, `f(T)* = (star ∘ f)(T)`.
    Since `star ∘ f = f` pointwise, `functionalCalculus_congr` gives
    `(star ∘ f)(T) = f(T)`. -/
theorem functionalCalculus_isSelfAdjoint (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hf_real : ∀ t, starRingEnd ℂ (f t) = f t)
    (hsf_int : ∀ z : H, Integrable (star ∘ f) (P.diagonalMeasure z))
    (hsf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(star ∘ f) t‖ ≤ M) :
    IsSelfAdjoint (functionalCalculus P f hf_int hf_bdd) := by
  rw [isSelfAdjoint_iff]
  -- star = adjoint for CLMs
  rw [ContinuousLinearMap.star_eq_adjoint]
  -- adjoint(f(T)) = (star ∘ f)(T) by functionalCalculus_star
  rw [functionalCalculus_star P f hf_int hf_bdd hsf_int hsf_bdd]
  -- (star ∘ f)(T) = f(T) since star ∘ f = f
  exact functionalCalculus_congr P (star ∘ f) f hsf_int hsf_bdd hf_int hf_bdd
    (fun t => hf_real t)

/-! ### Positivity -/

/-- If `f(t) ≥ 0` as a real number for all `t`, then `re⟨x, f(T)x⟩ ≥ 0`.

    This means `f(T)` is a positive operator.

    Proof: `⟨x, f(T)x⟩ = ∫ f dμ_x`. Since f takes nonneg real values,
    `∫ f dμ_x = ↑(∫ r dμ_x)` where `r ≥ 0`, so `re(⟨x, f(T)x⟩) ≥ 0`. -/
theorem functionalCalculus_inner_self_nonneg (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    -- f takes nonneg real values: f(t) = ↑(r(t)) with r(t) ≥ 0
    (r : ℝ → ℝ) (hr_nonneg : ∀ t, 0 ≤ r t) (hr_eq : ∀ t, f t = ↑(r t))
    (x : H) :
    0 ≤ RCLike.re (@inner ℂ H _ x (functionalCalculus P f hf_int hf_bdd x)) := by
  rw [functionalCalculus_inner_self P f hf_int hf_bdd x]
  -- Goal: 0 ≤ re(∫ f dμ_x)
  have hre : RCLike.re (∫ t, f t ∂P.diagonalMeasure x) =
    ∫ t, RCLike.re (f t) ∂P.diagonalMeasure x := (integral_re (hf_int x)).symm
  rw [hre]
  apply integral_nonneg fun t => ?_
  simp only [Pi.zero_apply]
  rw [hr_eq t]; simp [hr_nonneg t]

/-! ### Scalar multiplication -/

/-- Scalar multiplication: `(c • f)(T) = c • f(T)`.

    Proof: By polarization, it suffices to show diagonal inner products agree.
    Uses `functionalCalculus_inner_self_flip` + `integral_smul`. -/
theorem SpectralMeasure.functionalCalculus_smul (P : SpectralMeasure H) (c : ℂ) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hcf_int : ∀ z : H, Integrable (c • f) (P.diagonalMeasure z))
    (hcf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(c • f) t‖ ≤ M) :
    functionalCalculus P (c • f) hcf_int hcf_bdd =
    c • functionalCalculus P f hf_int hf_bdd := by
  apply ContinuousLinearMap.ext_inner_self
  intro x
  rw [ContinuousLinearMap.smul_apply, inner_smul_left]
  rw [functionalCalculus_inner_self_flip P (c • f) hcf_int hcf_bdd x,
      functionalCalculus_inner_self_flip P f hf_int hf_bdd x]
  rw [← map_mul (starRingEnd ℂ)]
  congr 1
  simp_rw [Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

/-! ### Power functions of the identity -/

private theorem integrable_of_bounded_finite {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℝ → ℂ} (hf_meas : AEStronglyMeasurable f μ)
    (M : ℝ) (hf : ∀ t, ‖f t‖ ≤ M) :
    Integrable f μ := by
  exact ⟨hf_meas, HasFiniteIntegral.of_bounded
    (Eventually.of_forall fun x => hf x)⟩

private theorem measurable_ofReal_pow (n : ℕ) :
    Measurable (fun t : ℝ => (t : ℂ) ^ n) :=
  Complex.continuous_ofReal.measurable.pow_const n

private theorem ofReal_pow_mul (n : ℕ) :
    (fun t : ℝ => (t : ℂ) ^ n) * (fun t : ℝ => (t : ℂ)) =
    (fun t : ℝ => (t : ℂ) ^ (n + 1)) := by
  ext t
  simp [pow_succ, mul_comm]

private theorem pow_integrable_diag (P : SpectralMeasure H) (M : ℝ) (_hM : 0 ≤ M)
    (hbnd : ∀ t : ℝ, ‖(t : ℂ)‖ ≤ M) (n : ℕ) (z : H) :
    Integrable (fun t : ℝ => (t : ℂ) ^ n) (P.diagonalMeasure z) :=
  integrable_of_bounded_finite
    (measurable_ofReal_pow n).aestronglyMeasurable (M ^ n)
    (fun t => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbnd t) n)

private theorem id_integrable_diag (P : SpectralMeasure H) (M : ℝ) (_hM : 0 ≤ M)
    (hbnd : ∀ t : ℝ, ‖(t : ℂ)‖ ≤ M) (z : H) :
    Integrable (fun t : ℝ => (t : ℂ)) (P.diagonalMeasure z) :=
  integrable_of_bounded_finite
    Complex.continuous_ofReal.measurable.aestronglyMeasurable M hbnd

private theorem pow_bdd (M : ℝ) (hM : 0 ≤ M)
    (hbnd : ∀ t : ℝ, ‖(t : ℂ)‖ ≤ M) (n : ℕ) :
    ∃ M', 0 ≤ M' ∧ ∀ t : ℝ, ‖(t : ℂ) ^ n‖ ≤ M' :=
  ⟨M ^ n, pow_nonneg hM n, fun t => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbnd t) n⟩

namespace SpectralMeasure

/-- Integer powers of the spectral image of the identity coincide with the spectral
image of the corresponding power function. This is the algebraic integer-time
step behind the semigroup spectral representation. -/
theorem functionalCalculus_pow_ofReal (P : SpectralMeasure H) (M : ℝ) (hM : 0 ≤ M)
    (hbnd : ∀ t : ℝ, ‖(t : ℂ)‖ ≤ M)
    (n : ℕ) (hn : 0 < n) :
    (functionalCalculus P (fun t : ℝ => (t : ℂ))
      (fun z => id_integrable_diag P M hM hbnd z)
      ⟨M, hM, hbnd⟩) ^ n =
    functionalCalculus P (fun t : ℝ => (t : ℂ) ^ n)
      (fun z => pow_integrable_diag P M hM hbnd n z)
      (pow_bdd M hM hbnd n) := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          rw [pow_one]
          exact (functionalCalculus_congr P
            (fun t : ℝ => (t : ℂ) ^ 1)
            (fun t : ℝ => (t : ℂ))
            (fun z => pow_integrable_diag P M hM hbnd 1 z)
            (pow_bdd M hM hbnd 1)
            (fun z => id_integrable_diag P M hM hbnd z)
            ⟨M, hM, hbnd⟩
            (fun t => by simp [pow_one])).symm
      | succ n =>
          have hn' : 0 < n + 1 := Nat.succ_pos n
          rw [pow_succ (n := n + 1), ih hn']
          have hmul := functionalCalculus_mul P
            (fun t : ℝ => (t : ℂ) ^ (n + 1))
            (fun t : ℝ => (t : ℂ))
            (fun z => pow_integrable_diag P M hM hbnd (n + 1) z)
            (pow_bdd M hM hbnd (n + 1))
            (fun z => id_integrable_diag P M hM hbnd z)
            ⟨M, hM, hbnd⟩
            (by
              rw [ofReal_pow_mul]
              intro z
              exact pow_integrable_diag P M hM hbnd (n + 2) z)
            (by
              rw [show (fun t : ℝ => (t : ℂ) ^ (n + 1)) * (fun t : ℝ => (t : ℂ)) =
                  (fun t : ℝ => (t : ℂ) ^ (n + 2)) from ofReal_pow_mul (n + 1)]
              exact pow_bdd M hM hbnd (n + 2))
            Complex.continuous_ofReal.measurable
          show functionalCalculus P (fun t : ℝ => (t : ℂ) ^ (n + 1)) _ _ *
              functionalCalculus P (fun t : ℝ => (t : ℂ)) _ _ =
            functionalCalculus P (fun t : ℝ => (t : ℂ) ^ (n + 2)) _ _
          rw [show (HMul.hMul : (H →L[ℂ] H) → _ → _) = ContinuousLinearMap.comp from rfl]
          rw [← hmul]
          congr 1

end SpectralMeasure

/-! ### Strong-limit commutation and projection approximation -/

omit [CompleteSpace H] in
/-- If `A` commutes with each `Tₙ` and `Tₙ → T` strongly, then `A` commutes with `T`. -/
theorem ContinuousLinearMap.comm_of_strong_limit (A : H →L[ℂ] H)
    (Tₙ : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hcomm : ∀ n, A ∘L Tₙ n = Tₙ n ∘L A)
    (hlim : ∀ x, Tendsto (fun n => Tₙ n x) atTop (nhds (T x))) :
    A ∘L T = T ∘L A := by
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  have h1 : Tendsto (fun n => A (Tₙ n x)) atTop (nhds (A (T x))) :=
    (A.continuous.tendsto _).comp (hlim x)
  have h2 : ∀ n, A (Tₙ n x) = Tₙ n (A x) := by
    intro n
    exact congr_fun (congrArg DFunLike.coe (hcomm n)) x
  have h3 : Tendsto (fun n => Tₙ n (A x)) atTop (nhds (T (A x))) :=
    hlim (A x)
  simp_rw [h2] at h1
  exact tendsto_nhds_unique h1 h3

private theorem indicator_integrable (P : SpectralMeasure H) (E : Set ℝ) (hE : MeasurableSet E) :
    ∀ z : H, Integrable (E.indicator (fun _ => (1 : ℂ))) (P.diagonalMeasure z) := by
  intro z
  haveI := P.diagonalMeasure_isFiniteMeasure z
  exact (integrable_const (1 : ℂ)).indicator hE

private theorem indicator_bdd (E : Set ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ t, ‖E.indicator (fun _ => (1 : ℂ)) t‖ ≤ M := by
  refine ⟨1, zero_le_one, ?_⟩
  intro t
  by_cases ht : t ∈ E
  · simp [Set.indicator_of_mem, ht]
  · simp [Set.indicator_of_notMem, ht]

private theorem indicator_measurable (E : Set ℝ) (hE : MeasurableSet E) :
    Measurable (E.indicator (fun _ => (1 : ℂ))) :=
  measurable_const.indicator hE

private theorem indicator_norm_le_one (E : Set ℝ) :
    ∀ t, ‖E.indicator (fun _ => (1 : ℂ)) t‖ ≤ 1 := by
  intro t
  by_cases ht : t ∈ E
  · simp [Set.indicator_of_mem, ht]
  · simp [Set.indicator_of_notMem, ht]

private theorem one_sq_integrable (P : SpectralMeasure H) :
    ∀ z : H, Integrable (fun _ : ℝ => ((1 : ℝ) ^ 2)) (P.diagonalMeasure z) := by
  intro z
  haveI := P.diagonalMeasure_isFiniteMeasure z
  simpa using (integrable_const ((1 : ℝ) ^ 2))

namespace SpectralMeasure

/-- If bounded measurable functions converge pointwise to an indicator, then the
corresponding spectral-calculus operators converge strongly to the spectral projection. -/
theorem functionalCalculus_tendsto_projection_apply (P : SpectralMeasure H)
    (E : Set ℝ) (hE : MeasurableSet E)
    (f : ℕ → ℝ → ℂ)
    (hf_tend : ∀ t, Tendsto (fun n => f n t) atTop (nhds (E.indicator (fun _ => (1 : ℂ)) t)))
    (hf_bound : ∀ n t, ‖f n t‖ ≤ 1)
    (hf_int : ∀ n z, Integrable (f n) (P.diagonalMeasure z))
    (hf_bdd : ∀ n, ∃ M, 0 ≤ M ∧ ∀ t, ‖f n t‖ ≤ M)
    (hf_meas : ∀ n, Measurable (f n))
    (x : H) :
    Tendsto (fun n => functionalCalculus P (f n) (hf_int n) (hf_bdd n) x)
      atTop (nhds (P.proj E x)) := by
  let χE : ℝ → ℂ := E.indicator (fun _ => (1 : ℂ))
  have hχ_int : ∀ z : H, Integrable χE (P.diagonalMeasure z) :=
    indicator_integrable P E hE
  have hχ_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖χE t‖ ≤ M := indicator_bdd E
  have hχ_meas : Measurable χE := indicator_measurable E hE
  have hlim :=
    functionalCalculus_tendsto_SOT P f χE hf_tend
      (fun _ => (1 : ℝ)) (fun _ => zero_le_one) hf_bound (indicator_norm_le_one E)
      ⟨1, fun _ => le_rfl⟩ (one_sq_integrable P) hf_int hf_bdd hχ_int hχ_bdd hf_meas hχ_meas x
  have hproj : functionalCalculus P χE hχ_int hχ_bdd = P.proj E :=
    functionalCalculus_indicator P E hE hχ_int hχ_bdd
  simp [χE, hproj] at hlim
  exact hlim

/-- If `A` commutes with a sequence of spectral-calculus approximants converging
strongly to `P(E)`, then `A` commutes with the spectral projection `P(E)`. -/
theorem commute_projection_of_commute_approximants (P : SpectralMeasure H)
    (A : H →L[ℂ] H) (E : Set ℝ) (hE : MeasurableSet E)
    (f : ℕ → ℝ → ℂ)
    (hf_tend : ∀ t, Tendsto (fun n => f n t) atTop (nhds (E.indicator (fun _ => (1 : ℂ)) t)))
    (hf_bound : ∀ n t, ‖f n t‖ ≤ 1)
    (hf_int : ∀ n z, Integrable (f n) (P.diagonalMeasure z))
    (hf_bdd : ∀ n, ∃ M, 0 ≤ M ∧ ∀ t, ‖f n t‖ ≤ M)
    (hf_meas : ∀ n, Measurable (f n))
    (hcomm : ∀ n,
      A ∘L functionalCalculus P (f n) (hf_int n) (hf_bdd n) =
        functionalCalculus P (f n) (hf_int n) (hf_bdd n) ∘L A) :
    A ∘L P.proj E = P.proj E ∘L A := by
  apply ContinuousLinearMap.comm_of_strong_limit A
    (fun n => functionalCalculus P (f n) (hf_int n) (hf_bdd n))
    (P.proj E)
  · exact hcomm
  · intro x
    exact P.functionalCalculus_tendsto_projection_apply E hE f
      hf_tend hf_bound hf_int hf_bdd hf_meas x

end SpectralMeasure

end
