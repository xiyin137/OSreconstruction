/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction
import OSReconstruction.Wightman.Reconstruction.AnalyticContinuation
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions

/-!
# Forward Tube Lorentz Action

Lorentz invariance infrastructure for the forward tube: cone preservation,
tube preservation, change of variables for integrals, and distributional
boundary value covariance.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-! ### Distribution Theory Axioms for the Forward Tube

These axioms specialize the general tube domain results from `SCV.TubeDistributions`
to the forward tube `T_n = { z ∈ ℂ^{n(d+1)} | Im(z_k - z_{k-1}) ∈ V₊ }`.

The forward tube is a tube domain over the product cone `V₊^n` in difference coordinates.
The rigorous transport results used here are the regular flattened-input theorems
from `ForwardTubeDistributions`, obtained after the linear change of variables from
absolute to difference coordinates and the identification
`Fin n → Fin (d+1) → ℂ ≅ Fin (n*(d+1)) → ℂ`.

Ref: Vladimirov, "Methods of the Theory of Generalized Functions" §25-26;
     Streater-Wightman, Theorems 2-6, 2-9 -/

/-! #### Helper lemmas for Lorentz invariance on the forward tube -/

/-- A restricted Lorentz transformation preserves the open forward light cone.

    If Λ ∈ SO⁺(1,d) and η ∈ V₊ (η₀ > 0, η² < 0), then Λη ∈ V₊.

    Part (a): Metric preservation — minkowskiNormSq(Λη) = minkowskiNormSq(η) < 0.
    Part (b): Time component positivity — (Λη)₀ > 0, using Λ₀₀ ≥ 1, Cauchy-Schwarz,
    and the hyperbolic bound.

    Ref: Streater-Wightman, §2.4 -/
theorem restricted_preserves_forward_cone
    (Λ : LorentzGroup.Restricted (d := d))
    (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η) :
    InOpenForwardCone d (fun μ => ∑ ν, Λ.val.val μ ν * η ν) := by
  obtain ⟨hη0_pos, hη_neg⟩ := hη
  constructor
  · -- Part (b): (Λη)₀ > 0
    -- (Λη)₀ = Λ₀₀ · η₀ + Σ_{j≠0} Λ₀ⱼ · ηⱼ
    -- By first_row_timelike: Λ₀₀² = 1 + Σ_{j≠0} Λ₀ⱼ²
    -- By Cauchy-Schwarz: |Σ_{j≠0} Λ₀ⱼ ηⱼ| ≤ √(Σ Λ₀ⱼ²) · √(Σ ηⱼ²)
    -- Since η ∈ V₊: η₀² > Σ ηⱼ² (from minkowskiNormSq < 0)
    -- And Λ₀₀ ≥ 1 (orthochronous)
    -- So (Λη)₀ ≥ η₀(Λ₀₀ - √(Λ₀₀² - 1)) > 0
    have hΛ_lorentz := Λ.val.property
    have hΛ_ortho : LorentzGroup.IsOrthochronous Λ.val := Λ.property.2
    have hΛ00 : Λ.val.val 0 0 ≥ 1 := hΛ_ortho
    have hrow := IsLorentzMatrix.first_row_timelike Λ.val.val hΛ_lorentz
    -- η is timelike: η₀² > spatial norm
    have hη_timelike : MinkowskiSpace.minkowskiNormSq d η < 0 := hη_neg
    have hη_time_dom : (η 0) ^ 2 > MinkowskiSpace.spatialNormSq d η :=
      MinkowskiSpace.timelike_time_dominates_space d η hη_timelike
    -- Split the sum into j=0 and j≠0
    have hsplit : (∑ ν : Fin (d + 1), Λ.val.val 0 ν * η ν) =
        Λ.val.val 0 0 * η 0 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val.val 0 j * η j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : Fin (d + 1)))]
      simp [Finset.filter_eq', Finset.mem_univ]
    show (∑ ν : Fin (d + 1), Λ.val.val 0 ν * η ν) > 0
    rw [hsplit]
    -- Define spatial sums
    set SΛ := ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val.val 0 j ^ 2
    set Sη := MinkowskiSpace.spatialNormSq d η
    -- SΛ = Λ₀₀² - 1
    have hSΛ_eq : SΛ = Λ.val.val 0 0 ^ 2 - 1 := by linarith [hrow]
    have hSΛ_nonneg : SΛ ≥ 0 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hSη_nonneg : Sη ≥ 0 := MinkowskiSpace.spatialNormSq_nonneg d η
    -- Cauchy-Schwarz on spatial part
    have hCS_sq : (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val.val 0 j * η j) ^ 2 ≤ SΛ * Sη := by
      -- The spatial sum of ηⱼ² equals spatialNormSq reindexed
      -- Relate Sη = spatialNormSq to a sum over filter (· ≠ 0)
      have hSη_eq : Sη = ∑ j ∈ Finset.univ.filter (· ≠ (0 : Fin (d + 1))), η j ^ 2 := by
        show MinkowskiSpace.spatialNormSq d η = _
        unfold MinkowskiSpace.spatialNormSq
        apply Finset.sum_nbij Fin.succ
        · intro i _; simp [Finset.mem_filter, Fin.succ_ne_zero]
        · intro i _ j _ hij; exact Fin.succ_injective _ hij
        · intro j hj
          have hj_ne : j ≠ 0 := by simpa using hj
          exact ⟨j.pred hj_ne, by simp, Fin.succ_pred j hj_ne⟩
        · intro i _; rfl
      rw [hSη_eq]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    -- Bound: spatial sum ≥ -√(SΛ · Sη)
    have hCS : |∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val.val 0 j * η j| ≤
        Real.sqrt SΛ * Real.sqrt Sη := by
      rw [← Real.sqrt_mul hSΛ_nonneg Sη, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hCS_sq
    have hbound : -(Real.sqrt SΛ * Real.sqrt Sη) ≤
        ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val.val 0 j * η j := by
      linarith [neg_abs_le (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val.val 0 j * η j), hCS]
    -- Now: (Λη)₀ ≥ Λ₀₀ · η₀ - √SΛ · √Sη
    --     = Λ₀₀ · η₀ - √(Λ₀₀² - 1) · √Sη
    --     > Λ₀₀ · η₀ - √(Λ₀₀² - 1) · η₀  (since √Sη < η₀)
    --     = η₀ · (Λ₀₀ - √(Λ₀₀² - 1)) > 0
    have hη0_sq_pos : (η 0) ^ 2 > Sη := hη_time_dom
    have hη0_pos' : η 0 > 0 := hη0_pos
    have hSη_lt_η0sq : Real.sqrt Sη < η 0 := by
      rw [← Real.sqrt_sq (le_of_lt hη0_pos')]
      exact Real.sqrt_lt_sqrt hSη_nonneg hη0_sq_pos
    -- Use hyperbolic bound: Λ₀₀ · η₀ - √(Λ₀₀² - 1) · √(η₀² - ε) > 0 when Λ₀₀ ≥ 1, η₀ > 0
    -- Simpler: Λ₀₀ · η₀ - √(Λ₀₀² - 1) · η₀ ≥ η₀ · (1 - 0) = η₀ > 0 when Λ₀₀ = 1
    -- In general, Λ₀₀ - √(Λ₀₀² - 1) > 0 for Λ₀₀ ≥ 1
    have hΛ_hyp : Λ.val.val 0 0 - Real.sqrt (Λ.val.val 0 0 ^ 2 - 1) > 0 := by
      have h1 : Λ.val.val 0 0 ^ 2 - 1 ≥ 0 := by nlinarith
      have h2 : Λ.val.val 0 0 > 0 := by linarith
      have h3 : Real.sqrt (Λ.val.val 0 0 ^ 2 - 1) < Λ.val.val 0 0 := by
        calc Real.sqrt (Λ.val.val 0 0 ^ 2 - 1)
            < Real.sqrt (Λ.val.val 0 0 ^ 2) := Real.sqrt_lt_sqrt h1 (by linarith)
          _ = Λ.val.val 0 0 := Real.sqrt_sq (le_of_lt h2)
      linarith
    -- Lower bound: (Λη)₀ = Λ₀₀η₀ + spatial ≥ Λ₀₀η₀ - √SΛ·√Sη
    --   > Λ₀₀η₀ - √SΛ·η₀ = η₀(Λ₀₀ - √(Λ₀₀²-1)) > 0
    -- We need √SΛ·√Sη ≤ √SΛ·η₀ (since √Sη < η₀)
    -- and Λ₀₀ - √SΛ = Λ₀₀ - √(Λ₀₀²-1) > 0
    have key : Λ.val.val 0 0 * η 0 +
        ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val.val 0 j * η j > 0 := by
      have h_sqrt_SΛ_eq : Real.sqrt SΛ = Real.sqrt (Λ.val.val 0 0 ^ 2 - 1) := by
        congr 1
      -- The spatial sum is bounded below by -√SΛ·√Sη ≥ -√SΛ·η₀
      have h1 : ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val.val 0 j * η j ≥
          -(Real.sqrt SΛ * η 0) := by
        calc ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val.val 0 j * η j
            ≥ -(Real.sqrt SΛ * Real.sqrt Sη) := hbound
          _ ≥ -(Real.sqrt SΛ * η 0) := by
              apply neg_le_neg
              exact mul_le_mul_of_nonneg_left (le_of_lt hSη_lt_η0sq) (Real.sqrt_nonneg _)
      -- So (Λη)₀ ≥ Λ₀₀η₀ - √SΛ·η₀ = η₀(Λ₀₀ - √(Λ₀₀²-1))
      have h2 : Λ.val.val 0 0 * η 0 - Real.sqrt SΛ * η 0 > 0 := by
        rw [← sub_mul, h_sqrt_SΛ_eq]
        exact mul_pos hΛ_hyp hη0_pos'
      linarith
    exact key
  · -- Part (a): Metric preservation -- minkowskiNormSq(Lη) = minkowskiNormSq(η) < 0
    -- Uses the defining Lorentz property to show the Minkowski norm is preserved.
    have hΛ := Λ.val.property
    have hmetric : Λ.val.val.transpose * minkowskiMatrix d * Λ.val.val = minkowskiMatrix d := hΛ
    show MinkowskiSpace.minkowskiNormSq d (fun μ => ∑ ν, Λ.val.val μ ν * η ν) < 0
    -- The norm of Λη equals that of η by the Lorentz condition
    suffices hnorm_eq : MinkowskiSpace.minkowskiNormSq d (fun μ => ∑ ν, Λ.val.val μ ν * η ν) =
        MinkowskiSpace.minkowskiNormSq d η by
      rw [hnorm_eq]; exact hη_neg
    -- Expand both sides as quadratic forms and use the Lorentz matrix identity
    unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    simp only [MinkowskiSpace.metricSignature]
    -- Extract the Lorentz condition entry-wise: (ΛᵀηΛ)_νρ = η_νρ
    have hentry : ∀ ν ρ : Fin (d + 1),
        ∑ μ : Fin (d + 1), (if μ = 0 then (-1 : ℝ) else 1) * Λ.val.val μ ν * Λ.val.val μ ρ =
        if ν = ρ then (if ν = 0 then (-1 : ℝ) else 1) else 0 := by
      intro ν ρ
      have h1 : (Λ.val.val.transpose * minkowskiMatrix d * Λ.val.val) ν ρ =
          (minkowskiMatrix d) ν ρ := by rw [hmetric]
      simp only [Matrix.mul_apply, minkowskiMatrix, Matrix.diagonal_apply,
        Matrix.transpose_apply, MinkowskiSpace.metricSignature] at h1
      convert h1 using 1
      apply Finset.sum_congr rfl; intro μ _
      rw [Finset.sum_eq_single μ]
      · by_cases hμ : μ = 0 <;> simp [hμ]
      · intro k _ hk; simp [hk]
      · simp
    -- Distribute each summand: s_μ * (Σ_ν Λ_μν η_ν) * (Σ_ρ Λ_μρ η_ρ)
    --   = Σ_ν Σ_ρ s_μ * Λ_μν * Λ_μρ * η_ν * η_ρ
    have hlhs : ∀ μ : Fin (d + 1),
        ((if μ = 0 then (-1:ℝ) else 1) * ∑ ν, Λ.val.val μ ν * η ν) *
        (∑ ρ, Λ.val.val μ ρ * η ρ) =
        ∑ ν, ∑ ρ, (if μ = 0 then (-1:ℝ) else 1) * Λ.val.val μ ν * Λ.val.val μ ρ *
          η ν * η ρ := by
      intro μ
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _; ring
    simp_rw [hlhs]
    -- Swap outer sum μ with ν
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro ν _
    -- For fixed ν: swap μ with ρ, factor out η, apply hentry
    rw [Finset.sum_comm]
    -- Factor out η_ν η_ρ and apply hentry
    have hstep : ∀ ρ : Fin (d + 1),
        ∑ μ, (if μ = 0 then (-1:ℝ) else 1) * Λ.val.val μ ν * Λ.val.val μ ρ * η ν * η ρ =
        ((if ν = ρ then (if ν = 0 then (-1:ℝ) else 1) else 0) * η ν * η ρ) := by
      intro ρ
      have hfactor : ∀ μ : Fin (d + 1),
          (if μ = 0 then (-1:ℝ) else 1) * Λ.val.val μ ν * Λ.val.val μ ρ * η ν * η ρ =
          ((if μ = 0 then (-1:ℝ) else 1) * Λ.val.val μ ν * Λ.val.val μ ρ) * (η ν * η ρ) := by
        intro μ; ring
      simp_rw [hfactor, ← Finset.sum_mul, hentry ν ρ]; ring
    simp_rw [hstep]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- A restricted Lorentz transformation preserves the forward tube.

    If Λ ∈ SO⁺(1,d) and z ∈ ForwardTube, then Λz ∈ ForwardTube.
    Key: Λ is real, so Im(Λz_k) = Λ · Im(z_k). The successive differences
    Im((Λz)_k - (Λz)_{k-1}) = Λ · Im(z_k - z_{k-1}) ∈ V₊. -/
theorem restricted_preserves_forward_tube
    (Λ : LorentzGroup.Restricted (d := d))
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) ∈ ForwardTube d n := by
  intro k
  -- The imaginary part of (Λz)_k,μ = Σ_ν Λ_μν · z_k_ν
  -- Since Λ is real: Im(Σ_ν Λ_μν z_k_ν) = Σ_ν Λ_μν · Im(z_k_ν)
  -- The successive difference of imaginary parts:
  -- Im((Λz)_k - (Λz)_{k-1}) = Λ · Im(z_k - z_{k-1})
  -- This lies in V₊ by restricted_preserves_forward_cone
  let prev_z := if h : k.val = 0 then (0 : Fin (d + 1) → ℂ) else z ⟨k.val - 1, by omega⟩
  have hk := hz k -- InOpenForwardCone d (fun μ => (z k μ - prev_z μ).im) [up to let]
  -- The difference η_k for the original z
  let η_k : Fin (d + 1) → ℝ := fun μ => (z k μ - prev_z μ).im
  -- Need to show InOpenForwardCone d (fun μ => ((Λz)_k μ - (Λz)_{k-1} μ).im)
  -- = InOpenForwardCone d (fun μ => Σ_ν Λ_μν · (z k ν - prev_z ν).im)
  -- = InOpenForwardCone d (fun μ => Σ_ν Λ_μν · η_k ν)
  -- This follows from restricted_preserves_forward_cone
  -- The goal from `ForwardTube` unfolds via `let` bindings that match η_k
  -- We show the imaginary part of the difference equals Λ · η_k
  suffices h : InOpenForwardCone d (fun μ => ∑ ν, Λ.val.val μ ν * η_k ν) by
    -- Show the goal (from ForwardTube unfolding) matches our suffices
    -- The key: for real Λ, Im(Σ_ν Λ_μν * z_ν) = Σ_ν Λ_μν * Im(z_ν)
    -- So Im of difference = Λ applied to Im of difference = Λ · η_k
    -- The imaginary part of the Lorentz-rotated difference equals Λ · η_k
    -- because Λ is real: Im(Σ_ν Λ_μν * z_ν) = Σ_ν Λ_μν * Im(z_ν)
    -- Key fact: Im distributes over sums and Im(r * z) = r * Im(z) for r ∈ ℝ
    have him_linear : ∀ (w : Fin (d + 1) → ℂ) (μ : Fin (d + 1)),
        (∑ ν, (Λ.val.val μ ν : ℂ) * w ν).im = ∑ ν, Λ.val.val μ ν * (w ν).im := by
      intro w μ
      rw [Complex.im_sum]
      apply Finset.sum_congr rfl; intro ν _
      exact Complex.im_ofReal_mul _ _
    convert h using 1
    ext μ
    simp only [Complex.sub_im]
    rw [him_linear (z k) μ]
    split_ifs with h0
    · -- k = 0: prev for Λz is 0
      simp only [Pi.zero_apply, Complex.zero_im, sub_zero]
      apply Finset.sum_congr rfl; intro ν _
      congr 1
      show (z k ν).im = (z k ν - prev_z ν).im
      simp [prev_z, h0]
    · -- k > 0: prev for Λz is Λ · z_{k-1}
      rw [him_linear (z ⟨k.val - 1, by omega⟩) μ]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro ν _
      rw [← mul_sub]
      congr 1
      show (z k ν).im - (z ⟨k.val - 1, by omega⟩ ν).im = (z k ν - prev_z ν).im
      simp [prev_z, h0, Complex.sub_im]
  exact restricted_preserves_forward_cone Λ η_k (by exact hk)

/-- The composition z ↦ W_analytic(Λz) is holomorphic on the forward tube
    when Λ ∈ SO⁺(1,d), since z ↦ Λz is ℂ-linear and preserves the forward tube. -/
theorem W_analytic_lorentz_holomorphic
    (Wfn : WightmanFunctions d) (n : ℕ)
    (Λ : LorentzGroup.Restricted (d := d)) :
    DifferentiableOn ℂ
      (fun z => (Wfn.spectrum_condition n).choose
        (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν))
      (ForwardTube d n) := by
  -- W_analytic is holomorphic on ForwardTube, and z ↦ Λz maps ForwardTube to ForwardTube
  -- and is differentiable (ℂ-linear), so the composition is holomorphic.
  apply DifferentiableOn.comp (Wfn.spectrum_condition n).choose_spec.1
  · -- z ↦ Λz is differentiable on ForwardTube (it's ℂ-linear)
    intro z _
    apply DifferentiableAt.differentiableWithinAt
    -- The map z ↦ (fun k μ => Σ_ν Λ_μν * z k ν) is a finite sum of
    -- constant * coordinate projection, hence differentiable
    apply differentiableAt_pi.mpr; intro k
    apply differentiableAt_pi.mpr; intro μ
    have hcoord : ∀ (k : Fin n) (ν : Fin (d + 1)),
        DifferentiableAt ℂ (fun x : Fin n → Fin (d + 1) → ℂ => x k ν) z :=
      fun k' ν' => differentiableAt_pi.mp (differentiableAt_pi.mp differentiableAt_id k') ν'
    suffices h : ∀ (s : Finset (Fin (d + 1))),
        DifferentiableAt ℂ (fun x : Fin n → Fin (d + 1) → ℂ =>
          ∑ ν ∈ s, (↑(Λ.val.val μ ν) : ℂ) * x k ν) z by
      exact h Finset.univ
    intro s
    induction s using Finset.induction with
    | empty => simp [differentiableAt_const]
    | @insert ν s hν ih =>
      simp only [Finset.sum_insert hν]
      exact ((differentiableAt_const _).mul (hcoord k ν)).add ih
  · intro z hz
    exact restricted_preserves_forward_tube Λ z hz

/-! ### Textbook Axioms

These are standard results from distribution theory and functional analysis
that we axiomatize to avoid lengthy measure-theoretic plumbing. Each is a
well-known textbook theorem stated at greater generality than the specific
instances used here.
-/

/-- Polynomial growth of a holomorphic function on a fixed interior slice of a tube domain.

    If F is holomorphic on ForwardTube d n, has tempered distributional boundary
    values, and ε > 0 with η ∈ V₊^n, then the
    restriction x ↦ F(x + iεη) satisfies polynomial growth:
    ‖F(x + iεη)‖ ≤ C · (1 + ‖x‖)^N for some C, N depending on F, ε, η.

    Here this is obtained through `ForwardTubeDistributions`: convert Schwartz BV
    data to flat-coordinate BV (`schwartz_bv_to_flat_bv`) and then apply
    `polynomial_growth_forwardTube` on the compact singleton `{εη}`.

    Current status:
    this is still a weak placeholder theorem. Its previous proof relied on the
    weak forward-tube boundary-value transport chain, which is now explicitly
    reopened in `ForwardTubeDistributions`.

    Ref: Vladimirov, "Methods of the Theory of Generalized Functions", Theorem 25.5 -/
theorem polynomial_growth_on_slice {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (h_bv : ∃ (T : SchwartzNPoint d n → ℂ), Continuous T ∧
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T f)))
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η)
    (ε : ℝ) (hε : ε > 0) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : NPointDomain d n),
        ‖F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖ ≤
          C_bd * (1 + ‖x‖) ^ N := by
  -- Blocked: the previous proof depended on the weak forward-tube BV transport
  -- chain, which has now been reopened as honest placeholder interface.
  sorry

/-- Proved slice-growth theorem under regular flattened-tube Fourier-Laplace input. -/
theorem polynomial_growth_on_slice_of_flatRegular {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm))
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η)
    (ε : ℝ) (hε : ε > 0) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : NPointDomain d n),
        ‖F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖ ≤
          C_bd * (1 + ‖x‖) ^ N := by
  let y0 : Fin n → Fin (d + 1) → ℝ := fun k μ => ε * η k μ
  have hη_abs : η ∈ ForwardConeAbs d n :=
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) η).1 hη
  have hy0_mem : y0 ∈ ForwardConeAbs d n := forwardConeAbs_smul d n ε hε η hη_abs
  have hK_sub : ({y0} : Set (Fin n → Fin (d + 1) → ℝ)) ⊆ ForwardConeAbs d n := by
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hy0_mem
  obtain ⟨C_bd, N, hC_pos, hbound⟩ :=
    polynomial_growth_forwardTube_of_flatRegular
      (d := d) (n := n) hF hRegular {y0} isCompact_singleton hK_sub
  refine ⟨C_bd, N, hC_pos, ?_⟩
  intro x
  simpa [y0, mul_assoc, mul_left_comm, mul_comm]
    using hbound x y0 (by simp)

/-- A function with polynomial growth times a Schwartz function is integrable.

    If g : E → ℂ satisfies ‖g(x)‖ ≤ C · (1 + ‖x‖)^N and f is Schwartz,
    then g · f is integrable, because Schwartz functions decay faster than
    any polynomial.

    Proof uses `add_pow_le` to bound (1+‖x‖)^N ≤ 2^(N-1) * (1 + ‖x‖^N),
    then `SchwartzMap.integrable` and `SchwartzMap.integrable_pow_mul` from Mathlib
    (via `HasTemperateGrowth` for volume on finite-dimensional Pi types). -/
theorem polynomial_growth_mul_schwartz_integrable {d n : ℕ} [NeZero d]
    (g : NPointDomain d n → ℂ)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hg : ∀ x, ‖g x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (f : SchwartzNPoint d n) :
    MeasureTheory.Integrable (fun x => g x * f x) MeasureTheory.volume := by
  -- Provide instances for Schwartz integrability
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  have hf_int := f.integrable (μ := MeasureTheory.volume)
  have hpow_int := SchwartzMap.integrable_pow_mul MeasureTheory.volume f N
  -- The dominating function: C_bd * 2^(N-1) * (‖f x‖ + ‖x‖^N * ‖f x‖)
  have hg_dom_int : MeasureTheory.Integrable
      (fun x => C_bd * 2 ^ (N - 1) * (‖f x‖ + ‖x‖ ^ N * ‖f x‖))
      MeasureTheory.volume :=
    (hf_int.norm.add hpow_int).const_mul _
  -- Measurability of g * f
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun x => g x * f x)
      MeasureTheory.volume :=
    hg_meas.mul f.continuous.aestronglyMeasurable
  -- Pointwise bound using add_pow_le
  have hbound : ∀ x : NPointDomain d n,
      ‖g x * f x‖ ≤ C_bd * 2 ^ (N - 1) * (‖f x‖ + ‖x‖ ^ N * ‖f x‖) := by
    intro x
    rw [norm_mul]
    have h1 := hg x
    have hnf : (0 : ℝ) ≤ ‖f x‖ := norm_nonneg _
    have h2 : (1 + ‖x‖) ^ N ≤ 2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N) :=
      add_pow_le (by positivity) (norm_nonneg x) N
    have step1 : ‖g x‖ * ‖f x‖ ≤ C_bd * (1 + ‖x‖) ^ N * ‖f x‖ :=
      mul_le_mul_of_nonneg_right h1 hnf
    have step2 : C_bd * (1 + ‖x‖) ^ N * ‖f x‖ ≤
        C_bd * (2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N)) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (le_of_lt hC)) hnf
    have step3 : C_bd * (2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N)) * ‖f x‖ =
        C_bd * 2 ^ (N - 1) * (‖f x‖ + ‖x‖ ^ N * ‖f x‖) := by
      simp only [one_pow]; ring
    linarith
  exact hg_dom_int.mono' hmeas (Filter.Eventually.of_forall hbound)

/-- The slice map x ↦ F(x + εηi) is AEStronglyMeasurable when F is holomorphic
    on the forward tube and εη has forward cone components.
    Follows from: the affine embedding x ↦ x + εηi maps into the forward tube,
    F is continuous there (holomorphic → continuous), and composition with
    the continuous affine map is continuous, hence measurable. -/
theorem forward_tube_slice_aestrongly_measurable {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η)
    (ε : ℝ) (hε : ε > 0) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d n => F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
      MeasureTheory.volume := by
  -- The affine embedding φ(x) = x + iεη is continuous and maps into ForwardTube
  -- F is continuous on ForwardTube (holomorphic → continuous), so F∘φ is continuous
  -- Step 1: φ(x) ∈ ForwardTube for all x
  have h_in_tube : ∀ x : NPointDomain d n,
      (fun k μ => (↑(x k μ) : ℂ) + ε * ↑(η k μ) * Complex.I) ∈ ForwardTube d n := by
    intro x k
    -- Goal: Im((x_k + iεη_k) - prev) ∈ V⁺
    -- Since x is real, Im = ε · (η_k - η_{k-1}), which is in V⁺ by InForwardCone
    have hk := hη k
    -- Convert goal to match ε * (η_k - prev_η)
    let diff : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    suffices hsuff : InOpenForwardCone d (fun μ => ε * diff μ) by
      convert hsuff using 1
      ext μ; simp only [diff]
      split_ifs with h
      · simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im]
      · simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im]; ring
    -- ε * diff ∈ V⁺ since diff ∈ V⁺ and ε > 0
    obtain ⟨hk0, hkneg⟩ := hk
    refine ⟨by exact mul_pos hε hk0, ?_⟩
    -- minkowskiNormSq(ε · diff) = ε² · minkowskiNormSq(diff)
    show MinkowskiSpace.minkowskiNormSq d (fun μ => ε * diff μ) < 0
    simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
    have : ∑ i : Fin (d + 1), MinkowskiSpace.metricSignature d i * (ε * diff i) * (ε * diff i) =
        ε ^ 2 * ∑ i : Fin (d + 1), MinkowskiSpace.metricSignature d i * diff i * diff i := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this]
    exact mul_neg_of_pos_of_neg (pow_pos hε 2) hkneg
  -- Step 2: The affine map is continuous
  have h_cont_affine : Continuous (fun x : NPointDomain d n =>
      (fun k μ => (↑(x k μ) : ℂ) + ε * ↑(η k μ) * Complex.I)) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    exact (Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply k))).add
      continuous_const
  -- Step 3: F is continuous on ForwardTube, compose with continuous affine map
  exact (hF.continuousOn.comp_continuous h_cont_affine h_in_tube).aestronglyMeasurable

theorem forward_tube_bv_integrable {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (h_bv : ∃ (T : SchwartzNPoint d n → ℂ), Continuous T ∧
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T f)))
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η)
    (ε : ℝ) (hε : ε > 0) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      MeasureTheory.volume := by
  -- Decompose via polynomial growth on the slice + Schwartz decay
  obtain ⟨C_bd, N, hC, hgrowth⟩ := polynomial_growth_on_slice F hF h_bv η hη ε hε
  -- Measurability: the slice map x ↦ F(x + εηi) is continuous since F is holomorphic
  -- on the forward tube and the affine embedding maps into it
  have hg_meas : MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d n => F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
      MeasureTheory.volume :=
    forward_tube_slice_aestrongly_measurable F hF η hη ε hε
  exact polynomial_growth_mul_schwartz_integrable
    (fun x : NPointDomain d n => F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
    hg_meas C_bd N hC hgrowth f

/-- Extract the matrix product identities for a restricted Lorentz transformation. -/
theorem lorentz_mul_inv_eq_one {d : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d)) :
    Λ.val.val * Λ.val⁻¹.val = 1 := by
  have h1 := LorentzGroup.ext_iff.mp (mul_inv_cancel Λ.val)
  rw [show (Λ.val * Λ.val⁻¹).val = Λ.val.val * Λ.val⁻¹.val from rfl] at h1
  rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
  exact h1

theorem lorentz_inv_mul_eq_one {d : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d)) :
    Λ.val⁻¹.val * Λ.val.val = 1 := by
  have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ.val)
  rw [show (Λ.val⁻¹ * Λ.val).val = Λ.val⁻¹.val * Λ.val.val from rfl] at h1
  rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
  exact h1

/-- The componentwise Lorentz action on NPointDomain preserves Lebesgue measure.

    Follows the same pattern as `integral_orthogonal_eq_self` but uses
    `|det Λ| = 1` from properness instead of orthogonality. -/
theorem integral_lorentz_eq_self {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d))
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => Matrix.mulVec Λ.val.val (x i)) =
    ∫ x : NPointDomain d n, h x := by
  have hdet_ne : Λ.val.val.det ≠ 0 := by
    have hp := Λ.property.1
    simp only [LorentzGroup.IsProper] at hp
    rw [hp]; exact one_ne_zero
  have habs : |Λ.val.val.det| = 1 := by
    have hp := Λ.property.1
    simp only [LorentzGroup.IsProper] at hp
    rw [hp]; simp
  have hΛ_mul_inv := lorentz_mul_inv_eq_one Λ
  have hΛinv_mul := lorentz_inv_mul_eq_one Λ
  have hmv : (fun v => Λ.val.val.mulVec v) = Matrix.toLin' Λ.val.val := by
    ext v; simp [Matrix.toLin'_apply]
  have hcont_Λ : Continuous (Matrix.toLin' Λ.val.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcont_Λinv : Continuous (Matrix.toLin' Λ.val⁻¹.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hmp_factor : MeasureTheory.MeasurePreserving
      (fun v : Fin (d+1) → ℝ => Λ.val.val.mulVec v)
      MeasureTheory.volume MeasureTheory.volume := by
    rw [hmv]; constructor
    · exact hcont_Λ.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet_ne]
      simp [abs_inv, habs]
  let e : (Fin n → Fin (d+1) → ℝ) ≃ᵐ (Fin n → Fin (d+1) → ℝ) :=
    { toEquiv := {
        toFun := fun a i => Λ.val.val.mulVec (a i)
        invFun := fun a i => Λ.val⁻¹.val.mulVec (a i)
        left_inv := fun a => by ext i j; simp [Matrix.mulVec_mulVec, hΛinv_mul]
        right_inv := fun a => by ext i j; simp [Matrix.mulVec_mulVec, hΛ_mul_inv] }
      measurable_toFun :=
        measurable_pi_lambda _ fun i => hcont_Λ.measurable.comp (measurable_pi_apply i)
      measurable_invFun :=
        measurable_pi_lambda _ fun i => hcont_Λinv.measurable.comp (measurable_pi_apply i) }
  have hmp : MeasureTheory.MeasurePreserving (⇑e)
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_pi (fun (_ : Fin n) => hmp_factor)
  exact hmp.integral_comp' h

/-- The ContinuousLinearEquiv for the inverse Lorentz action on a single spacetime factor. -/
noncomputable def lorentzInvCLEquiv {d : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d)) :
    (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) := by
  have hΛinv_mul := lorentz_inv_mul_eq_one Λ
  have hΛ_mul_inv := lorentz_mul_inv_eq_one Λ
  exact {
    toLinearEquiv := {
      toLinearMap := (Matrix.toLin' Λ.val⁻¹.val)
      invFun := Matrix.toLin' Λ.val.val
      left_inv := fun v => by
        show (Matrix.toLin' Λ.val.val) ((Matrix.toLin' Λ.val⁻¹.val) v) = v
        rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛ_mul_inv, Matrix.toLin'_one]
        simp
      right_inv := fun v => by
        show (Matrix.toLin' Λ.val⁻¹.val) ((Matrix.toLin' Λ.val.val) v) = v
        rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛinv_mul, Matrix.toLin'_one]
        simp
    }
    continuous_toFun := LinearMap.continuous_of_finiteDimensional _
    continuous_invFun := LinearMap.continuous_of_finiteDimensional _
  }

/-- Composing a Schwartz function on NPointDomain with the inverse Lorentz action
    yields another Schwartz function. -/
noncomputable def lorentzCompSchwartz {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d))
    (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.piCongrRight (fun (_ : Fin n) => lorentzInvCLEquiv Λ)) f

/-- The pointwise evaluation of lorentzCompSchwartz: g(x) = f(Λ⁻¹ · x). -/
theorem lorentzCompSchwartz_apply {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d))
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (lorentzCompSchwartz Λ f).toFun x =
    f.toFun (fun i => Matrix.mulVec Λ.val⁻¹.val (x i)) := by
  simp only [lorentzCompSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.piCongrRight, lorentzInvCLEquiv]
  rfl

/-- After applying Lorentz COV, the composition g(Λx) = f(Λ⁻¹(Λx)) = f(x). -/
theorem lorentzCompSchwartz_comp_lorentz {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d))
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (lorentzCompSchwartz Λ f).toFun (fun i => Matrix.mulVec Λ.val.val (x i)) =
    f.toFun x := by
  rw [lorentzCompSchwartz_apply]
  congr 1; ext i j
  simp only [Matrix.mulVec_mulVec, lorentz_inv_mul_eq_one, Matrix.one_mulVec]

/-- **Lorentz covariance of distributional boundary values**
    (Streater-Wightman, §2.4; Jost, Ch. IV).

If F is holomorphic on the forward tube with distributional boundary values
equal to a Lorentz-covariant tempered distribution W_n, then the BV limit
of F(Λ · ) also gives W_n. That is, the distributional boundary values are
Lorentz covariant.

This combines three standard results:
1. Schwartz space S(ℝⁿ) is invariant under linear automorphisms (Rudin, FA §7.1)
2. Measure preservation: |det(diag(Λ,...,Λ))| = |det Λ|ⁿ = 1 for proper Lorentz Λ,
   so the change of variables ∫ g(Λx)f(x) dx = ∫ g(y)f(Λ⁻¹y) dy holds
   (Mathlib: `map_matrix_volume_pi_eq_smul_volume_pi`)
3. Wightman Lorentz covariance: W_n(f ∘ Λ⁻¹) = W_n(f) (axiom R5)

General form: applies to any holomorphic F on T_n whose BVs equal W_n,
not just the specific analytic continuation from spectrum_condition. -/
theorem lorentz_covariant_distributional_bv {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (_hF_hol : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)))
    (Λ : LorentzGroup.Restricted (d := d))
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n f)) := by
  -- Define the Lorentz-rotated direction and test function
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val.val μ ν * η k ν
  let g : SchwartzNPoint d n := lorentzCompSchwartz Λ f
  -- Λη is in the forward cone (successive differences preserved by Lorentz)
  have hΛη : InForwardCone d n Λη := by
    intro k
    -- The successive difference of Λη at k equals Λ applied to the successive difference of η
    have hk := hη k
    -- hk : InOpenForwardCone d (fun μ => η k μ - (if k.val = 0 then 0 else η ⟨k.val - 1, ..⟩) μ)
    -- Goal: InOpenForwardCone d (fun μ => Λη k μ - (if k.val = 0 then 0 else Λη ⟨k.val - 1, ..⟩) μ)
    -- Key: Λη k μ - prev μ = ∑ ν, Λ_μν * (η k ν - prev_η ν) by linearity of sum
    -- So the result follows from restricted_preserves_forward_cone
    let diff_η : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    have hdiff : InOpenForwardCone d diff_η := hk
    have hΛdiff := restricted_preserves_forward_cone Λ diff_η hdiff
    -- Now show the goal matches Λ · diff_η
    convert hΛdiff using 1
    ext μ
    simp only [Λη, diff_η]
    -- Goal: (∑ ν, Λ_μν * η k ν) - (if k.val = 0 then 0 else ∑ ν, Λ_μν * η ⟨k.val-1,..⟩ ν) =
    --       ∑ ν, Λ_μν * (η k ν - (if k.val = 0 then 0 else η ⟨k.val-1,..⟩) ν)
    split_ifs with h
    · simp [sub_zero]
    · rw [← Finset.sum_sub_distrib]
      congr 1; ext ν; ring
  -- Apply hF_bv with test function g and direction Λη
  have hbv_g := hF_bv g Λη hΛη
  -- By Lorentz covariance (R5), W n f = W n g
  have hWfg : Wfn.W n f = Wfn.W n g := by
    apply Wfn.lorentz_covariant n Λ.val f g
    exact fun x => lorentzCompSchwartz_apply Λ f x
  -- Show the integrals agree after COV
  suffices heq : ∀ ε : ℝ,
      ∫ x : NPointDomain d n,
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x) =
      ∫ y : NPointDomain d n,
        F (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) * (g y) by
    rw [hWfg]
    exact Filter.Tendsto.congr (fun ε => (heq ε).symm) hbv_g
  intro ε
  -- Step 1: Rewrite integrand by distributing Λ over the sum
  -- F(Λ(x + iεη)) = F(Λx + iεΛη)
  have hlin : ∀ x : NPointDomain d n,
      (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
        (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
      (fun k μ => ↑((fun i => Λ.val.val.mulVec (x i)) k μ) +
        ε * ↑(Λη k μ) * Complex.I) := by
    intro x; funext k μ
    simp only [Λη, Matrix.mulVec]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · -- ∑ ↑(Λ μ ν) * ↑(x k ν) = ↑((Λ μ ·) ⬝ᵥ x k)
      simp only [dotProduct]
      push_cast
      rfl
    · -- Pull ε * I out of the sum
      -- Goal: ∑ x, ↑(Λ μ x) * (↑ε * ↑(η k x) * I) = (↑ε * ∑ x, ↑(Λ μ x) * ↑(η k x)) * I
      conv_lhs =>
        arg 2; ext ν
        rw [show (↑(Λ.val.val μ ν) : ℂ) * (↑ε * ↑(η k ν) * Complex.I) =
            ↑ε * (↑(Λ.val.val μ ν) * ↑(η k ν)) * Complex.I from by ring]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
  -- Step 2: Apply COV via integral_lorentz_eq_self (backwards direction)
  -- integral_lorentz_eq_self says: ∫ x, h(Λx) = ∫ x, h(x)
  -- We use this with h(y) = F(↑y + iεΛη) · g(y)
  -- Then h(Λx) = F(↑(Λx) + iεΛη) · g(Λx) = F(↑(Λx) + iεΛη) · f(x)
  -- So: ∫ x, F(↑(Λx) + iεΛη) · f(x) = ∫ x, h(Λx) = ∫ y, h(y) = ∫ y, F(↑y + iεΛη) · g(y)
  -- Rewrite integrand using hlin
  have hlhs : (∫ x : NPointDomain d n,
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
        (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x)) =
    ∫ x : NPointDomain d n,
      (fun y => F (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) * (g y))
        (fun i => Λ.val.val.mulVec (x i)) := by
    congr 1; ext x
    rw [hlin x]
    congr 1
    exact (lorentzCompSchwartz_comp_lorentz Λ f x).symm
  rw [hlhs]
  exact integral_lorentz_eq_self Λ
    (fun y => F (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) * (g y))

/-- The set of Euclidean configurations whose Wick rotation does NOT lie in the
    permuted extended tube has Lebesgue measure zero.

    **Proof strategy (Jost's theorem):** A Wick-rotated configuration lies in
    the PET whenever some permutation σ makes the consecutive differences satisfy
    the Jost condition (spacelike with sufficient spatial spread for a complex
    Lorentz boost). The complement — configurations where NO permutation works —
    is contained in a finite union of proper algebraic subvarieties (coincident
    or collinear point configurations). Each such subvariety has codimension >= 1
    in ℝ^{n(d+1)}, hence Lebesgue measure zero (by induction on dimension + Fubini).

    Blocked by: (1) Jost characterization of PET membership (`swap_jost_set_exists`),
    and (2) Mathlib's algebraic-subvariety-measure-zero pipeline (not yet available).

    Ref: Jost, "The General Theory of Quantized Fields" §IV.4, Theorem IV.4;
    Streater-Wightman, Theorem 2-12 -/
theorem wickRotation_not_in_PET_null {d n : ℕ} [NeZero d] :
    MeasureTheory.volume
      {x : NPointDomain d n |
        (fun k => wickRotatePoint (x k)) ∉ PermutedExtendedTube d n} = 0 := by
  sorry

/-- **Almost every Euclidean Wick-rotated configuration lies in the permuted extended tube.**

    For a.e. configuration x = (x₁, ..., xₙ) of Euclidean spacetime points,
    the Wick-rotated configuration (iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) lies in the
    permuted extended tube T''_n.

    This is a consequence of Jost's theorem: the extended tube T'_n contains
    all "Jost points" (real points where consecutive differences are spacelike).
    The set of configurations that are NOT Jost points (after any permutation
    and complex Lorentz transformation) has measure zero.

    This suffices for all downstream uses: the Schwinger function properties
    (translation invariance, rotation invariance, permutation symmetry) are
    proved via integral identities that only need pointwise equality a.e.

    Ref: Jost, "The General Theory of Quantized Fields" §IV.4, Theorem IV.4;
    Streater-Wightman, Theorem 2-12 -/
theorem ae_euclidean_points_in_permutedTube {d n : ℕ} [NeZero d] :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n := by
  rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
  convert wickRotation_not_in_PET_null (d := d) (n := n) using 1

/-- The distributional boundary values of z ↦ W_analytic(Λz) and z ↦ W_analytic(z)
    agree, by Lorentz covariance of the Wightman distribution. -/
theorem W_analytic_lorentz_bv_agree
    (Wfn : WightmanFunctions d) (n : ℕ)
    (Λ : LorentzGroup.Restricted (d := d)) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          ((Wfn.spectrum_condition n).choose
            (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) -
           (Wfn.spectrum_condition n).choose
            (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  intro f η hη
  -- Strategy: Show both terms converge to W_n(f) individually, so their difference → 0.
  let W_a := (Wfn.spectrum_condition n).choose
  have hW_hol := (Wfn.spectrum_condition n).choose_spec.1
  have hW_bv := (Wfn.spectrum_condition n).choose_spec.2
  -- Term 2 limit: ∫ W_analytic(x + iεη) f(x) dx → W_n(f) by spectrum_condition
  have h_term2 : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        W_a (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n f)) := hW_bv f η hη
  -- Term 1 limit: ∫ W_analytic(Λ(x + iεη)) f(x) dx → W_n(f)
  -- by Lorentz covariance of distributional boundary values
  have h_term1 : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        W_a (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n f)) :=
    lorentz_covariant_distributional_bv (d := d) (n := n) Wfn W_a hW_hol hW_bv Λ f η hη
  -- The difference of two sequences both converging to W_n(f) converges to 0
  have hdiff := Filter.Tendsto.sub h_term1 h_term2
  simp only [sub_self] at hdiff
  -- Match the form: ∫ (F₁ - F₂) * f = ∫ F₁*f - ∫ F₂*f (using integral_sub for ε > 0)
  refine hdiff.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : ε ∈ Set.Ioi 0)
  rw [← MeasureTheory.integral_sub]
  · congr 1; ext x; ring
  · exact forward_tube_bv_integrable
      (fun z => W_a (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν))
      (W_analytic_lorentz_holomorphic Wfn n Λ)
      ⟨Wfn.W n, Wfn.tempered n, fun f' η' hη' =>
        lorentz_covariant_distributional_bv (d := d) (n := n)
          Wfn W_a hW_hol hW_bv Λ f' η' hη'⟩
      f η hη ε (Set.mem_Ioi.mp hε)
  · exact forward_tube_bv_integrable W_a hW_hol
      ⟨Wfn.W n, Wfn.tempered n, hW_bv⟩
      f η hη ε (Set.mem_Ioi.mp hε)


end
