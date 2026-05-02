/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction
import OSReconstruction.Wightman.Reconstruction.AnalyticContinuation
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.GeneralResults.SinusoidSeparation
import OSReconstruction.SCV.VladimirovTillmann

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

/-- A connected Lorentz transformation preserves the open forward light cone.

    If Λ ∈ SO⁺(1,d) and η ∈ V₊ (η₀ > 0, η² < 0), then Λη ∈ V₊.

    Part (a): Metric preservation — minkowskiNormSq(Λη) = minkowskiNormSq(η) < 0.
    Part (b): Time component positivity — (Λη)₀ > 0, using Λ₀₀ ≥ 1, Cauchy-Schwarz,
    and the hyperbolic bound.

    Ref: Streater-Wightman, §2.4 -/
theorem restricted_preserves_forward_cone
    (Λ : LorentzGroup d)
    (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η) :
    InOpenForwardCone d (fun μ => ∑ ν, Λ.val μ ν * η ν) := by
  obtain ⟨hη0_pos, hη_neg⟩ := hη
  constructor
  · -- Part (b): (Λη)₀ > 0
    -- (Λη)₀ = Λ₀₀ · η₀ + Σ_{j≠0} Λ₀ⱼ · ηⱼ
    -- By first_row_timelike: Λ₀₀² = 1 + Σ_{j≠0} Λ₀ⱼ²
    -- By Cauchy-Schwarz: |Σ_{j≠0} Λ₀ⱼ ηⱼ| ≤ √(Σ Λ₀ⱼ²) · √(Σ ηⱼ²)
    -- Since η ∈ V₊: η₀² > Σ ηⱼ² (from minkowskiNormSq < 0)
    -- And Λ₀₀ ≥ 1 (orthochronous)
    -- So (Λη)₀ ≥ η₀(Λ₀₀ - √(Λ₀₀² - 1)) > 0
    have hΛ_lorentz := Λ.property.1
    have hΛ_ortho : LorentzGroup.IsOrthochronous Λ := LorentzGroup.zero_zero_ge_one Λ
    have hΛ00 : Λ.val 0 0 ≥ 1 := hΛ_ortho
    have hrow := IsLorentzMatrix.first_row_timelike Λ.val hΛ_lorentz
    -- η is timelike: η₀² > spatial norm
    have hη_timelike : MinkowskiSpace.minkowskiNormSq d η < 0 := hη_neg
    have hη_time_dom : (η 0) ^ 2 > MinkowskiSpace.spatialNormSq d η :=
      MinkowskiSpace.timelike_time_dominates_space d η hη_timelike
    -- Split the sum into j=0 and j≠0
    have hsplit : (∑ ν : Fin (d + 1), Λ.val 0 ν * η ν) =
        Λ.val 0 0 * η 0 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : Fin (d + 1)))]
      simp [Finset.filter_eq', Finset.mem_univ]
    show (∑ ν : Fin (d + 1), Λ.val 0 ν * η ν) > 0
    rw [hsplit]
    -- Define spatial sums
    set SΛ := ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j ^ 2
    set Sη := MinkowskiSpace.spatialNormSq d η
    -- SΛ = Λ₀₀² - 1
    have hSΛ_eq : SΛ = Λ.val 0 0 ^ 2 - 1 := by linarith [hrow]
    have hSΛ_nonneg : SΛ ≥ 0 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hSη_nonneg : Sη ≥ 0 := MinkowskiSpace.spatialNormSq_nonneg d η
    -- Cauchy-Schwarz on spatial part
    have hCS_sq : (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j) ^ 2 ≤ SΛ * Sη := by
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
    have hCS : |∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j| ≤
        Real.sqrt SΛ * Real.sqrt Sη := by
      rw [← Real.sqrt_mul hSΛ_nonneg Sη, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hCS_sq
    have hbound : -(Real.sqrt SΛ * Real.sqrt Sη) ≤
        ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j := by
      linarith [neg_abs_le (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j), hCS]
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
    have hΛ_hyp : Λ.val 0 0 - Real.sqrt (Λ.val 0 0 ^ 2 - 1) > 0 := by
      have h1 : Λ.val 0 0 ^ 2 - 1 ≥ 0 := by nlinarith
      have h2 : Λ.val 0 0 > 0 := by linarith
      have h3 : Real.sqrt (Λ.val 0 0 ^ 2 - 1) < Λ.val 0 0 := by
        calc Real.sqrt (Λ.val 0 0 ^ 2 - 1)
            < Real.sqrt (Λ.val 0 0 ^ 2) := Real.sqrt_lt_sqrt h1 (by linarith)
          _ = Λ.val 0 0 := Real.sqrt_sq (le_of_lt h2)
      linarith
    -- Lower bound: (Λη)₀ = Λ₀₀η₀ + spatial ≥ Λ₀₀η₀ - √SΛ·√Sη
    --   > Λ₀₀η₀ - √SΛ·η₀ = η₀(Λ₀₀ - √(Λ₀₀²-1)) > 0
    -- We need √SΛ·√Sη ≤ √SΛ·η₀ (since √Sη < η₀)
    -- and Λ₀₀ - √SΛ = Λ₀₀ - √(Λ₀₀²-1) > 0
    have key : Λ.val 0 0 * η 0 +
        ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j > 0 := by
      have h_sqrt_SΛ_eq : Real.sqrt SΛ = Real.sqrt (Λ.val 0 0 ^ 2 - 1) := by
        congr 1
      -- The spatial sum is bounded below by -√SΛ·√Sη ≥ -√SΛ·η₀
      have h1 : ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j ≥
          -(Real.sqrt SΛ * η 0) := by
        calc ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j
            ≥ -(Real.sqrt SΛ * Real.sqrt Sη) := hbound
          _ ≥ -(Real.sqrt SΛ * η 0) := by
              apply neg_le_neg
              exact mul_le_mul_of_nonneg_left (le_of_lt hSη_lt_η0sq) (Real.sqrt_nonneg _)
      -- So (Λη)₀ ≥ Λ₀₀η₀ - √SΛ·η₀ = η₀(Λ₀₀ - √(Λ₀₀²-1))
      have h2 : Λ.val 0 0 * η 0 - Real.sqrt SΛ * η 0 > 0 := by
        rw [← sub_mul, h_sqrt_SΛ_eq]
        exact mul_pos hΛ_hyp hη0_pos'
      linarith
    exact key
  · -- Part (a): Metric preservation -- minkowskiNormSq(Lη) = minkowskiNormSq(η) < 0
    -- Uses the defining Lorentz property to show the Minkowski norm is preserved.
    have hΛ := Λ.property.1
    have hmetric : Λ.val.transpose * minkowskiMatrix d * Λ.val = minkowskiMatrix d := hΛ
    show MinkowskiSpace.minkowskiNormSq d (fun μ => ∑ ν, Λ.val μ ν * η ν) < 0
    -- The norm of Λη equals that of η by the Lorentz condition
    suffices hnorm_eq : MinkowskiSpace.minkowskiNormSq d (fun μ => ∑ ν, Λ.val μ ν * η ν) =
        MinkowskiSpace.minkowskiNormSq d η by
      rw [hnorm_eq]; exact hη_neg
    -- Expand both sides as quadratic forms and use the Lorentz matrix identity
    unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    simp only [MinkowskiSpace.metricSignature]
    -- Extract the Lorentz condition entry-wise: (ΛᵀηΛ)_νρ = η_νρ
    have hentry : ∀ ν ρ : Fin (d + 1),
        ∑ μ : Fin (d + 1), (if μ = 0 then (-1 : ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ =
        if ν = ρ then (if ν = 0 then (-1 : ℝ) else 1) else 0 := by
      intro ν ρ
      have h1 : (Λ.val.transpose * minkowskiMatrix d * Λ.val) ν ρ =
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
        ((if μ = 0 then (-1:ℝ) else 1) * ∑ ν, Λ.val μ ν * η ν) *
        (∑ ρ, Λ.val μ ρ * η ρ) =
        ∑ ν, ∑ ρ, (if μ = 0 then (-1:ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ *
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
        ∑ μ, (if μ = 0 then (-1:ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ * η ν * η ρ =
        ((if ν = ρ then (if ν = 0 then (-1:ℝ) else 1) else 0) * η ν * η ρ) := by
      intro ρ
      have hfactor : ∀ μ : Fin (d + 1),
          (if μ = 0 then (-1:ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ * η ν * η ρ =
          ((if μ = 0 then (-1:ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ) * (η ν * η ρ) := by
        intro μ; ring
      simp_rw [hfactor, ← Finset.sum_mul, hentry ν ρ]; ring
    simp_rw [hstep]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- An orthochronous Lorentz transformation preserves the open forward light cone.

This is the same geometric argument as `restricted_preserves_forward_cone`, but
it only uses the Lorentz condition together with `Λ₀₀ ≥ 1`; properness is not
needed. -/
theorem orthochronous_preserves_forward_cone
    (Λ : LorentzGroup d)
    (hΛ_ortho : LorentzGroup.IsOrthochronous Λ)
    (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η) :
    InOpenForwardCone d (fun μ => ∑ ν, Λ.val μ ν * η ν) := by
  obtain ⟨hη0_pos, hη_neg⟩ := hη
  constructor
  · have hΛ_lorentz := Λ.property.1
    have hΛ00 : Λ.val 0 0 ≥ 1 := hΛ_ortho
    have hrow := IsLorentzMatrix.first_row_timelike Λ.val hΛ_lorentz
    have hη_timelike : MinkowskiSpace.minkowskiNormSq d η < 0 := hη_neg
    have hη_time_dom : (η 0) ^ 2 > MinkowskiSpace.spatialNormSq d η :=
      MinkowskiSpace.timelike_time_dominates_space d η hη_timelike
    have hsplit : (∑ ν : Fin (d + 1), Λ.val 0 ν * η ν) =
        Λ.val 0 0 * η 0 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : Fin (d + 1)))]
      simp [Finset.filter_eq', Finset.mem_univ]
    show (∑ ν : Fin (d + 1), Λ.val 0 ν * η ν) > 0
    rw [hsplit]
    set SΛ := ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j ^ 2
    set Sη := MinkowskiSpace.spatialNormSq d η
    have hSΛ_eq : SΛ = Λ.val 0 0 ^ 2 - 1 := by linarith [hrow]
    have hSΛ_nonneg : SΛ ≥ 0 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hSη_nonneg : Sη ≥ 0 := MinkowskiSpace.spatialNormSq_nonneg d η
    have hCS_sq : (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j) ^ 2 ≤ SΛ * Sη := by
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
    have hCS : |∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j| ≤
        Real.sqrt SΛ * Real.sqrt Sη := by
      rw [← Real.sqrt_mul hSΛ_nonneg Sη, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hCS_sq
    have hbound : -(Real.sqrt SΛ * Real.sqrt Sη) ≤
        ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j := by
      linarith [neg_abs_le (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j), hCS]
    have hη0_sq_pos : (η 0) ^ 2 > Sη := hη_time_dom
    have hη0_pos' : η 0 > 0 := hη0_pos
    have hSη_lt_η0sq : Real.sqrt Sη < η 0 := by
      rw [← Real.sqrt_sq (le_of_lt hη0_pos')]
      exact Real.sqrt_lt_sqrt hSη_nonneg hη0_sq_pos
    have hΛ_hyp : Λ.val 0 0 - Real.sqrt (Λ.val 0 0 ^ 2 - 1) > 0 := by
      have h1 : Λ.val 0 0 ^ 2 - 1 ≥ 0 := by nlinarith
      have h2 : Λ.val 0 0 > 0 := by linarith
      have h3 : Real.sqrt (Λ.val 0 0 ^ 2 - 1) < Λ.val 0 0 := by
        calc Real.sqrt (Λ.val 0 0 ^ 2 - 1)
            < Real.sqrt (Λ.val 0 0 ^ 2) := Real.sqrt_lt_sqrt h1 (by linarith)
          _ = Λ.val 0 0 := Real.sqrt_sq (le_of_lt h2)
      linarith
    have key : Λ.val 0 0 * η 0 +
        ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j > 0 := by
      have h_sqrt_SΛ_eq : Real.sqrt SΛ = Real.sqrt (Λ.val 0 0 ^ 2 - 1) := by
        congr 1
      have h1 : ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j ≥
          -(Real.sqrt SΛ * η 0) := by
        calc ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ.val 0 j * η j
            ≥ -(Real.sqrt SΛ * Real.sqrt Sη) := hbound
          _ ≥ -(Real.sqrt SΛ * η 0) := by
              apply neg_le_neg
              exact mul_le_mul_of_nonneg_left (le_of_lt hSη_lt_η0sq) (Real.sqrt_nonneg _)
      have h2 : Λ.val 0 0 * η 0 - Real.sqrt SΛ * η 0 > 0 := by
        rw [← sub_mul, h_sqrt_SΛ_eq]
        exact mul_pos hΛ_hyp hη0_pos'
      linarith
    exact key
  · have hΛ := Λ.property.1
    show MinkowskiSpace.minkowskiNormSq d (fun μ => ∑ ν, Λ.val μ ν * η ν) < 0
    suffices hnorm_eq : MinkowskiSpace.minkowskiNormSq d (fun μ => ∑ ν, Λ.val μ ν * η ν) =
        MinkowskiSpace.minkowskiNormSq d η by
      rw [hnorm_eq]
      exact hη_neg
    unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    simp only [MinkowskiSpace.metricSignature]
    have hentry : ∀ ν ρ : Fin (d + 1),
        ∑ μ : Fin (d + 1), (if μ = 0 then (-1 : ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ =
        if ν = ρ then (if ν = 0 then (-1 : ℝ) else 1) else 0 := by
      intro ν ρ
      have h1 : (Λ.val.transpose * minkowskiMatrix d * Λ.val) ν ρ =
          (minkowskiMatrix d) ν ρ := by rw [hΛ]
      simp only [Matrix.mul_apply, minkowskiMatrix, Matrix.diagonal_apply,
        Matrix.transpose_apply, MinkowskiSpace.metricSignature] at h1
      convert h1 using 1
      apply Finset.sum_congr rfl
      intro μ _
      rw [Finset.sum_eq_single μ]
      · by_cases hμ : μ = 0 <;> simp [hμ]
      · intro k _ hk; simp [hk]
      · simp
    have hlhs : ∀ μ : Fin (d + 1),
        ((if μ = 0 then (-1:ℝ) else 1) * ∑ ν, Λ.val μ ν * η ν) *
        (∑ ρ, Λ.val μ ρ * η ρ) =
        ∑ ν, ∑ ρ, (if μ = 0 then (-1:ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ *
          η ν * η ρ := by
      intro μ
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ν _
      apply Finset.sum_congr rfl
      intro ρ _
      ring
    simp_rw [hlhs]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_comm]
    have hstep : ∀ ρ : Fin (d + 1),
        ∑ μ, (if μ = 0 then (-1:ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ * η ν * η ρ =
        ((if ν = ρ then (if ν = 0 then (-1:ℝ) else 1) else 0) * η ν * η ρ) := by
      intro ρ
      have hfactor : ∀ μ : Fin (d + 1),
          (if μ = 0 then (-1:ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ * η ν * η ρ =
          ((if μ = 0 then (-1:ℝ) else 1) * Λ.val μ ν * Λ.val μ ρ) * (η ν * η ρ) := by
        intro μ
        ring
      simp_rw [hfactor, ← Finset.sum_mul, hentry ν ρ]
      ring
    simp_rw [hstep]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- A connected Lorentz transformation preserves the forward tube.

    If Λ ∈ SO⁺(1,d) and z ∈ ForwardTube, then Λz ∈ ForwardTube.
    Key: Λ is real, so Im(Λz_k) = Λ · Im(z_k). The successive differences
    Im((Λz)_k - (Λz)_{k-1}) = Λ · Im(z_k - z_{k-1}) ∈ V₊. -/
theorem restricted_preserves_forward_tube
    (Λ : LorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν) ∈ ForwardTube d n := by
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
  suffices h : InOpenForwardCone d (fun μ => ∑ ν, Λ.val μ ν * η_k ν) by
    -- Show the goal (from ForwardTube unfolding) matches our suffices
    -- The key: for real Λ, Im(Σ_ν Λ_μν * z_ν) = Σ_ν Λ_μν * Im(z_ν)
    -- So Im of difference = Λ applied to Im of difference = Λ · η_k
    -- The imaginary part of the Lorentz-rotated difference equals Λ · η_k
    -- because Λ is real: Im(Σ_ν Λ_μν * z_ν) = Σ_ν Λ_μν * Im(z_ν)
    -- Key fact: Im distributes over sums and Im(r * z) = r * Im(z) for r ∈ ℝ
    have him_linear : ∀ (w : Fin (d + 1) → ℂ) (μ : Fin (d + 1)),
        (∑ ν, (Λ.val μ ν : ℂ) * w ν).im = ∑ ν, Λ.val μ ν * (w ν).im := by
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

/-- An orthochronous Lorentz transformation preserves the forward tube.

This is the same forward-tube geometry as `restricted_preserves_forward_tube`,
but only uses preservation of the open forward cone, so properness is not
needed. -/
theorem orthochronous_preserves_forward_tube
    (Λ : LorentzGroup d) (hΛ_ortho : LorentzGroup.IsOrthochronous Λ)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν) ∈ ForwardTube d n := by
  intro k
  let prev_z := if h : k.val = 0 then (0 : Fin (d + 1) → ℂ) else z ⟨k.val - 1, by omega⟩
  have hk := hz k
  let η_k : Fin (d + 1) → ℝ := fun μ => (z k μ - prev_z μ).im
  suffices h : InOpenForwardCone d (fun μ => ∑ ν, Λ.val μ ν * η_k ν) by
    have him_linear : ∀ (w : Fin (d + 1) → ℂ) (μ : Fin (d + 1)),
        (∑ ν, (Λ.val μ ν : ℂ) * w ν).im = ∑ ν, Λ.val μ ν * (w ν).im := by
      intro w μ
      rw [Complex.im_sum]
      apply Finset.sum_congr rfl
      intro ν _
      exact Complex.im_ofReal_mul _ _
    convert h using 1
    ext μ
    simp only [Complex.sub_im]
    rw [him_linear (z k) μ]
    split_ifs with h0
    · simp only [Pi.zero_apply, Complex.zero_im, sub_zero]
      apply Finset.sum_congr rfl
      intro ν _
      congr 1
      show (z k ν).im = (z k ν - prev_z ν).im
      simp [prev_z, h0]
    · rw [him_linear (z ⟨k.val - 1, by omega⟩) μ]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ν _
      rw [← mul_sub]
      congr 1
      show (z k ν).im - (z ⟨k.val - 1, by omega⟩ ν).im = (z k ν - prev_z ν).im
      simp [prev_z, h0, Complex.sub_im]
  exact orthochronous_preserves_forward_cone (d := d) Λ hΛ_ortho η_k hk

/-- The composition z ↦ W_analytic(Λz) is holomorphic on the forward tube
    when Λ ∈ SO⁺(1,d), since z ↦ Λz is ℂ-linear and preserves the forward tube. -/
theorem W_analytic_lorentz_holomorphic
    (Wfn : WightmanFunctions d) (n : ℕ)
    (Λ : LorentzGroup d) :
    DifferentiableOn ℂ
      (fun z => (Wfn.spectrum_condition n).choose
        (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν))
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
          ∑ ν ∈ s, (↑(Λ.val μ ν) : ℂ) * x k ν) z by
      exact h Finset.univ
    intro s
    induction s using Finset.induction with
    | empty => simp [differentiableAt_const]
    | @insert ν s hν ih =>
      simp only [Finset.sum_insert hν]
      exact ((differentiableAt_const _).mul (hcoord k ν)).add ih
  · intro z hz
    exact restricted_preserves_forward_tube Λ z hz

/-- Global forward-tube polynomial growth is stable under real Lorentz
    precomposition. -/
theorem forward_tube_lorentz_growth
    {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup d)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_growth : ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ z, z ∈ ForwardTube d n → ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ z, z ∈ ForwardTube d n →
        ‖F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν)‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  obtain ⟨C_bd₀, N, hC₀, hF_growth⟩ := hF_growth
  let A : ℝ := ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1), ‖(Λ.val μ ν : ℂ)‖
  have hA_nonneg : 0 ≤ A := by
    unfold A
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C_bd₀ * (1 + A) ^ N, N, by positivity, ?_⟩
  intro z hz
  have hz_tube :
      (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν) ∈ ForwardTube d n :=
    restricted_preserves_forward_tube Λ z hz
  have hAz :
      ‖(fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν)‖ ≤ A * ‖z‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hA_nonneg (norm_nonneg z))).2 ?_
    intro k
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hA_nonneg (norm_nonneg z))).2 ?_
    intro μ
    calc
      ‖∑ ν, (Λ.val μ ν : ℂ) * z k ν‖ ≤ ∑ ν, ‖(Λ.val μ ν : ℂ) * z k ν‖ := norm_sum_le _ _
      _ = ∑ ν, ‖(Λ.val μ ν : ℂ)‖ * ‖z k ν‖ := by simp
      _ ≤ ∑ ν, ‖(Λ.val μ ν : ℂ)‖ * ‖z‖ := by
            refine Finset.sum_le_sum ?_
            intro ν _
            gcongr
            exact (norm_le_pi_norm (z k) ν).trans (norm_le_pi_norm z k)
      _ = (∑ ν, ‖(Λ.val μ ν : ℂ)‖) * ‖z‖ := by rw [Finset.sum_mul]
      _ ≤ A * ‖z‖ := by
            have hrow : ∑ ν, ‖(Λ.val μ ν : ℂ)‖ ≤ A := by
              unfold A
              have hnonneg :
                  ∀ μ' ∈ (Finset.univ : Finset (Fin (d + 1))),
                    0 ≤ ∑ ν : Fin (d + 1), ‖(Λ.val μ' ν : ℂ)‖ := by
                intro μ' _
                exact Finset.sum_nonneg fun ν _ => norm_nonneg _
              exact Finset.single_le_sum
                hnonneg
                (by exact Finset.mem_univ μ)
            exact mul_le_mul_of_nonneg_right hrow (norm_nonneg z)
  have hnorm :
      1 + ‖(fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν)‖ ≤ (1 + A) * (1 + ‖z‖) := by
    have hnorm' : 1 + ‖(fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν)‖ ≤ 1 + A * ‖z‖ := by
      linarith
    have hprod : 1 + A * ‖z‖ ≤ (1 + A) * (1 + ‖z‖) := by
      nlinarith [hA_nonneg, norm_nonneg z]
    exact hnorm'.trans hprod
  calc
    ‖F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν)‖
        ≤ C_bd₀ * (1 + ‖(fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν)‖) ^ N :=
      hF_growth _ hz_tube
    _ ≤ C_bd₀ * ((1 + A) * (1 + ‖z‖)) ^ N := by
          gcongr
    _ = C_bd₀ * (1 + A) ^ N * (1 + ‖z‖) ^ N := by rw [mul_pow]; ring
    _ = (C_bd₀ * (1 + A) ^ N) * (1 + ‖z‖) ^ N := by ring

/-! ### Textbook Axioms

These are standard results from distribution theory and functional analysis
that we axiomatize to avoid lengthy measure-theoretic plumbing. Each is a
well-known textbook theorem stated at greater generality than the specific
instances used here.
-/

/-- The forward cone is salient: its closure contains no complete line. -/
theorem forwardConeAbs_salient (d n : ℕ) [NeZero d] :
    IsSalientCone (ForwardConeAbs d n) := by
  intro y hy hny
  have h_time_diff_zero : ∀ j : Fin n,
      y j 0 - (if h : j.val = 0 then 0 else y ⟨j.val - 1, by omega⟩ 0) = 0 := by
    intro j
    have hδ_cont : Continuous (fun w : Fin n → Fin (d + 1) → ℝ =>
        w j 0 - if h : j.val = 0 then 0 else w (⟨j.val - 1, by omega⟩ : Fin n) 0) := by
      apply Continuous.sub ((continuous_apply (0 : Fin (d + 1))).comp (continuous_apply j))
      split_ifs with h
      · exact continuous_const
      · exact (continuous_apply (0 : Fin (d + 1))).comp
          (continuous_apply (⟨j.val - 1, by omega⟩ : Fin n))
    have hprev_eq : ∀ (w : Fin n → Fin (d + 1) → ℝ) (ν : Fin (d + 1)),
        (if h : j.val = 0 then (0 : Fin (d + 1) → ℝ) else w (⟨j.val - 1, by omega⟩ : Fin n)) ν =
        (if h : j.val = 0 then 0 else w (⟨j.val - 1, by omega⟩ : Fin n) ν) := by
      intro w ν
      split_ifs <;> simp
    have h_nonneg : 0 ≤ y j 0 - (if h : j.val = 0 then 0 else y ⟨j.val - 1, by omega⟩ 0) := by
      have hForward_sub : ForwardConeAbs d n ⊆
          {w : Fin n → Fin (d + 1) → ℝ | (0 : ℝ) <
            w j 0 - if h : j.val = 0 then 0 else w (⟨j.val - 1, by omega⟩ : Fin n) 0} := by
        intro w hw
        have h1 := (hw j).1
        simp only [hprev_eq] at h1
        exact h1
      exact (closure_lt_subset_le continuous_const hδ_cont) (closure_mono hForward_sub hy)
    have h_nonpos : y j 0 - (if h : j.val = 0 then 0 else y ⟨j.val - 1, by omega⟩ 0) ≤ 0 := by
      have hForward_sub : ForwardConeAbs d n ⊆
          {w : Fin n → Fin (d + 1) → ℝ | (0 : ℝ) <
            w j 0 - if h : j.val = 0 then 0 else w (⟨j.val - 1, by omega⟩ : Fin n) 0} := by
        intro w hw
        have h1 := (hw j).1
        simp only [hprev_eq] at h1
        exact h1
      have h1 : 0 ≤ (-y) j 0 - (if h : j.val = 0 then 0 else (-y) (⟨j.val - 1, by omega⟩ : Fin n) 0) :=
        (closure_lt_subset_le continuous_const hδ_cont) (closure_mono hForward_sub hny)
      have heq :
          (-y) j 0 - (if h : j.val = 0 then 0 else (-y) (⟨j.val - 1, by omega⟩ : Fin n) 0) =
            -(y j 0 - (if h : j.val = 0 then 0 else y ⟨j.val - 1, by omega⟩ 0)) := by
        simp only [Pi.neg_apply]
        split_ifs <;> ring
      linarith [heq ▸ h1]
    linarith
  have h_all_diff_zero : ∀ j : Fin n, ∀ μ : Fin (d + 1),
      y j μ - (if h : j.val = 0 then 0 else y ⟨j.val - 1, by omega⟩ μ) = 0 := by
    intro j μ
    by_cases hμ : μ = 0
    · subst hμ
      exact h_time_diff_zero j
    · let spatial_sq_sum : (Fin n → Fin (d + 1) → ℝ) → ℝ := fun w =>
        ∑ i : Fin d, (w j (Fin.succ i) -
          (if h : j.val = 0 then 0 else w (⟨j.val - 1, by omega⟩ : Fin n) (Fin.succ i))) ^ 2
      have hS_cont : Continuous spatial_sq_sum := by
        apply continuous_finset_sum
        intro i _
        apply Continuous.pow
        apply Continuous.sub
        · exact (continuous_apply (Fin.succ i)).comp (continuous_apply j)
        · split_ifs with h
          · exact continuous_const
          · exact (continuous_apply (Fin.succ i)).comp
              (continuous_apply (⟨j.val - 1, by omega⟩ : Fin n))
      have h_spatial_nonpos : spatial_sq_sum y ≤ 0 := by
        let time_sq : (Fin n → Fin (d + 1) → ℝ) → ℝ := fun w =>
          (w j 0 - (if h : j.val = 0 then 0 else w (⟨j.val - 1, by omega⟩ : Fin n) 0)) ^ 2
        have hT_cont : Continuous time_sq := by
          apply Continuous.pow
          apply Continuous.sub
          · exact (continuous_apply (0 : Fin (d + 1))).comp (continuous_apply j)
          · split_ifs with h
            · exact continuous_const
            · exact (continuous_apply (0 : Fin (d + 1))).comp
                (continuous_apply (⟨j.val - 1, by omega⟩ : Fin n))
        have h_on_cone : ∀ w ∈ ForwardConeAbs d n, spatial_sq_sum w ≤ time_sq w := by
          intro w hw
          have hj := hw j
          have hQ := MinkowskiSpace.minkowskiNormSq_eq d
            (fun ν => w j ν - (if h : j.val = 0 then 0 else w (⟨j.val - 1, by omega⟩ : Fin n) ν))
          simp only [MinkowskiSpace.timeComponent, MinkowskiSpace.spatialComponents] at hQ
          have hfun_eq :
              (fun μ => w j μ -
                (if h : j.val = 0 then (0 : Fin (d + 1) → ℝ) else
                  w (⟨j.val - 1, by omega⟩ : Fin n)) μ) =
              (fun ν => w j ν - if h : j.val = 0 then 0 else
                w (⟨j.val - 1, by omega⟩ : Fin n) ν) := by
            ext ν
            split_ifs <;> simp [Pi.zero_apply]
          have hj2 : MinkowskiSpace.minkowskiNormSq d
              (fun ν => w j ν - (if h : j.val = 0 then 0 else
                w (⟨j.val - 1, by omega⟩ : Fin n) ν)) < 0 := by
            rw [← hfun_eq]
            exact hj.2
          linarith [hj2, hQ]
        have h_le : spatial_sq_sum y ≤ time_sq y :=
          closure_minimal h_on_cone (isClosed_le hS_cont hT_cont) hy
        have h_time_sq_zero : time_sq y = 0 := by
          show (y j 0 - (if h : j.val = 0 then 0 else y ⟨j.val - 1, by omega⟩ 0)) ^ 2 = 0
          rw [h_time_diff_zero j]
          ring
        linarith
      have h_each_zero : ∀ i : Fin d,
          (y j (Fin.succ i) -
            (if h : j.val = 0 then 0 else y ⟨j.val - 1, by omega⟩ (Fin.succ i))) ^ 2 = 0 :=
        fun i => le_antisymm
          (le_trans
            (Finset.single_le_sum
              (fun k _ => sq_nonneg (y j (Fin.succ k) -
                (if h : j.val = 0 then 0 else y ⟨j.val - 1, by omega⟩ (Fin.succ k))))
              (Finset.mem_univ i))
            h_spatial_nonpos)
          (sq_nonneg _)
      have hμ_pos : 0 < μ := Fin.pos_of_ne_zero hμ
      have hμ_pred : μ = Fin.succ ⟨μ.val - 1, by omega⟩ := by
        ext
        simp
        omega
      rw [hμ_pred]
      have := h_each_zero ⟨μ.val - 1, by omega⟩
      rwa [sq_eq_zero_iff] at this
  ext k μ
  suffices ∀ m : ℕ, ∀ k : Fin n, k.val = m → y k μ = 0 by
    exact this k.val k rfl
  intro m
  induction m with
  | zero =>
      intro k hk
      have := h_all_diff_zero k μ
      have hk0 : k.val = 0 := hk
      simp only [hk0, ↓reduceDIte] at this
      linarith
  | succ m ih =>
      intro k hk
      have hkv : ¬k.val = 0 := by omega
      have hd := h_all_diff_zero k μ
      simp only [hkv, ↓reduceDIte] at hd
      have hpred_lt : k.val - 1 < n := by omega
      have hprev : y ⟨k.val - 1, hpred_lt⟩ μ = 0 :=
        ih ⟨k.val - 1, hpred_lt⟩
          (show (⟨k.val - 1, hpred_lt⟩ : Fin n).val = m by simp; omega)
      linarith

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
    (hF_growth : ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ z, z ∈ ForwardTube d n → ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (h_bv : ∃ (W : SchwartzNPoint d n →L[ℂ] ℂ),
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W f)))
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η)
    (ε : ℝ) (hε : ε > 0) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      MeasureTheory.volume := by
  obtain ⟨C_bd₀, N, hC₀, hgrowth₀⟩ := hF_growth
  let shift : Fin n → Fin (d + 1) → ℂ := fun k μ => ε * ↑(η k μ) * Complex.I
  have hshift_nonneg : 0 ≤ ‖shift‖ := norm_nonneg _
  have h_in_tube : ∀ x : NPointDomain d n,
      (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) ∈ ForwardTube d n := by
    intro x k
    have hk := hη k
    let diff : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    suffices hsuff : InOpenForwardCone d (fun μ => ε * diff μ) by
      convert hsuff using 1
      ext μ
      simp only [diff]
      split_ifs with h
      · simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im]
      · simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im]
        ring
    obtain ⟨hk0, hkneg⟩ := hk
    refine ⟨mul_pos hε hk0, ?_⟩
    show MinkowskiSpace.minkowskiNormSq d (fun μ => ε * diff μ) < 0
    simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
    have hsq :
        ∑ i : Fin (d + 1), MinkowskiSpace.metricSignature d i * (ε * diff i) * (ε * diff i) =
          ε ^ 2 * ∑ i : Fin (d + 1), MinkowskiSpace.metricSignature d i * diff i * diff i := by
      rw [Finset.mul_sum]
      congr 1
      ext i
      ring
    rw [hsq]
    exact mul_neg_of_pos_of_neg (pow_pos hε 2) hkneg
  obtain ⟨C_bd, N, hC, hgrowth⟩ : ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ x : NPointDomain d n,
        ‖F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
    refine ⟨C_bd₀ * (1 + ‖shift‖) ^ N, N, by positivity, ?_⟩
    intro x
    have hofReal_norm :
        ‖(fun k μ => (↑(x k μ) : ℂ))‖ ≤ ‖x‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_
      intro k
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_
      intro μ
      simpa using (norm_le_pi_norm (x k) μ).trans (norm_le_pi_norm x k)
    have hslice_norm :
        ‖(fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖ ≤ ‖x‖ + ‖shift‖ := by
      calc
        ‖(fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖
            ≤ ‖(fun k μ => (↑(x k μ) : ℂ))‖ + ‖shift‖ := by
              simpa [shift] using
                norm_add_le (fun k μ => (↑(x k μ) : ℂ)) shift
        _ ≤ ‖x‖ + ‖shift‖ := by gcongr
    have hslice_growth :
        1 + ‖(fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖ ≤
          (1 + ‖shift‖) * (1 + ‖x‖) := by
      have hstep :
          1 + ‖(fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖ ≤
            1 + (‖x‖ + ‖shift‖) := by
        linarith
      have hprod : 1 + (‖x‖ + ‖shift‖) ≤ (1 + ‖shift‖) * (1 + ‖x‖) := by
        nlinarith [norm_nonneg x, hshift_nonneg]
      exact hstep.trans hprod
    calc
      ‖F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖
          ≤ C_bd₀ * (1 + ‖(fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖) ^ N :=
        hgrowth₀ _ (h_in_tube x)
      _ ≤ C_bd₀ * ((1 + ‖shift‖) * (1 + ‖x‖)) ^ N := by
            gcongr
      _ = C_bd₀ * (1 + ‖shift‖) ^ N * (1 + ‖x‖) ^ N := by rw [mul_pow]; ring
      _ = (C_bd₀ * (1 + ‖shift‖) ^ N) * (1 + ‖x‖) ^ N := by ring
  -- Measurability: the slice map x ↦ F(x + εηi) is continuous since F is holomorphic
  -- on the forward tube and the affine embedding maps into it
  have hg_meas : MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d n => F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
      MeasureTheory.volume :=
    forward_tube_slice_aestrongly_measurable F hF η hη ε hε
  exact polynomial_growth_mul_schwartz_integrable
    (fun x : NPointDomain d n => F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
    hg_meas C_bd N hC hgrowth f

/-- Extract the matrix product identities for a connected Lorentz transformation. -/
theorem lorentz_mul_inv_eq_one {d : ℕ} [NeZero d]
    (Λ : LorentzGroup d) :
    Λ.val * Λ⁻¹.val = 1 := by
  have h1 : (Λ * Λ⁻¹).val = (1 : LorentzGroup d).val :=
    congrArg (fun g : LorentzGroup d => g.val) (mul_inv_cancel Λ)
  rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
  exact h1

theorem lorentz_inv_mul_eq_one {d : ℕ} [NeZero d]
    (Λ : LorentzGroup d) :
    Λ⁻¹.val * Λ.val = 1 := by
  have h1 : (Λ⁻¹ * Λ).val = (1 : LorentzGroup d).val :=
    congrArg (fun g : LorentzGroup d => g.val) (inv_mul_cancel Λ)
  rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
  exact h1

/-- The componentwise Lorentz action on NPointDomain preserves Lebesgue measure.

    Follows the same pattern as `integral_orthogonal_eq_self` but uses
    `|det Λ| = 1` from properness instead of orthogonality. -/
theorem integral_lorentz_eq_self {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup d)
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => Matrix.mulVec Λ.val (x i)) =
    ∫ x : NPointDomain d n, h x := by
  have hdet_ne : Λ.val.det ≠ 0 := by
    rw [LorentzGroup.det_eq_one Λ]
    exact one_ne_zero
  have habs : |Λ.val.det| = 1 := by
    rw [LorentzGroup.det_eq_one Λ]
    simp
  have hΛ_mul_inv := lorentz_mul_inv_eq_one Λ
  have hΛinv_mul := lorentz_inv_mul_eq_one Λ
  have hmv : (fun v => Λ.val.mulVec v) = Matrix.toLin' Λ.val := by
    ext v; simp [Matrix.toLin'_apply]
  have hcont_Λ : Continuous (Matrix.toLin' Λ.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcont_Λinv : Continuous (Matrix.toLin' Λ⁻¹.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hmp_factor : MeasureTheory.MeasurePreserving
      (fun v : Fin (d+1) → ℝ => Λ.val.mulVec v)
      MeasureTheory.volume MeasureTheory.volume := by
    rw [hmv]; constructor
    · exact hcont_Λ.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet_ne]
      simp [abs_inv, habs]
  let e : (Fin n → Fin (d+1) → ℝ) ≃ᵐ (Fin n → Fin (d+1) → ℝ) :=
    { toEquiv := {
        toFun := fun a i => Λ.val.mulVec (a i)
        invFun := fun a i => Λ⁻¹.val.mulVec (a i)
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
    (Λ : LorentzGroup d) :
    (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) := by
  have hΛinv_mul := lorentz_inv_mul_eq_one Λ
  have hΛ_mul_inv := lorentz_mul_inv_eq_one Λ
  exact {
    toLinearEquiv := {
      toLinearMap := (Matrix.toLin' Λ⁻¹.val)
      invFun := Matrix.toLin' Λ.val
      left_inv := fun v => by
        show (Matrix.toLin' Λ.val) ((Matrix.toLin' Λ⁻¹.val) v) = v
        rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛ_mul_inv, Matrix.toLin'_one]
        simp
      right_inv := fun v => by
        show (Matrix.toLin' Λ⁻¹.val) ((Matrix.toLin' Λ.val) v) = v
        rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛinv_mul, Matrix.toLin'_one]
        simp
    }
    continuous_toFun := LinearMap.continuous_of_finiteDimensional _
    continuous_invFun := LinearMap.continuous_of_finiteDimensional _
  }

/-- Composing a Schwartz function on NPointDomain with the inverse Lorentz action
    yields another Schwartz function. -/
noncomputable def lorentzCompSchwartz {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup d)
    (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.piCongrRight (fun (_ : Fin n) => lorentzInvCLEquiv Λ)) f

/-- The pointwise evaluation of lorentzCompSchwartz: g(x) = f(Λ⁻¹ · x). -/
theorem lorentzCompSchwartz_apply {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup d)
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (lorentzCompSchwartz Λ f).toFun x =
    f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
  simp only [lorentzCompSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.piCongrRight, lorentzInvCLEquiv]
  rfl

/-- After applying Lorentz COV, the composition g(Λx) = f(Λ⁻¹(Λx)) = f(x). -/
theorem lorentzCompSchwartz_comp_lorentz {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup d)
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (lorentzCompSchwartz Λ f).toFun (fun i => Matrix.mulVec Λ.val (x i)) =
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
theorem lorentz_covariant_distributional_bv_of_restrictedCovariance
    {d n : ℕ} [NeZero d]
    (W_n : SchwartzNPoint d n → ℂ)
    (_hW_linear : IsLinearMap ℂ W_n)
    (_hW_cont : Continuous W_n)
    (hW_lorentz :
      ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (_hF_hol : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (Λ : LorentzGroup d)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n f)) := by
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val μ ν * η k ν
  let g : SchwartzNPoint d n := lorentzCompSchwartz Λ f
  have hΛη : InForwardCone d n Λη := by
    intro k
    have hk := hη k
    let diff_η : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    have hdiff : InOpenForwardCone d diff_η := hk
    have hΛdiff := restricted_preserves_forward_cone Λ diff_η hdiff
    convert hΛdiff using 1
    ext μ
    simp only [Λη, diff_η]
    split_ifs with h
    · simp [sub_zero]
    · rw [← Finset.sum_sub_distrib]
      congr 1
      ext ν
      ring
  have hbv_g := hF_bv g Λη hΛη
  have hWfg : W_n f = W_n g := by
    apply hW_lorentz Λ f g
    exact fun x => lorentzCompSchwartz_apply Λ f x
  suffices heq : ∀ ε : ℝ,
      ∫ x : NPointDomain d n,
        F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x) =
      ∫ y : NPointDomain d n,
        F (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) * (g y) by
    rw [hWfg]
    exact Filter.Tendsto.congr (fun ε => (heq ε).symm) hbv_g
  intro ε
  have hlin : ∀ x : NPointDomain d n,
      (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
        (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
      (fun k μ => ↑((fun i => Λ.val.mulVec (x i)) k μ) +
        ε * ↑(Λη k μ) * Complex.I) := by
    intro x
    funext k μ
    simp only [Λη, Matrix.mulVec]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · simp only [dotProduct]
      push_cast
      rfl
    · conv_lhs =>
        arg 2
        ext ν
        rw [show (↑(Λ.val μ ν) : ℂ) * (↑ε * ↑(η k ν) * Complex.I) =
            ↑ε * (↑(Λ.val μ ν) * ↑(η k ν)) * Complex.I from by ring]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hlhs : (∫ x : NPointDomain d n,
      F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
        (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x)) =
    ∫ x : NPointDomain d n,
        (fun y => F (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) * (g y))
        (fun i => Λ.val.mulVec (x i)) := by
    congr 1
    ext x
    rw [hlin x]
    congr 1
    exact (lorentzCompSchwartz_comp_lorentz Λ f x).symm
  rw [hlhs]
  exact integral_lorentz_eq_self Λ
    (fun y => F (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) * (g y))

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
    (Λ : LorentzGroup d)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n f)) :=
  lorentz_covariant_distributional_bv_of_restrictedCovariance
    (d := d) (n := n)
    (Wfn.W n) (Wfn.linear n) (Wfn.tempered n)
    (fun Λ f g hfg => Wfn.lorentz_covariant n Λ f g hfg)
    F _hF_hol hF_bv Λ f η hη

/-! ### W11: A.e. Wick-rotated Euclidean configs lie in the PET

The standard physics forward tube uses only n-1 difference conditions, with
no basepoint condition on `z₀`. Our `ForwardTube` definition adds `Im(z₀) ∈ V⁺`,
making the PET slightly smaller. The `TranslatedPET` below corrects for this by
allowing a uniform complex translation (which cancels in differences).

See `W11Counterexample.lean` for a proof that the original statement using
`PermutedExtendedTube` directly is false for n ≥ d+2.

Ref: Jost, "The General Theory of Quantized Fields" §IV.4, Theorem IV.4;
Streater-Wightman, Theorem 2-12 -/

/-- The translated permuted extended tube: configurations that lie in the PET
    after a uniform complex translation. The translation cancels in differences,
    so this only relaxes the k=0 basepoint condition `Im(z₀) ∈ V⁺`. -/
def TranslatedPET (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∃ c : Fin (d + 1) → ℂ, (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n }

/-- The PET is contained in the translated PET (take c = 0). -/
theorem PermutedExtendedTube_subset_TranslatedPET {d n : ℕ} [NeZero d] :
    PermutedExtendedTube d n ⊆ TranslatedPET d n := by
  intro z hz
  exact ⟨0, by simpa using hz⟩

/-- `TranslatedPET` is stable under uniform complex translations. -/
theorem translatedPET_translate {d n : ℕ} [NeZero d]
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ TranslatedPET d n)
    (c : Fin (d + 1) → ℂ) :
    (fun k μ => z k μ + c μ) ∈ TranslatedPET d n := by
  rcases hz with ⟨a, ha⟩
  refine ⟨fun μ => a μ - c μ, ?_⟩
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ha

/-- Translation by a uniform complex vector is an equivalence on
`TranslatedPET`. -/
theorem translatedPET_translate_iff {d n : ℕ} [NeZero d]
    (z : Fin n → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ) :
    (fun k μ => z k μ + c μ) ∈ TranslatedPET d n ↔
      z ∈ TranslatedPET d n := by
  constructor
  · intro hz
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      translatedPET_translate (d := d) (n := n) hz (-c)
  · intro hz
    exact translatedPET_translate (d := d) (n := n) hz c

/-- `TranslatedPET` is open: it is the union of translated preimages of the
open permuted extended tube. -/
theorem isOpen_translatedPET {d n : ℕ} [NeZero d] :
    IsOpen (TranslatedPET d n) := by
  rw [TranslatedPET]
  have hset :
      {z : Fin n → Fin (d + 1) → ℂ |
        ∃ c : Fin (d + 1) → ℂ,
          (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n} =
        ⋃ c : Fin (d + 1) → ℂ,
          {z : Fin n → Fin (d + 1) → ℂ |
            (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n} := by
    ext z
    simp
  rw [hset]
  refine isOpen_iUnion fun c => ?_
  have hcont :
      Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          fun k μ => z k μ + c μ) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    have hk :
        Continuous
          (fun z : Fin n → Fin (d + 1) → ℂ => z k) :=
      continuous_apply k
    have hcoord :
        Continuous
          (fun z : Fin n → Fin (d + 1) → ℂ => z k μ) :=
      (continuous_apply μ).comp hk
    exact hcoord.add continuous_const
  exact
    (BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube).preimage
      hcont

/-- The permuted extended tube is stable under coordinate permutations. -/
theorem permutedExtendedTube_perm {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ PermutedExtendedTube d n) :
    (fun k => z (σ k)) ∈ PermutedExtendedTube d n := by
  rw [← BHW_permutedExtendedTube_eq (d := d) (n := n)] at hz ⊢
  obtain ⟨π, hπ⟩ := Set.mem_iUnion.mp hz
  rcases hπ with ⟨Λ, w, hw, hzw⟩
  refine Set.mem_iUnion.mpr ⟨σ.symm * π, ⟨Λ, fun k => w (σ k), ?_, ?_⟩⟩
  · simpa [BHW.PermutedForwardTube] using hw
  · ext k μ
    simp [hzw, BHW.complexLorentzAction]

/-- `TranslatedPET` is stable under coordinate permutations. -/
theorem translatedPET_perm {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ TranslatedPET d n) :
    (fun k => z (σ k)) ∈ TranslatedPET d n := by
  rcases hz with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  simpa using permutedExtendedTube_perm (d := d) (n := n) σ hc

/-- Coordinate permutation is an equivalence on `TranslatedPET`. -/
theorem translatedPET_perm_iff {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    (fun k => z (σ k)) ∈ TranslatedPET d n ↔ z ∈ TranslatedPET d n := by
  constructor
  · intro hz
    have hback :=
      translatedPET_perm (d := d) (n := n) σ.symm
        (z := fun k => z (σ k)) hz
    simpa using hback
  · intro hz
    exact translatedPET_perm (d := d) (n := n) σ hz

/-! #### Generic values on `TranslatedPET`

The following small API separates the purely geometric witness-independence
argument from the specific BHW or selected-OS analytic extension that supplies
the PET value.  If a scalar `F` is invariant under uniform complex translations
where both endpoints lie in `PermutedExtendedTube`, then evaluating `F` at any
PET translate of a `TranslatedPET` point is independent of the chosen translate.
-/

/-- A PET scalar with uniform-translation invariance has a well-defined value
at a translated-PET point: any two PET witnesses give the same scalar. -/
theorem translatedPET_value_eq_of_translation_invariant {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_translate :
      ∀ (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n →
        F (fun k μ => z k μ + c μ) = F z)
    (z : Fin n → Fin (d + 1) → ℂ)
    (c₁ c₂ : Fin (d + 1) → ℂ)
    (h₁ : (fun k μ => z k μ + c₁ μ) ∈ PermutedExtendedTube d n)
    (h₂ : (fun k μ => z k μ + c₂ μ) ∈ PermutedExtendedTube d n) :
    F (fun k μ => z k μ + c₁ μ) =
      F (fun k μ => z k μ + c₂ μ) := by
  have key := hF_translate (fun k μ => z k μ + c₁ μ)
    (fun μ => c₂ μ - c₁ μ) h₁
    (by
      convert h₂ using 1
      ext k μ
      ring)
  simpa [sub_eq_add_neg, add_assoc] using key.symm

/-- Evaluate a PET scalar at a translated-PET point using the chosen PET
witness.  `translatedPET_value_eq_of_translation_invariant` proves that this
choice is independent once the PET scalar has uniform-translation invariance. -/
noncomputable def translatedPETValue {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) : ℂ :=
  F (fun k μ => z k μ + hz.choose μ)

/-- On the original PET, the translated-PET value agrees with the PET scalar. -/
theorem translatedPETValue_eq_on_PET {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_translate :
      ∀ (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n →
        F (fun k μ => z k μ + c μ) = F z)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz_pet : z ∈ PermutedExtendedTube d n)
    (hz_tpet : z ∈ TranslatedPET d n) :
    translatedPETValue F z hz_tpet = F z := by
  unfold translatedPETValue
  have hzero :
      (fun k μ => z k μ + (0 : Fin (d + 1) → ℂ) μ) ∈
        PermutedExtendedTube d n := by
    simpa using hz_pet
  have h :=
    translatedPET_value_eq_of_translation_invariant
      (d := d) (n := n) F hF_translate z hz_tpet.choose 0
      hz_tpet.choose_spec hzero
  simpa using h

/-- The translated-PET value is invariant under uniform complex translations,
provided both translated-PET memberships are supplied. -/
theorem translatedPETValue_translation_invariant {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_translate :
      ∀ (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n →
        F (fun k μ => z k μ + c μ) = F z)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ TranslatedPET d n) :
    translatedPETValue F z hz =
      translatedPETValue F (fun k μ => z k μ + c μ) hzc := by
  unfold translatedPETValue
  have h₂ :
      (fun k μ => z k μ + (fun μ => c μ + hzc.choose μ) μ) ∈
        PermutedExtendedTube d n := by
    convert hzc.choose_spec using 1
    ext k μ
    ring
  have h :=
    translatedPET_value_eq_of_translation_invariant
      (d := d) (n := n) F hF_translate z hz.choose
      (fun μ => c μ + hzc.choose μ) hz.choose_spec h₂
  convert h using 2
  ext k μ
  ring

/-- Total version of `translatedPETValue`: outside `TranslatedPET` it is zero.
This is only an honest integrand when paired with a support or a.e. theorem
showing the non-`TranslatedPET` locus is irrelevant. -/
noncomputable def translatedPETValueTotal {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) : ℂ :=
  if hz : z ∈ TranslatedPET d n then
    translatedPETValue F z hz
  else 0

/-- On the original PET, the total translated-PET value agrees with the PET
scalar. -/
theorem translatedPETValueTotal_eq_on_PET {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_translate :
      ∀ (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n →
        F (fun k μ => z k μ + c μ) = F z)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz_pet : z ∈ PermutedExtendedTube d n) :
    translatedPETValueTotal F z = F z := by
  have hz_tpet : z ∈ TranslatedPET d n :=
    PermutedExtendedTube_subset_TranslatedPET hz_pet
  simp only [translatedPETValueTotal, dif_pos hz_tpet]
  exact translatedPETValue_eq_on_PET F hF_translate z hz_pet hz_tpet

/-- The total translated-PET value is translation-invariant on
`TranslatedPET`. -/
theorem translatedPETValueTotal_translation_invariant {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_translate :
      ∀ (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n →
        F (fun k μ => z k μ + c μ) = F z)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) :
    translatedPETValueTotal F z =
      translatedPETValueTotal F (fun k μ => z k μ + c μ) := by
  have hzc : (fun k μ => z k μ + c μ) ∈ TranslatedPET d n :=
    translatedPET_translate hz c
  simp only [translatedPETValueTotal, dif_pos hz, dif_pos hzc]
  exact translatedPETValue_translation_invariant F hF_translate z c hz hzc

/-- The coincident-time hyperplane `{x : x i 0 = x j 0}` is Haar-null for
    `i ≠ j`. -/
private theorem measure_timeEq_zero_local {d n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MeasureTheory.volume
      {x : NPointDomain d n | x i 0 = x j 0} = 0 := by
  let L : NPointDomain d n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x i 0 - x j 0
      map_add' := by intro x y; simp; ring
      map_smul' := by intro a x; simp; ring }
  have hset :
      {x : NPointDomain d n | x i 0 = x j 0} = (LinearMap.ker L : Set _) := by
    ext x; simp [L, LinearMap.mem_ker, sub_eq_zero]
  have hker_ne_top : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
    have hval : L (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0) = 0 := by
      simpa using congrArg
        (fun f => f (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0)) hzero
    have hji : j ≠ i := fun h => hij h.symm
    have : (1 : ℝ) = 0 := by simp [L, hji] at hval
    norm_num at this
  rw [hset]
  exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume
    (LinearMap.ker L) hker_ne_top

/-- The set of configurations with at least one pair of coincident times is a
    finite union of hyperplanes, hence Haar-null. -/
private theorem measure_timeCoinc_zero {d n : ℕ} [NeZero d] :
    MeasureTheory.volume
      {x : NPointDomain d n | ∃ i j : Fin n, i ≠ j ∧ x i 0 = x j 0} = 0 := by
  classical
  set S : Set (NPointDomain d n) :=
    {x | ∃ i j : Fin n, i ≠ j ∧ x i 0 = x j 0}
  have hS_cover :
      S ⊆ ⋃ p : {p : Fin n × Fin n // p.1 ≠ p.2}, {x | x p.1.1 0 = x p.1.2 0} := by
    intro x hx
    obtain ⟨i, j, hij, heq⟩ := hx
    exact Set.mem_iUnion.mpr ⟨⟨(i, j), hij⟩, heq⟩
  refine MeasureTheory.measure_mono_null hS_cover ?_
  apply MeasureTheory.measure_iUnion_null
  rintro ⟨⟨i, j⟩, hij⟩
  exact measure_timeEq_zero_local (d := d) (n := n) i j hij

/-- **A.e. Wick-rotated Euclidean configuration lies in the translated PET.**

    Proof strategy: if `x` has pairwise distinct times (a full-measure condition),
    shift by `a = (A, 0, …, 0)` where `A = 1 + Σ|x_i 0|`. Then `x + a` has
    strictly positive pairwise-distinct times, so `wick(x + a) ∈ PET` by
    `euclidean_distinct_in_permutedTube`. Since `wick(x + a) = wick(x) + wick(a)`
    (with `wick(a) = (iA, 0, …, 0)`), the vector `c := wick(a)` witnesses
    `wick(x) ∈ TranslatedPET`. -/
theorem wickRotation_in_translatedPET_null {d n : ℕ} [NeZero d] :
    MeasureTheory.volume
      {x : NPointDomain d n |
        (fun k => wickRotatePoint (x k)) ∉ TranslatedPET d n} = 0 := by
  refine MeasureTheory.measure_mono_null ?_ (measure_timeCoinc_zero (d := d) (n := n))
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  by_contra hdist_all
  push_neg at hdist_all
  -- hdist_all : ∀ i j, i ≠ j → x i 0 ≠ x j 0
  apply hx
  -- Goal: (fun k => wickRotatePoint (x k)) ∈ TranslatedPET d n
  -- Construct the shift a = (A, 0, ..., 0)
  let A : ℝ := 1 + ∑ i : Fin n, |x i 0|
  let a : SpacetimeDim d := fun μ => if μ = 0 then A else 0
  let xs : NPointDomain d n := fun k μ => x k μ + a μ
  have hpos : ∀ i : Fin n, xs i 0 > 0 := by
    intro i
    have hi_le : |x i 0| ≤ ∑ j : Fin n, |x j 0| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (x j 0)) (Finset.mem_univ i)
    have : 0 < x i 0 + A := by dsimp [A]; linarith [neg_abs_le (x i 0)]
    simpa [xs, a] using this
  have hdistinct_xs : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0 := by
    intro i j hij
    simpa [xs, a] using hdist_all i j hij
  have hxs_pet : (fun k => wickRotatePoint (xs k)) ∈ PermutedExtendedTube d n :=
    euclidean_distinct_in_permutedTube xs hdistinct_xs hpos
  have hwick_add :
      (fun k => wickRotatePoint (xs k)) =
        (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a μ) := by
    ext k μ
    simp only [xs, a, wickRotatePoint]
    split_ifs <;> push_cast <;> ring
  exact ⟨wickRotatePoint a, hwick_add ▸ hxs_pet⟩

/-- **Almost every Euclidean Wick-rotated configuration lies in the translated PET.**

    For a.e. configuration x = (x₁, ..., xₙ) of Euclidean spacetime points,
    the Wick-rotated configuration (iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) lies in the
    translated permuted extended tube.

    This suffices for all downstream uses: the Schwinger function properties
    (translation invariance, rotation invariance, permutation symmetry) are
    proved via integral identities that only need pointwise equality a.e.,
    and the Wightman function value is unchanged by translation (axiom R3).

    Ref: Jost, "The General Theory of Quantized Fields" §IV.4, Theorem IV.4;
    Streater-Wightman, Theorem 2-12 -/
theorem ae_euclidean_points_in_translatedPET {d n : ℕ} [NeZero d] :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      (fun k => wickRotatePoint (x k)) ∈ TranslatedPET d n := by
  rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
  convert wickRotation_in_translatedPET_null (d := d) (n := n) using 1

-- `wickRotation_not_in_PET_null` and `ae_euclidean_points_in_permutedTube`
-- were DELETED because the statements are FALSE for n ≥ d+2 (see W11Counterexample.lean).
-- Use `wickRotation_in_translatedPET_null` / `ae_euclidean_points_in_translatedPET` instead.

/-- Connected Lorentz covariance of the boundary distribution implies that the
boundary values of `z ↦ F(Λ z)` and `z ↦ F(z)` agree distributionally. This is
the connected-group version of the usual Wightman boundary-value
comparison. -/
theorem W_analytic_lorentz_bv_agree_of_restrictedCovariance
    {d n : ℕ} [NeZero d]
    (W_n : SchwartzNPoint d n → ℂ)
    (hW_linear : IsLinearMap ℂ W_n)
    (hW_cont : Continuous W_n)
    (hW_lorentz :
      ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_growth : ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ z, z ∈ ForwardTube d n → ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (hF_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (Λ : LorentzGroup d) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
              (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) -
           F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  intro f η hη
  have h_term2 : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n f)) := hF_bv f η hη
  have h_term1 : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n f)) :=
    lorentz_covariant_distributional_bv_of_restrictedCovariance
      (d := d) (n := n) W_n hW_linear hW_cont hW_lorentz
      F hF_hol hF_bv Λ f η hη
  have hdiff := Filter.Tendsto.sub h_term1 h_term2
  simp only [sub_self] at hdiff
  refine hdiff.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : ε ∈ Set.Ioi 0)
  have hF_lor_hol :
      DifferentiableOn ℂ
        (fun z => F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν))
        (ForwardTube d n) := by
    apply DifferentiableOn.comp hF_hol
    · intro z _hz
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_pi.mpr
      intro k
      apply differentiableAt_pi.mpr
      intro μ
      have hcoord : ∀ (k : Fin n) (ν : Fin (d + 1)),
          DifferentiableAt ℂ (fun x : Fin n → Fin (d + 1) → ℂ => x k ν) z :=
        fun k' ν' =>
          differentiableAt_pi.mp (differentiableAt_pi.mp differentiableAt_id k') ν'
      suffices h :
          ∀ (s : Finset (Fin (d + 1))),
            DifferentiableAt ℂ
              (fun x : Fin n → Fin (d + 1) → ℂ =>
                ∑ ν ∈ s, (↑(Λ.val μ ν) : ℂ) * x k ν) z by
        exact h Finset.univ
      intro s
      induction s using Finset.induction with
      | empty =>
          simp [differentiableAt_const]
      | @insert ν s hν ih =>
          simp only [Finset.sum_insert hν]
          exact ((differentiableAt_const _).mul (hcoord k ν)).add ih
    · intro z hz
      exact restricted_preserves_forward_tube Λ z hz
  rw [← MeasureTheory.integral_sub]
  · congr 1
    ext x
    ring
  · exact forward_tube_bv_integrable
      (fun z => F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν))
      hF_lor_hol
      (forward_tube_lorentz_growth Λ F hF_growth)
      ⟨{ toLinearMap := ⟨⟨W_n, hW_linear.map_add⟩, hW_linear.map_smul⟩, cont := hW_cont },
        fun f' η' hη' =>
          lorentz_covariant_distributional_bv_of_restrictedCovariance
            (d := d) (n := n) W_n hW_linear hW_cont hW_lorentz
            F hF_hol hF_bv Λ f' η' hη'⟩
      f η hη ε (Set.mem_Ioi.mp hε)
  · exact forward_tube_bv_integrable F hF_hol
      hF_growth
      ⟨{ toLinearMap := ⟨⟨W_n, hW_linear.map_add⟩, hW_linear.map_smul⟩, cont := hW_cont },
        hF_bv⟩
      f η hη ε (Set.mem_Ioi.mp hε)

/-- The distributional boundary values of z ↦ W_analytic(Λz) and z ↦ W_analytic(z)
    agree, by Lorentz covariance of the Wightman distribution. -/
theorem W_analytic_lorentz_bv_agree
    (Wfn : WightmanFunctions d) (n : ℕ)
    (Λ : LorentzGroup d) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          ((Wfn.spectrum_condition n).choose
            (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) -
           (Wfn.spectrum_condition n).choose
            (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) :=
  W_analytic_lorentz_bv_agree_of_restrictedCovariance
    (d := d) (n := n)
    (Wfn.W n) (Wfn.linear n) (Wfn.tempered n)
    (fun Λ f g hfg => Wfn.lorentz_covariant n Λ f g hfg)
    (Wfn.spectrum_condition n).choose
    (Wfn.spectrum_condition n).choose_spec.1
    (Wfn.spectrum_condition n).choose_spec.2.1
    (Wfn.spectrum_condition n).choose_spec.2.2
    Λ


end
