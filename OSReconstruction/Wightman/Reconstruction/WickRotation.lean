/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction
import OSReconstruction.Wightman.Reconstruction.AnalyticContinuation
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.SCV.PaleyWiener
import OSReconstruction.SCV.BochnerTubeTheorem

open scoped Classical

/-!
# Wick Rotation and the OS Bridge Theorems

This file develops the infrastructure for the Osterwalder-Schrader bridge theorems:
- **Theorem R→E** (`wightman_to_os`): Wightman functions → Schwinger functions (OS I, §5)
- **Theorem E'→R'** (`os_to_wightman`): Schwinger functions → Wightman functions (OS II, §IV-V)

## Theorem R→E (Wightman → OS)

Given Wightman functions W_n satisfying R0-R5, we construct Schwinger functions S_n
satisfying E0-E4. The construction (OS I, Section 5) proceeds as:

1. **Analytic continuation**: The spectrum condition (R3) implies W_n extends to a
   holomorphic function on the forward tube T_n.
2. **BHW extension**: The Bargmann-Hall-Wightman theorem extends W_n to the
   permuted extended tube T''_n, with complex Lorentz invariance and permutation symmetry.
3. **Define S_n**: Restrict the BHW extension to Euclidean points:
     S_n(τ₁, x⃗₁, ..., τₙ, x⃗ₙ) = W_analytic(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ)
4. **Verify E0-E4**:
   - E0 (temperedness): From R0 + geometric estimates (OS I, Prop 5.1)
   - E1 (Euclidean covariance): From complex Lorentz invariance (SO(d+1) ⊂ L₊(ℂ))
   - E2 (reflection positivity): From R2 (Wightman positivity)
   - E3 (permutation symmetry): From BHW permutation invariance
   - E4 (cluster): From R4

## Theorem E'→R' (OS → Wightman)

Given Schwinger functions S_n satisfying E0'-E4 (with E0' = linear growth condition),
we reconstruct Wightman functions satisfying R0'-R5. This follows OS II (1975).

The proof is inductive on the analytic continuation domain:

### Phase 1: Hilbert Space from Reflection Positivity (E2)
- Same GNS construction as Wightman reconstruction
- E2 gives positive semi-definite inner product on S₊ (positive-time test functions)
- Complete to Hilbert space H

### Phase 2: Semigroup from Euclidean Time Translation (E0' + E1)
- Translation in Euclidean time gives contraction semigroup e^{-tH} for t > 0
- E0' controls growth: the semigroup extends analytically
- H is a positive self-adjoint operator (the Hamiltonian)

### Phase 3: Analytic Continuation (OS II, Theorem 4.1-4.2, inductive)
- **Base case (A₀)**: Schwinger functions S_k(ξ) are analytic on ℝ₊^k, with estimates
- **Inductive step (Aᵣ)**: Extend to regions C_k^(r) in complexified time
- After d steps, reach the forward tube
- **Critical**: E0' is essential for temperedness estimates at each step

### Phase 4: Boundary Values → Wightman Distributions
- The analytic functions in the forward tube have distributional boundary values
- E0' ensures boundary values are tempered distributions
- Define W_n as these boundary values

### Phase 5: Verify Wightman Axioms
- R0 (temperedness): from E0' estimates
- R1 (Lorentz covariance): from E1 via BHW
- R2 (positivity): from E2
- R3 (spectrum condition): from the support of the analytic continuation
- R4 (cluster): from E4
- R5 (locality): from E3 + edge-of-the-wedge

## References

* Osterwalder-Schrader I (1973), "Axioms for Euclidean Green's Functions"
* Osterwalder-Schrader II (1975), "Axioms for Euclidean Green's Functions II"
* Glimm-Jaffe, "Quantum Physics", Chapter 19
-/

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Distribution Theory Axioms for the Forward Tube

These axioms specialize the general tube domain results from `SCV.TubeDistributions`
to the forward tube `T_n = { z ∈ ℂ^{n(d+1)} | Im(z_k - z_{k-1}) ∈ V₊ }`.

The forward tube is a tube domain over the product cone `V₊^n` in difference coordinates.
The general tube domain axioms (`continuous_boundary_tube`, `distributional_uniqueness_tube`)
apply after the linear change of variables from absolute to difference coordinates
and the identification `Fin n → Fin (d+1) → ℂ ≅ Fin (n*(d+1)) → ℂ`. We state the
forward-tube versions directly to avoid coordinate-change boilerplate.

Ref: Vladimirov, "Methods of the Theory of Generalized Functions" §25-26;
     Streater-Wightman, Theorems 2-6, 2-9 -/

/-! #### Helper lemmas for Lorentz invariance on the forward tube -/

/-- A restricted Lorentz transformation preserves the open forward light cone.

    If Λ ∈ SO⁺(1,d) and η ∈ V₊ (η₀ > 0, η² < 0), then Λη ∈ V₊.

    Part (a): Metric preservation — minkowskiNormSq(Λη) = minkowskiNormSq(η) < 0.
    Part (b): Time component positivity — (Λη)₀ > 0, using Λ₀₀ ≥ 1, Cauchy-Schwarz,
    and the hyperbolic bound.

    Ref: Streater-Wightman, §2.4 -/
private theorem restricted_preserves_forward_cone
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
private theorem restricted_preserves_forward_tube
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
private theorem W_analytic_lorentz_holomorphic
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

    If F is holomorphic on ForwardTube d n and ε > 0 with η ∈ V₊^n, then the
    restriction x ↦ F(x + iεη) satisfies polynomial growth:
    ‖F(x + iεη)‖ ≤ C · (1 + ‖x‖)^N for some C, N depending on F, ε, η.

    This follows from the Cauchy integral formula applied on polydiscs centered
    at x + iεη that fit inside the tube (since εη is in the interior of the cone).
    The Cauchy estimates give polynomial growth from the holomorphy.

    Blocked by: The full argument requires either the Cauchy integral formula
    for polydiscs in several complex variables, or the Fourier-Laplace representation
    of holomorphic functions on tube domains (Vladimirov §25). Neither is in Mathlib.

    Ref: Vladimirov, "Methods of the Theory of Generalized Functions", Theorem 25.5 -/
private theorem polynomial_growth_on_slice {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k))
    (ε : ℝ) (hε : ε > 0) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : NPointDomain d n),
        ‖F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)‖ ≤
          C_bd * (1 + ‖x‖) ^ N := by
  sorry

/-- A function with polynomial growth times a Schwartz function is integrable.

    If g : E → ℂ satisfies ‖g(x)‖ ≤ C · (1 + ‖x‖)^N and f is Schwartz,
    then g · f is integrable, because Schwartz functions decay faster than
    any polynomial.

    Proof uses `add_pow_le` to bound (1+‖x‖)^N ≤ 2^(N-1) * (1 + ‖x‖^N),
    then `SchwartzMap.integrable` and `SchwartzMap.integrable_pow_mul` from Mathlib
    (via `HasTemperateGrowth` for volume on finite-dimensional Pi types). -/
private theorem polynomial_growth_mul_schwartz_integrable {d n : ℕ} [NeZero d]
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
private theorem forward_tube_slice_aestrongly_measurable {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k))
    (ε : ℝ) (hε : ε > 0) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d n => F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
      MeasureTheory.volume := by
  sorry

theorem forward_tube_bv_integrable {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k))
    (ε : ℝ) (hε : ε > 0) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      MeasureTheory.volume := by
  -- Decompose via polynomial growth on the slice + Schwartz decay
  obtain ⟨C_bd, N, hC, hgrowth⟩ := polynomial_growth_on_slice F hF η hη ε hε
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
private theorem lorentz_mul_inv_eq_one {d : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d)) :
    Λ.val.val * Λ.val⁻¹.val = 1 := by
  have h1 := LorentzGroup.ext_iff.mp (mul_inv_cancel Λ.val)
  rw [show (Λ.val * Λ.val⁻¹).val = Λ.val.val * Λ.val⁻¹.val from rfl] at h1
  rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
  exact h1

private theorem lorentz_inv_mul_eq_one {d : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d)) :
    Λ.val⁻¹.val * Λ.val.val = 1 := by
  have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ.val)
  rw [show (Λ.val⁻¹ * Λ.val).val = Λ.val⁻¹.val * Λ.val.val from rfl] at h1
  rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
  exact h1

/-- The componentwise Lorentz action on NPointDomain preserves Lebesgue measure.

    Follows the same pattern as `integral_orthogonal_eq_self` but uses
    `|det Λ| = 1` from properness instead of orthogonality. -/
private theorem integral_lorentz_eq_self {d n : ℕ} [NeZero d]
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
private noncomputable def lorentzInvCLEquiv {d : ℕ} [NeZero d]
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
private noncomputable def lorentzCompSchwartz {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d))
    (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.piCongrRight (fun (_ : Fin n) => lorentzInvCLEquiv Λ)) f

/-- The pointwise evaluation of lorentzCompSchwartz: g(x) = f(Λ⁻¹ · x). -/
private theorem lorentzCompSchwartz_apply {d n : ℕ} [NeZero d]
    (Λ : LorentzGroup.Restricted (d := d))
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (lorentzCompSchwartz Λ f).toFun x =
    f.toFun (fun i => Matrix.mulVec Λ.val⁻¹.val (x i)) := by
  simp only [lorentzCompSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.piCongrRight, lorentzInvCLEquiv]
  rfl

/-- After applying Lorentz COV, the composition g(Λx) = f(Λ⁻¹(Λx)) = f(x). -/
private theorem lorentzCompSchwartz_comp_lorentz {d n : ℕ} [NeZero d]
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
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)))
    (Λ : LorentzGroup.Restricted (d := d))
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k)) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n f)) := by
  -- Define the Lorentz-rotated direction and test function
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val.val μ ν * η k ν
  let g : SchwartzNPoint d n := lorentzCompSchwartz Λ f
  -- Λη is in the forward cone (each component)
  have hΛη : ∀ k, InOpenForwardCone d (Λη k) :=
    fun k => restricted_preserves_forward_cone Λ (η k) (hη k)
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
private theorem W_analytic_lorentz_bv_agree
    (Wfn : WightmanFunctions d) (n : ℕ)
    (Λ : LorentzGroup.Restricted (d := d)) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
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
      (W_analytic_lorentz_holomorphic Wfn n Λ) f η hη ε (Set.mem_Ioi.mp hε)
  · exact forward_tube_bv_integrable W_a hW_hol f η hη ε (Set.mem_Ioi.mp hε)

/-! #### BHW extension (needed before constructing Schwinger functions) -/

/-- W_analytic inherits real Lorentz invariance from the Wightman distribution.

    Both z ↦ W_analytic(z) and z ↦ W_analytic(Λz) are holomorphic on the forward tube
    with the same distributional boundary values (by Lorentz invariance of W_n).
    By `distributional_uniqueness_forwardTube`, they agree on the forward tube.

    Ref: Streater-Wightman, §2.4 -/
private theorem W_analytic_lorentz_on_tube (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (Λ : LorentzGroup.Restricted (d := d))
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      (Wfn.spectrum_condition n).choose
        (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
      (Wfn.spectrum_condition n).choose z := by
  intro Λ z hz
  -- Apply distributional uniqueness: two holomorphic functions on the forward tube
  -- with the same distributional boundary values must agree.
  have huniq := distributional_uniqueness_forwardTube
    (W_analytic_lorentz_holomorphic Wfn n Λ)
    (Wfn.spectrum_condition n).choose_spec.1
    (W_analytic_lorentz_bv_agree Wfn n Λ)
  exact huniq z hz

/-- W_analytic extends continuously to the real boundary of the forward tube.

    Proved using `continuous_boundary_forwardTube`: the distributional boundary value
    condition from `spectrum_condition` provides the hypothesis.

    Ref: Streater-Wightman, Theorem 2-9 -/
private theorem W_analytic_continuous_boundary (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt (Wfn.spectrum_condition n).choose
        (ForwardTube d n) (fun k μ => (x k μ : ℂ)) := by
  intro x
  exact continuous_boundary_forwardTube (d := d) (n := n)
    (Wfn.spectrum_condition n).choose_spec.1
    ⟨Wfn.W n, Wfn.tempered n, (Wfn.spectrum_condition n).choose_spec.2⟩ x

/-- The distributional boundary values of W_analytic and W_analytic composed with
    swap(i, i+1) agree when evaluated against test functions supported on configurations
    where x_{i+1} - x_i is spacelike. This is the distributional form of local
    commutativity, combining `hLC` with `hBV`.

    Blocked by: verifying that swapping indices in the forward tube approximation
    yields an approximation from the correct direction (the i-th cone direction
    flips sign under swap, requiring the backward cone). -/
private theorem W_analytic_swap_distributional_agree {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ) +
              ε * ↑(η (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) * Complex.I) -
           W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  sorry

/-- Pointwise local commutativity of the analytic continuation at spacelike boundary.

    g(z) = W_analytic(swap(z)) - W_analytic(z) is holomorphic where defined.
    By `W_analytic_swap_distributional_agree`, g has zero distributional boundary
    values at real spacelike points. By the edge-of-the-wedge theorem (sorry-free
    in `EdgeOfWedge.lean`), g extends holomorphically across the boundary.
    Since g = 0 distributionally on an open real set, the identity theorem gives g = 0.

    Blocked by: multi-tube EOW application (expressing the forward and swapped tubes
    as tube domains) and the distributional-to-pointwise bridge via `eow_adj_swap_extension`.

    Ref: Streater-Wightman Thm 3-5; Jost §IV.3 -/
theorem analytic_boundary_local_commutativity {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hx : MinkowskiSpace.minkowskiNormSq d
      (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0) :
    W_analytic (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
    W_analytic (fun k μ => (x k μ : ℂ)) := by
  sorry

/-- Local commutativity of W_analytic at spacelike-separated boundary points.

    At real points where consecutive arguments are spacelike separated
    (Minkowski norm > 0), swapping those arguments doesn't change the boundary
    value. This follows from `analytic_boundary_local_commutativity` applied to
    the analytic continuation from `spectrum_condition`.

    Ref: Streater-Wightman, §3.3; Jost, §IV.3 -/
private theorem W_analytic_local_commutativity (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        MinkowskiSpace.minkowskiNormSq d
          (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0 →
        (Wfn.spectrum_condition n).choose
          (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        (Wfn.spectrum_condition n).choose (fun k μ => (x k μ : ℂ)) := by
  intro i hi x hx
  exact analytic_boundary_local_commutativity (d := d) (n := n)
    (Wfn.spectrum_condition n).choose
    (Wfn.spectrum_condition n).choose_spec.1
    Wfn.W
    (Wfn.spectrum_condition n).choose_spec.2
    Wfn.locally_commutative
    i hi x hx

/-- The BHW extension of W_analytic from the forward tube to the permuted extended tube.

    Proved by applying the `bargmann_hall_wightman` axiom (AnalyticContinuation.lean) to
    the holomorphic extension `W_analytic` from `spectrum_condition`, with:
    - Lorentz invariance from `W_analytic_lorentz_on_tube`
    - Continuous boundary values from `W_analytic_continuous_boundary`
    - Local commutativity from `W_analytic_local_commutativity`

    Ref: Streater-Wightman, Theorem 2-11; Jost, Ch. IV -/
noncomputable def W_analytic_BHW (Wfn : WightmanFunctions d) (n : ℕ) :
    { F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ //
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n,
        F_ext z = (Wfn.spectrum_condition n).choose z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = F_ext z) ∧
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) } := by
  let h := bargmann_hall_wightman n
      (Wfn.spectrum_condition n).choose
      (Wfn.spectrum_condition n).choose_spec.1
      (W_analytic_lorentz_on_tube Wfn n)
      (W_analytic_continuous_boundary Wfn n)
      (W_analytic_local_commutativity Wfn n)
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
    h.choose_spec.2.2.2.1⟩

/-! #### BHW extension helper lemmas and translation invariance

The BHW extension inherits translation invariance from the Wightman functions.
The proof uses BHW uniqueness (property 5 of `bargmann_hall_wightman`) and the
identity theorem for holomorphic functions on connected domains.

The proof is decomposed into three helpers:
1. `permutedExtendedTube_translation_closed` — PET is closed under z ↦ z + c
2. `W_analytic_translation_on_forwardTube` — W_analytic is translation-invariant on FT
3. `permutedExtendedTube_isConnected` — PET is connected

Each helper captures a specific gap in the current formalization infrastructure. -/

/-- The open forward light cone absorbs arbitrary perturbations when scaled large enough.
    For any η ∈ V₊ and any δ : Fin (d+1) → ℝ, there exists t > 0 such that t • η + δ ∈ V₊.

    This follows from V₊ being an open cone: t • η ∈ V₊ for all t > 0, and for large t
    the perturbation δ becomes negligible relative to t • η.

    Blocked by: detailed bound on MinkowskiSpace.minkowskiNormSq of a sum in terms of
    the individual norms and cross terms. The key estimate is that the quadratic form
    grows like t² while the perturbation is O(t). -/
private theorem inOpenForwardCone_absorb_perturbation {d : ℕ} [NeZero d]
    (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η)
    (δ : Fin (d + 1) → ℝ) :
    ∃ t : ℝ, t > 0 ∧ InOpenForwardCone d (fun μ => t * η μ + δ μ) := by
  obtain ⟨hη0, hηneg⟩ := hη
  -- The Minkowski norm of (tη + δ) is a downward-opening quadratic in t:
  --   Q(t) = minkowskiNormSq(η) · t² + 2·minkowskiInner(η,δ) · t + minkowskiNormSq(δ)
  -- with leading coefficient minkowskiNormSq(η) < 0. So Q(t) < 0 for large t.
  -- The time component t·η₀ + δ₀ > 0 for large t since η₀ > 0.
  -- Choose t = max(1, t₁, t₂) where t₁ handles positivity and t₂ handles the norm.
  set a := MinkowskiSpace.minkowskiNormSq d η with ha_def
  set b := MinkowskiSpace.minkowskiInner d η δ
  set c_norm := MinkowskiSpace.minkowskiNormSq d δ
  -- t₁: ensures time component positive
  set t₁ := 1 + |δ 0| / η 0 with ht₁_def
  have ht₁_pos : t₁ > 0 := by positivity
  have ht₁_time : t₁ * η 0 + δ 0 > 0 := by
    have := neg_abs_le (δ 0)
    have : |δ 0| / η 0 * η 0 = |δ 0| := by field_simp
    nlinarith
  -- t₂: ensures norm condition. Since a < 0, Q(t) < 0 for t > (-2|b| - |c_norm|) / a.
  -- We pick t₂ large enough.
  set t₂ := 1 + (|2 * b| + |c_norm| + 1) / |a| with ht₂_def
  have ha_neg : a < 0 := hηneg
  have ha_ne : a ≠ 0 := ne_of_lt ha_neg
  have ha_abs_pos : |a| > 0 := abs_pos.mpr ha_ne
  -- Use t = max(t₁, t₂)
  set t := max t₁ t₂
  refine ⟨t, lt_of_lt_of_le ht₁_pos (le_max_left _ _), ?_, ?_⟩
  · -- Time component positive: t * η 0 + δ 0 > 0
    calc t * η 0 + δ 0 ≥ t₁ * η 0 + δ 0 := by
          have : t ≥ t₁ := le_max_left _ _
          nlinarith
      _ > 0 := ht₁_time
  · -- Minkowski norm negative: Q(t) = a·t² + 2bt + c_norm < 0
    -- Since a < 0 and t is large enough, a·t² dominates.
    -- Q(t) = a·t² + 2bt + c_norm
    -- ≤ a·t₂² + |2b|·t₂ + |c_norm|  (since a < 0, t ≥ t₂ gives a·t² ≤ a·t₂²)
    -- Actually let's use the direct estimate.
    -- Q(t) := minkowskiNormSq(tη + δ) = t²·a + 2t·b + c_norm
    -- We show (fun μ => t * η μ + δ μ) = t • η + δ in the Pi-function sense
    have hfun : (fun μ => t * η μ + δ μ) = t • η + δ := by
      ext μ; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    -- Use bilinearity: ‖tη + δ‖² = t²‖η‖² + 2t⟨η,δ⟩ + ‖δ‖²
    have hexpand : MinkowskiSpace.minkowskiNormSq d (fun μ => t * η μ + δ μ) =
        t ^ 2 * a + 2 * t * b + c_norm := by
      simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner, a, b, c_norm]
      conv_lhs => rw [show (∑ i, MinkowskiSpace.metricSignature d i * (t * η i + δ i) *
        (t * η i + δ i)) =
        t ^ 2 * (∑ i, MinkowskiSpace.metricSignature d i * η i * η i) +
        2 * t * (∑ i, MinkowskiSpace.metricSignature d i * η i * δ i) +
        (∑ i, MinkowskiSpace.metricSignature d i * δ i * δ i) from by
          trans (∑ i, (t ^ 2 * (MinkowskiSpace.metricSignature d i * η i * η i) +
            2 * t * (MinkowskiSpace.metricSignature d i * η i * δ i) +
            MinkowskiSpace.metricSignature d i * δ i * δ i))
          · congr 1; ext i; ring
          · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]]
    rw [hexpand]
    have ht_ge_t₂ : t ≥ t₂ := le_max_right _ _
    have ht_pos : t > 0 := lt_of_lt_of_le ht₁_pos (le_max_left _ _)
    have ht₂_ge_one : t₂ ≥ 1 := le_add_of_nonneg_right (div_nonneg (by positivity) (le_of_lt ha_abs_pos))
    have ht_ge_one : t ≥ 1 := le_trans ht₂_ge_one ht_ge_t₂
    -- Key estimate: a * t ≤ -(|2*b| + |c_norm| + 1)
    have hkey : a * t ≤ -(|2 * b| + |c_norm| + 1) := by
      have h1 : t ≥ (|2 * b| + |c_norm| + 1) / |a| :=
        le_trans (le_add_of_nonneg_left (by linarith : (0 : ℝ) ≤ 1)) ht_ge_t₂
      rw [abs_of_neg ha_neg] at h1
      -- h1 : t ≥ (|2*b| + |c_norm| + 1) / (-a), and a < 0
      -- Since t ≥ X/(-a) and a < 0, we get a*t ≤ a*(X/(-a)) = -X
      have hna_pos : -a > 0 := by linarith
      -- h1 : (|2*b| + |c_norm| + 1) / (-a) ≤ t
      -- Multiply both sides by (-a) > 0: |2*b| + |c_norm| + 1 ≤ (-a) * t
      have h2 : (|2 * b| + |c_norm| + 1) / (-a) ≤ t := h1
      rw [div_le_iff₀ hna_pos] at h2
      linarith
    -- From hkey: a*t ≤ -(|2b| + |c_norm| + 1)
    -- t²*a + 2t*b + c_norm = t*(a*t) + 2t*b + c_norm
    --   ≤ t*(-(|2b| + |c_norm| + 1)) + 2t*b + c_norm
    --   = -t*|2b| - t*|c_norm| - t + 2t*b + c_norm
    --   ≤ -t*|2b| - t*|c_norm| - t + t*|2b| + |c_norm|   [since 2t*b ≤ t*|2b| and c_norm ≤ |c_norm|]
    --   = -t*|c_norm| - t + |c_norm|
    --   = (1 - t)*|c_norm| - t
    --   ≤ -t  [since t ≥ 1]
    --   < 0
    -- t²*a + 2tb + c_norm = t*(a*t) + 2tb + c_norm
    --   ≤ t*(-(|2b|+|c_norm|+1)) + 2tb + c_norm  [hkey]
    --   = -t*|2b| - t*|c_norm| - t + 2tb + c_norm
    --   ≤ -t*|c_norm| - t + |c_norm|  [since 2b ≤ |2b|, hence 2tb ≤ t|2b| for t>0]
    --   = |c_norm|*(1-t) - t ≤ -t < 0
    have h2b_le : 2 * t * b ≤ t * |2 * b| := by
      have : 2 * b ≤ |2 * b| := le_abs_self _
      nlinarith
    have hcn_le : c_norm ≤ |c_norm| := le_abs_self _
    -- t * (a * t) ≤ t * (-(|2*b| + |c_norm| + 1))
    have hstep1 : t * (a * t) ≤ t * (-(|2 * b| + |c_norm| + 1)) :=
      mul_le_mul_of_nonneg_left hkey (le_of_lt ht_pos)
    have hsq : t ^ 2 * a = t * (a * t) := by ring
    -- Chain: t²a + 2tb + c_norm = t(at) + 2tb + c_norm
    --   ≤ t(-(|2b|+|c|+1)) + 2tb + c_norm  = -t|2b| - t|c| - t + 2tb + c_norm
    --   ≤ -t|c| - t + c_norm  ≤ -t|c| - t + |c| ≤ -t < 0
    have step2 : t ^ 2 * a + 2 * t * b + c_norm ≤
        -t * |2 * b| - t * |c_norm| - t + 2 * t * b + c_norm := by linarith
    have step3 : -t * |2 * b| - t * |c_norm| - t + 2 * t * b + c_norm ≤
        -t * |c_norm| - t + |c_norm| := by linarith
    have step4 : -t * |c_norm| - t + |c_norm| ≤ -t := by
      have : |c_norm| * (1 - t) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
        linarith
      linarith
    linarith

/-- The forward tube is translation-invariant in the sense that adding a constant
    to all points preserves membership, provided the k=0 imaginary part is adjusted.

    Specifically, if w ∈ ForwardTube and δ is a constant with Im(δ) small enough
    relative to Im(w 0), then w + δ ∈ ForwardTube.

    The key fact: for k > 0, (w+δ)(k) - (w+δ)(k-1) = w(k) - w(k-1), so successive
    differences are preserved. For k = 0, the imaginary part shifts by Im(δ). -/
private theorem forwardTube_translate_of_deep_enough {d n : ℕ} [NeZero d]
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d n)
    (δ : Fin (d + 1) → ℂ)
    (hn : n ≥ 1)
    (hδ : InOpenForwardCone d (fun μ => (w ⟨0, by omega⟩ μ + δ μ).im)) :
    (fun k μ => w k μ + δ μ) ∈ ForwardTube d n := by
  intro k
  simp only [ForwardTube, Set.mem_setOf_eq] at hw ⊢
  by_cases hk : k.val = 0
  · -- k = 0: the condition is Im(w 0 + δ) ∈ V₊
    simp only [hk, ↓reduceDIte]
    have hk0 : k = ⟨0, by omega⟩ := Fin.eq_of_val_eq hk
    rw [hk0]
    convert hδ using 1
    ext μ; simp
  · -- k > 0: the successive difference (w+δ)(k) - (w+δ)(k-1) = w(k) - w(k-1)
    simp only [hk, ↓reduceDIte]
    have hk_orig := hw k
    simp only [hk, ↓reduceDIte] at hk_orig
    convert hk_orig using 1
    ext μ; simp [Complex.sub_im]

/-- Core algebraic lemma for PET translation invariance (n >= 1 case).

    In difference coordinates ξ_k = z_{k+1} - z_k, the forward tube condition
    depends only on the differences. A constant shift z ↦ z + c preserves all
    differences, so the tube condition is preserved for k > 0. The k = 0 absolute
    condition changes, but the union over complex Lorentz transforms in PET
    compensates: the shifted configuration can be expressed as a different Lorentz
    transform applied to a different forward tube member.

    The proof requires either:
    1. A formal difference-coordinate isomorphism and its compatibility with the
       absolute-coordinate ForwardTube definition, or
    2. An explicit algebraic construction using the transitivity of the complex
       Lorentz group on the forward light cone.

    Neither is currently available in the formalization infrastructure.

    Ref: Streater-Wightman §2.5; the proof is immediate in difference-coordinate
    formulations of the forward tube. -/
private theorem forwardTube_lorentz_translate_aux_core {d n : ℕ} [NeZero d]
    (π : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ PermutedForwardTube d n π)
    (c : Fin (d + 1) → ℂ)
    (hn : ¬n = 0) :
    ∃ (Λ' : ComplexLorentzGroup d) (w' : Fin n → Fin (d + 1) → ℂ),
      w' ∈ PermutedForwardTube d n π ∧
      (fun k μ => ∑ ν, Λ'.val μ ν * w' k ν) =
        fun k μ => (∑ ν, Λ.val μ ν * w k ν) + c μ := by
  sorry

/-- Helper: translating all points in ForwardTube by a constant preserves the
    successive-difference conditions (k > 0) since the constant cancels in
    z_k - z_{k-1}. The k = 0 condition Im(z₀ + δ) ∈ V₊ is preserved when the
    original Im(z₀) is deep enough in V₊ to absorb Im(δ).

    More precisely: given w ∈ PermutedForwardTube π and δ ∈ ℂ^{d+1}, there exist
    Λ' ∈ ComplexLorentzGroup and w' ∈ PermutedForwardTube π such that
    Λ'·w' = Λ·w + c (pointwise), where δ = Λ⁻¹·c.

    Ref: Streater-Wightman, PCT Spin and Statistics, §2.5 -/
private theorem forwardTube_lorentz_translate_aux {d n : ℕ} [NeZero d]
    (π : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ PermutedForwardTube d n π)
    (c : Fin (d + 1) → ℂ) :
    ∃ (Λ' : ComplexLorentzGroup d) (w' : Fin n → Fin (d + 1) → ℂ),
      w' ∈ PermutedForwardTube d n π ∧
      (fun k μ => ∑ ν, Λ'.val μ ν * w' k ν) =
        fun k μ => (∑ ν, Λ.val μ ν * w k ν) + c μ := by
  -- Strategy: use Λ' = Λ and w' = w + Λ⁻¹·c.
  -- Then Λ'·w' = Λ·(w + Λ⁻¹·c) = Λ·w + Λ·Λ⁻¹·c = Λ·w + c.
  -- The hard part is showing w' ∈ PermutedForwardTube.
  -- For n = 0, the statement is vacuous.
  by_cases hn : n = 0
  · subst hn
    exact ⟨Λ, w, hw, by ext k; exact Fin.elim0 k⟩
  · -- Strategy: Λ' = Λ, w' = w + Λ⁻¹·c (constant shift of all points).
    -- Then Λ'·w' = Λ·(w + Λ⁻¹·c) = Λ·w + c (matrix inverse cancels).
    -- Need: w' ∈ PermutedForwardTube π, i.e., fun k => w'(π k) ∈ ForwardTube.
    -- For k > 0: differences are preserved (constant shift cancels).
    -- For k = 0: need Im(w(π 0) + Λ⁻¹·c) ∈ V₊.
    -- Since Im(w(π 0)) ∈ V₊ (from hw) and V₊ is open, this holds when
    -- the perturbation Im(Λ⁻¹·c) is absorbed.
    -- By inOpenForwardCone_absorb_perturbation, ∃ t > 0 with
    -- t · Im(w(π 0)) + Im(Λ⁻¹·c) ∈ V₊.
    -- We use w_scaled = t · w (still in PFT by cone property) and
    -- w' = t · w + Λ⁻¹·c, with Λ' chosen so Λ'·w' = Λ·w + c.
    -- This requires Λ' = (1/t)·Λ, which is NOT in ComplexLorentzGroup.
    --
    -- Correct approach: work in difference coordinates where translation
    -- is trivially compatible, then transfer back. This requires a
    -- coordinate-change bridge not yet available.
    --
    -- Extract as atomic helper capturing the difference-coordinate argument.
    exact forwardTube_lorentz_translate_aux_core π Λ w hw c hn

/-- The permuted extended tube is closed under constant translation.

    For z ∈ PET, z + c ∈ PET for any constant c ∈ ℂ^{d+1}.

    In difference variables ξ_k = z_{k+1} - z_k, translation by c leaves all
    differences unchanged, so the tube condition is trivially preserved. In our
    absolute-coordinate formulation, the k = 0 condition (Im(z₀) ∈ V₊) changes
    under translation, but the union over all complex Lorentz transforms in PET
    compensates.

    Ref: The forward tube in difference variables is trivially translation-invariant;
    this lemma bridges the gap to our absolute-coordinate definition. -/
theorem permutedExtendedTube_translation_closed {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n) :
    (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n := by
  -- Unfold PET to get the witness: π, Λ, w with w ∈ PermutedFT π and z = Λ·w
  simp only [PermutedExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨π, Λ, w, hw, rfl⟩ := hz
  -- Use the helper to get Λ', w' with w' ∈ PermutedFT π and Λ'·w' = Λ·w + c
  obtain ⟨Λ', w', hw', heq⟩ := forwardTube_lorentz_translate_aux π Λ w hw c
  exact ⟨π, Λ', w', hw', heq.symm⟩

/-- The BV of x ↦ W_analytic(x + iεη + c) recovers W_n applied to the
    c-translated test function.

    By change of variables x → x - Re(c) in the Schwartz integral and
    the fact that Im(c) shifts the approach direction within V₊ (which
    doesn't change the BV by direction independence), the boundary value
    of the translated function is W_n(f(· - Re(c))).

    By translation invariance of W_n, this equals W_n(f).

    Blocked by: Formalizing the change of variables in the Bochner integral
    for Schwartz functions, and the direction-independence argument for the
    shifted approach direction iε·η + i·Im(c). These require integration
    infrastructure and the direction-independence theorem.

    Ref: Streater-Wightman §2.5; Vladimirov §26 -/
private theorem W_analytic_translated_bv_eq {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k)) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        (Wfn.spectrum_condition n).choose
          (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n f)) := by
  sorry

/-- Integrability of the translated holomorphic integrand.

    The function x ↦ W_a(x + iεη + c) * f(x) is integrable when W_a is holomorphic
    on ForwardTube and f is Schwartz. This requires polynomial growth of the translated
    slice, which follows from `polynomial_growth_on_slice` applied to z ↦ W_a(z + c).

    Blocked by: showing z ↦ W_a(z + c) is holomorphic on ForwardTube (requires c
    purely imaginary with small enough imaginary part, or translation-covariance
    of ForwardTube membership). More precisely, the translated function has polynomial
    growth on slices via the same Cauchy integral argument. -/
private theorem forward_tube_bv_integrable_translated {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (c : Fin (d + 1) → ℂ)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k))
    (ε : ℝ) (hε : ε > 0) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) * (f x))
      MeasureTheory.volume := by
  sorry

/-- The difference ∫ (W_a(x+iεη+c) - W_a(x+iεη)) * f(x) dx splits into the difference
    of integrals, given integrability of each term. This is a routine consequence of
    linearity of the Bochner integral. -/
private theorem translate_bv_integral_split {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k))
    (ε : ℝ) (hε : ε > 0) :
    (∫ x : NPointDomain d n,
      ((Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) -
       (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) *
      (f x)) =
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) *
      (f x)) -
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
      (f x)) := by
  have heq : ∀ x : NPointDomain d n,
      ((Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) -
       (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) *
      (f x) =
      (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) *
      (f x) -
      (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
      (f x) := fun x => by ring
  simp_rw [heq]
  exact MeasureTheory.integral_sub
    (forward_tube_bv_integrable_translated
      (Wfn.spectrum_condition n).choose
      (Wfn.spectrum_condition n).choose_spec.1
      c f η hη ε hε)
    (forward_tube_bv_integrable
      (Wfn.spectrum_condition n).choose
      (Wfn.spectrum_condition n).choose_spec.1
      f η hη ε hε)

private theorem W_analytic_translate_same_bv {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          ((Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) -
           (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) *
          (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  intro f η hη
  -- Both BV limits equal W_n(f), so the difference → 0.
  have h1 := W_analytic_translated_bv_eq Wfn c f η hη
  have h2 := (Wfn.spectrum_condition n).choose_spec.2 f η hη
  -- Rewrite 0 as W_n(f) - W_n(f)
  rw [show (0 : ℂ) = Wfn.W n f - Wfn.W n f from (sub_self _).symm]
  -- The integral of the difference equals the difference of integrals
  -- for ε > 0 (by translate_bv_integral_split). Each integral converges
  -- to W_n(f), so the difference converges to 0.
  have h_sub := Filter.Tendsto.sub h1 h2
  -- h_sub : Tendsto (fun ε => ∫ W_a(x+iεη+c)f - ∫ W_a(x+iεη)f) → W_n(f) - W_n(f)
  -- We need: Tendsto (fun ε => ∫ (W_a(x+iεη+c) - W_a(x+iεη))f) → W_n(f) - W_n(f)
  -- These agree for ε > 0 by translate_bv_integral_split.
  refine Filter.Tendsto.congr' ?_ h_sub
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨Set.Ioi 0, self_mem_nhdsWithin,
    fun ε hε => (translate_bv_integral_split Wfn c f η hη ε hε).symm⟩

/-- The intersection FT ∩ (FT - c) is open.

    FT is open in the product topology, and translation by -c is a homeomorphism,
    so FT - c is open. The intersection of two open sets is open. -/
private theorem forwardTube_isOpen_local {n : ℕ} : IsOpen (ForwardTube d n) := by
  simp only [ForwardTube, InOpenForwardCone, Set.setOf_forall]
  apply isOpen_iInter_of_finite; intro k
  have hcont : ∀ μ : Fin (d + 1), Continuous (fun z : Fin n → Fin (d + 1) → ℂ =>
      (z k μ - (if _ : (k : ℕ) = 0 then 0 else z ⟨(k : ℕ) - 1, by omega⟩) μ).im) := by
    intro μ
    apply Complex.continuous_im.comp
    apply Continuous.sub
    · exact (continuous_apply μ).comp (continuous_apply k)
    · by_cases hk : (k : ℕ) = 0
      · simp [hk]; exact continuous_const
      · simp [hk]
        exact (continuous_apply μ).comp (continuous_apply (⟨(k : ℕ) - 1, by omega⟩ : Fin n))
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (hcont 0)
  · unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    exact isOpen_lt
      (continuous_finset_sum _ fun i _ =>
        ((continuous_const.mul (hcont i)).mul (hcont i)))
      continuous_const

private theorem forwardTube_inter_translate_isOpen {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ) :
    IsOpen {z : Fin n → Fin (d + 1) → ℂ |
      z ∈ ForwardTube d n ∧ (fun k μ => z k μ + c μ) ∈ ForwardTube d n} := by
  apply IsOpen.inter
  · exact forwardTube_isOpen_local
  · apply forwardTube_isOpen_local.preimage
    apply continuous_pi; intro k
    apply continuous_pi; intro μ
    have : Continuous (fun z : Fin n → Fin (d + 1) → ℂ => z k μ) :=
      (continuous_apply μ).comp (continuous_apply k)
    exact this.add continuous_const

/-- Distributional uniqueness on the forward tube intersection.

    If G is holomorphic on the intersection {z ∈ FT : z+c ∈ FT} and has zero
    distributional BV (∫ G(x+iεη)f(x) dx → 0 for all Schwartz f and approach
    directions η ∈ V₊^n), then G = 0 on the intersection.

    The intersection is itself a tube domain (over the intersection of the
    forward cone with its c-translate in imaginary coordinates), so the general
    `distributional_uniqueness_tube` applies after flattening.

    Blocked by: Transferring the tube domain structure of the intersection through
    the flattening equivalence and verifying the cone properties. This is a
    routine transfer lemma, parallel to `distributional_uniqueness_forwardTube`
    but for the intersected cone instead of the full forward cone. -/
private theorem distributional_uniqueness_forwardTube_inter {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ)
    {F₁ F₂ : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁
      {z | z ∈ ForwardTube d n ∧ (fun k μ => z k μ + c μ) ∈ ForwardTube d n})
    (hF₂ : DifferentiableOn ℂ F₂
      {z | z ∈ ForwardTube d n ∧ (fun k μ => z k μ + c μ) ∈ ForwardTube d n})
    (h_agree : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) -
           F₂ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)) :
    ∀ z, z ∈ ForwardTube d n → (fun k μ => z k μ + c μ) ∈ ForwardTube d n →
      F₁ z = F₂ z := by
  sorry

private theorem W_analytic_translate_eq_on_forwardTube_inter {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ) :
    ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ForwardTube d n →
      (fun k μ => z k μ + c μ) ∈ ForwardTube d n →
      (Wfn.spectrum_condition n).choose (fun k μ => z k μ + c μ) =
      (Wfn.spectrum_condition n).choose z := by
  -- Apply distributional uniqueness on the intersection.
  -- F₁(z) = W_a(z+c), F₂(z) = W_a(z), both holomorphic on the intersection.
  -- Their distributional BV difference → 0 by W_analytic_translate_same_bv.
  let W_a := (Wfn.spectrum_condition n).choose
  have hW_hol := (Wfn.spectrum_condition n).choose_spec.1
  apply distributional_uniqueness_forwardTube_inter c
  · -- F₁(z) = W_a(z+c) is holomorphic on the intersection
    apply hW_hol.comp
    · -- z ↦ (fun k μ => z k μ + c μ) is differentiable (linear + constant)
      intro z _
      apply DifferentiableAt.differentiableWithinAt
      show DifferentiableAt ℂ (fun z : Fin n → Fin (d + 1) → ℂ => fun k μ => z k μ + c μ) z
      exact differentiableAt_id.add (differentiableAt_const _)
    · exact fun z hz => hz.2
  · -- F₂(z) = W_a(z) is holomorphic on FT, hence on the intersection
    exact hW_hol.mono (fun z hz => hz.1)
  · -- BV difference → 0
    exact W_analytic_translate_same_bv Wfn c

/-- The analytic continuation W_analytic (from spectrum_condition) is
    translation-invariant on the forward tube.

    Since W_n is translation-invariant as a distribution, its analytic continuation
    to the forward tube inherits this property: W_analytic(z + c) = W_analytic(z)
    for z, z + c ∈ ForwardTube.

    Ref: Streater-Wightman §2.5 -/
theorem W_analytic_translation_on_forwardTube {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ ForwardTube d n) :
    (Wfn.spectrum_condition n).choose (fun k μ => z k μ + c μ) =
    (Wfn.spectrum_condition n).choose z :=
  W_analytic_translate_eq_on_forwardTube_inter Wfn c z hz hzc

/-- The permuted extended tube is connected.

    PET = ⋃_{π,Λ} Λ·π·FT is connected because the forward tube FT is connected
    (it is convex), adjacent permutation sectors are joined via the edge-of-the-wedge
    theorem at Jost points (spacelike boundary configurations), and the complex Lorentz
    group is connected.

    This fact is used in the BHW uniqueness proof (Property 5 of
    `bargmann_hall_wightman_theorem` in Connectedness.lean) where it currently
    appears as a local sorry. This lemma extracts it as a standalone statement.

    Ref: Jost, "The General Theory of Quantized Fields" Ch. IV -/
theorem permutedExtendedTube_isConnected (d n : ℕ) [NeZero d] :
    IsConnected (PermutedExtendedTube d n) := by
  rw [← BHW_permutedExtendedTube_eq]
  exact @BHW.isConnected_permutedExtendedTube d n

/-- The forward tube intersected with its c-translate is nonempty.

    For any c ∈ ℂ^{d+1}, there exists z ∈ FT with z + c ∈ FT. We construct such z
    by choosing Im(z₀) deep enough in V₊ that Im(z₀) + Im(c) remains in V₊, and
    choosing successive differences with large enough forward-cone components. -/
theorem forwardTube_inter_translate_nonempty {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ) :
    ∃ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ForwardTube d n ∧ (fun k μ => z k μ + c μ) ∈ ForwardTube d n := by
  -- Witness: z_k(μ) = i·(k+1)·M·δ_{μ,0} for M large enough.
  -- Successive differences have imaginary part M·e₀ ∈ V₊.
  -- For z+c at k=0, need (M + Im(c 0), Im(c 1), ...) ∈ V₊, ensured by large M.
  set Ssp := MinkowskiSpace.spatialNormSq d (fun μ => (c μ).im)
  set M : ℝ := 1 + |(c 0).im| + Real.sqrt Ssp
  have hSsp_nn : 0 ≤ Ssp := by
    simp only [Ssp, MinkowskiSpace.spatialNormSq]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hM_pos : M > 0 := by positivity
  have hMc_pos : M + (c 0).im > 0 := by
    have := neg_abs_le (c 0).im; linarith [Real.sqrt_nonneg Ssp]
  have hMc_gt_sqrt : M + (c 0).im > Real.sqrt Ssp := by
    have h1 : -|(c 0).im| ≤ (c 0).im := neg_abs_le (c 0).im
    linarith
  -- M·e₀ ∈ V₊
  have hMe0_cone : InOpenForwardCone d (fun μ => if μ = 0 then M else 0) := by
    refine ⟨by simp; exact hM_pos, ?_⟩
    rw [MinkowskiSpace.minkowskiNormSq_decomp]
    simp only [MinkowskiSpace.spatialNormSq, ↓reduceIte, Fin.succ_ne_zero]
    simp; nlinarith [sq_nonneg M]
  -- (M + Im(c 0), Im(c 1), ...) ∈ V₊
  have hMc_cone : InOpenForwardCone d
      (fun μ => if μ = 0 then M + (c 0).im else (c μ).im) := by
    refine ⟨by simp; exact hMc_pos, ?_⟩
    rw [MinkowskiSpace.minkowskiNormSq_decomp]
    simp only [↓reduceIte]
    -- spatialNormSq of the shifted vector = Ssp
    have hsp : MinkowskiSpace.spatialNormSq d
        (fun μ => if μ = 0 then M + (c 0).im else (c μ).im) = Ssp := by
      simp only [MinkowskiSpace.spatialNormSq, Ssp, Fin.succ_ne_zero, ↓reduceIte]
    rw [hsp]
    have h1 : (M + (c 0).im) ^ 2 > Ssp := by
      have hsq : Real.sqrt Ssp ^ 2 = Ssp := Real.sq_sqrt hSsp_nn
      have hge : Real.sqrt Ssp ≥ 0 := Real.sqrt_nonneg Ssp
      nlinarith [sq_abs (M + (c 0).im - Real.sqrt Ssp)]
    linarith
  -- The witness z
  set z : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => if μ = 0 then Complex.I * ((↑(k : ℕ) + 1) * M) else 0
  -- Imaginary successive differences for z equal M·e₀
  have him_diff_z : ∀ k : Fin n, (fun μ =>
      (z k μ - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im) =
      fun μ => if μ = 0 then M else 0 := by
    intro k; ext μ
    by_cases hk : (k : ℕ) = 0
    · simp [z, hk]; split_ifs with hμ
      · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
      · simp
    · simp only [z, hk, ↓reduceDIte]; split_ifs with hμ
      · subst hμ; simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]
        have hk1 : (1 : ℕ) ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk
        rw [Nat.cast_sub hk1]; ring
      · simp
  -- For z+c at k > 0, c cancels in successive differences
  have him_diff_zc_pos : ∀ k : Fin n, (k : ℕ) ≠ 0 → (fun μ =>
      ((z k μ + c μ) - (if h : k.val = 0 then (0 : Fin (d+1) → ℂ) else
        fun μ => z ⟨k.val - 1, by omega⟩ μ + c μ) μ).im) =
      fun μ => (z k μ - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im := by
    intro k hk; ext μ; simp [hk, Complex.sub_im]
  -- For z+c at k = 0, get (M + Im(c 0), Im(c_i))
  have him_diff_zc_zero : ∀ k : Fin n, (k : ℕ) = 0 → (fun μ =>
      ((z k μ + c μ) - (if h : k.val = 0 then (0 : Fin (d+1) → ℂ) else
        fun μ => z ⟨k.val - 1, by omega⟩ μ + c μ) μ).im) =
      fun μ => if μ = 0 then M + (c 0).im else (c μ).im := by
    intro k hk; ext μ; simp [hk]; split_ifs with hμ
    · subst hμ; simp [z, hk, Complex.mul_im, Complex.I_re, Complex.I_im]
    · simp [z, hμ]
  refine ⟨z, ?_, ?_⟩
  · -- z ∈ ForwardTube
    intro k; show InOpenForwardCone d _
    rw [him_diff_z]; exact hMe0_cone
  · -- z + c ∈ ForwardTube
    intro k; show InOpenForwardCone d _
    by_cases hk : (k : ℕ) = 0
    · rw [him_diff_zc_zero k hk]; exact hMc_cone
    · rw [him_diff_zc_pos k hk, him_diff_z]; exact hMe0_cone

/-- **BHW extension is translation invariant on the permuted extended tube.**

    The n-point Wightman function W_n(z₁, ..., zₙ) depends only on the differences
    z_k - z_{k-1}, hence is invariant under simultaneous translation z_k ↦ z_k + c
    for any constant c ∈ ℂ^{d+1}. The BHW extension inherits this property.

    **Proof outline.** By BHW uniqueness (property 5 of `bargmann_hall_wightman`):
    1. F_ext is holomorphic on PET (BHW property 1).
    2. G(z) := F_ext(z + c) is holomorphic on PET (by `permutedExtendedTube_translation_closed`
       ensuring z + c ∈ PET, composed with the holomorphic affine map z ↦ z + c).
    3. G and F_ext agree on FT ∩ (FT - c): for z in this set, G(z) = F_ext(z+c) = W_analytic(z+c)
       = W_analytic(z) = F_ext(z) (using `W_analytic_translation_on_forwardTube` and BHW property 2).
    4. FT ∩ (FT - c) is nonempty and open in PET (`forwardTube_inter_translate_nonempty`).
    5. By the identity theorem on the connected domain PET, G = F_ext everywhere on PET.

    Ref: Streater-Wightman §2.5 (translation invariance);
    Jost, "The General Theory of Quantized Fields" §III.1 -/
theorem bhw_translation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c μ) =
    (W_analytic_BHW Wfn n).val z := by
  -- Abbreviations
  set F_ext := (W_analytic_BHW Wfn n).val with hF_ext_def
  set W_analytic := (Wfn.spectrum_condition n).choose
  set G : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z => F_ext (fun k μ => z k μ + c μ)
  -- BHW properties
  have hF_holo := (W_analytic_BHW Wfn n).property.1
  have hF_eq := (W_analytic_BHW Wfn n).property.2.1
  -- PET topology
  have hPET_open : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  have hPET_conn := permutedExtendedTube_isConnected d n
  have hFT_open : IsOpen (ForwardTube d n) :=
    BHW_forwardTube_eq (d := d) (n := n) ▸ BHW.isOpen_forwardTube
  -- Step 1: G is holomorphic on PET
  -- The translation map τ(z)(k)(μ) = z(k)(μ) + c(μ) sends PET into PET
  -- and is holomorphic, so G = F_ext ∘ τ is holomorphic on PET.
  have hG_holo : DifferentiableOn ℂ G (PermutedExtendedTube d n) := by
    intro z₀ hz₀
    -- z₀ + c ∈ PET
    have hz₀c := permutedExtendedTube_translation_closed c z₀ hz₀
    -- F_ext is differentiable at z₀ + c within PET
    have hF_at := hF_holo (fun k μ => z₀ k μ + c μ) hz₀c
    -- The translation map is differentiable
    -- G = F_ext ∘ τ where τ is affine, and τ maps PET → PET
    -- Use DifferentiableWithinAt of composition
    show DifferentiableWithinAt ℂ G (PermutedExtendedTube d n) z₀
    change DifferentiableWithinAt ℂ
      (fun z => F_ext (fun k μ => z k μ + c μ)) (PermutedExtendedTube d n) z₀
    apply DifferentiableWithinAt.comp z₀ hF_at
    · exact differentiableWithinAt_id.add (differentiableWithinAt_const _)
    · intro w hw
      exact permutedExtendedTube_translation_closed c w hw
  -- Step 2: G and F_ext agree on FT ∩ (FT - c)
  -- For z ∈ FT with z + c ∈ FT:
  --   G(z) = F_ext(z + c) = W_analytic(z + c) = W_analytic(z) = F_ext(z)
  have hagree_on_FT : ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ForwardTube d n → (fun k μ => z k μ + c μ) ∈ ForwardTube d n →
      G z = F_ext z := by
    intro w hw hwc
    show F_ext (fun k μ => w k μ + c μ) = F_ext w
    simp only [hF_ext_def]
    rw [hF_eq _ hwc, hF_eq _ hw]
    exact W_analytic_translation_on_forwardTube Wfn c w hw hwc
  -- Step 3: Find z₀ ∈ FT ∩ (FT - c) (nonempty intersection)
  obtain ⟨z₀, hz₀_ft, hz₀c_ft⟩ := forwardTube_inter_translate_nonempty c
  have hz₀_pet : z₀ ∈ PermutedExtendedTube d n :=
    (BHW_permutedExtendedTube_eq (d := d) (n := n) ▸
      BHW.forwardTube_subset_permutedExtendedTube)
      (BHW_forwardTube_eq (d := d) (n := n) ▸ hz₀_ft)
  -- Step 4: G and F_ext agree in a neighborhood of z₀
  -- FT is open and z₀ ∈ FT, so nhds z₀ contains FT-elements.
  -- FT ∩ (FT - c) is open (intersection of two open sets) and contains z₀.
  have hagree_nhds : G =ᶠ[nhds z₀] F_ext := by
    have hU_open : IsOpen (ForwardTube d n ∩
        {w | (fun k μ => w k μ + c μ) ∈ ForwardTube d n}) := by
      apply IsOpen.inter hFT_open
      -- {w | w + c ∈ FT} is open: preimage of FT under continuous translation
      apply hFT_open.preimage
      exact continuous_id.add continuous_const
    have hz₀_mem : z₀ ∈ ForwardTube d n ∩
        {w | (fun k μ => w k μ + c μ) ∈ ForwardTube d n} :=
      ⟨hz₀_ft, hz₀c_ft⟩
    apply Filter.eventuallyEq_of_mem (hU_open.mem_nhds hz₀_mem)
    intro w ⟨hw_ft, hwc_ft⟩
    exact hagree_on_FT w hw_ft hwc_ft
  -- Step 5: By identity theorem on connected PET, G = F_ext on all of PET
  have h_eq := identity_theorem_product hPET_open hPET_conn hG_holo hF_holo hz₀_pet hagree_nhds
  -- Apply at z
  exact h_eq hz

/-- The smeared BHW extension equals the smeared W_analytic for approach directions
    within the forward tube cone.

    When the approach direction η has successive differences in V₊ (not just
    per-component V₊), the point x + iεη lies in the forward tube for all ε > 0.
    Since F_ext = W_analytic on the forward tube (BHW property 2), the integrals
    agree pointwise in ε, so the limits (distributional boundary values) also agree.

    This captures the forward-tube membership calculation: for z_k = x_k + iεη_k,
    the successive difference of imaginary parts is ε(η_k - η_{k-1}), which lies in
    V₊ when η has successive differences in V₊ and ε > 0 (V₊ is a cone).

    Ref: Streater-Wightman, Theorem 2-11; BHW property 2 -/
private theorem bhw_smeared_eq_W_analytic_forwardTube_direction {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη_ft : ∀ k : Fin n,
      let prev := if _h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩
      InOpenForwardCone d (fun μ => η k μ - prev μ))
    (ε : ℝ) (hε : ε > 0) :
    (∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n).val
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
  congr 1; ext x; congr 1
  -- F_ext and W_analytic agree at x + iεη because x + iεη ∈ ForwardTube
  apply (W_analytic_BHW Wfn n).property.2.1
  -- x + iεη ∈ ForwardTube: successive differences of Im parts are ε·(η_k - η_{k-1}) ∈ V₊
  intro k
  show InOpenForwardCone d _
  -- The imaginary part of the successive difference is ε·(η_k - η_{k-1})
  have him : (fun μ => ((↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) -
      (if h : k.val = 0 then 0 else
        fun μ => ↑(x ⟨k.val - 1, by omega⟩ μ) + ↑ε * ↑(η ⟨k.val - 1, by omega⟩ μ) * Complex.I) μ).im) =
      ε • (fun μ => η k μ - (if h : k.val = 0 then 0 else η ⟨k.val - 1, by omega⟩) μ) := by
    ext μ
    by_cases hk : (k : ℕ) = 0
    · simp [hk, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
            Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
    · simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
            Complex.ofReal_re, Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
      ring
  rw [him]
  exact inOpenForwardCone_smul d ε hε _ (hη_ft k)

/-- Convex interpolation of approach directions: if η, η' ∈ V₊ componentwise, then
    for any s ∈ [0,1], the convex combination (1-s)η + sη' also has components in V₊.

    This is because V₊ is convex (inOpenForwardCone_convex). -/
private theorem convex_approach_direction {d n : ℕ} [NeZero d]
    (η η' : Fin n → Fin (d + 1) → ℝ)
    (hη : ∀ k, InOpenForwardCone d (η k))
    (hη' : ∀ k, InOpenForwardCone d (η' k))
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ k, InOpenForwardCone d (fun μ => (1 - s) * η k μ + s * η' k μ) := by
  intro k
  -- Bridge InOpenForwardCone ↔ BHW.InOpenForwardCone (same definition modulo naming)
  have norm_eq : ∀ v : Fin (d + 1) → ℝ,
      MinkowskiSpace.minkowskiNormSq d v = ∑ μ, LorentzLieGroup.minkowskiSignature d μ * v μ ^ 2 := by
    intro v
    simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.metricSignature, LorentzLieGroup.minkowskiSignature]
    congr 1; ext i; ring
  have to_bhw : ∀ v, InOpenForwardCone d v → BHW.InOpenForwardCone d v := by
    intro v ⟨hv0, hv_norm⟩
    exact ⟨hv0, norm_eq v ▸ hv_norm⟩
  have from_bhw : ∀ v, BHW.InOpenForwardCone d v → InOpenForwardCone d v := by
    intro v ⟨hv0, hv_norm⟩
    exact ⟨hv0, (norm_eq v).symm ▸ hv_norm⟩
  have hη_bhw : η k ∈ {η : Fin (d + 1) → ℝ | BHW.InOpenForwardCone d η} := to_bhw _ (hη k)
  have hη'_bhw : η' k ∈ {η : Fin (d + 1) → ℝ | BHW.InOpenForwardCone d η} := to_bhw _ (hη' k)
  have hmem := BHW.inOpenForwardCone_convex hη_bhw hη'_bhw (by linarith : 0 ≤ 1 - s)
    hs0 (by ring : (1 - s) + s = 1)
  simp only [Set.mem_setOf_eq] at hmem
  exact from_bhw _ hmem

/-- The BV limit along a convex combination of approach directions equals the
    BV limit along either endpoint.

    If the BV limit exists along η (giving L), then for any s ∈ [0,1], the BV
    limit along η_s = (1-s)η + sη' also equals L. This is because:
    1. The function Φ(s) := lim_{ε→0+} ∫ F(x + iε·η_s) f(x) dx is well-defined
       for all s ∈ [0,1] (η_s ∈ V₊ by convexity of V₊)
    2. Φ is constant on [0,1]: the holomorphic dependence on the approach parameter
       and the Cauchy integral formula show Φ is analytic in s, and the dominated
       convergence + polynomial growth estimates show it's continuous. A continuous
       function on a connected set that's locally constant is constant.
    3. Φ(0) = L, so Φ(1) = L.

    This is the core of Vladimirov's direction-independence theorem (Ch.12).

    Blocked by: The holomorphic parameter dependence (Cauchy integral formula for
    the s-parameter) and the interchange of limit and integral (dominated convergence
    using polynomial growth estimates from Vladimirov Thm 25.5).

    Ref: Vladimirov §12.4; Streater-Wightman, Theorem 2-11 -/
private theorem bv_limit_constant_along_convex_path {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (PermutedExtendedTube d n))
    (f : SchwartzNPoint d n)
    (η η' : Fin n → Fin (d + 1) → ℝ)
    (hη : ∀ k, InOpenForwardCone d (η k))
    (hη' : ∀ k, InOpenForwardCone d (η' k))
    (L : ℂ)
    (hL : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L))
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑((1 - s) * η k μ + s * η' k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  sorry

private theorem distributional_bv_direction_independence {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (PermutedExtendedTube d n))
    (f : SchwartzNPoint d n)
    (η η' : Fin n → Fin (d + 1) → ℝ)
    (hη : ∀ k, InOpenForwardCone d (η k))
    (hη' : ∀ k, InOpenForwardCone d (η' k))
    (L : ℂ)
    (hL : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑(η' k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  -- Use bv_limit_constant_along_convex_path with s = 1:
  -- η₁ = (1-1)·η + 1·η' = η'
  have h := bv_limit_constant_along_convex_path F hF f η η' hη hη' L hL 1 (by norm_num) le_rfl
  -- Simplify: (1-1)*η k μ + 1*η' k μ = η' k μ
  simp only [sub_self, zero_mul, zero_add, one_mul] at h
  exact h

/-- The BHW extension has the same distributional boundary values as W_n.

    The BHW extension F_ext agrees with W_analytic on the forward tube, and
    W_analytic has distributional boundary values recovering W_n by `spectrum_condition`.
    Therefore F_ext also has these boundary values: for η with each η_k ∈ V+,
    lim_{ε→0+} ∫ F_ext(x + iεη) f(x) dx = W_n(f).

    **Proof strategy:** We decompose the argument into two steps:

    1. **Forward tube directions** (`bhw_smeared_eq_W_analytic_forwardTube_direction`):
       For approach directions η where successive differences η_k - η_{k-1} ∈ V+,
       the point x + iεη lies in the forward tube, so F_ext = W_analytic pointwise.
       The integrals agree, and `spectrum_condition` gives the BV limit = W_n(f).

    2. **Direction independence** (`distributional_bv_direction_independence`):
       The distributional BV of a holomorphic function on a tube domain is independent
       of the approach direction within the cone. This standard result (Vladimirov,
       Streater-Wightman Thm 2-11) extends the BV from forward-tube directions to
       all per-component V+ directions.

    **Approach direction convention:** This theorem uses the same per-component approach
    direction `∀ k, η_k ∈ V+` as `spectrum_condition` and `IsWickRotationPair`.

    Ref: Streater-Wightman Theorem 2-11 -/
theorem bhw_distributional_boundary_values {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic_BHW Wfn n).val
            (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)) := by
  intro f η hη
  -- Step 1: Construct a "nice" approach direction η₀ with successive differences in V₊.
  -- Define η₀_k(μ) := (k+1) · η_0(μ), so that:
  --   η₀_0 = η_0 ∈ V₊
  --   η₀_k - η₀_{k-1} = η_0 ∈ V₊  for all k > 0
  -- This ensures x + iεη₀ ∈ ForwardTube for all ε > 0.
  -- Each η₀_k = (k+1) · η_0 ∈ V₊ since V₊ is a cone.
  -- We pick η_0 from the given η (using η applied to any valid index).
  -- For this to work, we need n > 0. When n = 0, the statement is vacuous
  -- (Fin 0 is empty, so the integral is trivially equal).
  by_cases hn : n = 0
  · -- n = 0: the integral over Fin 0 → ... is a degenerate case.
    -- The integrand doesn't depend on ε (since Fin 0 is empty), so the
    -- function is constant and trivially converges.
    subst hn
    -- With n = 0, Fin 0 is empty, so z(x,ε) doesn't depend on ε.
    -- F_ext = W_analytic on ForwardTube, and ForwardTube d 0 = univ (vacuous conditions).
    -- The integrand is the same for F_ext and W_analytic, and spectrum_condition gives the limit.
    -- Step 1: F_ext and W_analytic agree at all points (ForwardTube d 0 = univ)
    have hft_univ : ∀ z : Fin 0 → Fin (d+1) → ℂ, z ∈ ForwardTube d 0 := by
      intro z k; exact Fin.elim0 k
    -- Step 2: The integrands are equal for all ε
    have hcongr : ∀ ε : ℝ,
        (∫ x : NPointDomain d 0,
          (W_analytic_BHW Wfn 0).val
            (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) * f x) =
        (∫ x : NPointDomain d 0,
          (Wfn.spectrum_condition 0).choose
            (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) * f x) := by
      intro ε; congr 1; ext x; congr 1
      exact (W_analytic_BHW Wfn 0).property.2.1 _ (hft_univ _)
    simp_rw [hcongr]
    -- Step 3: spectrum_condition gives the limit for W_analytic
    have hη_cone : ∀ k : Fin 0, InOpenForwardCone d (η k) := fun k => Fin.elim0 k
    exact (Wfn.spectrum_condition 0).choose_spec.2 f η hη_cone
  · -- n > 0: construct the nice approach direction
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    set η₀ : Fin n → Fin (d + 1) → ℝ :=
      fun k μ => (↑k.val + 1) * η ⟨0, hn_pos⟩ μ with hη₀_def
    -- η₀ has successive differences in V₊ (each difference = η_0)
    have hη₀_ft : ∀ k : Fin n,
        let prev := if h : k.val = 0 then (0 : Fin (d + 1) → ℝ)
          else η₀ ⟨k.val - 1, by omega⟩
        InOpenForwardCone d (fun μ => η₀ k μ - prev μ) := by
      intro k
      simp only [hη₀_def]
      split
      case isTrue h =>
        -- k = 0: difference is (0+1) · η_0 - 0 = η_0 ∈ V₊
        simp [h]
        exact hη ⟨0, hn_pos⟩
      case isFalse h =>
        -- k > 0: difference is (k+1)·η_0 - ((k-1)+1)·η_0 = η_0 ∈ V₊
        -- The difference simplifies to ((k+1) - k) · η_0 = η_0
        have hk_pos : 0 < k.val := Nat.pos_of_ne_zero h
        have h_diff : (fun μ => (↑k.val + 1) * η ⟨0, hn_pos⟩ μ -
            (↑(k.val - 1) + 1) * η ⟨0, hn_pos⟩ μ) =
            fun μ => η ⟨0, hn_pos⟩ μ := by
          ext μ
          have hcast : (↑(k.val - 1) : ℝ) = (↑k.val : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ k.val)]
            simp
          rw [hcast]; ring
        rw [h_diff]
        exact hη ⟨0, hn_pos⟩
    -- Each η₀_k ∈ V₊ (since V₊ is closed under positive scaling)
    have hη₀_cone : ∀ k, InOpenForwardCone d (η₀ k) := by
      intro k
      simp only [hη₀_def]
      have heq : (fun μ => ((↑↑k : ℝ) + 1) * η ⟨0, hn_pos⟩ μ) =
          ((↑↑k : ℝ) + 1) • η ⟨0, hn_pos⟩ := by
        ext μ; simp [Pi.smul_apply, smul_eq_mul]
      rw [heq]
      exact inOpenForwardCone_smul d ((↑↑k : ℝ) + 1) (by positivity) _ (hη ⟨0, hn_pos⟩)
    -- Step 2: BV of F_ext for η₀.
    -- spectrum_condition gives BV of W_analytic for η₀:
    --   lim ∫ W_analytic(x + iεη₀) f(x) dx = W_n(f)
    have h_sc := (Wfn.spectrum_condition n).choose_spec.2 f η₀ hη₀_cone
    -- F_ext = W_analytic on forward tube, and x + iεη₀ ∈ FT, so integrals agree
    have h_bv_η₀ : Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic_BHW Wfn n).val
            (fun k μ => ↑(x k μ) + ε * ↑(η₀ k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Wfn.W n f)) := by
      -- The F_ext integral equals the W_analytic integral for each ε > 0
      apply Filter.Tendsto.congr' _ h_sc
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε =>
        (bhw_smeared_eq_W_analytic_forwardTube_direction Wfn f η₀ hη₀_ft ε hε).symm⟩
    -- Step 3: Apply direction independence to go from η₀ to arbitrary η
    exact distributional_bv_direction_independence
      (W_analytic_BHW Wfn n).val
      (W_analytic_BHW Wfn n).property.1
      f η₀ η hη₀_cone hη (Wfn.W n f) h_bv_η₀

/-! #### Schwinger function construction -/

/-- Define Schwinger functions from Wightman functions via Wick rotation.

    The construction uses the BHW extension F_ext (from `W_analytic_BHW`) composed
    with the Wick rotation map (τ,x⃗) ↦ (iτ,x⃗):

      S_n(f) = ∫_x F_ext_n(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) f(x₁,...,xₙ) dx

    where F_ext is the BHW extension of W_analytic to the permuted extended tube.
    We use F_ext rather than W_analytic because F_ext is defined and well-behaved
    on all Euclidean points (not just time-ordered ones), and carries the complex
    Lorentz invariance and permutation symmetry needed for E1b and E3.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def constructSchwingerFunctions (Wfn : WightmanFunctions d) :
    SchwingerFunctions d :=
  fun n f =>
    ∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * (f x)

/-- **Vladimirov growth on the forward tube (no compact cone restriction).**

    For F holomorphic on ForwardTube d n with tempered distributional boundary values,
    ‖F(z)‖ ≤ C * (1 + ‖z‖)^N for all z in ForwardTube d n.

    This strengthens `polynomial_growth_forwardTube` (which requires Im(z) in compact K
    subset of the cone) to allow Im(z) anywhere in the forward cone, including approaching
    the boundary. The full Vladimirov estimate (Thm 25.5) gives
    ‖F(x+iy)‖ ≤ C(1+‖x‖+‖y‖)^N * dist(y,bdry C)^{-M}, and for holomorphic functions
    with tempered BV the combined expression is bounded by C'(1+‖z‖)^{N'}.

    Blocked by: Fourier-Laplace representation of tube domain holomorphic functions,
    Paley-Wiener-Schwartz theorem (neither in Mathlib).

    Ref: Vladimirov, "Methods of Generalized Functions", Theorem 25.5;
         Streater-Wightman Thm 2-6 -/
private theorem polynomial_growth_forwardTube_full {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (h_bv : ∀ (η : Fin n → Fin (d + 1) → ℝ), (∀ k, InOpenForwardCone d (η k)) →
      ∃ (T : NPointDomain d n → ℂ), ContinuousOn T Set.univ ∧
        ∀ (f : NPointDomain d n → ℂ), MeasureTheory.Integrable f →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x : NPointDomain d n,
              F (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ x, T x * f x))) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  sorry

/-- **Polynomial growth on the permuted extended tube.**

    The BHW extension F_ext satisfies polynomial growth on the full PET.
    This combines `polynomial_growth_forwardTube_full` (Vladimirov estimate on each
    tube sector) with BHW Lorentz and permutation invariance to obtain a uniform
    bound across all sectors.

    For z in PET: z = Lambda * w where w is in PermutedForwardTube d n pi for some pi.
    By BHW Lorentz invariance, F_ext(z) = F_ext(w). By permutation invariance,
    F_ext(w) = F_ext(w circ pi) where w circ pi is in ForwardTube. The Vladimirov
    estimate bounds ‖F_ext(w circ pi)‖ and the norm relation ‖w circ pi‖ = ‖w‖
    transfers the bound. The Lorentz transform norm ‖w‖ vs ‖z‖ requires the
    complex Lorentz group structure (Λ invertible with bounded inverse on each orbit).

    Ref: Streater-Wightman Thm 2-6 -/
private theorem polynomial_growth_on_PET {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        ‖(W_analytic_BHW Wfn n).val z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  sorry

/-- Wick rotation of a single point preserves each component norm:
    `‖wickRotatePoint x i‖ = ‖x i‖` for each i.
    - i = 0: `‖I * ↑(x 0)‖ = |x 0|` since `‖I‖ = 1`
    - i > 0: `‖↑(x i)‖ = |x i|` since `Complex.norm_real` -/
private theorem wickRotatePoint_component_norm_eq {d : ℕ}
    (x : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    ‖wickRotatePoint x i‖ = ‖x i‖ := by
  simp only [wickRotatePoint]; split_ifs with h
  · subst h; rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
  · rw [Complex.norm_real]

/-- The norm of a Wick-rotated Euclidean configuration is at most the original norm.

    Since `‖wickRotatePoint(x k) i‖ = ‖x k i‖` componentwise, and the Pi norm
    is the sup over all components, the Wick-rotated norm equals the original.
    We prove ≤ which suffices for the polynomial growth argument. -/
private theorem wickRotate_norm_le {d n : ℕ}
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

private theorem bhw_polynomial_growth_on_euclidean {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : NPointDomain d n),
        (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n →
        ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤
          C_bd * (1 + ‖x‖) ^ N := by
  -- Get the polynomial growth bound on PET
  obtain ⟨C_bd, N, hC, hgrowth⟩ := polynomial_growth_on_PET Wfn
  refine ⟨C_bd, N, hC, fun x hx_pet => ?_⟩
  -- Apply the PET growth bound: ‖F_ext(z)‖ ≤ C * (1 + ‖z‖)^N
  have hz := hgrowth (fun k => wickRotatePoint (x k)) hx_pet
  -- Relate ‖z‖ to ‖x‖: ‖wickRotate(x)‖ ≤ ‖x‖
  calc ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖
      ≤ C_bd * (1 + ‖fun k => wickRotatePoint (x k)‖) ^ N := hz
    _ ≤ C_bd * (1 + ‖x‖) ^ N := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply pow_le_pow_left₀ (by positivity)
        linarith [wickRotate_norm_le x]

/-- **Polynomial growth of the Wick-rotated BHW kernel.**

    The BHW extension F_ext, evaluated at Wick-rotated Euclidean points, has at most
    polynomial growth: there exist C > 0 and N ∈ ℕ such that for a.e. x ∈ ℝ^{n(d+1)},

        ‖F_ext(Wick(x))‖ ≤ C · (1 + ‖x‖)^N

    This combines two ingredients:
    1. `polynomial_growth_tube`: On each tube in the permuted extended tube, F_ext
       satisfies polynomial growth bounds (Streater-Wightman Thm 2-6).
    2. `ae_euclidean_points_in_permutedTube`: For a.e. Euclidean configuration x,
       the Wick-rotated point lies in PET.

    The bound holds uniformly because the n! tubes in PET each contribute a polynomial
    bound, and the finite maximum of polynomially bounded functions is polynomially bounded.

    Ref: Streater-Wightman Thm 2-6; OS I Prop 5.1 -/
theorem bhw_euclidean_polynomial_bound {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
        ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤
          C_bd * (1 + ‖x‖) ^ N := by
  -- Get the pointwise polynomial growth bound on PET
  obtain ⟨C_bd, N, hC, hgrowth⟩ := bhw_polynomial_growth_on_euclidean Wfn
  exact ⟨C_bd, N, hC,
    Filter.Eventually.mono ae_euclidean_points_in_permutedTube (fun x hx => hgrowth x hx)⟩

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
private theorem schwartz_polynomial_kernel_continuous {d n : ℕ} [NeZero d]
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

/-- Schwinger functions constructed via Wick rotation are tempered (E0).

    The integral S_n(f) = ∫ F_ext(Wick(x)) f(x) dx defines a continuous linear
    functional on the Schwartz space. The proof combines:

    1. `bhw_euclidean_polynomial_bound`: The kernel F_ext(Wick(x)) has polynomial
       growth for a.e. x (from polynomial_growth_tube + ae_euclidean_points_in_permutedTube).
    2. `bhw_euclidean_kernel_measurable`: The kernel is a.e. strongly measurable.
    3. `schwartz_continuous_of_polynomial_bound`: A polynomially bounded measurable kernel
       defines a continuous functional on Schwartz space via integration.

    Ref: OS I (1973) Proposition 5.1 -/
theorem wick_rotated_schwinger_tempered {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (n : ℕ) :
    Continuous (constructSchwingerFunctions Wfn n) := by
  -- The goal is: Continuous (fun f => ∫ x, F_ext(Wick(x)) * f(x) dx)
  -- Obtain the polynomial bound on the BHW kernel at Euclidean points
  obtain ⟨C_bd, N, hC, hbound⟩ := bhw_euclidean_polynomial_bound (n := n) Wfn
  -- Obtain measurability of the kernel
  have hmeas := bhw_euclidean_kernel_measurable (n := n) Wfn
  -- The function constructSchwingerFunctions Wfn n is definitionally equal to
  -- fun f => ∫ x, K(x) * f(x) where K(x) = F_ext(Wick(x))
  show Continuous (fun f : SchwartzNPoint d n =>
    ∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * (f x))
  exact schwartz_continuous_of_polynomial_bound
    (fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)))
    hmeas C_bd N hC hbound

/-- The Schwinger functions constructed from Wightman functions satisfy temperedness (E0).

    This follows from the temperedness of Wightman functions (R0) and the
    geometric estimates in OS I, Proposition 5.1: the Wick-rotated kernel
    composed with f is integrable and the integral depends continuously on f. -/
theorem constructedSchwinger_tempered (Wfn : WightmanFunctions d) (n : ℕ) :
    Continuous (constructSchwingerFunctions Wfn n) := by
  exact wick_rotated_schwinger_tempered Wfn n

/-- The BHW extension F_ext inherits translation invariance from the Wightman
    distribution W_n.

    Both z ↦ F_ext(z) and z ↦ F_ext(z + c) (for real c) are holomorphic on the
    permuted extended tube with the same distributional boundary values (by
    translation invariance of W_n). By uniqueness of analytic continuation on the
    connected permuted extended tube, they agree.

    Requires: identity theorem for holomorphic functions on tube domains in ℂⁿ.
    The multi-dimensional identity theorem is proved in `SCV/IdentityTheorem.lean`
    (modulo Hartogs analyticity).

    Ref: Streater-Wightman, Theorem 2.8 (uniqueness of holomorphic extension to tubes) -/
private theorem F_ext_translation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (a : SpacetimeDim d) (x : NPointDomain d n)
    (htube : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
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
    (fun k => wickRotatePoint (x k)) htube).symm

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
  -- K is translation-invariant a.e.: K(x) = K(x + a') for a.e. x with wick(x) ∈ PET
  have hK_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      K x = K (x + a') := by
    filter_upwards [ae_euclidean_points_in_permutedTube] with x hx
    exact F_ext_translation_invariant Wfn n a x hx
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
private theorem F_ext_rotation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
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

/-- The OS inner product for Wick-rotated Schwinger functions reduces to
    the Wightman positivity form after the rotation.

    For test functions F supported in τ > 0, the time-reflection θ sends
    τ to -τ, which under Wick rotation corresponds to complex conjugation
    of the time variables. The resulting quadratic form equals the Wightman
    inner product, which is non-negative by R2.

    Blocked by: the explicit computation showing that time-reflection + Wick rotation
    = complex conjugation of the analytic continuation, and the identification of
    the OS inner product with the Wightman inner product after this substitution.

    Ref: OS I, Section 5 (proof that E2 follows from R2); Glimm-Jaffe Ch. 19 -/
private theorem os_inner_product_eq_wightman_positivity (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
      x ∈ PositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 := by
  sorry

theorem constructedSchwinger_reflection_positive (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
      x ∈ PositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 :=
  os_inner_product_eq_wightman_positivity Wfn F hsupp

/-- F_ext is invariant under permutations of arguments at all Euclidean points.

    For Euclidean points with distinct positive times, this follows directly from
    BHW permutation symmetry (`schwinger_permutation_symmetric` in
    AnalyticContinuation.lean) + `euclidean_distinct_in_permutedTube`. For general
    configurations, it extends by analyticity of F_ext ∘ Wick.

    Ref: Jost, §IV.5; Streater-Wightman, Theorem 3.6 -/
private theorem F_ext_permutation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
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
private theorem bhw_pointwise_cluster_euclidean (Wfn : WightmanFunctions d) (n m : ℕ)
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

/-! ### OS to Wightman (Theorem E'→R') -/

/-- Phase 2: The Euclidean time translation semigroup.

    For t > 0, define the operator T(t) on the Hilbert space by:
      T(t) [f](τ₁,...,τₙ) = [f(τ₁ + t,..., τₙ + t)]

    This gives a contraction semigroup with:
    - T(s)T(t) = T(s+t)
    - ‖T(t)‖ ≤ 1 (contraction, from E2)
    - T(t) → I as t → 0⁺ (strong continuity, from E0)

    By the Hille-Yosida theorem, T(t) = e^{-tH} where H ≥ 0 is self-adjoint.
    This H is the Hamiltonian of the reconstructed QFT. -/
structure EuclideanSemigroup (OS : OsterwalderSchraderAxioms d) where
  /-- The semigroup parameter (Euclidean time) -/
  T : ℝ → (BorchersSequence d → BorchersSequence d)
  /-- Semigroup property: T(s) ∘ T(t) = T(s+t) -/
  semigroup : ∀ s t : ℝ, s > 0 → t > 0 → T s ∘ T t = T (s + t)
  /-- Contraction: ‖T(t)F‖ ≤ ‖F‖ -/
  contraction : ∀ t : ℝ, t > 0 → ∀ F : BorchersSequence d,
    (OSInnerProduct d OS.S (T t F) (T t F)).re ≤
    (OSInnerProduct d OS.S F F).re
  /-- Positivity: T(t) ≥ 0 as an operator -/
  positive : ∀ t : ℝ, t > 0 → ∀ F : BorchersSequence d,
    (OSInnerProduct d OS.S F (T t F)).re ≥ 0

/- Phase 3: Analytic continuation from Euclidean to Minkowski.

    The analytic continuation proceeds inductively. Starting from Schwinger functions
    S_n defined on Euclidean configurations, we extend to complex times.

    **Inductive structure** (OS II, Theorem 4.1):
    - A₀: S_k(ξ) is analytic on {ξ ∈ ℝ^k : ξⱼ > 0 for all j}
    - Aᵣ: S_k has analytic continuation to the region C_k^(r) ⊂ ℂ^k
      where r of the ξ-variables are complexified
    - After n = d + 1 steps, reach the full forward tube

    **Key estimate** (OS II, Theorem 4.2): At each step, the linear growth
    condition E0' provides the bounds needed for the continuation. -/

/-- The region C_k^(r) from OS II: the domain after r steps of analytic continuation.
    C_k^(0) = {ξ ∈ ℝ^k : ξⱼ > 0} (positive real half-space, all coordinates real)
    C_k^(r+1) extends the first r+1 spacetime coordinates to complex (Im diff > 0),
    while the remaining d-r coordinates stay real (Im = 0).

    **Note**: C_k^(d+1) is a tube over the positive orthant (0,∞)^{d+1} (each
    component of imaginary differences is positive). This is STRICTLY SMALLER
    than the forward tube T_k (which requires imaginary differences in V₊, the
    forward light cone). To reach T_k from C_k^(d+1), one needs:
    1. Euclidean rotation invariance (E1) to extend to SO(d+1)-rotated copies
    2. Bochner's tube theorem to extend to the convex hull = forward tube

    The regions EXPAND as r increases: C_k^(r) ⊂ C_k^(r+1), because each step
    frees one more coordinate from the "must be real" constraint. -/
def AnalyticContinuationRegion (d k r : ℕ) [NeZero d] :
    Set (Fin k → Fin (d + 1) → ℂ) :=
  match r with
  | 0 => -- All real, positive Euclidean times
    { z | (∀ i : Fin k, ∀ μ : Fin (d + 1), (z i μ).im = 0) ∧
          (∀ i : Fin k, (z i 0).re > 0) }
  | r + 1 => -- First r+1 coordinates complex with positive imaginary part,
    -- remaining coordinates must be real
    { z | (∀ i : Fin k,
        ∀ μ : Fin (d + 1), μ.val ≤ r →
          let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
          (z i μ - prev μ).im > 0) ∧
       (∀ i : Fin k,
        ∀ μ : Fin (d + 1), μ.val > r →
          (z i μ).im = 0) }

/-- **Inductive analytic continuation (OS II, Theorem 4.1).**

    Given S holomorphic on C_k^(r) (where r spacetime coordinates are complex),
    extend it analytically to C_k^(r+1) (one more coordinate becomes complex).

    The proof at each step uses the **Paley-Wiener theorem** (one variable):
    1. Fix all variables except the (r+1)-th spacetime component of each ξ_j.
       The result is a function of k−1 real variables (the (r+1)-th components
       of the difference vectors ξ_1, ..., ξ_{k−1}).
    2. The E0' linear growth condition gives polynomial bounds on each variable.
    3. The spectral condition (from reflection positivity / positivity of the
       Hamiltonian) ensures the Fourier transform in each variable has one-sided
       support in [0, ∞). Physically: the spectral measure is supported in the
       forward cone V̄₊, so each spatial momentum component is bounded by the
       energy (|p^μ| ≤ p^0).
    4. The **Paley-Wiener theorem**: a function on ℝ with polynomial growth
       whose Fourier transform has support in [0, ∞) extends holomorphically to
       the upper half-plane {Im z > 0}, with polynomial growth.
    5. Extend one variable at a time, then apply Osgood's lemma
       (`osgood_lemma`, proved in SeparatelyAnalytic.lean) for joint holomorphicity.

    None of this is currently in Mathlib: the Paley-Wiener theorem for tempered
    distributions, the spectral representation of reflection-positive functionals,
    and the extraction of one-sided Fourier support from E0' + E2.

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 (Paley-Wiener);
    Vladimirov §26 (Fourier-Laplace representation) -/
theorem inductive_analytic_continuation {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) (r : ℕ) (hr : r < d + 1)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z := by
  -- The proof uses Paley-Wiener to extend one spacetime coordinate at a time.
  -- Key mathematical inputs (extracted as atomic helpers):
  -- 1. One-sided Fourier support from E0' + E2 (spectral condition from
  --    reflection positivity + linear growth)
  -- 2. Polynomial growth in each variable from E0'
  -- Given these, the Paley-Wiener theorem (paley_wiener_one_step_simple in
  -- PaleyWiener.lean) extends holomorphicity from the real line to the upper
  -- half-plane in the (r+1)-th spacetime coordinate.
  -- Joint holomorphicity then follows from Osgood's lemma.
  --
  -- The assembly of paley_wiener_one_step + Osgood into the region extension
  -- is a routine but technically involved plumbing exercise. We decompose:
  -- Step 1: For each fixed z' in C_k^(r), the r-th coordinate slice satisfies PW
  -- Step 2: The PW extension gives holomorphicity in the new coordinate
  -- Step 3: Osgood's lemma gives joint holomorphicity on C_k^(r+1)
  -- Step 4: Agreement on C_k^(r) follows from PW agreement on the real line
  --
  -- Each step depends on infrastructure from PaleyWiener.lean (which has sorry
  -- for paley_wiener_one_step_simple but is correctly typed).
  sorry

/-! ### Full analytic continuation from Euclidean to forward tube

After d+1 applications of `inductive_analytic_continuation`, we reach C_k^(d+1),
a tube over the positive orthant. To reach the full forward tube, we use:
1. Euclidean rotation invariance (E1) to extend to rotated copies
2. Bochner's tube theorem to extend to the convex hull = forward tube

Ref: OS II, Sections IV-V; Bochner (1938); Vladimirov Section 20.2 -/

/-- Iterate `inductive_analytic_continuation` d+1 times: from C_k^(0) to C_k^(d+1).
    Blocked by: formal iteration + composing agreement conditions.
    Ref: OS II, Theorem 4.1 -/
private theorem iterated_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (k : ℕ)
    (S_base : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_base : DifferentiableOn ℂ S_base (AnalyticContinuationRegion d k 0)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (d + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k 0, S_ext z = S_base z := by
  sorry

/-- Schwinger functions on C_k^(0), recovering S_k via integration.
    Blocked by: pointwise extraction from S_k and smoothness in positive-time region.
    Ref: OS II, Section IV (base case) -/
private theorem schwinger_holomorphic_on_base_region
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (k : ℕ) :
    ∃ (S_base : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_base (AnalyticContinuationRegion d k 0) ∧
      (∀ (f : SchwartzNPoint d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_base (fun j => wickRotatePoint (x j)) * (f x)) := by
  sorry

/-- Extend from C_k^(d+1) to the forward tube via E1 + Bochner.
    Blocked by: tube domain identification and `bochner_tube_extension`.
    Ref: OS II, Section V; Bochner (1938) -/
private theorem extend_to_forward_tube_via_bochner (k : ℕ)
    (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_ext : DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (d + 1)))
    (h_rot : ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ z ∈ AnalyticContinuationRegion d k (d + 1),
        S_ext (fun i μ => ∑ ν, (R μ ν : ℂ) * z i ν) = S_ext z) :
    ∃ (W : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W (ForwardTube d k) ∧
      ∀ z ∈ AnalyticContinuationRegion d k (d + 1), W z = S_ext z := by
  sorry

theorem full_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : SchwartzNPoint d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f x)) := by
  -- Step 1: Base case
  obtain ⟨S_base, hS_base_hol, hS_base_euclid⟩ :=
    schwinger_holomorphic_on_base_region OS lgc k
  -- Step 2: Iterate d+1 times
  obtain ⟨S_ext, hS_ext_hol, hS_ext_agree⟩ :=
    iterated_analytic_continuation OS lgc k S_base hS_base_hol
  -- Step 3: Rotation invariance from E1 + analytic continuation uniqueness
  have h_rot : ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ z ∈ AnalyticContinuationRegion d k (d + 1),
        S_ext (fun i μ => ∑ ν, (R μ ν : ℂ) * z i ν) = S_ext z := by
    sorry
  -- Step 4: E1 + Bochner to extend to forward tube
  obtain ⟨W, hW_hol, hW_agree⟩ := extend_to_forward_tube_via_bochner k S_ext hS_ext_hol h_rot
  refine ⟨W, hW_hol, fun f => ?_⟩
  -- Step 5: Euclidean restriction chain
  -- W(wick(x)) = S_ext(wick(x)) = S_base(wick(x)) for wick(x) in C_k^(0)
  sorry

/-! ### Phase 4: Tempered boundary values

**Critical**: E0' (linear growth condition) is essential for temperedness.
Without growth control, boundary values might fail to be tempered
(the gap in OS I Lemma 8.8). E0' gives |W_n(f)| <= C_n * ||f||_{s,n}
where C_n has at most factorial growth.

Ref: OS II, Section VI -/

/-- Distributional boundary values of the forward tube analytic continuation
    exist and are tempered.

    Given F holomorphic on ForwardTube d n with polynomial growth (from E0'),
    the distributional BV ∫ F(x + iεη) f(x) dx converges as ε → 0+ for
    all Schwartz f and approach directions η ∈ V₊^n.

    Blocked by: Vladimirov's distributional boundary value theorem for tube
    domains (Theorem 26.1 in Vladimirov's "Methods of Generalized Functions"),
    which requires polynomial growth estimates from E0'.

    Ref: Vladimirov Section 26; Streater-Wightman Theorem 2-9 -/
private theorem forward_tube_bv_tempered
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n)) :
    ∃ (W_n : SchwartzNPoint d n → ℂ),
      Continuous W_n ∧ IsLinearMap ℂ W_n ∧
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W_n f))) ∧
      ∃ (C : ℝ) (s : ℕ), C > 0 ∧
        ∀ f : SchwartzNPoint d n,
          ‖W_n f‖ ≤ C * lgc.alpha * lgc.beta ^ n * (n.factorial : ℝ) ^ lgc.gamma *
            SchwartzMap.seminorm ℝ s s f := by
  sorry

theorem boundary_values_tempered
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ (W_n : SchwartzNPoint d n → ℂ) (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- W_n is continuous (tempered distribution)
      Continuous W_n ∧
      -- W_n is linear
      IsLinearMap ℂ W_n ∧
      -- F_analytic is holomorphic on the forward tube
      DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
      -- Boundary values of F_analytic give W_n
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W_n f))) ∧
      -- Euclidean restriction of F_analytic gives S_n
      (∀ (f : SchwartzNPoint d n),
        OS.S n f = ∫ x : NPointDomain d n,
          F_analytic (fun k => wickRotatePoint (x k)) * (f x)) ∧
      -- Growth estimate (linear growth condition on Wightman side, R0')
      ∃ (C : ℝ) (s : ℕ), C > 0 ∧
        ∀ f : SchwartzNPoint d n,
          ‖W_n f‖ ≤ C * lgc.alpha * lgc.beta ^ n * (n.factorial : ℝ) ^ lgc.gamma *
            SchwartzMap.seminorm ℝ s s f := by
  -- Step 1: Get the analytic continuation from full_analytic_continuation
  obtain ⟨F_analytic, hF_hol, hF_euclid⟩ := full_analytic_continuation OS lgc n
  -- Step 2: Get tempered boundary values from forward_tube_bv_tempered
  obtain ⟨W_n, hW_cont, hW_lin, hW_bv, hW_growth⟩ :=
    forward_tube_bv_tempered OS lgc n F_analytic hF_hol
  exact ⟨W_n, F_analytic, hW_cont, hW_lin, hF_hol, hW_bv, hF_euclid, hW_growth⟩

/-! ### Constructing WightmanFunctions from OS Data

Each Wightman axiom is derived from the corresponding OS axiom via analytic
continuation. The helper lemmas below capture each derivation. -/

/-- The n-point Wightman distribution `W_n` extracted from `boundary_values_tempered`.

    `boundary_values_tempered` returns `∃ W_n F_analytic, Continuous W_n ∧ IsLinearMap ℂ W_n ∧ ...`.
    This definition extracts `W_n` via `.choose` (the first existential witness).

    `W_n` is the tempered distributional boundary value of the analytically continued
    function `F_analytic` on the forward tube. It is continuous (tempered) and linear,
    and satisfies factorial growth bounds from the OS linear growth condition.

    Note: `boundary_values_tempered` is currently sorry'd, so `bvt_W` and all downstream
    properties extracted from it are logically contingent on that proof obligation. -/
private def bvt_W (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    SchwartzNPoint d n → ℂ :=
  (boundary_values_tempered OS lgc n).choose

/-- The holomorphic function `F_analytic` on the forward tube, extracted from
    `boundary_values_tempered`.

    `boundary_values_tempered` returns `∃ W_n F_analytic, ... ∧ DifferentiableOn ℂ F_analytic
    (ForwardTube d n) ∧ ...`. This definition extracts `F_analytic` via
    `.choose_spec.choose` (the second existential witness, nested inside the first).

    `F_analytic` is holomorphic on `ForwardTube d n`, its distributional boundary values
    recover `bvt_W` (the Wightman distribution), and its Euclidean restriction
    (via Wick rotation) recovers the Schwinger functions `OS.S n`.

    Note: `boundary_values_tempered` is currently sorry'd, so `bvt_F` and all downstream
    properties extracted from it are logically contingent on that proof obligation. -/
private def bvt_F (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  (boundary_values_tempered OS lgc n).choose_spec.choose

private theorem bvt_F_holomorphic (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    DifferentiableOn ℂ (bvt_F OS lgc n) (ForwardTube d n) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.1

private theorem bvt_boundary_values (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc n f)) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.2.1

private theorem bvt_euclidean_restriction (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : SchwartzNPoint d n),
      OS.S n f = ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (f x) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.2.2.1

/-! #### Helper lemmas for property transfer: OS axiom → F_analytic → W_n

Each bvt_* property follows a three-step transfer:
1. OS axiom (E0-E4) gives a property of S_n
2. S_n = F_analytic ∘ wickRotate (Euclidean restriction) transfers to F_analytic
3. W_n = BV(F_analytic) (boundary value) transfers to W_n

The following helpers isolate the transfer steps as smaller sorry targets. -/

/-- E2R normalization: The 0-point BV is evaluation at the origin.

    For n = 0, the domain Fin 0 → Fin (d+1) → ℝ is a zero-dimensional space
    (a single point). The forward tube ForwardTube d 0 is all of the (trivial)
    domain. The analytic function F_analytic is a constant. The BV condition
    reduces to: the constant value times f(0) = W_0(f), so W_0(f) = c * f(0).
    Combining with the OS normalization (S_0 is normalized by the Euclidean
    restriction), we get c = 1, hence W_0(f) = f(0).

    This requires: (1) identifying the integral over the zero-dimensional space,
    (2) the OS normalization condition S_0(f) = f(0). -/
private theorem bv_zero_point_is_evaluation (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W_0 : SchwartzNPoint d 0 → ℂ)
    (F_0 : (Fin 0 → Fin (d + 1) → ℂ) → ℂ)
    (hW_cont : Continuous W_0)
    (hW_lin : IsLinearMap ℂ W_0)
    (hBV : ∀ (f : SchwartzNPoint d 0) (η : Fin 0 → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_0 f)))
    (hEuclid : ∀ (f : SchwartzNPoint d 0),
      OS.S 0 f = ∫ x : Fin 0 → Fin (d + 1) → ℝ,
        F_0 (fun k => wickRotatePoint (x k)) * (f x)) :
    ∀ f : SchwartzNPoint d 0, W_0 f = f 0 := by
  sorry

/-- E2R translation: Translation invariance transfers from S_n (via E1) through
    the analytic continuation to the BV.

    The argument: E1 says S_n is translation-invariant. The Euclidean restriction
    shows F_analytic is translation-invariant at Euclidean points. By analytic
    continuation, F_analytic is translation-invariant on the forward tube. The BV
    limit preserves translation invariance. -/
private theorem bv_translation_invariance_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : SchwartzNPoint d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f x))
    (hE1 : ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      OS.S n f = OS.S n g) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  sorry

/-- E2R Lorentz: Lorentz covariance transfers from E1 (Euclidean rotation
    invariance) through BHW to the BV.

    The argument: E1 gives SO(d+1)-invariance of S_n. The analytic continuation
    extends this to SO(d+1,C)-invariance of F_analytic. The restricted Lorentz
    group SO+(1,d) embeds in SO(d+1,C) (Bargmann-Hall-Wightman), giving
    real Lorentz invariance of F_analytic. The BV preserves this invariance. -/
private theorem bv_lorentz_covariance_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : SchwartzNPoint d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f x))
    (hE1_rot : ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
      OS.S n f = OS.S n g) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  sorry

/-- E2R locality: Local commutativity transfers from E3 (permutation symmetry)
    + edge-of-the-wedge to the BV.

    The argument: E3 says S_n is permutation-symmetric. The Euclidean restriction
    shows F_analytic is permutation-symmetric at Euclidean points. By analytic
    continuation (Jost's theorem), this extends to the permuted extended tube.
    Edge-of-the-wedge at the boundary gives local commutativity of W_n. -/
private theorem bv_local_commutativity_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hE3 : ∀ (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
      OS.S n f = OS.S n g) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  sorry

/-- E2R positivity: Positive definiteness transfers from E2 (reflection positivity)
    through the Wick rotation.

    The argument: The Wightman inner product sum_{n,m} W_{n+m}(f*_n x f_m) is
    related to the OS inner product sum_{n,m} S_{n+m}(theta(f*_n) x f_m) by
    analytic continuation. E2 ensures the OS inner product is non-negative,
    hence the Wightman inner product is non-negative. -/
private theorem bv_positive_definiteness_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hW_eq : ∀ n, W n = bvt_W OS lgc n)
    (hE2 : ∀ (F : BorchersSequence d),
      (∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
        x ∈ PositiveTimeRegion d n) →
      (OSInnerProduct d OS.S F F).re ≥ 0) :
    ∀ F : BorchersSequence d, (WightmanInnerProduct d W F F).re ≥ 0 := by
  sorry

/-- E2R Hermiticity: Hermiticity of W_n from reality of Schwinger functions.

    The Schwinger functions are real-valued on real configurations. Under
    analytic continuation, this gives a Schwarz reflection principle for
    F_analytic. Taking BV, this yields the Hermiticity condition
    W_n(f~) = conj(W_n(f)). -/
private theorem bv_hermiticity_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : SchwartzNPoint d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f x)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  sorry

/-- S44: W_0 = 1 (normalization).
    The 0-point Schwinger function S_0 = 1 (OS normalization). Its analytic
    continuation is the constant function 1 on the (trivial) forward tube.
    The distributional BV of 1 is evaluation: W_0(f) = f(0). -/
private theorem bvt_normalized (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsNormalized d (bvt_W OS lgc) := by
  intro f
  exact bv_zero_point_is_evaluation OS lgc
    (bvt_W OS lgc 0)
    (bvt_F OS lgc 0)
    (boundary_values_tempered OS lgc 0).choose_spec.choose_spec.1
    (boundary_values_tempered OS lgc 0).choose_spec.choose_spec.2.1
    (bvt_boundary_values OS lgc 0)
    (bvt_euclidean_restriction OS lgc 0)
    f

/-- S45: Translation invariance of W_n from E1. -/
private theorem bvt_translation_invariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsTranslationInvariantWeak d (bvt_W OS lgc) := by
  intro n a f g hfg
  exact bv_translation_invariance_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    (OS.E1_translation_invariant n)
    a f g hfg

/-- S46: Lorentz covariance of W_n from E1 via BHW. -/
private theorem bvt_lorentz_covariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLorentzCovariantWeak d (bvt_W OS lgc) := by
  intro n Λ f g hfg
  exact bv_lorentz_covariance_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    (OS.E1_rotation_invariant n)
    Λ f g hfg

/-- S47: Local commutativity of W_n from E3 + edge-of-the-wedge. -/
private theorem bvt_locally_commutative (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  intro n i j f g hsupp hswap
  exact bv_local_commutativity_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (OS.E3_symmetric n)
    i j f g hsupp hswap

/-- S48: Positive definiteness of W_n from E2 (reflection positivity). -/
private theorem bvt_positive_definite (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsPositiveDefinite d (bvt_W OS lgc) := by
  exact bv_positive_definiteness_transfer OS lgc
    (bvt_W OS lgc)
    (fun _ => rfl)
    OS.E2_reflection_positive

/-- S49: Hermiticity of W_n from reality of Schwinger functions. -/
private theorem bvt_hermitian (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f) := by
  intro n f g hfg
  exact bv_hermiticity_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    f g hfg

/-- Given OS axioms with linear growth condition, construct the full collection
    of Wightman functions from the analytic continuation boundary values. -/
def constructWightmanFunctions (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    WightmanFunctions d where
  W := bvt_W OS lgc
  linear := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.1
  tempered := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.1
  normalized := bvt_normalized OS lgc
  translation_invariant := bvt_translation_invariant OS lgc
  lorentz_covariant := bvt_lorentz_covariant OS lgc
  spectrum_condition := by
    intro n
    have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
    exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
      h.2.2.1, h.2.2.2.1⟩
  locally_commutative := bvt_locally_commutative OS lgc
  positive_definite := bvt_positive_definite OS lgc
  hermitian := bvt_hermitian OS lgc

/-- The OS pre-Hilbert space constructed from the Wightman functions obtained
    via analytic continuation of Schwinger functions.

    In the OS reconstruction (OS II, 1975), the Wightman functions are obtained
    from the Schwinger functions by analytic continuation, using the linear growth
    condition E0' to control the distribution order growth.

    The pre-Hilbert space uses the Wightman inner product:
      ⟨F, G⟩ = Σ_{n,m} W_{n+m}(f̄_n ⊗ g_m)
    where W_n are the boundary values of the analytic continuation of S_n.

    **Requires the linear growth condition E0'**: Without it, the analytic
    continuation may fail to produce tempered boundary values (OS I, Lemma 8.8 gap).

    Ref: OS II (1975), Sections IV-VI -/
def osPreHilbertSpace (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :=
  PreHilbertSpace (constructWightmanFunctions OS lgc)

/-! ### The Bridge Theorems -/

-- `IsWickRotationPair` is defined in Reconstruction.lean (available via import).

/-- **Theorem R→E**: Wightman functions produce Schwinger functions satisfying E0-E4.

    The Schwinger functions are related to the Wightman functions by Wick rotation
    (analytic continuation). -/
theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (OS : OsterwalderSchraderAxioms d),
      -- The Schwinger functions are the Wick rotation of the Wightman functions
      IsWickRotationPair OS.S Wfn.W := by
  -- Construct OS axioms from Wightman functions
  refine ⟨⟨constructSchwingerFunctions Wfn,
    constructedSchwinger_tempered Wfn,
    constructedSchwinger_translation_invariant Wfn,
    constructedSchwinger_rotation_invariant Wfn,
    constructedSchwinger_reflection_positive Wfn,
    constructedSchwinger_symmetric Wfn,
    constructedSchwinger_cluster Wfn⟩, ?_⟩
  -- Prove the Wick rotation pair property
  intro n
  -- Use the BHW extension F_ext as the IsWickRotationPair witness.
  -- F_ext = BHW extension, holomorphic on PET (hence on the forward tube).
  -- Its boundary values agree with W_n since F_ext = W_analytic on the forward tube.
  refine ⟨(W_analytic_BHW Wfn n).val,
    (W_analytic_BHW Wfn n).property.1.mono
      (ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)),
    ?_, fun _ => rfl⟩
  · -- Boundary values: use bhw_distributional_boundary_values directly.
    -- The previous approach tried to show x + iεη ∈ ForwardTube, which is false
    -- due to coordinate convention mismatch (absolute vs difference coordinates).
    intro f η hη
    exact bhw_distributional_boundary_values Wfn f η hη

/-- **Theorem E'→R'**: OS axioms with linear growth condition produce Wightman functions.

    The Wightman functions are the boundary values of the analytic continuation
    of the Schwinger functions to the forward tube. -/
theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      -- The Wightman functions are the Wick rotation of the Schwinger functions
      IsWickRotationPair OS.S Wfn.W := by
  refine ⟨constructWightmanFunctions OS lgc, fun n => ?_⟩
  -- The analytic continuation, boundary values, and euclidean restriction are
  -- exactly the fields constructed inside `boundary_values_tempered`.
  have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
  exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-! ### Wired Corollaries

The theorems `wightman_to_os` and `os_to_wightman` in `Reconstruction.lean` have
identical signatures to `wightman_to_os_full` and `os_to_wightman_full` above
(both use `IsWickRotationPair`). They are sorry'd because WickRotation.lean
imports Reconstruction.lean (circular import prevents wiring from there).
The `_full` versions here serve as the actual proofs. -/

end
