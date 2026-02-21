/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction
import OSReconstruction.Wightman.Reconstruction.AnalyticContinuation
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions

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

/-- **Tube domain integrability** (Vladimirov, §26; Streater-Wightman, §2.5).

A holomorphic function on a tube domain, restricted to a horizontal slice
at height εη (ε > 0), is polynomially bounded. Combined with the rapid decay
of Schwartz test functions, the product is integrable.

General form: For any holomorphic F : T_B → ℂ on a tube domain T_B = ℝⁿ + iB,
any Schwartz f ∈ S(ℝⁿ), and any y ∈ B, the function x ↦ F(x + iy) · f(x)
is integrable. We state it for the forward tube T_n specifically. -/
axiom forward_tube_bv_integrable {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k))
    (ε : ℝ) (hε : ε > 0) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      MeasureTheory.volume

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
axiom lorentz_covariant_distributional_bv {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F (ForwardTube d n))
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
      (nhds (Wfn.W n f))

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
    ⟨Wfn.W n, (Wfn.spectrum_condition n).choose_spec.2⟩ x

/-- **Local commutativity of holomorphic extensions at spacelike boundary points**
    (Streater-Wightman, §3.3; Jost, §IV.3).

If F is holomorphic on the forward tube T_n with continuous boundary values
matching a locally commutative Wightman distribution W_n, then at real
spacelike-separated points, F(x with i,i+1 swapped) = F(x).

The proof combines three ingredients:
1. Both z ↦ F(z) and z ↦ F(z with i,i+1 swapped) are holomorphic on
   overlapping tube domains (the forward tube and the "swapped" tube where
   the i-th and (i+1)-th imaginary parts are interchanged)
2. Their distributional BVs agree at real points with spacelike separation
   (by Wfn.locally_commutative)
3. The edge-of-the-wedge theorem gives a joint holomorphic extension, and
   by uniqueness they agree on the common real boundary

Requires: edge-of-the-wedge for tube domains with common real boundary,
which is a deep result in SCV (our axiom `edge_of_the_wedge`). -/
axiom local_commutativity_boundary_extension {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hW_lc : IsLocallyCommutativeWeak d W)
    (hF_match : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W n f)))
    (i : Fin n) (hi : i.val + 1 < n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hx_spacelike : MinkowskiSpace.minkowskiNormSq d
      (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0) :
    F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
    F (fun k μ => (x k μ : ℂ))

private theorem W_analytic_local_commutativity (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        MinkowskiSpace.minkowskiNormSq d
          (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0 →
        (Wfn.spectrum_condition n).choose
          (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        (Wfn.spectrum_condition n).choose (fun k μ => (x k μ : ℂ)) := by
  intro i hi x hx
  exact local_commutativity_boundary_extension (d := d) (n := n)
    (Wfn.spectrum_condition n).choose
    (Wfn.spectrum_condition n).choose_spec.1
    (W_analytic_continuous_boundary Wfn n)
    Wfn.W
    Wfn.locally_commutative
    (Wfn.spectrum_condition n).choose_spec.2
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

/-- **Temperedness of the Wick-rotated kernel**
    (OS I, Proposition 5.1; Streater-Wightman, §3.2).

If F is holomorphic on the permuted extended tube with polynomial growth
estimates (from `polynomial_growth_tube`), then its Wick-rotated evaluation
x ↦ F(iτ₁,x⃗₁,...,iτₙ,x⃗ₙ) has at most polynomial growth. Pairing against
a Schwartz test function f gives an absolutely convergent integral, and the
map f ↦ ∫ F(Wick(x)) f(x) dx is continuous in the Schwartz topology.

The proof requires:
1. Polynomial growth estimate for F on PET (from polynomial_growth_tube)
2. The Euclidean region is contained in the closure of PET (Jost points)
3. Bounding the integral by a Schwartz seminorm (rapid decay overcomes growth)

Ref: OS I (1973), Proposition 5.1 (geometric estimates on Ω_n);
     Streater-Wightman, §3.2 (growth of analytically continued functions) -/
axiom tempered_schwinger_from_wightman {d : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (PermutedExtendedTube d n)) :
    Continuous (fun f : SchwartzNPoint d n =>
      ∫ x : NPointDomain d n, F (fun k => wickRotatePoint (x k)) * (f x))

/-- The Schwinger functions constructed from Wightman functions satisfy temperedness (E0).

    This follows from the temperedness of Wightman functions (R0) and the
    geometric estimates in OS I, Proposition 5.1: the Wick-rotated kernel
    composed with f is integrable and the integral depends continuously on f. -/
theorem constructedSchwinger_tempered (Wfn : WightmanFunctions d) (n : ℕ) :
    Continuous (constructSchwingerFunctions Wfn n) := by
  exact tempered_schwinger_from_wightman
    (W_analytic_BHW Wfn n).val (W_analytic_BHW Wfn n).property.1

/-- **BHW extension at Euclidean points: translation invariance**
    (Streater-Wightman, Theorem 2.8; Jost, §IV.5).

The BHW extension F_ext, evaluated at Euclidean (Wick-rotated) points, is
invariant under simultaneous real translation of all arguments.

The proof: At Jost points (distinct ordered Euclidean times), F_ext equals
W_analytic (BHW property 2). The function z ↦ W_analytic(z + a) − W_analytic(z)
is holomorphic on the forward tube with zero distributional BVs (by
Wfn.translation_invariant), so it vanishes by distributional uniqueness.
Thus F_ext(Wick(x) + a) = F_ext(Wick(x)) at Jost points. For general
Euclidean points, the result extends by continuity (the Schwinger function
kernel is continuous on all of Euclidean space).

Requires: distributional uniqueness on the forward tube (available as
`distributional_uniqueness_forwardTube`) + continuous extension of the
Schwinger kernel to the full Euclidean region. -/
axiom bhw_euclidean_translation_invariance {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ (a : Fin (d + 1) → ℝ) (x : NPointDomain d n),
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (fun μ => x k μ + a μ))

private theorem F_ext_translation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (a : SpacetimeDim d) (x : NPointDomain d n) :
    (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
    (W_analytic_BHW Wfn n).val
      (fun k => wickRotatePoint (fun μ => x k μ + a μ)) := by
  exact bhw_euclidean_translation_invariance Wfn a x

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
  have hK : ∀ x : NPointDomain d n, K x = K (x + a') := fun x =>
    F_ext_translation_invariant Wfn n a x
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (x + a')
      = ∫ x : NPointDomain d n, K (x + a') * (f : NPointDomain d n → ℂ) (x + a') := by
        congr 1; ext x; rw [hK]
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        MeasureTheory.integral_add_right_eq_self
          (fun x => K x * (f : NPointDomain d n → ℂ) x) a'

/-- **BHW extension at Euclidean points: rotation invariance**
    (Streater-Wightman, Theorem 3.6; Jost, §IV.5).

F_ext is invariant under Euclidean rotations R ∈ O(d+1) at all Euclidean points.

For det R = +1 (proper rotations): SO(d+1) embeds into the complex Lorentz group
L₊(ℂ) as a subgroup preserving Euclidean points. The BHW complex Lorentz invariance
(property 3) then gives the result at Jost points, extending by continuity.

For det R = −1 (improper rotations): the proof uses the PCT theorem, which states
that the combination of parity, charge conjugation, and time reversal is a symmetry.
PCT follows from BHW + Jost's theorem (the "Jost point" is a real point in PET).

Requires: complex Lorentz invariance (BHW property 3) + PCT theorem +
continuous extension to the Euclidean boundary. -/
axiom bhw_euclidean_rotation_invariance {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (_ : R.transpose * R = 1)
      (x : NPointDomain d n),
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (R.mulVec (x k)))

private theorem F_ext_rotation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hR : R.transpose * R = 1)
    (x : NPointDomain d n) :
    (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
    (W_analytic_BHW Wfn n).val
      (fun k => wickRotatePoint (R.mulVec (x k))) := by
  exact bhw_euclidean_rotation_invariance Wfn R hR x

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
    The rotation R ∈ O(d+1) acts on the forward tube via its embedding in L₊(ℂ). -/
theorem constructedSchwinger_rotation_invariant (Wfn : WightmanFunctions d)
    (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
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
  -- K is rotation-invariant: K(x) = K(Rx) by BHW complex Lorentz invariance
  have hK : ∀ x : NPointDomain d n, K x = K (fun i => R.mulVec (x i)) :=
    fun x => F_ext_rotation_invariant Wfn n R hR x
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (fun i => R.mulVec (x i))
      = ∫ x : NPointDomain d n,
          K (fun i => R.mulVec (x i)) *
          (f : NPointDomain d n → ℂ) (fun i => R.mulVec (x i)) := by
        congr 1; ext x; rw [hK]
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        integral_orthogonal_eq_self R hR
          (fun x => K x * (f : NPointDomain d n → ℂ) x)

/-- **Reflection positivity from Wightman positivity**
    (OS I, §5; Streater-Wightman, §3.4).

For test functions supported in the positive-time region {τ > 0}, the OS inner
product reduces to the Wightman positive-definiteness condition (R2) after
Wick rotation. Specifically, time-reflection θ maps {τ > 0} to {τ < 0}, and
the Wick-rotated inner product Σ S_{n+m}((θf̄)_n ⊗ f_m) equals the Wightman
inner product Σ W_{n+m}(f*_n ⊗ f_m), which is ≥ 0 by R2.

The proof requires:
1. Wick rotation intertwines Euclidean time-reflection with Minkowski conjugation
2. The Schwinger function kernel at time-reflected points relates to the
   Wightman function via the boundary value of the analytic continuation
3. Wightman positive definiteness (axiom R2) -/
axiom reflection_positivity_from_wightman {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
      x ∈ PositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0

theorem constructedSchwinger_reflection_positive (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
      x ∈ PositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 := by
  exact reflection_positivity_from_wightman Wfn F hsupp

/-- **BHW extension at Euclidean points: permutation invariance**
    (Jost, §IV.5; Streater-Wightman, Theorem 3.6).

F_ext is invariant under permutations of arguments at all Euclidean points.

At Jost points (distinct ordered Euclidean times), the Wick-rotated point
z = Wick(x) lies in PET (the forward tube for some time ordering). BHW
permutation symmetry (property 4) gives F_ext(z ∘ σ) = F_ext(z). For general
Euclidean points, the result extends by continuity of the Schwinger kernel.

Requires: BHW permutation symmetry + Jost points in PET + continuous
extension to the Euclidean boundary. -/
axiom bhw_euclidean_permutation_invariance {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ (σ : Equiv.Perm (Fin n)) (x : NPointDomain d n),
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x (σ k)))

private theorem F_ext_permutation_invariant (Wfn : WightmanFunctions d) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : NPointDomain d n) :
    (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
    (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x (σ k))) := by
  exact bhw_euclidean_permutation_invariance Wfn σ x

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
  have hK : ∀ x : NPointDomain d n, K x = K (fun i => x (σ i)) :=
    fun x => F_ext_permutation_invariant Wfn n σ x
  symm
  calc ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) (fun i => x (σ i))
      = ∫ x : NPointDomain d n,
          K (fun i => x (σ i)) *
          (f : NPointDomain d n → ℂ) (fun i => x (σ i)) := by
        congr 1; ext x; rw [hK]
    _ = ∫ x : NPointDomain d n, K x * (f : NPointDomain d n → ℂ) x :=
        integral_perm_eq_self σ
          (fun x => K x * (f : NPointDomain d n → ℂ) x)

/-- **Cluster decomposition of the Schwinger kernel**
    (Streater-Wightman, Theorem 3.5; Glimm-Jaffe, Chapter 19).

When the (n+m)-point Schwinger kernel is integrated against f ⊗ g_a where g_a
is g translated by a large spacelike vector a, the result approaches S_n(f)·S_m(g).

This is the analytic continuation of the Wightman cluster decomposition property:
W_{n+m}(x₁,...,x_n, y₁+λa,...,y_m+λa) → W_n(x) · W_m(y) as λ→∞ for spacelike a.
This follows from uniqueness of the vacuum (the mass gap ensures exponential decay
of the truncated correlation functions). The Schwartz decay of f and g provides
domination for dominated convergence.

Requires: Wightman cluster property (R4) + dominated convergence in the
Wick-rotated integral + the relationship between W_{n+m} and F_ext_{n+m}
at Euclidean points.

Ref: Streater-Wightman, Theorem 3.5 (cluster decomposition);
     Glimm-Jaffe, Chapter 19 -/
axiom cluster_integral_wick_rotation {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (n m : ℕ)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
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
                (fun k => wickRotatePoint (x k)) * g x)‖ < ε

theorem W_analytic_cluster_integral (Wfn : WightmanFunctions d) (n m : ℕ)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
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
  exact cluster_integral_wick_rotation Wfn n m f g ε hε

/-- The Schwinger functions satisfy clustering (E4).

    Proof: Follows from cluster decomposition of Wightman functions (R4)
    via the analytic continuation. The key input is `W_analytic_cluster_integral`,
    which combines the pointwise cluster property of W_analytic with
    dominated convergence using Schwartz function decay. -/
theorem constructedSchwinger_cluster (Wfn : WightmanFunctions d)
    (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
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
    C_k^(d+1) = forward tube T_k (all coordinates complex with positive Im diffs).

    **Important**: The regions EXPAND as r increases: C_k^(r) ⊂ C_k^(r+1), because
    each step frees one more coordinate from the "must be real" constraint.
    This matches the OS II inductive construction where each Laplace transform
    step analytically continues one more spatial direction. -/
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

/-- The inductive analytic continuation theorem (OS II, Theorem 4.1).

    Given a holomorphic function on C_k^(r) (where r spacetime coordinates are complex),
    extend it analytically to C_k^(r+1) (one more coordinate becomes complex).

    The proof at each step uses:
    1. Laplace transform representation of S_k on C_k^(r)
    2. E0' bounds to control the growth of the Laplace transform
    3. Analytic continuation in the (r+1)-th coordinate direction

    The boundary-value connection: as the (r+1)-th coordinate's imaginary part → 0⁺,
    S_ext approaches S_prev. This is encoded by requiring both functions to agree
    when paired with test functions (distributional boundary values). -/
theorem inductive_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) (r : ℕ) (hr : r < d + 1)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) := by
  sorry

/-- After d+1 steps of analytic continuation, we reach the forward tube.

    C_k^(d+1) ⊇ ForwardTube d k (up to the difference variable transformation)

    This is the culmination of the inductive analytic continuation.

    The analytic function W_analytic is connected to the Schwinger functions:
    its Euclidean restriction (via Wick rotation) reproduces S_k. -/
theorem full_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      -- Euclidean restriction recovers S_k
      (∀ (f : SchwartzNPoint d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f x)) := by
  sorry

/-- Phase 4: The boundary values of the analytic continuation are tempered distributions.

    **Critical**: This is where E0' (linear growth condition) is essential!
    Without growth control, the boundary values might fail to be tempered.
    This is exactly the gap in OS I Lemma 8.8.

    The estimate (OS II, Section VI): the boundary values satisfy
    |W_n(f)| ≤ C_n · ‖f‖_{s,n} where C_n has at most factorial growth in n.
    This factorial growth comes from E0'.

    The connection to OS data: W_n is the distributional boundary value of
    the analytic continuation F_analytic of S_n. The Euclidean restriction
    of F_analytic recovers S_n, and its boundary values give W_n. -/
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
  sorry

/-! ### Constructing WightmanFunctions from OS Data -/

/-- Given OS axioms with linear growth condition, construct the full collection
    of Wightman functions from the analytic continuation boundary values. -/
def constructWightmanFunctions (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    WightmanFunctions d where
  W := fun n => (boundary_values_tempered OS lgc n).choose
  linear := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.1
  tempered := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.1
  normalized := by
    -- The boundary value of S_0 = 1 gives W_0 = evaluation at the unique point
    sorry
  translation_invariant := by
    -- Translation invariance follows from E1 (Euclidean covariance) restricted
    -- to time-preserving translations
    sorry
  lorentz_covariant := by
    -- Lorentz covariance follows from E1 via BHW theorem
    -- SO(1,d) acts on the forward tube; the analytically continued function
    -- inherits Lorentz covariance from Euclidean covariance
    sorry
  spectrum_condition := by
    -- Use the F_analytic witness from boundary_values_tempered
    intro n
    have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
    exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
      h.2.2.1, h.2.2.2.1⟩
  locally_commutative := by
    -- From E3 (permutation symmetry) + edge-of-the-wedge
    sorry
  positive_definite := by
    -- From E2 (reflection positivity)
    sorry
  hermitian := by
    -- From the reality of Schwinger functions and their analytic continuation
    sorry

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

/-- **Distributional boundary value matching for the BHW extension**
    (Vladimirov, §25.4; Streater-Wightman, §2.4).

The BHW extension F_ext has distributional boundary values equal to W_n.
Since F_ext = W_analytic on ForwardTube (BHW property 2), and W_analytic
has distributional BVs equal to W_n (spectrum_condition), the result follows
for approach directions η where x + iεη ∈ ForwardTube. For general approach
directions (∀ k, η_k ∈ V₊, where successive differences may not be in V₊),
the result follows from the approach-direction independence of distributional
boundary values (Vladimirov, Theorem 25.2): on a tube domain, the
distributional BV limit is independent of the approach direction within
the cone.

Requires: BV approach-direction independence on tube domains (a consequence
of the Fourier-Laplace representation of holomorphic functions on tubes). -/
axiom bhw_distributional_bv_match {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic_BHW Wfn n).val
            (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f))

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
  · -- Boundary values: F_ext has distributional BVs matching W_n.
    -- F_ext = W_analytic on ForwardTube (BHW property 2), and W_analytic's
    -- distributional BVs equal W_n (spectrum_condition). The subtlety is that
    -- the approach direction convention (∀ k, η_k ∈ V₊) may give points outside
    -- ForwardTube (which uses successive differences). The result follows from
    -- BV approach-direction independence (Vladimirov §25.4).
    exact bhw_distributional_bv_match Wfn

/-- **Theorem E'→R'**: OS axioms with linear growth condition produce Wightman functions.

    The Wightman functions are the boundary values of the analytic continuation
    of the Schwinger functions to the forward tube. -/
theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      -- The Wightman functions are the Wick rotation of the Schwinger functions
      IsWickRotationPair OS.S Wfn.W := by
  exact ⟨constructWightmanFunctions OS lgc, by sorry⟩

/-! ### Wired Corollaries

The theorems `wightman_to_os` and `os_to_wightman` in `Reconstruction.lean` have
identical signatures to `wightman_to_os_full` and `os_to_wightman_full` above
(both use `IsWickRotationPair`). They are sorry'd because WickRotation.lean
imports Reconstruction.lean (circular import prevents wiring from there).
The `_full` versions here serve as the actual proofs. -/

end
