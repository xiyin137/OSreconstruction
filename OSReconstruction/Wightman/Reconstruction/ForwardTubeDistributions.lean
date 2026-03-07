/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDistributions
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.Wightman.Reconstruction

/-!
# Forward Tube Distribution Theory

This file derives distribution-theoretic results for the forward tube from
the general tube domain axioms in `SCV.TubeDistributions`.

## Main results

Weak placeholder interfaces still carried for downstream compatibility:

* `continuous_boundary_forwardTube`
* `distributional_uniqueness_forwardTube`
* `boundary_value_recovery_forwardTube`

These remain open or depend on open SCV placeholder theory and should not be
treated as settled mathematics.

Rigorous proved transport results under regular flattened-tube input:

* `boundary_function_continuous_forwardTube_of_flatRegular`
* `boundary_value_recovery_forwardTube_of_flatRegular`
* `distributional_uniqueness_forwardTube_of_flatRegular`

## Strategy

The forward tube `T_n = { z | ∀ k, Im(z_k - z_{k-1}) ∈ V₊ }` is a tube domain
`{ z | Im(z) ∈ C }` where `C = { y | ∀ k, y_k - y_{k-1} ∈ V₊ }` is an open convex
nonempty cone in `(Fin n → Fin (d+1) → ℝ)`.

The general axioms work with `Fin m → ℂ`. We transfer via the canonical isometry
`(Fin n → Fin (d+1) → ℂ) ≃ₗᵢ[ℂ] (Fin (n * (d+1)) → ℂ)` (the "flattening").

## References

* Vladimirov, "Methods of the Theory of Generalized Functions" §25-26
* Streater-Wightman, "PCT, Spin and Statistics", Theorems 2-6, 2-9
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set

variable {d : ℕ} [NeZero d]

/-! ### The Forward Cone -/

/-- The forward cone in absolute coordinates: the set of imaginary parts
    `y : Fin n → Fin (d+1) → ℝ` such that each difference `y_k - y_{k-1}`
    lies in the open forward light cone `V₊`. -/
def ForwardConeAbs (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℝ) :=
  { y | ∀ k : Fin n,
    let prev : Fin (d + 1) → ℝ := if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩
    InOpenForwardCone d (fun μ => y k μ - prev μ) }

/-- The forward tube equals `{ z | Im(z) ∈ ForwardConeAbs }`. -/
theorem forwardTube_eq_imPreimage (d n : ℕ) [NeZero d] :
    ForwardTube d n = { z | (fun k μ => (z k μ).im) ∈ ForwardConeAbs d n } := by
  ext z
  simp only [ForwardTube, ForwardConeAbs, Set.mem_setOf_eq, InOpenForwardCone]
  constructor <;> intro h k <;> {
    have hk := h k
    constructor
    · convert hk.1 using 1
      split_ifs <;> simp [Complex.sub_im]
    · convert hk.2 using 2
      ext μ
      split_ifs <;> simp [Complex.sub_im] }

/-- The forward cone is open. -/
private theorem continuous_minkowskiNormSq (d : ℕ) :
    Continuous (fun η : Fin (d + 1) → ℝ => MinkowskiSpace.minkowskiNormSq d η) := by
  simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
  apply continuous_finset_sum
  intro i _
  exact ((continuous_const.mul (continuous_apply i)).mul (continuous_apply i))

private theorem isOpen_inOpenForwardCone (d : ℕ) [NeZero d] :
    IsOpen { η : Fin (d + 1) → ℝ | InOpenForwardCone d η } := by
  -- V₊ = { η | η 0 > 0 } ∩ { η | minkowskiNormSq d η < 0 }
  simp only [InOpenForwardCone, Set.setOf_and]
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (continuous_apply 0)
  · exact isOpen_lt (continuous_minkowskiNormSq d) continuous_const

theorem forwardConeAbs_isOpen (d n : ℕ) [NeZero d] :
    IsOpen (ForwardConeAbs d n) := by
  -- ForwardConeAbs = ⋂ k, { y | InOpenForwardCone d (y_k - y_{k-1}) }
  -- Finite intersection of open sets is open
  simp only [ForwardConeAbs, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro k
  -- Define the difference map for index k
  let diff_k : (Fin n → Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ) := fun y μ =>
    y k μ - if h : (k : ℕ) = 0 then 0 else y ⟨(k : ℕ) - 1, by omega⟩ μ
  -- The set is the preimage under diff_k
  suffices IsOpen (diff_k ⁻¹' { η | InOpenForwardCone d η }) by
    convert this using 1
    ext y; simp only [diff_k, Set.mem_setOf_eq, Set.mem_preimage, InOpenForwardCone]
    constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by convert h1; split_ifs <;> simp,
      by convert h2 using 2; ext μ; split_ifs <;> simp⟩
  apply (isOpen_inOpenForwardCone d).preimage
  -- diff_k is continuous
  apply continuous_pi; intro μ
  by_cases hk : (k : ℕ) = 0
  · simp [diff_k, hk]
    exact (continuous_apply μ).comp (continuous_apply k)
  · simp [diff_k, hk]
    exact ((continuous_apply μ).comp (continuous_apply k)).sub
      ((continuous_apply μ).comp (continuous_apply (⟨(k : ℕ) - 1, by omega⟩ : Fin n)))

/-- The forward cone is convex. -/
-- The open forward light cone is convex.
-- Proof: For η, η' ∈ V₊ and a+b=1 with a,b ≥ 0:
--   (aη + bη')₀ = aη₀ + bη'₀ > 0  (convex combination of positives)
--   For the norm: ‖aη + bη'‖² = a²‖η‖² + 2ab⟨η,η'⟩ + b²‖η'‖² (spatial part)
--   while (aη₀ + bη'₀)² ≥ a²η₀² + b²η'₀² + 2abη₀η'₀ > a²‖η_sp‖² + b²‖η'_sp‖² + 2ab‖η_sp‖‖η'_sp‖
--   ≥ ‖aη_sp + bη'_sp‖² by Cauchy-Schwarz. So minkowskiNormSq (aη+bη') < 0.
-- Decompose minkowskiNormSq into time² and spatial² parts
private theorem minkowskiNormSq_decomp (d : ℕ) [NeZero d] (η : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiNormSq d η =
    -(η 0) ^ 2 + ∑ i : Fin d, (η (Fin.succ i)) ^ 2 := by
  simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
  rw [Fin.sum_univ_succ]; congr 1
  simp [MinkowskiSpace.metricSignature]; ring

private theorem convex_inOpenForwardCone (d : ℕ) [NeZero d] :
    Convex ℝ { η : Fin (d + 1) → ℝ | InOpenForwardCone d η } := by
  intro η hη η' hη' a b ha hb hab
  simp only [Set.mem_setOf_eq, InOpenForwardCone] at hη hη' ⊢
  obtain ⟨hη0, hηQ⟩ := hη; obtain ⟨hη'0, hη'Q⟩ := hη'
  -- Spatial squared norms < time²
  have hη_sq : ∑ i : Fin d, (η (Fin.succ i)) ^ 2 < (η 0) ^ 2 := by
    linarith [minkowskiNormSq_decomp d η]
  have hη'_sq : ∑ i : Fin d, (η' (Fin.succ i)) ^ 2 < (η' 0) ^ 2 := by
    linarith [minkowskiNormSq_decomp d η']
  set ξ := a • η + b • η'
  have hξv : ∀ i, ξ i = a * η i + b * η' i :=
    fun i => by simp [ξ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- Abbreviations
  set Sx := ∑ i : Fin d, (η (Fin.succ i)) ^ 2
  set Sy := ∑ i : Fin d, (η' (Fin.succ i)) ^ 2
  set Sxy := ∑ i : Fin d, η (Fin.succ i) * η' (Fin.succ i)
  constructor
  · -- Time component: ξ 0 > 0
    rw [hξv]
    by_cases ha0 : a = 0
    · rw [ha0] at hab ⊢; simp at hab; rw [hab]; simp; exact hη'0
    · linarith [mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hη0, mul_nonneg hb hη'0.le]
  · -- Minkowski norm: minkowskiNormSq d ξ < 0
    rw [minkowskiNormSq_decomp]
    -- Need: ∑ (ξ (succ i))² < (ξ 0)²
    have goal_rw : ∑ i : Fin d, (ξ (Fin.succ i)) ^ 2 =
        ∑ i : Fin d, (a * η (Fin.succ i) + b * η' (Fin.succ i)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [hξv])
    rw [goal_rw, hξv 0]
    -- Expand ∑ (ax + by)² = a²Sx + 2ab Sxy + b²Sy
    have expand_lhs : ∑ i : Fin d, (a * η (Fin.succ i) + b * η' (Fin.succ i)) ^ 2 =
        a ^ 2 * Sx + 2 * a * b * Sxy + b ^ 2 * Sy := by
      trans ∑ i : Fin d, (a ^ 2 * (η (Fin.succ i)) ^ 2 +
          2 * a * b * (η (Fin.succ i) * η' (Fin.succ i)) +
          b ^ 2 * (η' (Fin.succ i)) ^ 2)
      · exact Finset.sum_congr rfl (fun i _ => by ring)
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Sx, Sy, Sxy]
    rw [expand_lhs]
    -- Cauchy-Schwarz: Sxy² ≤ Sx * Sy
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin d => η (Fin.succ i)) (fun i : Fin d => η' (Fin.succ i))
    -- Sxy < η₀ * η'₀ (via Cauchy-Schwarz + spatial < time²)
    have h_Sxy : Sxy < η 0 * η' 0 := by
      by_contra h; push_neg at h
      have := sq_le_sq' (by linarith [mul_pos hη0 hη'0]) h
      have h_Sx_nn : 0 ≤ Sx := Finset.sum_nonneg (fun i _ => sq_nonneg (η (Fin.succ i)))
      have h_Sy_nn : 0 ≤ Sy := Finset.sum_nonneg (fun i _ => sq_nonneg (η' (Fin.succ i)))
      nlinarith [pow_pos hη0 2, pow_pos hη'0 2]
    -- Now close: a²Sx + 2ab·Sxy + b²Sy < (aη₀ + bη'₀)²
    by_cases ha0 : a = 0
    · rw [ha0] at hab ⊢; simp at hab; rw [hab]; ring_nf; linarith
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      nlinarith [sq_nonneg b, mul_nonneg ha hb, pow_pos ha_pos 2]

/-- The open forward light cone is closed under positive scalar multiplication. -/
theorem inOpenForwardCone_smul (d : ℕ) [NeZero d]
    (c : ℝ) (hc : c > 0) (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η) :
    InOpenForwardCone d (c • η) := by
  constructor
  · simp [Pi.smul_apply, smul_eq_mul]; exact mul_pos hc hη.1
  · rw [minkowskiNormSq_decomp]
    have := minkowskiNormSq_decomp d η
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 : ∑ i : Fin d, (c * η (Fin.succ i)) ^ 2 =
        c ^ 2 * ∑ i : Fin d, (η (Fin.succ i)) ^ 2 := by
      simp_rw [mul_pow]; rw [← Finset.mul_sum]
    rw [h1]; nlinarith [hη.2, pow_pos hc 2, minkowskiNormSq_decomp d η]

/-- The open forward light cone is closed under addition (it's a convex cone). -/
private theorem inOpenForwardCone_add (d : ℕ) [NeZero d]
    (η η' : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η) (hη' : InOpenForwardCone d η') :
    InOpenForwardCone d (η + η') := by
  -- η + η' = 2 • ((1/2) • η + (1/2) • η'), where the inner part is in V₊ by convexity
  have hmid : (2 : ℝ)⁻¹ • η + (2 : ℝ)⁻¹ • η' ∈
      { η | InOpenForwardCone d η } :=
    convex_inOpenForwardCone d hη hη' (by norm_num) (by norm_num) (by norm_num)
  have heq : η + η' = (2 : ℝ) • ((2 : ℝ)⁻¹ • η + (2 : ℝ)⁻¹ • η') := by
    ext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [heq]; exact inOpenForwardCone_smul d 2 (by norm_num) _ hmid

/-- Elements of `ForwardConeAbs` have each component in the forward cone.
    Since ForwardConeAbs requires η₀ ∈ V₊ and η_k - η_{k-1} ∈ V₊ for all k,
    each η_k = η₀ + Σ_{j=1}^{k} (η_j - η_{j-1}) is a sum of V₊ elements,
    and V₊ is closed under addition. -/
theorem forwardConeAbs_implies_allForwardCone {d n : ℕ} [NeZero d]
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ ForwardConeAbs d n) :
    ∀ k : Fin n, InOpenForwardCone d (η k) := by
  intro ⟨kv, hkv⟩
  -- Induction on the natural number index
  induction kv with
  | zero =>
    have h0 := hη ⟨0, hkv⟩
    simp only [dite_true] at h0
    convert h0 using 1; ext μ; simp
  | succ k ih =>
    -- η_{k+1} = η_k + (η_{k+1} - η_k), both in V₊
    have hk : InOpenForwardCone d (η ⟨k, by omega⟩) := ih (by omega)
    have hdiff := hη ⟨k + 1, hkv⟩
    simp only [Nat.succ_ne_zero, dite_false] at hdiff
    have hprev : (⟨k + 1 - 1, by omega⟩ : Fin n) = ⟨k, by omega⟩ := by
      ext; exact Nat.succ_sub_one k
    rw [hprev] at hdiff
    have heq : η ⟨k + 1, hkv⟩ = η ⟨k, by omega⟩ +
        (fun μ => η ⟨k + 1, hkv⟩ μ - η ⟨k, by omega⟩ μ) := by
      ext μ; simp
    rw [heq]; exact inOpenForwardCone_add d _ _ hk hdiff

/-- `InForwardCone` (from WightmanAxioms) is definitionally equivalent to `ForwardConeAbs`
    membership. Both require successive differences to lie in V₊. -/
theorem inForwardCone_iff_mem_forwardConeAbs {d n : ℕ} [NeZero d]
    (η : Fin n → Fin (d + 1) → ℝ) :
    InForwardCone d n η ↔ η ∈ ForwardConeAbs d n :=
  Iff.rfl

/-- `InForwardCone` implies each component is in V₊ (bridge from successive-difference
    to per-component condition). -/
theorem inForwardCone_implies_allForwardCone {d n : ℕ} [NeZero d]
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η) :
    ∀ k : Fin n, InOpenForwardCone d (η k) :=
  forwardConeAbs_implies_allForwardCone η hη

theorem forwardConeAbs_convex (d n : ℕ) [NeZero d] :
    Convex ℝ (ForwardConeAbs d n) := by
  intro y hy y' hy' a b ha hb hab k
  simp only [ForwardConeAbs, Set.mem_setOf_eq] at hy hy' ⊢
  -- The difference (a•y + b•y')_k - (a•y + b•y')_{k-1}
  --   = a•(y_k - y_{k-1}) + b•(y'_k - y'_{k-1})
  -- Both terms are in V₊, and V₊ is convex.
  have hyk := hy k
  have hy'k := hy' k
  -- Rewrite the combination's difference as a convex combination of the individual differences
  suffices h : (fun μ => (a • y + b • y') k μ -
      (if h : (k : ℕ) = 0 then 0 else (a • y + b • y') ⟨(k : ℕ) - 1, by omega⟩) μ) =
    (fun μ => a * ((fun μ => y k μ - (if h : (k : ℕ) = 0 then 0
        else y ⟨(k : ℕ) - 1, by omega⟩) μ) μ) +
      b * ((fun μ => y' k μ - (if h : (k : ℕ) = 0 then 0
        else y' ⟨(k : ℕ) - 1, by omega⟩) μ) μ)) by
    rw [h]
    have heq : (fun μ => a * ((fun μ => y k μ - (if h : (k : ℕ) = 0 then 0
        else y ⟨(k : ℕ) - 1, by omega⟩) μ) μ) +
      b * ((fun μ => y' k μ - (if h : (k : ℕ) = 0 then 0
        else y' ⟨(k : ℕ) - 1, by omega⟩) μ) μ)) =
      (a • (fun μ => y k μ - (if h : (k : ℕ) = 0 then 0
        else y ⟨(k : ℕ) - 1, by omega⟩) μ) +
       b • (fun μ => y' k μ - (if h : (k : ℕ) = 0 then 0
        else y' ⟨(k : ℕ) - 1, by omega⟩) μ)) := by
      ext μ; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact convex_inOpenForwardCone d hyk hy'k ha hb hab
  ext μ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with hk
  · simp
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The forward cone is nonempty. -/
theorem forwardConeAbs_nonempty (d n : ℕ) [NeZero d] :
    (ForwardConeAbs d n).Nonempty := by
  -- Witness: y_k = (k+1) • e₀ where e₀ = Pi.single 0 1
  -- Then y_k - y_{k-1} = e₀ ∈ V₊
  let η₀ : Fin (d + 1) → ℝ := Pi.single 0 1
  have hη₀ : InOpenForwardCone d η₀ := by
    constructor
    · simp [η₀]
    · simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner, η₀,
        Pi.single_apply]
      have : ∀ i : Fin (d + 1), (MinkowskiSpace.metricSignature d i *
          (if i = 0 then (1 : ℝ) else 0)) * (if i = 0 then 1 else 0) =
          if i = 0 then -1 else 0 := by
        intro i; split_ifs with h <;> simp [MinkowskiSpace.metricSignature, h]
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      norm_num
  refine ⟨fun k μ => (↑(k : ℕ) + 1 : ℝ) * η₀ μ, ?_⟩
  intro k
  simp only []
  convert hη₀ using 1
  ext μ
  split_ifs with h
  · simp [h]
  · simp only
    have hk_pos : (k : ℕ) ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    have : (↑(↑k - 1 : ℕ) : ℝ) = (↑(k : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub hk_pos]; simp
    rw [this]; ring

/-! ### Flattening Equivalence -/

/-- Uncurrying `(Fin n → Fin d → 𝕜) ≃ₗ (Fin n × Fin d → 𝕜)`. -/
def uncurryLinearEquiv (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin n × Fin d → 𝕜) :=
  { (Equiv.curry (Fin n) (Fin d) 𝕜).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Concrete flattening `(Fin n → Fin d → 𝕜) ≃ₗ (Fin (n * d) → 𝕜)`.
    Composition of uncurrying with reindexing via `finProdFinEquiv`. -/
def flattenLinearEquiv (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin (n * d) → 𝕜) :=
  (uncurryLinearEquiv n d 𝕜).trans (LinearEquiv.funCongrLeft 𝕜 𝕜 finProdFinEquiv.symm)

/-- The flattening is a continuous linear equivalence over ℂ.
    Concrete: `f ↦ fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2`. -/
def flattenCLEquiv (n d : ℕ) :
    (Fin n → Fin d → ℂ) ≃L[ℂ] (Fin (n * d) → ℂ) :=
  (flattenLinearEquiv n d ℂ).toContinuousLinearEquiv

/-- The real version of the flattening. -/
def flattenCLEquivReal (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃L[ℝ] (Fin (n * d) → ℝ) :=
  (flattenLinearEquiv n d ℝ).toContinuousLinearEquiv

@[simp] theorem flattenCLEquiv_apply (n d : ℕ) (f : Fin n → Fin d → ℂ) (k : Fin (n * d)) :
    flattenCLEquiv n d f k = f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := rfl

@[simp] theorem flattenCLEquivReal_apply (n d : ℕ) (f : Fin n → Fin d → ℝ) (k : Fin (n * d)) :
    flattenCLEquivReal n d f k = f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := rfl

@[simp] theorem flattenCLEquiv_symm_apply (n d : ℕ) (w : Fin (n * d) → ℂ) (i : Fin n) (j : Fin d) :
    (flattenCLEquiv n d).symm w i j = w (finProdFinEquiv (i, j)) := rfl

@[simp] theorem flattenCLEquivReal_symm_apply (n d : ℕ) (w : Fin (n * d) → ℝ) (i : Fin n) (j : Fin d) :
    (flattenCLEquivReal n d).symm w i j = w (finProdFinEquiv (i, j)) := rfl

/-- Imaginary parts commute with the concrete flattening. -/
theorem flattenCLEquiv_im (n d : ℕ) (z : Fin n → Fin d → ℂ) :
    (fun k => (flattenCLEquiv n d z k).im) =
      flattenCLEquivReal n d (fun i j => (z i j).im) := by
  ext k; simp

/-- The flattening as a `MeasurableEquiv`. Composition of uncurrying
    `(Fin n → Fin d → ℝ) ≃ᵐ (Fin n × Fin d → ℝ)` with reindexing
    `(Fin n × Fin d → ℝ) ≃ᵐ (Fin (n * d) → ℝ)`. -/
def flattenMeasurableEquiv (n d : ℕ) : (Fin n → Fin d → ℝ) ≃ᵐ (Fin (n * d) → ℝ) :=
  (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finProdFinEquiv)

@[simp] theorem flattenMeasurableEquiv_apply (n d : ℕ) (f : Fin n → Fin d → ℝ)
    (k : Fin (n * d)) :
    flattenMeasurableEquiv n d f k =
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp [flattenMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_curry_symm, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Function.uncurry]

/-- Uncurrying preserves the product Lebesgue measure. The measure on
    `Fin n → Fin d → ℝ` is `∏_i ∏_j λ`, and the measure on `Fin n × Fin d → ℝ`
    is `∏_{(i,j)} λ`. The curry map identifies these by associativity of
    finite products: `∏_i ∏_j aᵢⱼ = ∏_{(i,j)} aᵢⱼ`. -/
private theorem volume_map_curry_symm (n d : ℕ) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin d → ℝ)).map
      (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm =
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n × Fin d → ℝ)) := by
  symm; apply MeasureTheory.Measure.pi_eq; intro s hs
  rw [MeasureTheory.Measure.map_apply
    (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have h_preimage : (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm ⁻¹'
      (Set.univ.pi s) = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, MeasurableEquiv.coe_curry_symm,
      Function.uncurry]
    exact ⟨fun h i j => h (i, j), fun h ⟨i, j⟩ => h i j⟩
  rw [h_preimage, MeasureTheory.volume_pi_pi]
  simp_rw [MeasureTheory.volume_pi_pi]
  rw [← Finset.prod_product', ← Finset.univ_product_univ]

/-- The flattening equivalence preserves Lebesgue measure. -/
theorem flattenMeasurableEquiv_measurePreserving (n d : ℕ) :
    MeasureTheory.MeasurePreserving (flattenMeasurableEquiv n d)
      MeasureTheory.volume MeasureTheory.volume := by
  exact (MeasureTheory.MeasurePreserving.mk
    (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.measurable
    (volume_map_curry_symm n d)).trans
    (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ => ℝ) finProdFinEquiv)

/-- **Change of variables for the flatten equivalence.**

    For any function `g`, integrals are preserved under the flatten coordinate change:
    `∫ x, g(x) dx = ∫ y, g(flatten(y)) dy` where x ranges over `Fin (n*d) → ℝ`
    and y over `Fin n → Fin d → ℝ`.

    The flatten is a composition of:
    1. Uncurrying: `(Fin n → Fin d → ℝ) → (Fin n × Fin d → ℝ)` (associativity of
       product measures)
    2. Reindexing: `(Fin n × Fin d → ℝ) → (Fin (n*d) → ℝ)` via `finProdFinEquiv`
       (permutation of coordinates, measure-preserving by
       `volume_measurePreserving_piCongrLeft`) -/
theorem integral_flatten_change_of_variables (n d : ℕ) (g : (Fin (n * d) → ℝ) → ℂ) :
    ∫ x, g x = ∫ y, g (flattenCLEquivReal n d y) := by
  rw [show (fun y => g (flattenCLEquivReal n d y)) =
      (fun y => g (flattenMeasurableEquiv n d y)) from by
    ext y; congr 1; ext k; simp [flattenMeasurableEquiv_apply]]
  exact ((flattenMeasurableEquiv_measurePreserving n d).integral_comp' g).symm

/-- The flattened forward cone. -/
def ForwardConeFlat (d n : ℕ) [NeZero d] : Set (Fin (n * (d + 1)) → ℝ) :=
  (flattenCLEquivReal n (d + 1)) '' ForwardConeAbs d n

/-- The flattened forward cone is open. -/
theorem forwardConeFlat_isOpen (d n : ℕ) [NeZero d] :
    IsOpen (ForwardConeFlat d n) := by
  exact (flattenCLEquivReal n (d + 1)).toHomeomorph.isOpenMap _ (forwardConeAbs_isOpen d n)

/-- The flattened forward cone is convex. -/
theorem forwardConeFlat_convex (d n : ℕ) [NeZero d] :
    Convex ℝ (ForwardConeFlat d n) := by
  exact (forwardConeAbs_convex d n).linear_image
    ((flattenCLEquivReal n (d + 1)).toLinearEquiv.toLinearMap)

/-- The flattened forward cone is nonempty. -/
theorem forwardConeFlat_nonempty (d n : ℕ) [NeZero d] :
    (ForwardConeFlat d n).Nonempty :=
  Set.Nonempty.image _ (forwardConeAbs_nonempty d n)

/-- ForwardConeAbs is a cone: closed under positive scalar multiplication. -/
theorem forwardConeAbs_smul (d n : ℕ) [NeZero d]
    (t : ℝ) (ht : 0 < t) (y : Fin n → Fin (d + 1) → ℝ) (hy : y ∈ ForwardConeAbs d n) :
    t • y ∈ ForwardConeAbs d n := by
  intro k
  have hk := hy k
  -- The successive difference of t • y is t • (successive difference of y)
  suffices InOpenForwardCone d
      (t • fun μ => y k μ - (if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩) μ) from by
    convert this using 1; ext μ; split <;> simp [Pi.smul_apply, smul_eq_mul, mul_sub]
  exact inOpenForwardCone_smul d t ht _ hk

/-- ForwardConeFlat is a cone: closed under positive scalar multiplication. -/
theorem forwardConeFlat_isCone (d n : ℕ) [NeZero d]
    (t : ℝ) (ht : 0 < t) (y : Fin (n * (d + 1)) → ℝ) (hy : y ∈ ForwardConeFlat d n) :
    t • y ∈ ForwardConeFlat d n := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨t • y', forwardConeAbs_smul d n t ht y' hy', ?_⟩
  exact (flattenCLEquivReal n (d + 1)).map_smul t y'

/-! ### Tube Domain Correspondence -/

/-- The forward tube, after flattening, equals `TubeDomain (ForwardConeFlat d n)`. -/
theorem forwardTube_flatten_eq_tubeDomain (d n : ℕ) [NeZero d] :
    (flattenCLEquiv n (d + 1)) '' (ForwardTube d n) =
      SCV.TubeDomain (ForwardConeFlat d n) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  ext w
  simp only [Set.mem_image, SCV.TubeDomain, ForwardConeFlat, Set.mem_setOf_eq]
  constructor
  · -- (→) w = e z for z ∈ ForwardTube
    rintro ⟨z, hz, rfl⟩
    rw [forwardTube_eq_imPreimage] at hz
    exact ⟨fun k μ => (z k μ).im, hz, by ext i; simp⟩
  · -- (←) Im(w) ∈ eR '' ForwardConeAbs
    rintro ⟨y, hy, hyw⟩
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    rw [forwardTube_eq_imPreimage]
    simp only [ForwardConeAbs, Set.mem_setOf_eq] at hy ⊢
    -- Need: Im(e.symm w) matches y (up to the difference structure)
    -- Since Im(e.symm w k μ) = (w (finProdFinEquiv (k,μ))).im
    -- and hyw : eR y = fun i => (w i).im, so (w i).im = y (finProdFinEquiv.symm i).1 (...)
    -- hence (w (finProdFinEquiv (k,μ))).im = y k μ
    have him : ∀ k μ, ((e.symm w) k μ).im = y k μ := by
      intro k μ
      simp only [e, flattenCLEquiv_symm_apply]
      have := congr_fun hyw (finProdFinEquiv (k, μ))
      simp only [flattenCLEquivReal_apply, Equiv.symm_apply_apply] at this
      linarith
    intro k
    have hyk := hy k
    constructor
    · convert hyk.1 using 1
      split_ifs with h <;> simp [him]
    · convert hyk.2 using 2
      ext μ; split_ifs with h <;> simp [him]

/-- Helper: transport DifferentiableOn through the flattening. -/
private theorem differentiableOn_flatten {n : ℕ} {d : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n)) :
    DifferentiableOn ℂ (F ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.TubeDomain (ForwardConeFlat d n)) := by
  rw [← forwardTube_flatten_eq_tubeDomain]
  refine hF.comp (flattenCLEquiv n (d + 1)).symm.differentiableOn (fun w hw => ?_)
  obtain ⟨z, hz, rfl⟩ := hw
  convert hz using 1
  exact (flattenCLEquiv n (d + 1)).symm_apply_apply z

/-! ### Main Theorems -/

/-- **Continuous boundary values for the forward tube.**

    Warning: this is currently a placeholder interface, not a completed theorem.

    The previous proof flattened to a weak SCV boundary-continuity front that has
    since been removed: bare distributional boundary values do not, by themselves,
    imply pointwise boundary continuity.

    The honest forward-tube repair is:
    1. build the strong regular Fourier-Laplace package on the flattened tube, then
    2. transport the resulting boundary continuity theorem back through the
       flattening equivalence.

    Ref: Vladimirov §26.2; Streater-Wightman, Theorem 2-9 -/
theorem continuous_boundary_forwardTube {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (h_bv : ∃ (T : SchwartzNPoint d n → ℂ), Continuous T ∧
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T f)))
    (x : Fin n → Fin (d + 1) → ℝ) :
    ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)) := by
  sorry

/-- **Distributional uniqueness for the forward tube.**

    Current status:
    the assertion remains part of the live interface because downstream BHW work
    uses it, but the previous proof only flattened to
    a weak SCV uniqueness front whose proof route factored through weak
    boundary-continuity placeholders.

    So this is now carried as an explicit blocker rather than a fake closure. -/
theorem distributional_uniqueness_forwardTube {d n : ℕ} [NeZero d]
    {F₁ F₂ : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (ForwardTube d n))
    (hF₂ : DifferentiableOn ℂ F₂ (ForwardTube d n))
    (h_agree : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) -
           F₂ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0)) :
    ∀ z ∈ ForwardTube d n, F₁ z = F₂ z := by
  sorry

/-! ### Boundary Value Recovery on Forward Tube -/

/-- Distributional boundary values on the forward tube are recovered by
    integrating the real-boundary trace.

    Warning: this is currently the forward-tube analogue of the overstrong weak-BV
    recovery theorem in `SCV.TubeDistributions`.

    The previous proof flattened to a weak SCV recovery front. The honest route
    needs the strong regular Fourier-Laplace package on the flattened tube. -/
theorem boundary_value_recovery_forwardTube {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    {T : SchwartzNPoint d n → ℂ}
    (hT_cont : Continuous T)
    (h_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T f)))
    (f : SchwartzNPoint d n) :
    T f = ∫ x : NPointDomain d n, F (fun k μ => (x k μ : ℂ)) * (f x) := by
  sorry

/-- The real-boundary trace of a holomorphic forward-tube function with tempered
    distributional boundary values is continuous.

    This is the forward-tube specialization of Vladimirov's boundary continuity
    theorem transported through the flattening equivalence.

    Current status:
    the previous proof incorrectly upgraded bare Schwartz distributional boundary
    values to the strong regular Fourier-Laplace package on the flattened tube.
    That upgrade is not presently available. The honest repair is to prove the
    flat strong-input theorem first, then transport it back. -/
theorem boundary_function_continuous_forwardTube {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    {T : SchwartzNPoint d n → ℂ}
    (hT_cont : Continuous T)
    (h_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f))) :
    Continuous (fun x : NPointDomain d n => F (fun k μ => (x k μ : ℂ))) := by
  -- Blocked: after flattening to a standard tube domain, the available SCV theorem
  -- needs strong boundary-value input data / `HasFourierLaplaceReprRegular`, not only
  -- bare distributional boundary-value data. The previous proof incorrectly passed
  -- through `exists_fourierLaplaceRepr`, which is the weak BV package only.
  sorry

/-! ### Proved versions under regular flattened FL input -/

/-- Proved boundary continuity of the real trace under regular flattened-tube
    Fourier-Laplace input. -/
theorem boundary_function_continuous_forwardTube_of_flatRegular {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm)) :
    Continuous (fun x : NPointDomain d n => F (fun k μ => (x k μ : ℂ))) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  have hG_diff : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF
  have hcont_G : Continuous (fun x : Fin (n * (d + 1)) → ℝ => G (SCV.realEmbed x)) :=
    hRegular.boundary_continuous
  have hcomp := hcont_G.comp eR.continuous
  have hEq :
      (fun x : NPointDomain d n => F (fun k μ => (x k μ : ℂ))) =
      (fun x : NPointDomain d n => G (SCV.realEmbed (eR x))) := by
    funext x
    change F (fun k μ => (x k μ : ℂ)) = F (e.symm (SCV.realEmbed (eR x)))
    congr 1
    funext k
    funext μ
    have hxk : eR x (finProdFinEquiv (k, μ)) = x k μ := by
      simp [eR, flattenCLEquivReal_apply]
    rw [show (e.symm (SCV.realEmbed (eR x))) k μ =
        (SCV.realEmbed (eR x)) (finProdFinEquiv (k, μ)) by
          simp [e, flattenCLEquiv_symm_apply]]
    simp [SCV.realEmbed, hxk]
  rw [hEq]
  exact hcomp

/-- Proved forward-tube boundary-value recovery under regular flattened-tube
    Fourier-Laplace input. -/
theorem boundary_value_recovery_forwardTube_of_flatRegular {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm))
    (f : SchwartzNPoint d n) :
    hRegular.dist
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (flattenCLEquivReal n (d + 1)).symm) f) =
      ∫ x : NPointDomain d n, F (fun k μ => (x k μ : ℂ)) * (f x) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  have hG_diff : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF
  let pushforward : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR.symm
  let fFlat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ := pushforward f
  have hrecover := SCV.fourierLaplace_boundary_recovery
    (forwardConeFlat_isOpen d n)
    (forwardConeFlat_convex d n)
    (forwardConeFlat_nonempty d n)
    (forwardConeFlat_isCone d n)
    hG_diff hRegular fFlat
  have hright :
      (∫ x : Fin (n * (d + 1)) → ℝ, G (SCV.realEmbed x) * fFlat x) =
      (∫ y : NPointDomain d n, F (fun k μ => (y k μ : ℂ)) * (f y)) := by
    rw [integral_flatten_change_of_variables]
    congr 1
    ext y
    have hFarg : F (e.symm (SCV.realEmbed (eR y))) = F (fun k μ => (y k μ : ℂ)) := by
      congr 1
      funext k μ
      simp [e, eR, SCV.realEmbed]
    have hfarg : fFlat (eR y) = f y := by
      simp [fFlat, pushforward, eR]
    calc
      G (SCV.realEmbed (eR y)) * fFlat (eR y)
          = F (e.symm (SCV.realEmbed (eR y))) * f y := by
              simp [G, hfarg]
      _ = F (fun k μ => (y k μ : ℂ)) * f y := by
            rw [hFarg]
  simpa [fFlat, pushforward] using hrecover.trans hright

/-- Proved forward-tube distributional uniqueness under regular flattened-tube
    input for the difference `F₁ - F₂`. -/
theorem distributional_uniqueness_forwardTube_of_flatRegular {d n : ℕ} [NeZero d]
    {F₁ F₂ : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (ForwardTube d n))
    (hF₂ : DifferentiableOn ℂ F₂ (ForwardTube d n))
    (hRegular_G : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (fun z =>
        (F₁ ∘ (flattenCLEquiv n (d + 1)).symm) z -
        (F₂ ∘ (flattenCLEquiv n (d + 1)).symm) z))
    (h_dist_zero : ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ), hRegular_G.dist f = 0) :
    ∀ z ∈ ForwardTube d n, F₁ z = F₂ z := by
  let e := flattenCLEquiv n (d + 1)
  let G₁ : (Fin (n * (d + 1)) → ℂ) → ℂ := F₁ ∘ e.symm
  let G₂ : (Fin (n * (d + 1)) → ℂ) → ℂ := F₂ ∘ e.symm
  have hG₁_diff : DifferentiableOn ℂ G₁ (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF₁
  have hG₂_diff : DifferentiableOn ℂ G₂ (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF₂
  have huniq := SCV.distributional_uniqueness_tube_of_regular
    (forwardConeFlat_isOpen d n)
    (forwardConeFlat_convex d n)
    (forwardConeFlat_nonempty d n)
    (forwardConeFlat_isCone d n)
    hG₁_diff hG₂_diff hRegular_G h_dist_zero
  intro z hz
  have hmem : e z ∈ SCV.TubeDomain (ForwardConeFlat d n) := by
    rw [← forwardTube_flatten_eq_tubeDomain]
    exact Set.mem_image_of_mem e hz
  have := huniq (e z) hmem
  simpa [G₁, G₂, e, Function.comp] using this

/-! ### Norm Preservation under Flattening -/

/-- The real flattening preserves norms.
    Both sides are the sup norm over all components `|x i j|`, just indexed differently.
    Proof uses `Finset.sup_product_left` to relate `sup_{(i,j)} = sup_i (sup_j ...)`. -/
theorem flattenCLEquivReal_norm_eq (n d : ℕ) (x : Fin n → Fin d → ℝ) :
    ‖flattenCLEquivReal n d x‖ = ‖x‖ := by
  simp only [Pi.norm_def]
  congr 1
  -- Goal: sup_{k : Fin (n*d)} ‖eR x k‖₊ = sup_{i : Fin n} ‖x i‖₊
  simp only [Pi.nnnorm_def, flattenCLEquivReal_apply]
  -- Goal: sup_{k : Fin (n*d)} ‖x (k.divNat) (k.modNat)‖₊ =
  --       sup_{i : Fin n} sup_{j : Fin d} ‖x i j‖₊
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

/-! ### Polynomial Growth for the Forward Tube -/

/-- Proved forward-tube polynomial growth under regular flattened-tube
    Fourier-Laplace input. -/
theorem polynomial_growth_forwardTube_of_flatRegular {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm))
    (K : Set (Fin n → Fin (d + 1) → ℝ)) (hK : IsCompact K)
    (hK_sub : K ⊆ ForwardConeAbs d n) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : Fin n → Fin (d + 1) → ℝ) (y : Fin n → Fin (d + 1) → ℝ), y ∈ K →
        ‖F (fun k μ => ↑(x k μ) + ↑(y k μ) * Complex.I)‖ ≤
          C_bd * (1 + ‖x‖) ^ N := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  have hG_diff : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF
  let K_flat : Set (Fin (n * (d + 1)) → ℝ) := eR '' K
  have hK_flat_compact : IsCompact K_flat := hK.image eR.continuous
  have hK_flat_sub : K_flat ⊆ ForwardConeFlat d n := Set.image_mono hK_sub
  obtain ⟨C_bd, N, hC_pos, hgrowth_flat⟩ :=
    SCV.fourierLaplace_polynomial_growth
      (forwardConeFlat_isOpen d n)
      (forwardConeFlat_convex d n)
      (forwardConeFlat_nonempty d n)
      hG_diff hRegular K_flat hK_flat_compact hK_flat_sub
  refine ⟨C_bd, N, hC_pos, fun x y hy => ?_⟩
  have harg : G (fun i => ↑(eR x i) + ↑(eR y i) * Complex.I) =
      F (fun k μ => ↑(x k μ) + ↑(y k μ) * Complex.I) := by
    show F (e.symm (fun i => ↑(eR x i) + ↑(eR y i) * Complex.I)) =
      F (fun k μ => ↑(x k μ) + ↑(y k μ) * Complex.I)
    congr 1
    ext k μ
    have hxk : eR x (finProdFinEquiv (k, μ)) = x k μ := by
      simp [eR, flattenCLEquivReal_apply]
    have hyk : eR y (finProdFinEquiv (k, μ)) = y k μ := by
      simp [eR, flattenCLEquivReal_apply]
    rw [show (e.symm (fun i => ↑(eR x i) + ↑(eR y i) * Complex.I)) k μ =
        (fun i => ↑(eR x i) + ↑(eR y i) * Complex.I) (finProdFinEquiv (k, μ)) by
          simp [e, flattenCLEquiv_symm_apply]]
    simp [hxk, hyk]
  have h_flat := hgrowth_flat (eR x) (eR y) ⟨y, hy, rfl⟩
  rw [harg] at h_flat
  have h_norm : ‖eR x‖ = ‖x‖ := flattenCLEquivReal_norm_eq n (d + 1) x
  rw [h_norm] at h_flat
  exact h_flat

/-- Convert Schwartz-based boundary values on the forward tube into a genuine weak
    Fourier-Laplace representation on the flattened standard tube domain.

    This is a rigorous weak theorem: it transports only the distributional
    boundary-value package, not any boundary continuity or growth regularity. -/
noncomputable def schwartz_bv_to_flat_repr {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (h_bv : ∃ (T : SchwartzNPoint d n → ℂ), Continuous T ∧
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T f))) :
    SCV.HasFourierLaplaceRepr (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  have hG_diff : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF
  let T : SchwartzNPoint d n → ℂ := Classical.choose h_bv
  have hT_cont : Continuous T := (Classical.choose_spec h_bv).1
  have hBV :
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d n,
              F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (T f)) := (Classical.choose_spec h_bv).2
  let pullback : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
      SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR
  let Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ → ℂ := fun f => T (pullback f)
  have hTflat_cont : Continuous Tflat := hT_cont.comp pullback.continuous
  have hBVflat :
      ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) (η : Fin (n * (d + 1)) → ℝ),
        η ∈ ForwardConeFlat d n →
          Filter.Tendsto
            (fun ε : ℝ =>
              ∫ x : Fin (n * (d + 1)) → ℝ,
                G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (Tflat f)) := by
    intro f η hη
    rcases hη with ⟨η', hη', rfl⟩
    let fProd : SchwartzNPoint d n := pullback f
    have hEq :
        (fun ε : ℝ =>
          ∫ x : Fin (n * (d + 1)) → ℝ,
            G (fun i => ↑(x i) + ↑ε * ↑((eR η') i) * Complex.I) * f x)
        =
        (fun ε : ℝ =>
          ∫ y : NPointDomain d n,
            F (fun k μ => ↑(y k μ) + ε * ↑(η' k μ) * Complex.I) * fProd y) := by
      funext ε
      rw [integral_flatten_change_of_variables n (d + 1)
        (fun x : Fin (n * (d + 1)) → ℝ =>
          G (fun i => ↑(x i) + ↑ε * ↑((eR η') i) * Complex.I) * f x)]
      congr 1
      ext y
      have hFarg :
          G (fun i => ↑(eR y i) + ↑ε * ↑(eR η' i) * Complex.I) =
            F (fun k μ => ↑(y k μ) + ε * ↑(η' k μ) * Complex.I) := by
        change F (e.symm (fun i => ↑(eR y i) + ↑ε * ↑(eR η' i) * Complex.I)) =
          F (fun k μ => ↑(y k μ) + ε * ↑(η' k μ) * Complex.I)
        congr 1
        ext k μ
        have hyk : eR y (finProdFinEquiv (k, μ)) = y k μ := by
          simp [eR, flattenCLEquivReal_apply]
        have hηk : eR η' (finProdFinEquiv (k, μ)) = η' k μ := by
          simp [eR, flattenCLEquivReal_apply]
        rw [show (e.symm (fun i => ↑(eR y i) + ↑ε * ↑(eR η' i) * Complex.I)) k μ =
            (fun i => ↑(eR y i) + ↑ε * ↑(eR η' i) * Complex.I) (finProdFinEquiv (k, μ)) by
              simp [e, flattenCLEquiv_symm_apply]]
        simp [hyk, hηk]
      have hfarg : f (eR y) = fProd y := by
        simp [fProd, pullback, eR]
      rw [hFarg, hfarg]
    have hηcone : InForwardCone d n η' := (inForwardCone_iff_mem_forwardConeAbs η').2 hη'
    have h := hBV fProd η' hηcone
    rw [hEq]
    simpa [Tflat, fProd, pullback] using h
  exact SCV.exists_fourierLaplaceRepr
    (forwardConeFlat_isOpen d n)
    (forwardConeFlat_convex d n)
    (forwardConeFlat_nonempty d n)
    hG_diff hTflat_cont hBVflat

/-- The distributional boundary-value functional of `schwartz_bv_to_flat_repr` is the explicit
    pullback of the original product-coordinate witness. -/
theorem schwartz_bv_to_flat_repr_dist_apply {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    {T : SchwartzNPoint d n → ℂ}
    (hT_cont : Continuous T)
    (h_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)))
    (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) :
    (schwartz_bv_to_flat_repr hF ⟨T, hT_cont, h_bv⟩).dist f =
      T ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (flattenCLEquivReal n (d + 1))) f) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  let pullback : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
      SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR
  obtain ⟨ηflat, hηflat⟩ := forwardConeFlat_nonempty d n
  rcases hηflat with ⟨η, hη, rfl⟩
  have hflat :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ x : Fin (n * (d + 1)) → ℝ,
            G (fun i => ↑(x i) + ↑ε * ↑((eR η) i) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((schwartz_bv_to_flat_repr hF ⟨T, hT_cont, h_bv⟩).dist f)) :=
    (schwartz_bv_to_flat_repr hF ⟨T, hT_cont, h_bv⟩).boundary_value f (eR η) ⟨η, hη, rfl⟩
  have hprod :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d n,
            F (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) * (pullback f y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T (pullback f))) :=
    h_bv (pullback f) η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : Fin (n * (d + 1)) → ℝ,
          G (fun i => ↑(x i) + ↑ε * ↑((eR η) i) * Complex.I) * f x) =
      (fun ε : ℝ =>
        ∫ y : NPointDomain d n,
          F (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) * (pullback f y)) := by
    funext ε
    rw [integral_flatten_change_of_variables n (d + 1)
      (fun x : Fin (n * (d + 1)) → ℝ =>
        G (fun i => ↑(x i) + ↑ε * ↑((eR η) i) * Complex.I) * f x)]
    congr 1
    ext y
    have hFarg :
        G (fun i => ↑(eR y i) + ↑ε * ↑(eR η i) * Complex.I) =
          F (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) := by
      change F (e.symm (fun i => ↑(eR y i) + ↑ε * ↑(eR η i) * Complex.I)) =
        F (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I)
      congr 1
      ext k μ
      have hyk : eR y (finProdFinEquiv (k, μ)) = y k μ := by
        simp [eR, flattenCLEquivReal_apply]
      have hηk : eR η (finProdFinEquiv (k, μ)) = η k μ := by
        simp [eR, flattenCLEquivReal_apply]
      rw [show (e.symm (fun i => ↑(eR y i) + ↑ε * ↑(eR η i) * Complex.I)) k μ =
          (fun i => ↑(eR y i) + ↑ε * ↑(eR η i) * Complex.I) (finProdFinEquiv (k, μ)) by
            simp [e, flattenCLEquiv_symm_apply]]
      simp [hyk, hηk]
    have hfarg : f (eR y) = pullback f y := by
      simp [pullback, eR]
    rw [hFarg, hfarg]
  have hflat' :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d n,
            F (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) * (pullback f y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((schwartz_bv_to_flat_repr hF ⟨T, hT_cont, h_bv⟩).dist f)) := by
    simpa [hEq] using hflat
  exact tendsto_nhds_unique hflat' hprod

/-- If a forward-tube function carries both a regular flattened tube package and an explicit
    product-coordinate boundary-value witness, then the two resulting boundary-value functionals
    agree after flattening. -/
theorem flatRegular_dist_eq_schwartz_bv {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm))
    {T : SchwartzNPoint d n → ℂ}
    (hT_cont : Continuous T)
    (h_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f))) :
    hRegular.dist = (schwartz_bv_to_flat_repr hF ⟨T, hT_cont, h_bv⟩).dist := by
  exact SCV.fourierLaplace_repr_dist_unique
    (forwardConeFlat_nonempty d n)
    hRegular.toHasFourierLaplaceRepr
    (schwartz_bv_to_flat_repr hF ⟨T, hT_cont, h_bv⟩)

/-- Boundary-value recovery on the forward tube from explicit regular flattened input together
    with product-coordinate BV data. This is the honest bridge used by downstream BHW arguments:
    regularity is supplied explicitly, while the recovered boundary distribution is still the
    original product-coordinate witness `T`. -/
theorem boundary_value_recovery_forwardTube_of_flatRegular_from_bv {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm))
    {T : SchwartzNPoint d n → ℂ}
    (hT_cont : Continuous T)
    (h_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)))
    (f : SchwartzNPoint d n) :
    T f = ∫ x : NPointDomain d n, F (fun k μ => (x k μ : ℂ)) * (f x) := by
  let h_bv_ex :
      ∃ (T' : SchwartzNPoint d n → ℂ), Continuous T' ∧
        ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
          InForwardCone d n η →
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d n,
              F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (T' f)) := ⟨T, hT_cont, h_bv⟩
  let hRepr : SCV.HasFourierLaplaceRepr (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm) :=
    schwartz_bv_to_flat_repr hF h_bv_ex
  let pushforward : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivReal n (d + 1)).symm
  have hdist :
      hRegular.dist = hRepr.dist :=
    SCV.fourierLaplace_repr_dist_unique
      (forwardConeFlat_nonempty d n) hRegular.toHasFourierLaplaceRepr hRepr
  have hrecover := boundary_value_recovery_forwardTube_of_flatRegular hF hRegular f
  have hpush_id :
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivReal n (d + 1)))
        (pushforward f) = f := by
    ext x
    simp [pushforward]
  have hpush :
      hRepr.dist (pushforward f) = T f := by
    simpa [hRepr, h_bv_ex, hpush_id]
      using schwartz_bv_to_flat_repr_dist_apply hF hT_cont h_bv (pushforward f)
  calc
    T f = hRepr.dist (pushforward f) := hpush.symm
    _ = hRegular.dist (pushforward f) := by
          simpa using congrArg (fun W => W (pushforward f)) hdist.symm
    _ = ∫ x : NPointDomain d n, F (fun k μ => (x k μ : ℂ)) * (f x) := hrecover

/-- Distributional uniqueness on the forward tube from explicit regular flattened input plus
    zero product-coordinate boundary data for the difference. -/
theorem distributional_uniqueness_forwardTube_of_flatRegular_from_bvZero {d n : ℕ} [NeZero d]
    {F₁ F₂ : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (ForwardTube d n))
    (hF₂ : DifferentiableOn ℂ F₂ (ForwardTube d n))
    (hRegular_G : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (fun z =>
        (F₁ ∘ (flattenCLEquiv n (d + 1)).symm) z -
        (F₂ ∘ (flattenCLEquiv n (d + 1)).symm) z))
    (h_agree : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          ((F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) -
           (F₂ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)) :
    ∀ z ∈ ForwardTube d n, F₁ z = F₂ z := by
  let G : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z => F₁ z - F₂ z
  have hG : DifferentiableOn ℂ G (ForwardTube d n) := hF₁.sub hF₂
  let h_zero_bv :
      ∃ (T' : SchwartzNPoint d n → ℂ), Continuous T' ∧
        ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
          InForwardCone d n η →
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d n,
              G (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (T' f)) := ⟨0, continuous_const, h_agree⟩
  let hRepr : SCV.HasFourierLaplaceRepr (ForwardConeFlat d n)
      (fun z =>
        (F₁ ∘ (flattenCLEquiv n (d + 1)).symm) z -
        (F₂ ∘ (flattenCLEquiv n (d + 1)).symm) z) :=
    schwartz_bv_to_flat_repr hG h_zero_bv
  have hdist :
      hRegular_G.dist = hRepr.dist :=
    SCV.fourierLaplace_repr_dist_unique
      (forwardConeFlat_nonempty d n) hRegular_G.toHasFourierLaplaceRepr hRepr
  have hdist_zero : ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ), hRegular_G.dist f = 0 := by
    intro f
    calc
      hRegular_G.dist f = hRepr.dist f := by
        simpa using congrArg (fun W => W f) hdist
      _ = 0 := by
        simpa [hRepr, h_zero_bv]
          using schwartz_bv_to_flat_repr_dist_apply hG continuous_const h_agree f
  exact distributional_uniqueness_forwardTube_of_flatRegular hF₁ hF₂ hRegular_G hdist_zero

end
