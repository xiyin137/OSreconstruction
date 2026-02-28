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

* `continuous_boundary_forwardTube` — holomorphic functions on `ForwardTube d n`
  with distributional boundary values extend continuously to real boundary points.
* `distributional_uniqueness_forwardTube` — two holomorphic functions on
  `ForwardTube d n` with the same distributional boundary values are equal.

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

    Derived from `SCV.continuous_boundary_tube` via the flattening equivalence.
    A holomorphic function on `ForwardTube d n` with distributional boundary values
    extends continuously to the real boundary.

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
  let e := flattenCLEquiv n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  have hG_diff : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF
  -- The boundary value condition transfers through the flattening
  -- Use SchwartzMap.compCLMOfContinuousLinearEquiv to compose Schwartz functions
  -- with the flattening equivalence
  have hG_bv : ∃ (T : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ → ℂ), Continuous T ∧
      ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) (η : Fin (n * (d + 1)) → ℝ),
        η ∈ ForwardConeFlat d n →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin (n * (d + 1)) → ℝ,
            G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)) := by
    obtain ⟨T, hT_cont, hT⟩ := h_bv
    -- Pull back Schwartz functions through the real flattening
    let eR := flattenCLEquivReal n (d + 1)
    let pullback : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR
    refine ⟨fun f => T (pullback f), hT_cont.comp pullback.continuous, fun f η hη => ?_⟩
    -- η ∈ ForwardConeFlat = eR '' ForwardConeAbs, so η = eR η' for some η' ∈ ForwardConeAbs
    obtain ⟨η', hη', rfl⟩ := hη
    -- η' ∈ ForwardConeAbs ↔ InForwardCone, so hT applies directly
    have hconv := hT (pullback f) η' hη'
    -- Show the integrands are equal pointwise, then use Filter.Tendsto.congr
    have heq : ∀ ε : ℝ,
        ∫ x : Fin (n * (d + 1)) → ℝ,
          (G fun i => ↑(x i) + ↑ε * ↑((flattenCLEquivReal n (d + 1)) η' i) * Complex.I) * f x =
        ∫ y : NPointDomain d n,
          (F fun k μ => ↑(y k μ) + ↑ε * ↑(η' k μ) * Complex.I) * (pullback f) y := by
      intro ε
      rw [integral_flatten_change_of_variables]
      congr 1; ext y
      -- G(eR(y) + iε·eR(η')) * f(eR(y)) = F(y + iε·η') * (pullback f)(y)
      simp only [G, Function.comp, e, eR, pullback,
        SchwartzMap.compCLMOfContinuousLinearEquiv]
      congr 1
      congr 1; funext k μ
      simp only [flattenCLEquiv_symm_apply, flattenCLEquivReal_apply,
        Equiv.symm_apply_apply]
    exact Filter.Tendsto.congr (fun ε => (heq ε).symm) hconv
  -- Apply the general axiom
  have hcont_G := SCV.continuous_boundary_tube
    (forwardConeFlat_isOpen d n)
    (forwardConeFlat_convex d n)
    (forwardConeFlat_nonempty d n)
    hG_diff hG_bv
    (flattenCLEquivReal n (d + 1) x)
  -- Pull back ContinuousWithinAt through the linear equiv
  -- Key: G ∘ e = F, e is continuous, e maps ForwardTube onto TubeDomain C_flat
  have h_map : MapsTo (⇑e) (ForwardTube d n) (SCV.TubeDomain (ForwardConeFlat d n)) := by
    intro z hz; rw [← forwardTube_flatten_eq_tubeDomain]; exact Set.mem_image_of_mem e hz
  have h_pt : e (fun k μ => (x k μ : ℂ)) = SCV.realEmbed (flattenCLEquivReal n (d + 1) x) := by
    ext i; simp [SCV.realEmbed, e]
  rw [← h_pt] at hcont_G
  have h_comp := hcont_G.comp e.continuous.continuousWithinAt h_map
  -- h_comp : ContinuousWithinAt (G ∘ e) (ForwardTube d n) (fun k μ => ↑(x k μ))
  convert h_comp using 1
  ext z; simp [G, Function.comp, e]

/-- **Distributional uniqueness for the forward tube.**

    Derived from `SCV.distributional_uniqueness_tube` via the flattening equivalence.
    Two holomorphic functions on `ForwardTube d n` with the same distributional
    boundary values are equal.

    Ref: Vladimirov §26.3; Streater-Wightman, Corollary to Theorem 2-9 -/
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
  let e := flattenCLEquiv n (d + 1)
  let G₁ : (Fin (n * (d + 1)) → ℂ) → ℂ := F₁ ∘ e.symm
  let G₂ : (Fin (n * (d + 1)) → ℂ) → ℂ := F₂ ∘ e.symm
  have hG₁_diff : DifferentiableOn ℂ G₁ (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF₁
  have hG₂_diff : DifferentiableOn ℂ G₂ (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF₂
  have hG_agree : ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
      (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
      Filter.Tendsto (fun ε : ℝ =>
        ∫ x : Fin (n * (d + 1)) → ℝ,
          (G₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) -
           G₂ (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    intro f η hη
    obtain ⟨η', hη', rfl⟩ := hη
    let eR := flattenCLEquivReal n (d + 1)
    let pullback : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR
    -- η' ∈ ForwardConeAbs ↔ InForwardCone, so h_agree applies directly
    have hconv := h_agree (pullback f) η' hη'
    -- Key lemma: the argument of F₁/F₂ matches after unflattening
    have harg : ∀ (y : NPointDomain d n) (ε : ℝ),
        (flattenCLEquiv n (d + 1)).symm (fun i =>
          ↑((flattenCLEquivReal n (d + 1)) y i) +
          ↑ε * ↑((flattenCLEquivReal n (d + 1)) η' i) * Complex.I) =
        fun k μ => ↑(y k μ) + ↑ε * ↑(η' k μ) * Complex.I := by
      intro y ε; funext k μ
      simp only [flattenCLEquiv_symm_apply, flattenCLEquivReal_apply,
        Equiv.symm_apply_apply]
    have heq : ∀ ε : ℝ,
        ∫ x : Fin (n * (d + 1)) → ℝ,
          ((G₁ fun i => ↑(x i) + ↑ε * ↑((flattenCLEquivReal n (d + 1)) η' i) * Complex.I) -
           (G₂ fun i => ↑(x i) + ↑ε * ↑((flattenCLEquivReal n (d + 1)) η' i) * Complex.I)) * f x =
        ∫ y : NPointDomain d n,
          ((F₁ fun k μ => ↑(y k μ) + ↑ε * ↑(η' k μ) * Complex.I) -
           (F₂ fun k μ => ↑(y k μ) + ↑ε * ↑(η' k μ) * Complex.I)) * (pullback f) y := by
      intro ε
      rw [integral_flatten_change_of_variables]
      congr 1; ext y
      show (F₁ (e.symm _) - F₂ (e.symm _)) * f (eR y) =
        (F₁ _ - F₂ _) * (pullback f) y
      rw [harg]; rfl
    exact Filter.Tendsto.congr (fun ε => (heq ε).symm) hconv
  -- Apply the general axiom
  have huniq := SCV.distributional_uniqueness_tube
    (forwardConeFlat_isOpen d n)
    (forwardConeFlat_convex d n)
    (forwardConeFlat_nonempty d n)
    (forwardConeFlat_isCone d n)
    hG₁_diff hG₂_diff hG_agree
  -- Pull back: for z ∈ ForwardTube, e(z) ∈ TubeDomain(C_flat), so G₁(e(z)) = G₂(e(z))
  intro z hz
  have hmem : e z ∈ SCV.TubeDomain (ForwardConeFlat d n) := by
    rw [← forwardTube_flatten_eq_tubeDomain]; exact Set.mem_image_of_mem e hz
  have := huniq (e z) hmem
  simp only [G₁, G₂, Function.comp, e.symm_apply_apply] at this
  exact this

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

/-- **Polynomial growth of holomorphic functions on the forward tube.**

    Derived from `SCV.polynomial_growth_tube` via the flattening equivalence.
    A holomorphic function on `ForwardTube d n` with tempered distributional boundary
    values satisfies polynomial growth estimates: for any compact K ⊆ ForwardConeAbs,
    there exist C > 0 and N such that

        ‖F(x + iy)‖ ≤ C · (1 + ‖x‖)^N

    for all real x and imaginary part y ∈ K.

    The boundary value condition is stated in the flat (Fin m → ℂ) coordinates
    because that is the form required by `polynomial_growth_tube`. The caller
    (typically `bhw_polynomial_growth_on_euclidean`) must convert from the
    product-coordinate BV condition to this flat form.

    Ref: Streater-Wightman, Theorem 2-6; Vladimirov §25.3 -/
theorem polynomial_growth_forwardTube {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (h_bv : ∀ (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
      ∃ (T : (Fin (n * (d + 1)) → ℝ) → ℂ), ContinuousOn T Set.univ ∧
        ∀ (f : (Fin (n * (d + 1)) → ℝ) → ℂ), MeasureTheory.Integrable f →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x : Fin (n * (d + 1)) → ℝ,
              (F ∘ (flattenCLEquiv n (d + 1)).symm)
                (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ x, T x * f x)))
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
  -- The compact subset in flat coordinates
  let K_flat : Set (Fin (n * (d + 1)) → ℝ) := eR '' K
  have hK_flat_compact : IsCompact K_flat := hK.image eR.continuous
  have hK_flat_sub : K_flat ⊆ ForwardConeFlat d n :=
    Set.image_mono hK_sub
  -- Apply polynomial_growth_tube to G on the flattened tube
  obtain ⟨C_bd, N, hC_pos, hgrowth_flat⟩ :=
    SCV.polynomial_growth_tube
      (forwardConeFlat_isOpen d n)
      (forwardConeFlat_convex d n)
      (forwardConeFlat_nonempty d n)
      hG_diff h_bv K_flat hK_flat_compact hK_flat_sub
  -- Transfer back to product coordinates
  refine ⟨C_bd, N, hC_pos, fun x y hy => ?_⟩
  -- The key: F(x + iy) = G(eR(x) + i·eR(y))
  have harg : G (fun i => ↑(eR x i) + ↑(eR y i) * Complex.I) =
      F (fun k μ => ↑(x k μ) + ↑(y k μ) * Complex.I) := by
    show F (e.symm (fun i => ↑(eR x i) + ↑(eR y i) * Complex.I)) =
      F (fun k μ => ↑(x k μ) + ↑(y k μ) * Complex.I)
    congr 1; ext k μ
    simp only [e, eR, flattenCLEquiv_symm_apply, flattenCLEquivReal_apply,
      Equiv.symm_apply_apply]
  -- Apply the flat bound
  have h_flat := hgrowth_flat (eR x) (eR y) ⟨y, hy, rfl⟩
  rw [harg] at h_flat
  -- The flattening preserves the sup norm: ‖eR x‖ = ‖x‖
  -- Both are sup norms over finite index sets, and flattening just reindexes:
  -- ‖x‖ = sup_i ‖x i‖ = sup_i (sup_j |x i j|) = sup_{(i,j)} |x i j| = ‖eR x‖
  have h_norm : ‖eR x‖ = ‖x‖ := flattenCLEquivReal_norm_eq n (d + 1) x
  rw [h_norm] at h_flat
  exact h_flat

/-- The boundary function of a holomorphic function on a tube domain (over a cone)
    with distributional BVs is continuous.

    Uses `continuous_boundary_tube` to get ContinuousWithinAt at each real point,
    then an epsilon-triangle argument using the cone property (which allows approaching
    the real boundary along arbitrarily small imaginary parts) and continuity of F
    on the tube to upgrade to full continuity of the boundary restriction.

    The cone property is essential: it ensures we can scale imaginary parts toward 0,
    so that `realEmbed x` lies in the closure of `TubeDomain C`.

    Ref: Vladimirov §26.2 -/
private theorem boundary_function_continuous {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (h_bv : ∃ (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ), Continuous T ∧
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f))) :
    Continuous (fun x => F (SCV.realEmbed x)) := by
  -- The Fourier-Laplace representation gives full continuity of the boundary function.
  obtain ⟨T, hT_cont, hT⟩ := h_bv
  exact SCV.fourierLaplace_boundary_continuous hC hconv hne hF
    (SCV.exists_fourierLaplaceRepr hC hconv hne hF hT_cont hT)

/-- **Polynomial growth from Schwartz distributional boundary values.**

    A holomorphic function on a tube domain T(C) (where C is an open convex cone)
    with tempered distributional boundary values (in the Schwartz sense) satisfies
    polynomial growth: for any compact K ⊆ C, there exist C_bd > 0 and N such that
      |F(x + iy)| ≤ C_bd · (1 + ‖x‖)^N for all x ∈ ℝ^m and y ∈ K.

    This is the same mathematical content as `polynomial_growth_tube` but takes
    Schwartz-based BV as input rather than integrable-function BV. The proof uses
    the Fourier-Laplace representation (Vladimirov §25.3): the Schwartz BV determines
    a tempered distribution whose Fourier transform has support in the dual cone C*,
    and the Laplace transform of such a distribution has polynomial growth.

    Ref: Vladimirov §25.3; Streater-Wightman, Theorem 2-6 -/
private theorem polynomial_growth_from_schwartz_bv {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (h_bv : ∃ (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ), Continuous T ∧
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)))
    (K : Set (Fin m → ℝ)) (hK : IsCompact K) (hK_sub : K ⊆ C) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : Fin m → ℝ) (y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => ↑(x i) + ↑(y i) * Complex.I)‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
  obtain ⟨T, hT_cont, hT⟩ := h_bv
  exact SCV.fourierLaplace_polynomial_growth hC hconv hne hF
    (SCV.exists_fourierLaplaceRepr hC hconv hne hF hT_cont hT) K hK hK_sub

private theorem boundary_integral_convergence {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (h_bv : ∃ (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ), Continuous T ∧
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)))
    (η : Fin m → ℝ) (hη : η ∈ C) :
    ∀ (f : (Fin m → ℝ) → ℂ), MeasureTheory.Integrable f →
      Filter.Tendsto (fun ε : ℝ =>
        ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, F (SCV.realEmbed x) * f x)) := by
  intro f hf
  -- Step 1: Pointwise convergence.
  -- For each x, F(x + iεη) → F(realEmbed x) as ε → 0⁺.
  -- Proof: x + iεη ∈ TubeDomain C (since εη ∈ C by cone) and x + iεη → realEmbed x.
  -- By ContinuousWithinAt F (TubeDomain C) (realEmbed x) from continuous_boundary_tube.
  have h_pw : ∀ x : Fin m → ℝ,
      Filter.Tendsto (fun ε : ℝ => F (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (F (SCV.realEmbed x))) := by
    intro x
    have h_cwa := SCV.continuous_boundary_tube hC hconv hne hF h_bv x
    -- Define the path φ : ℝ → (Fin m → ℂ) by φ(ε) i = x i + ε * η i * I
    let φ : ℝ → (Fin m → ℂ) := fun ε i => ↑(x i) + ↑ε * ↑(η i) * Complex.I
    -- Goal: Tendsto (F ∘ φ) (nhdsWithin 0 (Ioi 0)) (nhds (F(realEmbed x)))
    -- = Tendsto F (map φ (nhdsWithin 0 (Ioi 0))) (nhds (F(realEmbed x)))
    -- It suffices to show: map φ (nhdsWithin 0 (Ioi 0)) ≤ nhdsWithin (realEmbed x) (TubeDomain C)
    -- i.e., φ tends to realEmbed x AND φ maps (0,∞) into TubeDomain C.
    change Filter.Tendsto (F ∘ φ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (F (SCV.realEmbed x)))
    apply h_cwa.tendsto.comp
    -- Need: Tendsto φ (nhdsWithin 0 (Ioi 0)) (nhdsWithin (realEmbed x) (TubeDomain C))
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · -- φ(ε) → realEmbed x as ε → 0⁺ in nhds
      apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
      show Filter.Tendsto φ (nhds 0) (nhds (SCV.realEmbed x))
      have hφ0 : φ 0 = SCV.realEmbed x := by
        ext i; simp [φ, SCV.realEmbed]
      rw [← hφ0]
      apply Continuous.tendsto
      exact continuous_pi fun i =>
        continuous_const.add
          (((Complex.continuous_ofReal.comp continuous_id).mul continuous_const).mul
            continuous_const)
    · -- φ maps (0, ∞) into TubeDomain C
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      show (fun i => (φ ε i).im) ∈ C
      have him : (fun i => (φ ε i).im) = ε • η := by
        ext i; simp [φ, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im]
      rw [him]
      exact hcone ε hε η hη
  -- Step 2: Use the Fourier-Laplace representation for dominated convergence.
  -- The representation gives both the boundary continuity and the growth bounds
  -- needed for the dominated convergence argument.
  obtain ⟨T, hT_cont, hT⟩ := h_bv
  let hRepr : SCV.HasFourierLaplaceRepr C F :=
    SCV.exists_fourierLaplaceRepr hC hconv hne hF hT_cont hT
  -- The polynomial growth from the representation gives a dominating function.
  -- For ε ∈ (0, 1], εη ∈ C (by cone), and {εη : ε ∈ [1/2, 1]} is compact ⊆ C.
  -- Polynomial growth: |F(x+iy)| ≤ C_bd(1+‖x‖)^N for y in this compact set.
  -- The Fourier-Laplace representation implies that the boundary limit exists
  -- not just distributionally but in the L1-weak topology against integrable functions.
  -- This follows from: (1) boundary continuity + polynomial growth control, and
  -- (2) the Schwartz distributional BV determines the boundary function via
  -- boundary_value_recovery, which integrates against all Schwartz test functions,
  -- hence by density of Schwartz in L1, against all integrable functions.
  --
  -- The full dominated convergence argument requires:
  -- (a) Pointwise: F(x+iεη) → F(realEmbed x) [proved in h_pw]
  -- (b) Domination: |F(x+iεη)| ≤ g(x) where g is integrable
  --     This requires the Fourier-Laplace representation to give bounds
  --     that are integrable against f, not just polynomial growth.
  -- (c) Apply MeasureTheory.tendsto_integral_of_dominated_convergence
  --
  -- This is a consequence of the Fourier-Laplace theory (Vladimirov §25-26)
  -- captured in the infrastructure of LaplaceSchwartz.lean.
  exact SCV.fourierLaplace_boundary_integral_convergence hC hconv hne hcone hF hRepr η hη f hf

/-- Helper: convert Schwartz-based boundary values on the forward tube to the
    flat-coordinate integrable-function form needed by `polynomial_growth_tube`.

    Ref: Vladimirov §26.2-26.3 -/
theorem schwartz_bv_to_flat_bv {d n : ℕ} [NeZero d]
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
    ∀ (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
      ∃ (T : (Fin (n * (d + 1)) → ℝ) → ℂ), ContinuousOn T Set.univ ∧
        ∀ (f : (Fin (n * (d + 1)) → ℝ) → ℂ), MeasureTheory.Integrable f →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x : Fin (n * (d + 1)) → ℝ,
              (F ∘ (flattenCLEquiv n (d + 1)).symm)
                (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ x, T x * f x)) := by
  intro η hη
  -- Step 1: Set up the flattened function G
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  have hG_diff : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten hF
  -- Step 2: Convert Schwartz BV from product to flat coordinates
  have hG_bv : ∃ (T : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ → ℂ), Continuous T ∧
      ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) (η : Fin (n * (d + 1)) → ℝ),
        η ∈ ForwardConeFlat d n →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin (n * (d + 1)) → ℝ,
            G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)) := by
    obtain ⟨T, hT_cont, hT⟩ := h_bv
    let pullback : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR
    refine ⟨fun f => T (pullback f), hT_cont.comp pullback.continuous, fun f η' hη' => ?_⟩
    obtain ⟨η'', hη'', rfl⟩ := hη'
    -- η'' ∈ ForwardConeAbs ↔ InForwardCone, so hT applies directly
    have hconv := hT (pullback f) η'' hη''
    have heq : ∀ ε : ℝ,
        ∫ x : Fin (n * (d + 1)) → ℝ,
          (G fun i => ↑(x i) + ↑ε * ↑(eR η'' i) * Complex.I) * f x =
        ∫ y : NPointDomain d n,
          (F fun k μ => ↑(y k μ) + ↑ε * ↑(η'' k μ) * Complex.I) * (pullback f) y := by
      intro ε
      rw [integral_flatten_change_of_variables]
      congr 1; ext y
      simp only [G, Function.comp, e, eR, pullback,
        SchwartzMap.compCLMOfContinuousLinearEquiv]
      congr 1
      congr 1; funext k μ
      simp only [flattenCLEquiv_symm_apply, flattenCLEquivReal_apply,
        Equiv.symm_apply_apply]
    exact Filter.Tendsto.congr (fun ε => (heq ε).symm) hconv
  -- Step 3: Use boundary_value_recovery and continuous_boundary_tube
  obtain ⟨T_schwartz, hT_schwartz_cont, hT_schwartz⟩ := hG_bv
  -- Define the boundary value function T(x) = G(realEmbed x)
  refine ⟨fun x => G (SCV.realEmbed x), ?_, ?_⟩
  · -- ContinuousOn T univ: the boundary function is continuous.
    -- Proof sketch:
    -- 1. continuous_boundary_tube gives ContinuousWithinAt G (TubeDomain C) (realEmbed x) ∀x
    -- 2. boundary_value_recovery identifies T_schwartz f = ∫ G(realEmbed x) * f(x) dx
    -- 3. By the fundamental lemma of distribution theory, a distribution given by
    --    integration against a function that has ContinuousWithinAt at every boundary
    --    point is continuous.
    -- This is a consequence of the Fourier-Laplace representation underlying
    -- continuous_boundary_tube (Vladimirov §26.2).
    rw [continuousOn_univ]
    exact boundary_function_continuous (forwardConeFlat_isOpen d n)
      (forwardConeFlat_convex d n) (forwardConeFlat_nonempty d n)
      (forwardConeFlat_isCone d n) hG_diff ⟨T_schwartz, hT_schwartz_cont, hT_schwartz⟩
  · -- Convergence against integrable f:
    -- ∫ G(x+iεη)f(x)dx → ∫ G(realEmbed x)f(x)dx as ε → 0⁺
    -- Proof sketch:
    -- 1. Pointwise: G(realEmbed x + iεη) → G(realEmbed x) by ContinuousWithinAt
    -- 2. Domination: polynomial_growth_tube gives |G(x+iy)| ≤ C(1+|x|)^N for y in compact
    -- 3. Dominated convergence theorem gives integral convergence
    exact boundary_integral_convergence (forwardConeFlat_isOpen d n)
      (forwardConeFlat_convex d n) (forwardConeFlat_nonempty d n)
      (forwardConeFlat_isCone d n) hG_diff ⟨T_schwartz, hT_schwartz_cont, hT_schwartz⟩ η hη

end
