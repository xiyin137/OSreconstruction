/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.BHWCore
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Difference Coordinates for the Forward Tube

This file defines the **difference-coordinate map** `L` that transforms the forward tube
from "absolute coordinates" `z₀, z₁, ..., z_{n-1}` to "difference coordinates"
`ξ₀ = z₀, ξₖ = zₖ - z_{k-1}` for `k > 0`.

In difference coordinates, the forward tube becomes a **product tube domain**:
each `ξₖ` independently satisfies `Im(ξₖ) ∈ V₊` (the open forward light cone).

## Main definitions

* `BHW.diffCoordFun` — the difference-coordinate function `L : z ↦ ξ`
* `BHW.partialSumFun` — the inverse (partial-sum) function `L⁻¹ : ξ ↦ z`
* `BHW.diffCoordEquiv` — the continuous linear equivalence `L`
* `BHW.ProductForwardCone` — the product tube domain `{w | ∀ k, Im(w k) ∈ V₊}`

## Main results

* `BHW.forwardTube_eq_diffCoord_preimage` — `ForwardTube d n = L⁻¹(ProductForwardCone d n)`

## References

* Streater & Wightman, *PCT, Spin and Statistics*, §2.4
* Jost (1965), *The General Theory of Quantized Fields*, Ch. IV
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter Finset

variable {d : ℕ}

namespace BHW

/-- Re-export of the forward tube from `BHWCore` for difference-coordinate results. -/
abbrev ForwardTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  BHWCore.ForwardTube d n

/-! ### Difference-coordinate functions -/

/-- The difference-coordinate function `L`:
    - `L(z)(0) = z(0)` (base point)
    - `L(z)(k) = z(k) - z(k-1)` for `k > 0` (successive differences) -/
def diffCoordFun (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    if h : k.val = 0 then z k μ
    else z k μ - z ⟨k.val - 1, by omega⟩ μ

/-- The partial-sum function `L⁻¹`:
    - `L⁻¹(ξ)(k) = ∑_{j=0}^{k} ξ(j)` -/
def partialSumFun (n d : ℕ) (ξ : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ => ∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ

/-! ### Telescoping lemmas -/

/-- Key telescoping: the partial sum of differences equals the original value. -/
private lemma partialSum_diffCoord_val (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ)
    (m : ℕ) (hm : m < n) (μ : Fin (d + 1)) :
    (∑ j : Fin (m + 1), diffCoordFun n d z ⟨j.val, by omega⟩ μ) = z ⟨m, hm⟩ μ := by
  induction m with
  | zero =>
    simp [diffCoordFun]
  | succ m ih =>
    -- Split: ∑_{j=0}^{m+1} f(j) = ∑_{j=0}^{m} f(castSucc j) + f(last)
    rw [Fin.sum_univ_castSucc]
    -- Convert (castSucc j).val to j.val so ih matches, then apply ih
    simp_rw [Fin.val_castSucc]
    rw [ih (by omega)]
    -- Goal: z ⟨m, _⟩ μ + diffCoordFun n d z ⟨(Fin.last (m+1)).val, _⟩ μ = z ⟨m+1, hm⟩ μ
    simp only [Fin.val_last, diffCoordFun, show ¬(m + 1 = 0) from Nat.succ_ne_zero m, ↓reduceDIte]
    have : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ :=
      Fin.ext (show m + 1 - 1 = m by omega)
    rw [this]; ring

/-- `L⁻¹ ∘ L = id`: partial sums of differences recover the original. -/
theorem partialSum_diffCoord (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ) :
    partialSumFun n d (diffCoordFun n d z) = z := by
  funext k μ
  exact partialSum_diffCoord_val n d z k.val k.isLt μ

/-! ### Linear maps -/

/-- The difference-coordinate map as a linear map. -/
def diffCoordLM (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → Fin (d + 1) → ℂ) where
  toFun := diffCoordFun n d
  map_add' z₁ z₂ := by
    funext k μ
    simp only [diffCoordFun, Pi.add_apply]
    by_cases hk : k.val = 0 <;> simp [hk, sub_add_sub_comm]
  map_smul' c z := by
    funext k μ
    simp only [diffCoordFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    by_cases hk : k.val = 0 <;> simp [hk, mul_sub]

/-- The partial-sum map as a linear map. -/
def partialSumLM (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → Fin (d + 1) → ℂ) where
  toFun := partialSumFun n d
  map_add' ξ₁ ξ₂ := by
    funext k μ
    simp only [partialSumFun, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' c ξ := by
    funext k μ
    simp only [partialSumFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]

/-- `L ∘ L⁻¹ = id`: differences of partial sums recover the original.
    Proved by finite-dimensional linear algebra: since L⁻¹∘L = id, L is injective.
    On finite-dimensional spaces, injective linear maps are surjective.
    Therefore L⁻¹ is also a right inverse. -/
theorem diffCoord_partialSum (n d : ℕ) (ξ : Fin n → Fin (d + 1) → ℂ) :
    diffCoordFun n d (partialSumFun n d ξ) = ξ := by
  -- L⁻¹ ∘ L = id gives injectivity of L
  have h_left_inv : ∀ z, partialSumFun n d (diffCoordFun n d z) = z :=
    partialSum_diffCoord n d
  have h_inj : Function.Injective (diffCoordLM n d) := by
    intro a b h
    have : diffCoordFun n d a = diffCoordFun n d b := h
    calc a = partialSumFun n d (diffCoordFun n d a) := (h_left_inv a).symm
      _ = partialSumFun n d (diffCoordFun n d b) := congr_arg _ this
      _ = b := h_left_inv b
  -- Injective ↔ surjective for linear endomorphisms on finite-dimensional spaces
  have h_surj : Function.Surjective (diffCoordLM n d) :=
    LinearMap.injective_iff_surjective.mp h_inj
  -- For any ξ, find z with L(z) = ξ, then L(L⁻¹(ξ)) = L(L⁻¹(L(z))) = L(z) = ξ
  obtain ⟨z, rfl⟩ := h_surj ξ
  exact congr_arg (diffCoordFun n d) (h_left_inv z)

/-! ### Linear equivalence -/

/-- The difference-coordinate linear equivalence. -/
def diffCoordLinearEquiv (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin n → Fin (d + 1) → ℂ) where
  toLinearMap := diffCoordLM n d
  invFun := partialSumFun n d
  left_inv z := partialSum_diffCoord n d z
  right_inv ξ := diffCoord_partialSum n d ξ

/-- The difference-coordinate continuous linear equivalence. -/
def diffCoordEquiv (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
  (diffCoordLinearEquiv n d).toContinuousLinearEquiv

theorem diffCoordEquiv_apply (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ)
    (k : Fin n) (μ : Fin (d + 1)) :
    diffCoordEquiv n d z k μ =
      if _h : k.val = 0 then z k μ
      else z k μ - z ⟨k.val - 1, by omega⟩ μ := by
  show diffCoordFun n d z k μ = _
  simp [diffCoordFun]

theorem diffCoordEquiv_symm_apply (n d : ℕ) (ξ : Fin n → Fin (d + 1) → ℂ)
    (k : Fin n) (μ : Fin (d + 1)) :
    (diffCoordEquiv n d).symm ξ k μ =
      ∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ := rfl

/-! ### Flattening helpers (two-index ↔ one-index) -/

/-- Flatten configuration indices `(k, μ)` to a single `Fin (n*(d+1))` index. -/
def flattenCfg (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ) :
    Fin (n * (d + 1)) → ℂ :=
  fun i =>
    let p : Fin n × Fin (d + 1) := finProdFinEquiv.symm i
    z p.1 p.2

/-- Unflatten from `Fin (n*(d+1)) → ℂ` to two-index configurations. -/
def unflattenCfg (n d : ℕ) (w : Fin (n * (d + 1)) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ => w (finProdFinEquiv (k, μ))

/-- Real-valued flattening variant. -/
def flattenCfgReal (n d : ℕ) (z : Fin n → Fin (d + 1) → ℝ) :
    Fin (n * (d + 1)) → ℝ :=
  fun i =>
    let p : Fin n × Fin (d + 1) := finProdFinEquiv.symm i
    z p.1 p.2

/-- Real-valued unflattening variant. -/
def unflattenCfgReal (n d : ℕ) (w : Fin (n * (d + 1)) → ℝ) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ => w (finProdFinEquiv (k, μ))

theorem unflatten_flatten_cfg (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ) :
    unflattenCfg n d (flattenCfg n d z) = z := by
  funext k μ
  simp [unflattenCfg, flattenCfg]

theorem flatten_unflatten_cfg (n d : ℕ) (w : Fin (n * (d + 1)) → ℂ) :
    flattenCfg n d (unflattenCfg n d w) = w := by
  funext i
  change w (finProdFinEquiv (finProdFinEquiv.symm i)) = w i
  simpa using congrArg w (finProdFinEquiv.apply_symm_apply i)

theorem unflatten_flatten_cfg_real (n d : ℕ) (z : Fin n → Fin (d + 1) → ℝ) :
    unflattenCfgReal n d (flattenCfgReal n d z) = z := by
  funext k μ
  simp [unflattenCfgReal, flattenCfgReal]

theorem flatten_unflatten_cfg_real (n d : ℕ) (w : Fin (n * (d + 1)) → ℝ) :
    flattenCfgReal n d (unflattenCfgReal n d w) = w := by
  funext i
  change w (finProdFinEquiv (finProdFinEquiv.symm i)) = w i
  simpa using congrArg w (finProdFinEquiv.apply_symm_apply i)

/-! ### Product forward cone -/

/-- The product forward cone: the set of `ξ` where `Im(ξ k) ∈ V₊` for all `k`.
    In difference coordinates, the forward tube becomes exactly this product set. -/
def ProductForwardCone (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  { ξ | ∀ k : Fin n, InOpenForwardCone d (fun μ => (ξ k μ).im) }

/-- Real product forward cone (imaginary-part cone condition only). -/
def ProductForwardConeReal (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℝ) :=
  {η | ∀ k : Fin n, InOpenForwardCone d (η k)}

theorem mem_productForwardCone_iff_im_mem_real (n d : ℕ)
    (ξ : Fin n → Fin (d + 1) → ℂ) :
    ξ ∈ ProductForwardCone d n ↔
      (fun k μ => (ξ k μ).im) ∈ ProductForwardConeReal d n := by
  rfl

/-- Flattened real cone for one-indexed coordinate statements. -/
def FlatProductForwardConeReal (d n : ℕ) :
    Set (Fin (n * (d + 1)) → ℝ) :=
  {u | unflattenCfgReal n d u ∈ ProductForwardConeReal d n}

theorem mem_productForwardCone_iff_flat_im (n d : ℕ)
    (ξ : Fin n → Fin (d + 1) → ℂ) :
    ξ ∈ ProductForwardCone d n ↔
      (fun i => (flattenCfg n d ξ i).im) ∈ FlatProductForwardConeReal d n := by
  constructor
  · intro hξ
    have hfun :
        (unflattenCfgReal n d (fun i => (flattenCfg n d ξ i).im)) =
          (fun k μ => (ξ k μ).im) := by
      funext k μ
      simp [unflattenCfgReal, flattenCfg]
    change unflattenCfgReal n d (fun i => (flattenCfg n d ξ i).im) ∈
      ProductForwardConeReal d n
    rw [hfun]
    simpa using ((mem_productForwardCone_iff_im_mem_real n d ξ).mp hξ)
  · intro hflat
    have hfun :
        (unflattenCfgReal n d (fun i => (flattenCfg n d ξ i).im)) =
          (fun k μ => (ξ k μ).im) := by
      funext k μ
      simp [unflattenCfgReal, flattenCfg]
    have him : (fun k μ => (ξ k μ).im) ∈ ProductForwardConeReal d n := by
      change unflattenCfgReal n d (fun i => (flattenCfg n d ξ i).im) ∈
        ProductForwardConeReal d n at hflat
      rwa [hfun] at hflat
    exact (mem_productForwardCone_iff_im_mem_real n d ξ).mpr him

/-! ### Forward tube = preimage of product forward cone under L -/

/-- The forward tube condition at index k is equivalent to the InOpenForwardCone
    condition on the k-th difference coordinate. -/
private lemma forwardTube_cond_iff_diffCoord (n d : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) :
    InOpenForwardCone d
      (fun μ => (z k μ - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im) ↔
    InOpenForwardCone d (fun μ => (diffCoordFun n d z k μ).im) := by
  suffices heq : (fun μ => (z k μ -
      (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im) =
      (fun μ => (diffCoordFun n d z k μ).im) by rw [heq]
  funext μ; simp only [diffCoordFun]
  by_cases hk : k.val = 0 <;> simp [hk]

/-- The forward tube equals the preimage of the product forward cone under the
    difference-coordinate map. -/
theorem forwardTube_eq_diffCoord_preimage (n d : ℕ) [NeZero d] :
    ForwardTube d n = diffCoordEquiv n d ⁻¹' ProductForwardCone d n := by
  ext z
  simp only [Set.mem_preimage, ProductForwardCone, Set.mem_setOf_eq,
    ForwardTube, Set.mem_setOf_eq]
  exact ⟨fun hz k => (forwardTube_cond_iff_diffCoord n d z k).mp (hz k),
         fun hξ k => (forwardTube_cond_iff_diffCoord n d z k).mpr (hξ k)⟩

/-- The image of the forward tube under the difference-coordinate map is
    exactly the product forward cone. -/
theorem diffCoordEquiv_image_forwardTube (n d : ℕ) [NeZero d] :
    diffCoordEquiv n d '' ForwardTube d n = ProductForwardCone d n := by
  rw [forwardTube_eq_diffCoord_preimage]
  exact (diffCoordEquiv n d).toEquiv.image_preimage _

/-- Forward tube reformulated via flattened difference coordinates and
    real cone membership. -/
theorem forwardTube_iff_flattened_diffCone (n d : ℕ) [NeZero d]
    (z : Fin n → Fin (d + 1) → ℂ) :
    ForwardTube d n z ↔
      (fun i => (flattenCfg n d (diffCoordEquiv n d z) i).im) ∈
        FlatProductForwardConeReal d n := by
  constructor
  · intro hz
    have hpc : diffCoordEquiv n d z ∈ ProductForwardCone d n := by
      simpa [forwardTube_eq_diffCoord_preimage (n := n) (d := d)] using hz
    exact (mem_productForwardCone_iff_flat_im n d (diffCoordEquiv n d z)).mp hpc
  · intro hflat
    have hpc : diffCoordEquiv n d z ∈ ProductForwardCone d n :=
      (mem_productForwardCone_iff_flat_im n d (diffCoordEquiv n d z)).mpr hflat
    simpa [forwardTube_eq_diffCoord_preimage (n := n) (d := d)] using hpc

/-- The open forward cone is an open set. -/
private theorem isOpen_inOpenForwardCone :
    IsOpen {η : Fin (d + 1) → ℝ | InOpenForwardCone d η} :=
  IsOpen.inter
    (isOpen_lt continuous_const (continuous_apply 0))
    (isOpen_lt (continuous_finset_sum _ (fun μ _ =>
      (continuous_const.mul ((continuous_apply μ).pow 2)))) continuous_const)

/-- The product forward cone is open. -/
theorem isOpen_productForwardCone (n d : ℕ) [NeZero d] :
    IsOpen (ProductForwardCone d n) := by
  suffices h : ProductForwardCone d n =
      ⋂ k : Fin n, {ξ : Fin n → Fin (d + 1) → ℂ |
        InOpenForwardCone d (fun μ => (ξ k μ).im)} by
    rw [h]
    apply isOpen_iInter_of_finite
    intro k
    have : {ξ : Fin n → Fin (d + 1) → ℂ | InOpenForwardCone d (fun μ => (ξ k μ).im)} =
        (fun ξ => fun μ => (ξ k μ).im) ⁻¹' {η | InOpenForwardCone d η} := rfl
    rw [this]
    exact isOpen_inOpenForwardCone.preimage
      (continuous_pi (fun μ =>
        Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply k))))
  ext ξ; simp [ProductForwardCone, Set.mem_iInter]

/-- The real product forward cone is open. -/
theorem isOpen_productForwardConeReal (n d : ℕ) [NeZero d] :
    IsOpen (ProductForwardConeReal d n) := by
  suffices h : ProductForwardConeReal d n =
      ⋂ k : Fin n, {η : Fin n → Fin (d + 1) → ℝ |
        InOpenForwardCone d (fun μ => η k μ)} by
    rw [h]
    apply isOpen_iInter_of_finite
    intro k
    have : {η : Fin n → Fin (d + 1) → ℝ | InOpenForwardCone d (fun μ => η k μ)} =
        (fun η => fun μ => η k μ) ⁻¹' {ξ | InOpenForwardCone d ξ} := rfl
    rw [this]
    exact isOpen_inOpenForwardCone.preimage
      (continuous_pi (fun μ => (continuous_apply μ).comp (continuous_apply k)))
  ext η
  simp [ProductForwardConeReal, Set.mem_iInter]

/-- Positive real scaling preserves the product forward cone. -/
theorem productForwardCone_smul_pos (n d : ℕ) (t : ℝ) (ht : 0 < t)
    (ξ : Fin n → Fin (d + 1) → ℂ) (hξ : ξ ∈ ProductForwardCone d n) :
    t • ξ ∈ ProductForwardCone d n := by
  intro k
  have hk := hξ k
  have him : (fun μ => ((t • ξ) k μ).im) = t • (fun μ => (ξ k μ).im) := by
    ext μ
    simp [Pi.smul_apply, smul_eq_mul]
  rw [him]
  exact inOpenForwardCone_smul_pos hk ht

/-- Positive real scaling preserves the real product forward cone. -/
theorem productForwardConeReal_smul_pos (n d : ℕ) (t : ℝ) (ht : 0 < t)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ ProductForwardConeReal d n) :
    t • η ∈ ProductForwardConeReal d n := by
  intro k
  simpa [Pi.smul_apply, smul_eq_mul] using inOpenForwardCone_smul_pos (hη k) ht

/-- The product forward cone is convex. -/
theorem productForwardCone_convex (n d : ℕ) :
    Convex ℝ (ProductForwardCone d n) := by
  intro ξ₁ hξ₁ ξ₂ hξ₂ a b ha hb hab k
  have hk1 := hξ₁ k
  have hk2 := hξ₂ k
  have hconvSet := inOpenForwardCone_convex (d := d)
  have hconv : InOpenForwardCone d
      (a • (fun μ => (ξ₁ k μ).im) + b • (fun μ => (ξ₂ k μ).im)) :=
    hconvSet hk1 hk2 ha hb hab
  have hcoord :
      (fun μ => ((a • ξ₁ + b • ξ₂) k μ).im) =
      a • (fun μ => (ξ₁ k μ).im) + b • (fun μ => (ξ₂ k μ).im) := by
    ext μ
    simp [Pi.smul_apply, smul_eq_mul]
  simpa [hcoord] using hconv

/-- The real product forward cone is convex. -/
theorem productForwardConeReal_convex (n d : ℕ) :
    Convex ℝ (ProductForwardConeReal d n) := by
  intro η₁ hη₁ η₂ hη₂ a b ha hb hab k
  exact inOpenForwardCone_convex (hη₁ k) (hη₂ k) ha hb hab

/-- The product forward cone is nonempty. -/
theorem productForwardCone_nonempty (n d : ℕ) [NeZero d] :
    (ProductForwardCone d n).Nonempty := by
  refine ⟨fun _ μ => if μ = 0 then (Complex.I : ℂ) else 0, ?_⟩
  intro k
  constructor
  · simp
  · rw [minkowski_sum_decomp]
    simp [Fin.succ_ne_zero]

/-- The real product forward cone is nonempty. -/
theorem productForwardConeReal_nonempty (n d : ℕ) [NeZero d] :
    (ProductForwardConeReal d n).Nonempty := by
  refine ⟨fun _ μ => if μ = 0 then (1 : ℝ) else 0, ?_⟩
  intro k
  constructor
  · simp
  · rw [minkowski_sum_decomp]
    simp [Fin.succ_ne_zero]

/-- For `n > 0`, the product forward cone does not contain the zero configuration. -/
theorem zero_not_mem_productForwardCone (n d : ℕ) [NeZero n] :
    (0 : Fin n → Fin (d + 1) → ℂ) ∉ ProductForwardCone d n := by
  intro h0
  let k0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have hcone0 := h0 k0
  have htime : ((0 : Fin n → Fin (d + 1) → ℂ) k0 0).im > 0 := hcone0.1
  simp at htime

/-- For `n > 0`, the real product forward cone does not contain the zero configuration. -/
theorem zero_not_mem_productForwardConeReal (n d : ℕ) [NeZero n] :
    (0 : Fin n → Fin (d + 1) → ℝ) ∉ ProductForwardConeReal d n := by
  intro h0
  let k0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have hcone0 := h0 k0
  have htime : ((0 : Fin n → Fin (d + 1) → ℝ) k0 0) > 0 := hcone0.1
  simp at htime

private theorem continuous_unflattenCfgReal (n d : ℕ) :
    Continuous (unflattenCfgReal n d :
      (Fin (n * (d + 1)) → ℝ) → Fin n → Fin (d + 1) → ℝ) := by
  apply continuous_pi; intro k
  apply continuous_pi; intro μ
  simpa [unflattenCfgReal] using (continuous_apply (finProdFinEquiv (k, μ)))

/-- The flattened real product forward cone is open. -/
theorem isOpen_flatProductForwardConeReal (n d : ℕ) [NeZero d] :
    IsOpen (FlatProductForwardConeReal d n) := by
  simpa [FlatProductForwardConeReal] using
    (isOpen_productForwardConeReal (n := n) (d := d)).preimage
      (continuous_unflattenCfgReal n d)

/-- Positive real scaling preserves the flattened real product forward cone. -/
theorem flatProductForwardConeReal_smul_pos (n d : ℕ) (t : ℝ) (ht : 0 < t)
    (u : Fin (n * (d + 1)) → ℝ) (hu : u ∈ FlatProductForwardConeReal d n) :
    t • u ∈ FlatProductForwardConeReal d n := by
  change unflattenCfgReal n d (t • u) ∈ ProductForwardConeReal d n
  have hlin : unflattenCfgReal n d (t • u) = t • unflattenCfgReal n d u := by
    ext k μ
    simp [unflattenCfgReal, Pi.smul_apply]
  rw [hlin]
  exact productForwardConeReal_smul_pos (n := n) (d := d) t ht _ hu

/-- The flattened real product forward cone is convex. -/
theorem flatProductForwardConeReal_convex (n d : ℕ) :
    Convex ℝ (FlatProductForwardConeReal d n) := by
  intro u₁ hu₁ u₂ hu₂ a b ha hb hab
  change unflattenCfgReal n d (a • u₁ + b • u₂) ∈ ProductForwardConeReal d n
  have hlin :
      unflattenCfgReal n d (a • u₁ + b • u₂) =
      a • unflattenCfgReal n d u₁ + b • unflattenCfgReal n d u₂ := by
    ext k μ
    simp [unflattenCfgReal, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [hlin]
  exact productForwardConeReal_convex (n := n) (d := d) hu₁ hu₂ ha hb hab

/-- The flattened real product forward cone is nonempty. -/
theorem flatProductForwardConeReal_nonempty (n d : ℕ) [NeZero d] :
    (FlatProductForwardConeReal d n).Nonempty := by
  rcases productForwardConeReal_nonempty (n := n) (d := d) with ⟨η, hη⟩
  refine ⟨flattenCfgReal n d η, ?_⟩
  simpa [FlatProductForwardConeReal, unflatten_flatten_cfg_real] using hη

/-- For `n > 0`, zero is not in the flattened real product forward cone. -/
theorem zero_not_mem_flatProductForwardConeReal (n d : ℕ) [NeZero n] :
    (0 : Fin (n * (d + 1)) → ℝ) ∉ FlatProductForwardConeReal d n := by
  intro h0
  have h0' : (0 : Fin n → Fin (d + 1) → ℝ) ∈ ProductForwardConeReal d n := by
    simpa [FlatProductForwardConeReal] using h0
  exact zero_not_mem_productForwardConeReal (n := n) (d := d) h0'

/-- Pack the cone hypotheses used by `SCV.edge_of_the_wedge_theorem`. -/
theorem productForwardCone_eowReady (n d : ℕ) [NeZero d] [NeZero n] :
    IsOpen (ProductForwardCone d n) ∧
    Convex ℝ (ProductForwardCone d n) ∧
    ((0 : Fin n → Fin (d + 1) → ℂ) ∉ ProductForwardCone d n) ∧
    (∀ (t : ℝ) (y : Fin n → Fin (d + 1) → ℂ),
      0 < t → y ∈ ProductForwardCone d n → t • y ∈ ProductForwardCone d n) ∧
    (ProductForwardCone d n).Nonempty := by
  refine ⟨isOpen_productForwardCone (n := n) (d := d),
    productForwardCone_convex (n := n) (d := d),
    zero_not_mem_productForwardCone (n := n) (d := d),
    ?_, productForwardCone_nonempty (n := n) (d := d)⟩
  intro t y ht hy
  exact productForwardCone_smul_pos (n := n) (d := d) t ht y hy

/-- Flat real cone hypotheses in the exact shape used by
    `SCV.edge_of_the_wedge_theorem` after flattening difference coordinates. -/
theorem flatProductForwardConeReal_eowReady (n d : ℕ) [NeZero d] [NeZero n] :
    IsOpen (FlatProductForwardConeReal d n) ∧
    Convex ℝ (FlatProductForwardConeReal d n) ∧
    ((0 : Fin (n * (d + 1)) → ℝ) ∉ FlatProductForwardConeReal d n) ∧
    (∀ (t : ℝ) (y : Fin (n * (d + 1)) → ℝ),
      0 < t → y ∈ FlatProductForwardConeReal d n → t • y ∈ FlatProductForwardConeReal d n) ∧
    (FlatProductForwardConeReal d n).Nonempty := by
  refine ⟨isOpen_flatProductForwardConeReal (n := n) (d := d),
    flatProductForwardConeReal_convex (n := n) (d := d),
    zero_not_mem_flatProductForwardConeReal (n := n) (d := d),
    ?_, flatProductForwardConeReal_nonempty (n := n) (d := d)⟩
  intro t y ht hy
  exact flatProductForwardConeReal_smul_pos (n := n) (d := d) t ht y hy

/-! ### Swap action in difference coordinates -/

/-- In difference coordinates, swapping indices i and i+1 causes
    the (i+1)-th difference coordinate to flip sign.

    This is crucial because the sign flip creates the EOW setup:
    forward tube has Im(ξ_{i+1}) ∈ V₊, while the swapped tube has Im(-ξ_{i+1}) ∈ -V₊. -/
theorem diffCoord_swap_sign_flip (n d : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin (d + 1) → ℂ) (μ : Fin (d + 1)) :
    let σ := Equiv.swap i ⟨i.val + 1, hi⟩
    diffCoordFun n d (fun k => z (σ k)) ⟨i.val + 1, hi⟩ μ =
      -(diffCoordFun n d z ⟨i.val + 1, hi⟩ μ) := by
  simp only [diffCoordFun]
  have hk_ne : ¬ ((i.val + 1) = 0) := Nat.succ_ne_zero _
  simp only [hk_ne, ↓reduceDIte]
  have hpred : (⟨i.val + 1 - 1, by omega⟩ : Fin n) = i := by ext; simp
  rw [hpred, Equiv.swap_apply_right, Equiv.swap_apply_left]
  ring

/-- If the swapped configuration is in the forward tube, then in difference
    coordinates the swapped `(i+1)`-component lies in the negative cone. -/
theorem swap_forwardTube_implies_neg_cone (n d : ℕ) [NeZero d]
    (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzswap : (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ForwardTube d n) :
    InOpenForwardCone d
      (fun μ => (-(diffCoordFun n d z ⟨i.val + 1, hi⟩ μ)).im) := by
  set σ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hpre : diffCoordEquiv n d (fun k => z (σ k)) ∈ ProductForwardCone d n := by
    simpa [forwardTube_eq_diffCoord_preimage (n := n) (d := d)] using hzswap
  have hk : InOpenForwardCone d
      (fun μ =>
        (diffCoordEquiv n d (fun k => z (σ k)) ⟨i.val + 1, hi⟩ μ).im) := hpre ⟨i.val + 1, hi⟩
  have hk' : InOpenForwardCone d
      (fun μ =>
        (diffCoordFun n d (fun k => z (σ k)) ⟨i.val + 1, hi⟩ μ).im) := by
    simpa [diffCoordEquiv_apply] using hk
  have hfun :
      (fun μ =>
        (diffCoordFun n d (fun k => z (σ k)) ⟨i.val + 1, hi⟩ μ).im) =
      (fun μ => (-(diffCoordFun n d z ⟨i.val + 1, hi⟩ μ)).im) := by
    ext μ
    have hflip := diffCoord_swap_sign_flip (n := n) (d := d) i hi z μ
    simpa [σ] using congrArg Complex.im hflip
  simpa [hfun] using hk'

/-- Coordinates far from the swap are unchanged in difference coordinates. -/
theorem diffCoord_swap_far_unchanged (n d : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) (μ : Fin (d + 1))
    (hk_ne_i : k ≠ i) (hk_ne_ip1 : k ≠ ⟨i.val + 1, hi⟩)
    (hkm1_ne_i : k.val ≠ 0 → (⟨k.val - 1, by omega⟩ : Fin n) ≠ i)
    (hkm1_ne_ip1 : k.val ≠ 0 → (⟨k.val - 1, by omega⟩ : Fin n) ≠ ⟨i.val + 1, hi⟩) :
    let σ := Equiv.swap i ⟨i.val + 1, hi⟩
    diffCoordFun n d (fun k => z (σ k)) k μ = diffCoordFun n d z k μ := by
  simp only [diffCoordFun]
  by_cases hk0 : k.val = 0
  · simp only [hk0, ↓reduceDIte]
    congr 1
    exact Equiv.swap_apply_of_ne_of_ne hk_ne_i hk_ne_ip1
  · simp only [hk0, ↓reduceDIte]
    rw [Equiv.swap_apply_of_ne_of_ne hk_ne_i hk_ne_ip1,
        Equiv.swap_apply_of_ne_of_ne (hkm1_ne_i hk0) (hkm1_ne_ip1 hk0)]

end BHW

end
