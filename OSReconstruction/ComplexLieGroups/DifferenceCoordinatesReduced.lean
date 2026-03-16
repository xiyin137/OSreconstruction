/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.DifferenceCoordinates
import OSReconstruction.ComplexLieGroups.Connectedness.Action
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube

/-!
# Reduced Difference Coordinates

This file quotients the full difference-coordinate chart by the basepoint component
`ξ₀ = z₀`, keeping only the successive differences
`δ_j = z_{j+1} - z_j` for `j = 0, ..., n-2`.

The main constructions are:

* `tailDiffProj`        : drop the basepoint difference coordinate
* `prependZeroDiff`     : reinsert a zero basepoint coordinate
* `reducedDiffMap`      : absolute coordinates -> reduced difference coordinates
* `reducedDiffSection`  : reduced difference coordinates -> absolute coordinates
* `diffCoordEquiv_action` : Lorentz-equivariance of the full difference chart

These are the basic algebraic tools for the `(n-1)`-variable Route 1 translation
invariance refactor.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter Finset

namespace BHW

variable {d n : ℕ}

/-- The full difference-coordinate chart is Lorentz-equivariant. -/
theorem diffCoordEquiv_action (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    diffCoordEquiv n d (complexLorentzAction Λ z) =
      complexLorentzAction Λ (diffCoordEquiv n d z) := by
  ext k μ
  by_cases hk : k.val = 0
  · simp [hk, complexLorentzAction, diffCoordEquiv_apply]
  · simp [hk, complexLorentzAction, diffCoordEquiv_apply]
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext ν
    ring

/-- Drop the basepoint difference coordinate `ξ₀`, keeping `ξ₁, ..., ξ_{n-1}`. -/
noncomputable def tailDiffProj (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) →L[ℂ] (Fin (n - 1) → Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℂ) (ι := Fin n)
      (φ := fun _ => Fin (d + 1) → ℂ) ⟨j.val + 1, by omega⟩

@[simp] theorem tailDiffProj_apply (n d : ℕ)
    (ξ : Fin n → Fin (d + 1) → ℂ) (j : Fin (n - 1)) :
    tailDiffProj n d ξ j = ξ ⟨j.val + 1, by omega⟩ := rfl

/-- Reinsert a zero basepoint difference coordinate in front of a reduced
    difference configuration. -/
noncomputable def prependZeroDiff (n d : ℕ) :
    (Fin (n - 1) → Fin (d + 1) → ℂ) →L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi fun k =>
    if hk : k.val = 0 then 0
    else
      ContinuousLinearMap.proj (R := ℂ) (ι := Fin (n - 1))
        (φ := fun _ => Fin (d + 1) → ℂ) ⟨k.val - 1, by omega⟩

@[simp] theorem prependZeroDiff_apply_zero (n d : ℕ)
    (η : Fin (n - 1) → Fin (d + 1) → ℂ) (k : Fin n) (hk : k.val = 0) :
    prependZeroDiff n d η k = 0 := by
  simp [prependZeroDiff, hk]

@[simp] theorem prependZeroDiff_apply_succ (n d : ℕ)
    (η : Fin (n - 1) → Fin (d + 1) → ℂ) (k : Fin n) (hk : k.val ≠ 0) :
    prependZeroDiff n d η k = η ⟨k.val - 1, by omega⟩ := by
  simp [prependZeroDiff, hk]

/-- Dropping the prepended zero recovers the reduced difference configuration. -/
@[simp] theorem tailDiffProj_prependZeroDiff (n d : ℕ)
    (η : Fin (n - 1) → Fin (d + 1) → ℂ) :
    tailDiffProj n d (prependZeroDiff n d η) = η := by
  ext j μ
  simp [tailDiffProj, prependZeroDiff]

/-- Absolute coordinates to reduced `(n-1)`-difference coordinates. -/
noncomputable def reducedDiffMap (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) →L[ℂ] (Fin (n - 1) → Fin (d + 1) → ℂ) :=
  (tailDiffProj n d).comp (diffCoordEquiv n d).toContinuousLinearMap

@[simp] theorem reducedDiffMap_apply (n d : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) (j : Fin (n - 1)) :
    reducedDiffMap n d z j = diffCoordEquiv n d z ⟨j.val + 1, by omega⟩ := by
  rfl

/-- The reduced difference map is Lorentz-equivariant. -/
theorem reducedDiffMap_action (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    reducedDiffMap n d (complexLorentzAction Λ z) =
      complexLorentzAction Λ (reducedDiffMap n d z) := by
  ext j μ
  simp [reducedDiffMap_apply, diffCoordEquiv_action, complexLorentzAction]

/-- The reduced difference map records the successive differences
    `z_{j+1} - z_j`. -/
theorem reducedDiffMap_eq_successive_differences (n d : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) (j : Fin (n - 1)) (μ : Fin (d + 1)) :
    reducedDiffMap n d z j μ =
      z ⟨j.val + 1, by omega⟩ μ - z ⟨j.val, by omega⟩ μ := by
  simp [reducedDiffMap_apply, diffCoordEquiv_apply]

/-- Uniform translations are invisible in reduced difference coordinates. -/
theorem reducedDiffMap_translate_uniform_eq (n d : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ) :
    reducedDiffMap n d (fun k μ => z k μ + c μ) = reducedDiffMap n d z := by
  ext j μ
  rw [reducedDiffMap_eq_successive_differences, reducedDiffMap_eq_successive_differences]
  ring

/-- A zero-basepoint section from reduced differences back to absolute coordinates. -/
noncomputable def reducedDiffSection (n d : ℕ) :
    (Fin (n - 1) → Fin (d + 1) → ℂ) →L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
  (diffCoordEquiv n d).symm.toContinuousLinearMap.comp (prependZeroDiff n d)

/-- The reduced section is a right inverse to the reduced difference map. -/
@[simp] theorem reducedDiffMap_section (n d : ℕ)
    (η : Fin (n - 1) → Fin (d + 1) → ℂ) :
    reducedDiffMap n d (reducedDiffSection n d η) = η := by
  calc
    reducedDiffMap n d (reducedDiffSection n d η)
        = tailDiffProj n d
            ((diffCoordEquiv n d)
              ((diffCoordEquiv n d).symm (prependZeroDiff n d η))) := by
              rfl
    _ = tailDiffProj n d (prependZeroDiff n d η) := by
          simp
    _ = η := tailDiffProj_prependZeroDiff n d η

/-- The reduced forward cone is the product forward cone on the reduced
    `(n-1)`-difference variables. -/
abbrev ReducedForwardCone (d n : ℕ) :
    Set (Fin (n - 1) → Fin (d + 1) → ℂ) :=
  ProductForwardCone d (n - 1)

/-- The reduced forward tube is the reduced product forward cone. -/
def ReducedForwardTube (d n : ℕ) :
    Set (Fin (n - 1) → Fin (d + 1) → ℂ) :=
  ReducedForwardCone d n

theorem isOpen_reducedForwardCone (n d : ℕ) [NeZero d] :
    IsOpen (ReducedForwardCone d n) := by
  simpa [ReducedForwardCone] using isOpen_productForwardCone (n := n - 1) (d := d)

theorem reducedForwardCone_convex (n d : ℕ) :
    Convex ℝ (ReducedForwardCone d n) := by
  simpa [ReducedForwardCone] using productForwardCone_convex (n := n - 1) (d := d)

theorem reducedForwardCone_nonempty (n d : ℕ) [NeZero d] :
    (ReducedForwardCone d n).Nonempty := by
  simpa [ReducedForwardCone] using productForwardCone_nonempty (n := n - 1) (d := d)

/-- The absolute forward tube splits into the basepoint cone condition and the
    reduced forward cone condition on successive differences. -/
theorem mem_forwardTube_iff_basepoint_and_reducedDiff [NeZero d] [NeZero n]
    (z : Fin n → Fin (d + 1) → ℂ) :
    z ∈ ForwardTube d n ↔
      InOpenForwardCone d (fun μ => (z 0 μ).im) ∧
      reducedDiffMap n d z ∈ ReducedForwardCone d n := by
  constructor
  · intro hz
    have hfull : diffCoordEquiv n d z ∈ ProductForwardCone d n := by
      simpa [forwardTube_eq_diffCoord_preimage (n := n) (d := d)] using hz
    refine ⟨?_, ?_⟩
    · simpa [ProductForwardCone, diffCoordEquiv_apply] using hfull 0
    · intro j
      simpa [ReducedForwardCone, reducedDiffMap_apply] using
        hfull ⟨j.val + 1, by omega⟩
  · rintro ⟨h0, hred⟩
    have hfull : diffCoordEquiv n d z ∈ ProductForwardCone d n := by
      intro k
      by_cases hk : k.val = 0
      · have hk0 : k = 0 := Fin.ext hk
        subst hk0
        simpa [diffCoordEquiv_apply]
          using h0
      · let j : Fin (n - 1) := ⟨k.val - 1, by omega⟩
        have hj : InOpenForwardCone d
            (fun μ => (reducedDiffMap n d z j μ).im) := hred j
        have hk_eq : k = ⟨j.val + 1, by omega⟩ := by
          ext
          simp [j]
          omega
        rw [hk_eq]
        simpa [reducedDiffMap_apply] using hj
    simpa [forwardTube_eq_diffCoord_preimage (n := n) (d := d)] using hfull

theorem reducedForwardTube_eq_reducedForwardCone (d n : ℕ) :
    ReducedForwardTube d n = ReducedForwardCone d n := rfl

private lemma reducedDiffSection_reducedDiffMap_val (n d : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) (m : ℕ) (hm : m < n) (μ : Fin (d + 1)) :
    let fin0 : Fin n := ⟨0, by omega⟩
    reducedDiffSection n d (reducedDiffMap n d z) ⟨m, hm⟩ μ =
      z ⟨m, hm⟩ μ - z fin0 μ := by
  induction m with
  | zero =>
      have hsymm := diffCoordEquiv_symm_apply n d
        (prependZeroDiff n d (reducedDiffMap n d z)) ⟨0, hm⟩ μ
      simp only [reducedDiffSection, ContinuousLinearMap.comp_apply] at hsymm ⊢
      change (diffCoordEquiv n d).symm ((prependZeroDiff n d) (reducedDiffMap n d z))
        ⟨0, hm⟩ μ = z ⟨0, hm⟩ μ - z ⟨0, by omega⟩ μ
      rw [hsymm]
      simp [prependZeroDiff]
  | succ m ih =>
      have hsymm := diffCoordEquiv_symm_apply n d
        (prependZeroDiff n d (reducedDiffMap n d z)) ⟨m + 1, hm⟩ μ
      simp only [reducedDiffSection, ContinuousLinearMap.comp_apply] at hsymm ⊢
      change (diffCoordEquiv n d).symm ((prependZeroDiff n d) (reducedDiffMap n d z))
        ⟨m + 1, hm⟩ μ = z ⟨m + 1, hm⟩ μ - z ⟨0, by omega⟩ μ
      rw [hsymm]
      rw [Fin.sum_univ_castSucc]
      simp_rw [Fin.val_castSucc]
      have hprev := diffCoordEquiv_symm_apply n d
        (prependZeroDiff n d (reducedDiffMap n d z)) ⟨m, by omega⟩ μ
      have hih :
          (diffCoordEquiv n d).symm ((prependZeroDiff n d) (reducedDiffMap n d z))
            ⟨m, by omega⟩ μ =
            z ⟨m, by omega⟩ μ - z ⟨0, by omega⟩ μ := by
        simpa [reducedDiffSection, ContinuousLinearMap.comp_apply] using ih (by omega)
      rw [← hprev]
      rw [hih]
      have hlast :
          prependZeroDiff n d (reducedDiffMap n d z) ⟨m + 1, by omega⟩ μ =
            z ⟨m + 1, by omega⟩ μ - z ⟨m, by omega⟩ μ := by
        simp [prependZeroDiff, reducedDiffMap_eq_successive_differences]
      have hlast_last :
          prependZeroDiff n d (reducedDiffMap n d z) ⟨↑(Fin.last (m + 1)), by omega⟩ μ =
            z ⟨m + 1, by omega⟩ μ - z ⟨m, by omega⟩ μ := by
        simpa using hlast
      rw [hlast_last]
      ring

/-- Reconstructing from reduced differences normalizes the basepoint to zero,
    so `section(map z)` is `z` translated by `-z₀`. -/
theorem reducedDiffSection_reducedDiffMap_eq_sub_basepoint (n d : ℕ)
    [NeZero n] (z : Fin n → Fin (d + 1) → ℂ) :
    reducedDiffSection n d (reducedDiffMap n d z) =
      fun k μ => z k μ - z 0 μ := by
  ext k μ
  simpa using reducedDiffSection_reducedDiffMap_val n d z k.val k.isLt μ

/-- Permute absolute configurations by reindexing the particle slot. -/
noncomputable def permuteConfigCLM (π : Equiv.Perm (Fin n)) :
    (Fin n → Fin (d + 1) → ℂ) →L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi fun k =>
    ContinuousLinearMap.proj (R := ℂ) (ι := Fin n)
      (φ := fun _ => Fin (d + 1) → ℂ) (π k)

@[simp] theorem permuteConfigCLM_apply (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) :
    permuteConfigCLM (d := d) π z k = z (π k) := rfl

/-- The permutation action induced on reduced difference coordinates, defined by
    permuting a zero-basepoint representative and then quotienting again. -/
noncomputable def permOnReducedDiff (π : Equiv.Perm (Fin n)) :
    (Fin (n - 1) → Fin (d + 1) → ℂ) →L[ℂ]
      (Fin (n - 1) → Fin (d + 1) → ℂ) :=
  (reducedDiffMap n d).comp
    ((permuteConfigCLM (d := d) π).comp (reducedDiffSection n d))

@[simp] theorem permOnReducedDiff_apply (π : Equiv.Perm (Fin n))
    (η : Fin (n - 1) → Fin (d + 1) → ℂ) :
    permOnReducedDiff (d := d) (n := n) π η =
      reducedDiffMap n d (fun k => reducedDiffSection n d η (π k)) := rfl

@[simp] theorem permOnReducedDiff_one (η : Fin (n - 1) → Fin (d + 1) → ℂ) :
    permOnReducedDiff (d := d) (n := n) (1 : Equiv.Perm (Fin n)) η = η := by
  simp [permOnReducedDiff, permuteConfigCLM, reducedDiffMap_section]

/-- On reduced differences coming from an absolute configuration, the induced
    permutation action matches absolute reindexing. -/
theorem permOnReducedDiff_reducedDiffMap (π : Equiv.Perm (Fin n))
    [NeZero n]
    (z : Fin n → Fin (d + 1) → ℂ) :
    permOnReducedDiff (d := d) (n := n) π (reducedDiffMap n d z) =
      reducedDiffMap n d (fun k => z (π k)) := by
  have hsec :
      (fun k => reducedDiffSection n d (reducedDiffMap n d z) (π k)) =
        (fun k μ => z (π k) μ - z 0 μ) := by
    ext k μ
    simp [reducedDiffSection_reducedDiffMap_eq_sub_basepoint]
  rw [permOnReducedDiff_apply, hsec]
  have hshift := reducedDiffMap_translate_uniform_eq (n := n) (d := d)
    (fun k => z (π k)) (fun μ => -z 0 μ)
  have hminus :
      (fun k μ => z (π k) μ - z 0 μ) =
        (fun k μ => z (π k) μ + (-z 0 μ)) := by
    ext k μ
    ring
  rw [hminus]
  exact hshift

/-- The induced reduced permutation action composes according to the absolute
    reindexing action. -/
theorem permOnReducedDiff_mul (π₁ π₂ : Equiv.Perm (Fin n))
    [NeZero n]
    (η : Fin (n - 1) → Fin (d + 1) → ℂ) :
    permOnReducedDiff (d := d) (n := n) (π₁ * π₂) η =
      permOnReducedDiff (d := d) (n := n) π₂
        (permOnReducedDiff (d := d) (n := n) π₁ η) := by
  have hπ1 :
      permOnReducedDiff (d := d) (n := n) π₁ η =
        reducedDiffMap n d (fun k => reducedDiffSection n d η (π₁ k)) := by
    calc
      permOnReducedDiff (d := d) (n := n) π₁ η
          = permOnReducedDiff (d := d) (n := n) π₁
              (reducedDiffMap n d (reducedDiffSection n d η)) := by
                rw [reducedDiffMap_section (n := n) (d := d) η]
      _ = reducedDiffMap n d (fun k => reducedDiffSection n d η (π₁ k)) := by
            exact
              permOnReducedDiff_reducedDiffMap (d := d) (n := n) π₁
                (reducedDiffSection n d η)
  calc
    permOnReducedDiff (d := d) (n := n) (π₁ * π₂) η
        = reducedDiffMap n d (fun k => reducedDiffSection n d η ((π₁ * π₂) k)) := by
            calc
              permOnReducedDiff (d := d) (n := n) (π₁ * π₂) η
                  = permOnReducedDiff (d := d) (n := n) (π₁ * π₂)
                      (reducedDiffMap n d (reducedDiffSection n d η)) := by
                        rw [reducedDiffMap_section (n := n) (d := d) η]
              _ = reducedDiffMap n d
                    (fun k => reducedDiffSection n d η ((π₁ * π₂) k)) := by
                    exact
                      permOnReducedDiff_reducedDiffMap (d := d) (n := n) (π₁ * π₂)
                        (reducedDiffSection n d η)
    _ = reducedDiffMap n d (fun k => reducedDiffSection n d η (π₁ (π₂ k))) := rfl
    _ = permOnReducedDiff (d := d) (n := n) π₂
          (reducedDiffMap n d (fun k => reducedDiffSection n d η (π₁ k))) := by
            symm
            simpa using
              permOnReducedDiff_reducedDiffMap (d := d) (n := n) π₂
                (fun k => reducedDiffSection n d η (π₁ k))
    _ = permOnReducedDiff (d := d) (n := n) π₂
          (permOnReducedDiff (d := d) (n := n) π₁ η) := by
            rw [hπ1]

/-- Reduced permuted forward tube: the reduced difference configuration becomes
    forward after applying the induced permutation action. -/
def ReducedPermutedForwardTube (d n : ℕ) (π : Equiv.Perm (Fin n)) :
    Set (Fin (n - 1) → Fin (d + 1) → ℂ) :=
  {η | permOnReducedDiff (d := d) (n := n) π η ∈ ReducedForwardTube d n}

@[simp] theorem mem_reducedPermutedForwardTube (π : Equiv.Perm (Fin n))
    (η : Fin (n - 1) → Fin (d + 1) → ℂ) :
    η ∈ ReducedPermutedForwardTube d n π ↔
      permOnReducedDiff (d := d) (n := n) π η ∈ ReducedForwardTube d n := by
  rfl

/-- Absolute permuted forward-tube points descend to the reduced permuted
    forward tube. -/
theorem reducedDiffMap_mem_reducedPermutedForwardTube_of_mem_permutedForwardTube
    [NeZero d] [NeZero n] (π : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ PermutedForwardTube d n π) :
    reducedDiffMap n d z ∈ ReducedPermutedForwardTube d n π := by
  rw [mem_reducedPermutedForwardTube, permOnReducedDiff_reducedDiffMap]
  have hfull : diffCoordEquiv n d (fun k => z (π k)) ∈ ProductForwardCone d n := by
    have hz' : (fun k => z (π k)) ∈ ForwardTube d n := by
      simpa [PermutedForwardTube] using hz
    simpa [forwardTube_eq_diffCoord_preimage (n := n) (d := d)] using hz'
  show reducedDiffMap n d (fun k => z (π k)) ∈ ReducedForwardTube d n
  intro j
  simpa [ReducedForwardTube, ReducedForwardCone, reducedDiffMap_apply] using
    hfull ⟨j.val + 1, by omega⟩

/-- Real reduced difference map on `n` spacetime points:
    `δ_j = x_{j+1} - x_j` for `j = 0, ..., n-2`. -/
def reducedDiffMapReal (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (n - 1) → Fin (d + 1) → ℝ) where
  toFun := fun x j μ => x ⟨j.val + 1, by omega⟩ μ - x ⟨j.val, by omega⟩ μ
  map_add' x y := by
    ext j μ
    simp
    ring
  map_smul' a x := by
    ext j μ
    simp [smul_eq_mul]
    ring

/-- Real full difference coordinates:
    `ξ₀ = x₀`, `ξ_k = x_k - x_{k-1}` for `k > 0`. -/
def realDiffCoordFun (n d : ℕ) (x : Fin n → Fin (d + 1) → ℝ) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ =>
    if h : k.val = 0 then x k μ
    else x k μ - x ⟨k.val - 1, by omega⟩ μ

/-- Real partial sums, inverse to `realDiffCoordFun`. -/
def realPartialSumFun (n d : ℕ) (ξ : Fin n → Fin (d + 1) → ℝ) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ => ∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ

private lemma realPartialSum_diffCoord_val (n d : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) (m : ℕ) (hm : m < n) (μ : Fin (d + 1)) :
    (∑ j : Fin (m + 1), realDiffCoordFun n d x ⟨j.val, by omega⟩ μ) =
      x ⟨m, hm⟩ μ := by
  induction m with
  | zero =>
      simp [realDiffCoordFun]
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp_rw [Fin.val_castSucc]
      rw [ih (by omega)]
      simp only [Fin.val_last, realDiffCoordFun,
        show ¬ (m + 1 = 0) from Nat.succ_ne_zero m, ↓reduceDIte]
      have : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ :=
        Fin.ext (show m + 1 - 1 = m by omega)
      rw [this]
      ring

/-- Partial sums invert real difference coordinates. -/
theorem realPartialSum_diffCoord (n d : ℕ) (x : Fin n → Fin (d + 1) → ℝ) :
    realPartialSumFun n d (realDiffCoordFun n d x) = x := by
  funext k μ
  exact realPartialSum_diffCoord_val n d x k.val k.isLt μ

/-- Real difference coordinates invert real partial sums. -/
theorem realDiffCoord_partialSum (n d : ℕ) (ξ : Fin n → Fin (d + 1) → ℝ) :
    realDiffCoordFun n d (realPartialSumFun n d ξ) = ξ := by
  have h_left_inv : ∀ x, realPartialSumFun n d (realDiffCoordFun n d x) = x :=
    realPartialSum_diffCoord n d
  have h_inj : Function.Injective
      ({ toFun := realDiffCoordFun n d
         map_add' := by
           intro x y
           funext k μ
           simp only [realDiffCoordFun, Pi.add_apply]
           by_cases hk : k.val = 0 <;> simp [hk, sub_add_sub_comm]
         map_smul' := by
           intro a x
           funext k μ
           simp only [realDiffCoordFun, Pi.smul_apply, RingHom.id_apply]
           by_cases hk : k.val = 0 <;> simp [hk, mul_sub] } :
        (Fin n → Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin n → Fin (d + 1) → ℝ)) := by
    intro x y hxy
    have : realDiffCoordFun n d x = realDiffCoordFun n d y := hxy
    calc
      x = realPartialSumFun n d (realDiffCoordFun n d x) := (h_left_inv x).symm
      _ = realPartialSumFun n d (realDiffCoordFun n d y) := by rw [this]
      _ = y := h_left_inv y
  have h_surj :
      Function.Surjective
        ({ toFun := realDiffCoordFun n d
           map_add' := by
             intro x y
             funext k μ
             simp only [realDiffCoordFun, Pi.add_apply]
             by_cases hk : k.val = 0 <;> simp [hk, sub_add_sub_comm]
           map_smul' := by
             intro a x
             funext k μ
             simp only [realDiffCoordFun, Pi.smul_apply, RingHom.id_apply]
             by_cases hk : k.val = 0 <;> simp [hk, mul_sub] } :
          (Fin n → Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin n → Fin (d + 1) → ℝ)) :=
    LinearMap.injective_iff_surjective.mp h_inj
  obtain ⟨x, rfl⟩ := h_surj ξ
  exact congrArg (realDiffCoordFun n d) (h_left_inv x)

/-- Real full difference coordinates as a continuous linear equivalence. -/
def realDiffCoordLinearEquiv (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin n → Fin (d + 1) → ℝ) where
  toLinearMap :=
    { toFun := realDiffCoordFun n d
      map_add' := by
        intro x y
        funext k μ
        simp only [realDiffCoordFun, Pi.add_apply]
        by_cases hk : k.val = 0 <;> simp [hk, sub_add_sub_comm]
      map_smul' := by
        intro a x
        funext k μ
        simp only [realDiffCoordFun, Pi.smul_apply, RingHom.id_apply]
        by_cases hk : k.val = 0 <;> simp [hk, mul_sub] }
  invFun := realPartialSumFun n d
  left_inv := realPartialSum_diffCoord n d
  right_inv := realDiffCoord_partialSum n d

/-- Continuous real full difference coordinates. -/
def realDiffCoordCLE (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℝ) ≃L[ℝ] (Fin n → Fin (d + 1) → ℝ) :=
  (realDiffCoordLinearEquiv n d).toContinuousLinearEquiv

@[simp] theorem realDiffCoordCLE_apply (n d : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) (k : Fin n) (μ : Fin (d + 1)) :
    realDiffCoordCLE n d x k μ =
      if _h : k.val = 0 then x k μ
      else x k μ - x ⟨k.val - 1, by omega⟩ μ := by
  rfl

@[simp] theorem realDiffCoordCLE_symm_apply (n d : ℕ)
    (ξ : Fin n → Fin (d + 1) → ℝ) (k : Fin n) (μ : Fin (d + 1)) :
    (realDiffCoordCLE n d).symm ξ k μ =
      ∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ := by
  rfl

/-- Continuous real reduced difference map on `n` spacetime points. -/
noncomputable def reducedDiffMapRealCLM (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℝ) →L[ℝ] (Fin (n - 1) → Fin (d + 1) → ℝ) :=
  (reducedDiffMapReal n d).toContinuousLinearMap

@[simp] theorem reducedDiffMapReal_apply (n d : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) (j : Fin (n - 1)) (μ : Fin (d + 1)) :
    reducedDiffMapReal n d x j μ =
      x ⟨j.val + 1, by omega⟩ μ - x ⟨j.val, by omega⟩ μ := rfl

/-- Uniform real translations are invisible in reduced real difference coordinates. -/
theorem reducedDiffMapReal_translate_uniform_eq (n d : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) (a : Fin (d + 1) → ℝ) :
    reducedDiffMapReal n d (fun k μ => x k μ + a μ) = reducedDiffMapReal n d x := by
  ext j μ
  simp [reducedDiffMapReal]

/-- Pull back a function on reduced complex difference coordinates to absolute
    coordinates. -/
def pullbackReducedComplex (n d : ℕ) {α : Sort*}
    (G : (Fin (n - 1) → Fin (d + 1) → ℂ) → α) :
    (Fin n → Fin (d + 1) → ℂ) → α :=
  fun z => G (reducedDiffMap n d z)

/-- Any function pulled back from reduced complex difference coordinates is
    invariant under uniform complex translations. -/
theorem pullbackReducedComplex_translate_uniform (n d : ℕ) {α : Sort*}
    (G : (Fin (n - 1) → Fin (d + 1) → ℂ) → α)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ) :
    pullbackReducedComplex n d G (fun k μ => z k μ + c μ) =
      pullbackReducedComplex n d G z := by
  simp [pullbackReducedComplex, reducedDiffMap_translate_uniform_eq]

/-- Pull back a function on reduced real difference coordinates to absolute real
    coordinates. -/
def pullbackReducedReal (n d : ℕ) {α : Sort*}
    (G : (Fin (n - 1) → Fin (d + 1) → ℝ) → α) :
    (Fin n → Fin (d + 1) → ℝ) → α :=
  fun x => G (reducedDiffMapReal n d x)

/-- Any function pulled back from reduced real difference coordinates is
    invariant under uniform real translations. -/
theorem pullbackReducedReal_translate_uniform (n d : ℕ) {α : Sort*}
    (G : (Fin (n - 1) → Fin (d + 1) → ℝ) → α)
    (x : Fin n → Fin (d + 1) → ℝ) (a : Fin (d + 1) → ℝ) :
    pullbackReducedReal n d G (fun k μ => x k μ + a μ) =
      pullbackReducedReal n d G x := by
  simp [pullbackReducedReal, reducedDiffMapReal_translate_uniform_eq]

end BHW
