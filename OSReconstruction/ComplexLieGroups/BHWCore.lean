/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.PathConnected
import OSReconstruction.ComplexLieGroups.GeodesicConvexity

/-!
# BHW Core Infrastructure

This file contains shared geometric infrastructure for the BHW development:
the forward tube, complex Lorentz action, extended tube, and generic extension
helpers that only require complex-Lorentz invariance on the forward tube.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHWCore

variable {d n : ℕ}

/-- The forward tube T_n: successive imaginary-part differences lie in V⁺. -/
def ForwardTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∀ k : Fin n,
    let prev : Fin (d + 1) → ℂ := if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
    let η : Fin (d + 1) → ℝ := fun μ => (z k μ - prev μ).im
    BHW.InOpenForwardCone d η }

/-- The action of a complex Lorentz transformation on configurations. -/
def complexLorentzAction (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ => ∑ ν, Λ.val μ ν * z k ν

/-- Compatibility with multiplication. -/
theorem complexLorentzAction_mul (Λ₁ Λ₂ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (Λ₁ * Λ₂) z =
    complexLorentzAction Λ₁ (complexLorentzAction Λ₂ z) := by
  ext k μ
  simp only [complexLorentzAction, ComplexLorentzGroup.mul_val, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext ν
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

/-- Identity action. -/
theorem complexLorentzAction_one (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (1 : ComplexLorentzGroup d) z = z := by
  ext k μ
  simp only [complexLorentzAction,
    show (1 : ComplexLorentzGroup d).val = (1 : Matrix _ _ ℂ) from rfl,
    Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Inverse action. -/
theorem complexLorentzAction_inv (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ⁻¹ (complexLorentzAction Λ z) = z := by
  rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one]

/-- Forward tube openness. -/
theorem isOpen_forwardTube : IsOpen (ForwardTube d n) := by
  simp only [ForwardTube, BHW.InOpenForwardCone, Set.setOf_forall]
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
  · exact isOpen_lt
      (continuous_finset_sum _ fun μ _ => (continuous_const.mul ((hcont μ).pow 2)))
      continuous_const

/-- Continuity in first argument (Λ). -/
theorem continuous_complexLorentzAction_fst (z : Fin n → Fin (d + 1) → ℂ) :
    Continuous (fun Λ : ComplexLorentzGroup d => complexLorentzAction Λ z) := by
  apply continuous_pi; intro k
  apply continuous_pi; intro μ
  simp only [complexLorentzAction]
  exact continuous_finset_sum Finset.univ
    (fun ν _ => (ComplexLorentzGroup.continuous_entry μ ν).mul continuous_const)

/-- Continuity in second argument (z). -/
theorem continuous_complexLorentzAction_snd (Λ : ComplexLorentzGroup d) :
    Continuous (fun z : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ z) := by
  apply continuous_pi; intro k
  apply continuous_pi; intro μ
  simp only [complexLorentzAction]
  exact continuous_finset_sum Finset.univ
    (fun ν _ => continuous_const.mul ((continuous_apply ν).comp (continuous_apply k)))

/-- Differentiability in second argument (z). -/
theorem differentiable_complexLorentzAction_snd (Λ : ComplexLorentzGroup d) :
    Differentiable ℂ (fun z : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ z) := by
  apply differentiable_pi.mpr; intro k
  apply differentiable_pi.mpr; intro μ
  simp only [complexLorentzAction]
  apply Differentiable.fun_sum; intro ν _
  apply Differentiable.const_mul
  have h1 : Differentiable ℂ (fun z : Fin n → Fin (d + 1) → ℂ => z k) := differentiable_apply k
  exact (differentiable_apply ν).comp h1

/-- Extended tube: complex Lorentz orbit of FT. -/
def ExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ (Λ : ComplexLorentzGroup d),
    { z | ∃ w ∈ ForwardTube d n, z = complexLorentzAction Λ w }

/-- Permuted forward tube. -/
def PermutedForwardTube (d n : ℕ) (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | (fun k => z (π k)) ∈ ForwardTube d n }

/-- Permuted extended tube. -/
def PermutedExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ π : Equiv.Perm (Fin n),
    { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧
      z = complexLorentzAction Λ w }

/-- FT ⊆ ET. -/
theorem forwardTube_subset_extendedTube :
    ForwardTube d n ⊆ ExtendedTube d n := by
  intro z hz
  refine Set.mem_iUnion.mpr ⟨1, z, hz, ?_⟩
  simpa using (complexLorentzAction_one z).symm

/-- ET ⊆ PET. -/
theorem extendedTube_subset_permutedExtendedTube :
    ExtendedTube d n ⊆ PermutedExtendedTube d n := by
  intro z hz
  obtain ⟨Λ, w, hw, hzw⟩ := Set.mem_iUnion.mp hz
  refine Set.mem_iUnion.mpr ⟨Equiv.refl _, Λ, w, ?_, hzw⟩
  simpa [PermutedForwardTube] using hw

/-- FT ⊆ PET. -/
theorem forwardTube_subset_permutedExtendedTube :
    ForwardTube d n ⊆ PermutedExtendedTube d n :=
  fun _ hz => extendedTube_subset_permutedExtendedTube (forwardTube_subset_extendedTube hz)

/-- z ↦ Λ·z is an open map (homeomorphism). -/
theorem complexLorentzAction_isOpenMap (Λ : ComplexLorentzGroup d) :
    IsOpenMap (fun z : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ z) :=
  IsOpenMap.of_inverse
    (continuous_complexLorentzAction_snd Λ⁻¹)
    (fun z => by rw [← complexLorentzAction_mul, mul_inv_cancel, complexLorentzAction_one])
    (fun z => by rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one])

/-- Generic extension: choose a forward-tube preimage if it exists. -/
def extendF (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if h : ∃ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ ∃ (Λ : ComplexLorentzGroup d), z = complexLorentzAction Λ w
    then F h.choose
    else 0

/-- On FT, `extendF` agrees with `F` under complex Lorentz invariance on FT. -/
theorem extendF_eq_on_forwardTube (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_cinv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    extendF F z = F z := by
  simp only [extendF]
  have hex : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ : ComplexLorentzGroup d), z = complexLorentzAction Λ w :=
    ⟨z, hz, 1, (complexLorentzAction_one z).symm⟩
  rw [dif_pos hex]
  have hspec := hex.choose_spec
  have hw : hex.choose ∈ ForwardTube d n := hspec.1
  obtain ⟨Λ, hzΛw⟩ := hspec.2
  have hΛw : complexLorentzAction Λ hex.choose ∈ ForwardTube d n := hzΛw ▸ hz
  have key := hF_cinv Λ hex.choose hw hΛw
  exact key.symm.trans (congr_arg F hzΛw.symm)

/-- Any two FT-preimages of the same ET point give equal F-values under FT invariance. -/
theorem extendF_preimage_eq (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_cinv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z)
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ} (hw₁ : w₁ ∈ ForwardTube d n) (hw₂ : w₂ ∈ ForwardTube d n)
    {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : complexLorentzAction Λ₁ w₁ = complexLorentzAction Λ₂ w₂) :
    F w₁ = F w₂ := by
  have hrel : complexLorentzAction (Λ₂⁻¹ * Λ₁) w₁ = w₂ := by
    have := congr_arg (complexLorentzAction Λ₂⁻¹) h
    rwa [← complexLorentzAction_mul, complexLorentzAction_inv] at this
  have := hF_cinv (Λ₂⁻¹ * Λ₁) w₁ hw₁ (hrel ▸ hw₂)
  rw [hrel] at this
  exact this.symm

end BHWCore
