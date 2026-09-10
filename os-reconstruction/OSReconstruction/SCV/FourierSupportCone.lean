/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.DualCone
import OSReconstruction.SCV.LaplaceSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier









open scoped Classical ComplexConjugate BigOperators
open MeasureTheory SchwartzMap Complex
noncomputable section

variable {m : ℕ}



/-- The dual cone of a set S ⊆ ℝ^m using the standard dot product on `Fin m → ℝ`.
    This is the flat-type version of `DualConeEucl`, compatible with `SchwartzMap`
    and `fourierTransformCLM` which use `Fin m → ℝ` (not `EuclideanSpace`). -/
def DualConeFlat (S : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {ξ | ∀ y ∈ S, (0 : ℝ) ≤ ∑ i, y i * ξ i}

theorem mem_dualConeFlat {S : Set (Fin m → ℝ)} {ξ : Fin m → ℝ} :
    ξ ∈ DualConeFlat S ↔ ∀ y ∈ S, (0 : ℝ) ≤ ∑ i, y i * ξ i :=
  Iff.rfl



/-- A tempered distribution `T` has Fourier support in a closed set `S` if
    `T` vanishes on all Schwartz test functions whose support is disjoint from `S`.

    More precisely: for every φ ∈ S(ℝ^m) with `supp(φ) ∩ S = ∅`, we have `T(φ) = 0`.

    This is the "frequency-side" version: `T` is the Fourier transform of the
    original distribution, and `S` is the support in frequency space.
    The connection to `fourierTransformCLM` is made in individual theorems,
    not baked into the definition, to avoid `InnerProductSpace` requirements
    on `Fin m → ℝ`. -/
def HasFourierSupportIn (S : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
    (∀ x ∈ Function.support (φ : (Fin m → ℝ) → ℂ), x ∉ S) →
    T φ = 0

/-- A tempered distribution `T` has Fourier support in the dual cone `C*` of a set `S`. -/
def HasFourierSupportInDualCone (S : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  HasFourierSupportIn (DualConeFlat S) T



/-- If ξ is not in the dual cone of S, there exists y ∈ S with negative pairing.
    This is just the negation of the universal quantifier in the definition. -/
theorem exists_neg_pairing_of_not_mem_dualConeFlat {S : Set (Fin m → ℝ)} {ξ : Fin m → ℝ}
    (hξ : ξ ∉ DualConeFlat S) :
    ∃ y ∈ S, ∑ i, y i * ξ i < 0 := by
  simp only [DualConeFlat, Set.mem_setOf_eq, not_forall, not_le] at hξ
  obtain ⟨y, hy, hlt⟩ := hξ
  exact ⟨y, hy, hlt⟩



/-- If T has Fourier support in S, then T agrees on test functions that coincide on S. -/
theorem hasFourierSupportIn_eqOn {S : Set (Fin m → ℝ)}
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hT : HasFourierSupportIn S T)
    {φ ψ : SchwartzMap (Fin m → ℝ) ℂ}
    (h_eq : ∀ x ∈ S, (φ : (Fin m → ℝ) → ℂ) x = (ψ : (Fin m → ℝ) → ℂ) x) :
    T φ = T ψ := by
  have hsub : T (φ - ψ) = 0 := by
    apply hT
    intro x hx hxS
    simp only [SchwartzMap.sub_apply, Function.mem_support, ne_eq] at hx
    exact hx (sub_eq_zero.mpr (h_eq x hxS))
  exact sub_eq_zero.mp (by rw [← map_sub]; exact hsub)





end
