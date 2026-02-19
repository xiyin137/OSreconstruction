/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import OSReconstruction.Wightman.NuclearSpaces.NuclearSpace
import OSReconstruction.Wightman.NuclearSpaces.GaussianFieldBridge

/-!
# Schwartz Space is Nuclear

This file proves that the Schwartz space S(ℝⁿ) is a nuclear space, using two
complementary characterizations:

1. **Pietsch (OSReconstruction.NuclearSpace)**: nuclear dominance by seminorms.
   The `NuclearFrechet` presentation and `SchwartzMap.instNuclearSpace` use this.

2. **Dynin-Mityagin (GaussianField.NuclearSpace)**: Schauder basis with rapid decay.
   This is imported from the `gaussian-field` library via `GaussianFieldBridge`.
   The sorry-free Hermite function infrastructure lives there.

## Main Results

* `SchwartzMap.nuclearFrechet` - Schwartz space presented as a nuclear Fréchet space
* `SchwartzMap.instNuclearSpace` - S(ℝⁿ, ℝ) is nuclear (Pietsch, depends on sorry)
* `GaussianField.NuclearSpace (SchwartzMap D ℝ)` - S(D, ℝ) is nuclear (Dynin-Mityagin,
  sorry-free from gaussian-field, available via GaussianFieldBridge import)

## Hermite Function Infrastructure

The Hermite function definitions and theorems in this file are **superseded** by the
sorry-free versions from gaussian-field. Use the `gf`-prefixed re-exports from
`GaussianFieldBridge`:

* `gfHermiteFunction` — Hermite function definition
* `gfHermiteFunction_schwartz` — Schwartz membership (sorry-free)
* `gfHermiteFunction_orthonormal` — L² orthonormality (sorry-free)
* `gfHermiteFunction_seminorm_bound` — seminorm growth bounds (sorry-free)
* `gfHermiteFunction_complete` — completeness in L² (sorry-free)

## References

* Gel'fand-Vilenkin, "Generalized Functions IV" (1964), Ch. I, §3
* Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem V.13
* Trèves, "Topological Vector Spaces" (1967), Ch. 51
-/

noncomputable section

open scoped SchwartzMap
open MeasureTheory

/-! ### Schwartz Space Seminorms -/

/-- The standard Schwartz seminorm indexed by (k, l) ∈ ℕ × ℕ:
    p_{k,l}(f) = sup_x ‖x‖^k · ‖iteratedFDeriv ℝ l f x‖

    This is a continuous seminorm on S(ℝⁿ, F). -/
def SchwartzMap.schwartzSeminorm (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k l : ℕ) :
    Seminorm ℝ (𝓢(E, F)) :=
  SchwartzMap.seminorm ℝ k l

/-! ### Combined Schwartz Seminorm for Fréchet Presentation -/

private abbrev schwartzPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (N + 1) ×ˢ Finset.range (N + 1)

/-- The combined Schwartz seminorm: sum of all individual seminorms p_{k,l} for k,l ≤ N.
    This family is monotone in N (adding more non-negative terms) and generates the
    same topology as the full family {p_{k,l}}_{k,l ∈ ℕ}.

    Note: Mathlib's individual Schwartz seminorms p_{k,l}(f) = sup_x ‖x‖^k · ‖D^l f(x)‖
    are NOT monotone in k (since ‖x‖^k is not monotone for ‖x‖ < 1), so diagonal
    seminorms p_{n,n} don't form an increasing family. Using sums over all pairs
    up to (N,N) gives a genuinely increasing family that generates the same topology. -/
private def schwartzCombinedSeminorm (n : ℕ) (N : ℕ) :
    Seminorm ℝ (𝓢(EuclideanSpace ℝ (Fin n), ℝ)) :=
  (schwartzPairs N).sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2)

/-- Evaluating a combined seminorm at a point equals the real number sum. -/
private theorem schwartzCombinedSeminorm_apply (n N : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) :
    schwartzCombinedSeminorm n N f =
    (schwartzPairs N).sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2 f) := by
  unfold schwartzCombinedSeminorm
  -- Prove by induction on the finset using the AddMonoidHom property
  have key : ∀ (S : Finset (ℕ × ℕ)),
      (S.sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2)) f =
      S.sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2 f) := by
    intro S
    induction S using Finset.cons_induction with
    | empty => simp [Seminorm.zero_apply]
    | cons a s has ih =>
      rw [Finset.sum_cons, Finset.sum_cons, Seminorm.add_apply, ih]
  exact key _

/-- An individual seminorm p_{k,l} is bounded by the combined seminorm for N ≥ max(k,l). -/
private theorem le_schwartzCombinedSeminorm (n : ℕ) {k l N : ℕ}
    (hk : k ≤ N) (hl : l ≤ N) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) :
    SchwartzMap.seminorm ℝ k l f ≤ schwartzCombinedSeminorm n N f := by
  rw [schwartzCombinedSeminorm_apply]
  have hmem : (k, l) ∈ schwartzPairs N :=
    Finset.mk_mem_product (Finset.mem_range.mpr (by omega))
      (Finset.mem_range.mpr (by omega))
  calc SchwartzMap.seminorm ℝ k l f
      = (fun kl : ℕ × ℕ => SchwartzMap.seminorm ℝ kl.1 kl.2 f) (k, l) := rfl
    _ ≤ (schwartzPairs N).sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2 f) :=
        Finset.single_le_sum
          (fun (kl : ℕ × ℕ) _ => apply_nonneg (SchwartzMap.seminorm ℝ kl.1 kl.2) f) hmem

/-! ### Nuclear Fréchet Presentation -/

/-- The Schwartz space S(ℝⁿ, ℝ) has a nuclear Fréchet presentation.
    We use combined seminorms q_N = ∑_{k,l ≤ N} p_{k,l} which form a monotone
    family generating the Schwartz topology. -/
def SchwartzMap.nuclearFrechet (n : ℕ) : NuclearFrechet where
  Space := 𝓢(EuclideanSpace ℝ (Fin n), ℝ)
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instTopologicalSpace := inferInstance
  instIsTopologicalAddGroup := inferInstance
  seminorms := schwartzCombinedSeminorm n
  seminorms_mono := by
    intro N f
    rw [schwartzCombinedSeminorm_apply, schwartzCombinedSeminorm_apply]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.product_subset_product
        (Finset.range_mono (by omega)) (Finset.range_mono (by omega))
    · intro kl _ _; exact apply_nonneg _ _
  separating := by
    intro f hf
    have h00 : SchwartzMap.seminorm ℝ 0 0 f = 0 := by
      have hN0 := hf 0
      have hle := le_schwartzCombinedSeminorm n (Nat.le_refl 0) (Nat.le_refl 0) f
      linarith [apply_nonneg (SchwartzMap.seminorm ℝ 0 0) f]
    ext x
    have hbound := SchwartzMap.norm_le_seminorm ℝ f x
    simp only [SchwartzMap.coe_zero, Pi.zero_apply]
    exact norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg _))
  continuous_seminorms := by
    intro N
    show Continuous (fun x => (schwartzCombinedSeminorm n N) x)
    have hfun : (fun x => (schwartzCombinedSeminorm n N) x) =
        (fun x => (schwartzPairs N).sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2 x)) := by
      ext x; exact schwartzCombinedSeminorm_apply n N x
    rw [hfun]
    exact continuous_finset_sum _ fun kl _ =>
      (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin n)) ℝ).continuous_seminorm kl
  seminorms_generating := by
    intro p hp
    obtain ⟨s, C, hC, hle⟩ := Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin n)) ℝ) p hp
    by_cases hs : s.Nonempty
    · let N := s.sup' hs (fun kl => max kl.1 kl.2)
      refine ⟨N, (C : ℝ), ?_, ?_⟩
      · exact NNReal.coe_pos.mpr hC.bot_lt
      · intro x
        have hCnn := NNReal.coe_nonneg C
        set q := schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin n)) ℝ with hq_def
        -- Step 1: s.sup q ≤ ∑ i ∈ s, q i (Seminorm level)
        have hsup_le_sum : s.sup q ≤ ∑ i ∈ s, q i :=
          Seminorm.finset_sup_le_sum q s
        -- Step 2: ∑ i ∈ s, q i ≤ schwartzCombinedSeminorm n N (Seminorm level)
        have hsum_le_combined : (∑ i ∈ s, q i) ≤ schwartzCombinedSeminorm n N := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ⟨k, l⟩ hkl
            simp only [schwartzPairs, Finset.mem_product, Finset.mem_range]
            have hmax := Finset.le_sup' (f := fun kl : ℕ × ℕ => max kl.1 kl.2) hkl
            constructor <;> omega
          · intro kl _ _; exact bot_le
        -- Step 3: Combine pointwise
        have h23 : (s.sup q) x ≤ schwartzCombinedSeminorm n N x :=
          le_trans (Seminorm.le_def.mp hsup_le_sum x) (Seminorm.le_def.mp hsum_le_combined x)
        calc p x ≤ (C • s.sup q) x := hle x
          _ = C * (s.sup q) x := by simp [NNReal.smul_def]
          _ ≤ C * schwartzCombinedSeminorm n N x :=
              mul_le_mul_of_nonneg_left h23 hCnn
    · refine ⟨0, 1, one_pos, ?_⟩
      intro x
      have : p x ≤ (C • s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin n)) ℝ)) x :=
        hle x
      simp [Finset.not_nonempty_iff_eq_empty.mp hs] at this
      linarith [apply_nonneg (schwartzCombinedSeminorm n 0) x]
  nuclear_step := by
    intro k
    -- The nuclear step uses the Hermite function expansion.
    -- For any Schwartz function f, f = Σ_m ⟨f, h_m⟩ h_m in L²
    -- The Hermite coefficients satisfy |⟨f, h_m⟩| ≤ C · p_{k+N,k+N}(f) · m^{-N}
    -- for any N, where C depends on N and n.
    -- Choosing N large enough (N > n/2 + 1) makes the nuclear trace converge.
    --
    -- NOTE: The sorry-free proof of nuclearity exists in gaussian-field via
    -- GaussianField.NuclearSpace (the Dynin-Mityagin characterization).
    -- This Pietsch-style nuclear_step remains sorry'd pending the bridge
    -- between the two characterizations.
    sorry

/-! ### Schwartz Space is Nuclear -/

/-- **The Schwartz space S(ℝⁿ, ℝ) is a nuclear space (Pietsch characterization).**

    This follows from the nuclear Fréchet presentation: the Hermite function
    expansion provides the nuclear factorization at each level.

    **Note:** A sorry-free `GaussianField.NuclearSpace` instance for `SchwartzMap D ℝ`
    is available from the gaussian-field library (Dynin-Mityagin characterization).
    Import `GaussianFieldBridge` to use it. -/
theorem SchwartzMap.instNuclearSpace (n : ℕ) :
    NuclearSpace (𝓢(EuclideanSpace ℝ (Fin n), ℝ)) :=
  (SchwartzMap.nuclearFrechet n).toNuclearSpace

/-! ### Hermite Function Infrastructure

**NOTE:** The definitions and theorems below are superseded by sorry-free versions
from gaussian-field. Prefer the `gf`-prefixed re-exports from `GaussianFieldBridge`:
- `gfHermiteFunction` / `gfHermiteFunction_schwartz` / `gfHermiteFunction_orthonormal`
- `gfHermiteFunction_seminorm_bound` / `gfHermiteFunction_complete`

The definitions below use Mathlib's physicists' Hermite polynomials, while
gaussian-field uses probabilist Hermite polynomials. The two are related by
a √2 rescaling. -/

/-- The normalized Hermite functions form an orthonormal basis of L²(ℝ).
    h_m(x) = (2^m m! √π)^{-1/2} · H_m(x) · exp(-x²/2)
    where H_m is the m-th Hermite polynomial.

    Mathlib has `Polynomial.hermite m` (the physicists' Hermite polynomial).
    The Hermite *function* multiplies by the Gaussian weight.

    **Superseded** by `gfHermiteFunction` from gaussian-field. -/
def hermiteFunction (m : ℕ) : ℝ → ℝ :=
  fun x => ((Polynomial.hermite m).map (Int.castRingHom ℝ)).eval x *
    Real.exp (-x ^ 2 / 2) /
    Real.sqrt (2 ^ m * m.factorial * Real.sqrt Real.pi)

/-- Hermite functions are in the Schwartz space.
    **Superseded** by `gfHermiteFunction_schwartz` (sorry-free). -/
theorem hermiteFunction_schwartz (m : ℕ) :
    ∃ (f : 𝓢(ℝ, ℝ)), ∀ x, f x = hermiteFunction m x := by
  sorry

/-- Hermite functions are orthonormal in L²(ℝ).
    **Superseded** by `gfHermiteFunction_orthonormal` (sorry-free). -/
theorem hermiteFunction_orthonormal :
    ∀ m₁ m₂ : ℕ, ∫ x : ℝ, hermiteFunction m₁ x * hermiteFunction m₂ x =
      if m₁ = m₂ then 1 else 0 := by
  sorry

/-- The rapid decay property: Schwartz seminorms of Hermite functions decay polynomially.
    **Superseded** by `gfHermiteFunction_seminorm_bound` (sorry-free). -/
theorem hermiteFunction_seminorm_decay (k l N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      SchwartzMap.schwartzSeminorm ℝ ℝ k l
        (Classical.choose (hermiteFunction_schwartz m)) ≤ C * (m : ℝ) ^ (-(N : ℤ)) := by
  sorry

end
