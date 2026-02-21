/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Unbounded.Basic
import OSReconstruction.vNA.Spectral.CayleyTransform
import OSReconstruction.vNA.Spectral.SpectralViaCayleyRMK
import OSReconstruction.vNA.Spectral.SigmaAdditivity
import OSReconstruction.vNA.MeasureTheory.SpectralStieltjes
import OSReconstruction.vNA.MeasureTheory.SpectralIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Spectral Theory for Unbounded Self-Adjoint Operators

This file develops the spectral theory for unbounded self-adjoint operators,
which is essential for defining the modular operator Δ and its functional calculus.

## Main definitions

* `SpectralMeasure` - a projection-valued measure on ℝ
* `spectral_theorem` - existence of spectral measure for self-adjoint operators
* `functionalCalculus` - f(T) for bounded Borel functions f
* `unitaryGroup` - the one-parameter unitary group T^{it}

## Mathematical foundations (Reed-Simon/Rudin)

The spectral theorem for unbounded self-adjoint operators states that every
self-adjoint operator T has a unique spectral decomposition T = ∫ λ dP(λ)
where P is a projection-valued measure (PVM). The standard proofs use:

1. **Cayley transform**: Map T to the unitary U = (T-i)(T+i)⁻¹, apply the
   spectral theorem for unitary operators, then pull back.
   (Reed-Simon VIII.3, Rudin 13.30)

2. **Resolution of identity**: Construct P directly from the resolvent
   (T-z)⁻¹ using Stone's formula: P([a,b]) = s-lim ∫_a^b Im((T-λ-iε)⁻¹) dλ/π
   (Reed-Simon VII.3, Kato V.3.5)

The functional calculus properties follow from the construction:
- Multiplicativity: ∫ fg dP = (∫ f dP)(∫ g dP) (Reed-Simon VIII.5)
- Adjoint: (∫ f dP)* = ∫ f̄ dP (Reed-Simon VIII.5)

## Implementation notes

Several theorems are marked with `sorry` as they require deep functional
analysis infrastructure. These are fundamental results that would need either:
- A full development of the Cayley transform approach
- The theory of resolvents and Stone's formula
- Or axiomatization as trusted foundations

The logical structure is complete - all dependencies are properly tracked,
and filling in any sorry would not require changing the API.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I: Functional Analysis"
  - Chapter VII: The Spectral Theorem
  - Chapter VIII: Unbounded Operators
* Rudin, "Functional Analysis", Chapter 13
* Kato, "Perturbation Theory for Linear Operators", Chapter V
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical NNReal
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Spectral measures -/

/-- A projection-valued measure (PVM) on ℝ, also called a spectral measure.
    For each Borel set E ⊆ ℝ, P(E) is an orthogonal projection on H.

    A PVM satisfies:
    1. P(∅) = 0, P(ℝ) = 1
    2. P(E)² = P(E) and P(E)* = P(E) (orthogonal projections)
    3. P(E ∩ F) = P(E)P(F) (multiplicativity)
    4. For disjoint sequence (Eₙ), P(⋃ Eₙ) = Σ P(Eₙ) (σ-additivity, strong convergence)

    The σ-additivity implies that for each x ∈ H, the map E ↦ ⟨x, P(E)x⟩ is a
    positive Borel measure on ℝ with total mass ‖x‖². -/
structure SpectralMeasure (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The projection for each Borel set. For non-measurable sets, returns 0 by convention. -/
  proj : Set ℝ → (H →L[ℂ] H)
  /-- P(∅) = 0 -/
  empty : proj ∅ = 0
  /-- P(ℝ) = 1 -/
  univ : proj Set.univ = 1
  /-- Each P(E) is idempotent (for measurable E) -/
  isIdempotent : ∀ E, MeasurableSet E → proj E ∘L proj E = proj E
  /-- Each P(E) is self-adjoint (for measurable E) -/
  isSelfAdj : ∀ E, MeasurableSet E → ContinuousLinearMap.adjoint (proj E) = proj E
  /-- P(E ∩ F) = P(E) P(F) (for measurable E, F) -/
  inter : ∀ E F, MeasurableSet E → MeasurableSet F → proj (E ∩ F) = proj E ∘L proj F
  /-- Monotonicity: E ⊆ F implies P(E) ≤ P(F) in the operator order (for measurable E, F) -/
  monotone : ∀ E F, MeasurableSet E → MeasurableSet F → E ⊆ F →
    ∀ x : H, ‖proj E x‖ ≤ ‖proj F x‖
  /-- σ-additivity: for disjoint measurable sequence, P(⋃ Eₙ)x = Σ P(Eₙ)x -/
  sigma_additive : ∀ (E : ℕ → Set ℝ), (∀ i, MeasurableSet (E i)) →
    (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, proj (E i) x)
      Filter.atTop (nhds (proj (⋃ i, E i) x))
  /-- Non-measurable sets get the zero projection -/
  proj_nonmeasurable : ∀ E, ¬MeasurableSet E → proj E = 0

namespace SpectralMeasure

variable (P : SpectralMeasure H)

/-- The complex measure μ_{x,y}(E) = ⟨x, P(E)y⟩.
    This is a complex-valued Borel measure derived from the spectral measure.
    By polarization, μ_{x,y} determines P completely. -/
def complexMeasure (x y : H) (E : Set ℝ) : ℂ :=
  @inner ℂ H _ x (P.proj E y)

/-- The positive measure μ_x(E) = ⟨x, P(E)x⟩ = ‖P(E)x‖².
    This is a positive Borel measure with total mass ‖x‖².
    It is used to define the spectral integral. -/
def positiveMeasure (x : H) (E : Set ℝ) : ℝ :=
  ‖P.proj E x‖ ^ 2

/-- The positive measure as a real-valued function (for integration) -/
def scalarMeasure (x : H) (E : Set ℝ) : ℝ :=
  (@inner ℂ H _ x (P.proj E x)).re

/-- The support of the spectral measure: the smallest closed set with P(supp) = 1 -/
def support : Set ℝ :=
  { t | ∀ ε > 0, P.proj (Set.Ioo (t - ε) (t + ε)) ≠ 0 }

/-- For disjoint measurable E, F: P(E ∪ F) = P(E) + P(F) -/
theorem additive_disjoint (E F : Set ℝ) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEF : Disjoint E F) :
    P.proj (E ∪ F) = P.proj E + P.proj F := by
  -- Use P(E)P(F) = P(E ∩ F) = P(∅) = 0 for disjoint sets
  -- Combined with idempotence, this gives us additivity
  --
  -- Alternative approach using projections:
  -- P(E ∪ F)² = P(E ∪ F), and P(E ∪ F) projects onto ran(P(E)) ⊕ ran(P(F))
  -- For disjoint E, F: ran(P(E)) ⊥ ran(P(F)), so P(E ∪ F) = P(E) + P(F)
  --
  -- The rigorous proof uses σ-additivity for the two-element sequence
  -- and the fact that partial sums stabilize.
  ext x
  -- We show pointwise: P(E ∪ F)x = P(E)x + P(F)x
  -- Use the fact that P(E) and P(F) project onto orthogonal subspaces
  have hinter : P.proj (E ∩ F) = 0 := by
    have h := hEF
    rw [Set.disjoint_iff_inter_eq_empty] at h
    rw [h]
    exact P.empty
  -- P(E)P(F) = P(E ∩ F) = 0
  have hPEPF : P.proj E ∘L P.proj F = 0 := by rw [← P.inter E F hE hF, hinter]
  have hPFPE : P.proj F ∘L P.proj E = 0 := by rw [← P.inter F E hF hE, Set.inter_comm, hinter]
  -- For orthogonal projections with PQ = 0, P + Q is also a projection onto ran(P) ⊕ ran(Q)
  -- And P(E ∪ F) projects onto the same space
  -- This requires showing (P + Q)² = P + Q when PQ = QP = 0
  -- (P + Q)² = P² + PQ + QP + Q² = P + 0 + 0 + Q = P + Q
  -- Use σ-additivity for a two-element sequence
  let seq : ℕ → Set ℝ := fun n => if n = 0 then E else if n = 1 then F else ∅
  have hseq_disj : ∀ i j, i ≠ j → Disjoint (seq i) (seq j) := by
    intro i j hij
    simp only [seq]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
    simp_all [hEF.symm]
  have hunion : ⋃ i, seq i = E ∪ F := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_union, seq]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hi0 : i = 0
      · left; simp_all
      · by_cases hi1 : i = 1
        · right; simp_all
        · simp_all [Set.mem_empty_iff_false]
    · rintro (ht | ht)
      · exact ⟨0, by simp [ht]⟩
      · exact ⟨1, by simp [ht]⟩
  have hseq_meas : ∀ i, MeasurableSet (seq i) := by
    intro i; simp only [seq]
    by_cases hi0 : i = 0
    · simp [hi0]; exact hE
    · by_cases hi1 : i = 1
      · simp [hi1]; exact hF
      · simp [hi0, hi1]
  have hconv := P.sigma_additive seq hseq_meas hseq_disj x
  rw [hunion] at hconv
  -- The partial sums stabilize at P(E)x + P(F)x for n ≥ 2
  have hsum_stable : ∀ n ≥ 2, ∑ i ∈ Finset.range n, P.proj (seq i) x = P.proj E x + P.proj F x := by
    intro n hn
    have h2 : ∑ i ∈ Finset.range 2, P.proj (seq i) x = P.proj E x + P.proj F x := by
      simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, seq]
      simp only [↓reduceIte, one_ne_zero]
    calc ∑ i ∈ Finset.range n, P.proj (seq i) x
        = ∑ i ∈ Finset.range 2, P.proj (seq i) x +
          ∑ i ∈ Finset.Ico 2 n, P.proj (seq i) x := by
            rw [Finset.sum_range_add_sum_Ico _ hn]
      _ = P.proj E x + P.proj F x + ∑ i ∈ Finset.Ico 2 n, P.proj (seq i) x := by rw [h2]
      _ = P.proj E x + P.proj F x + 0 := by
            congr 1
            apply Finset.sum_eq_zero
            intro i hi
            simp only [Finset.mem_Ico] at hi
            have hge2 : i ≥ 2 := hi.1
            simp only [seq, if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hge2)),
                       if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hge2)),
                       P.empty, ContinuousLinearMap.zero_apply]
      _ = P.proj E x + P.proj F x := add_zero _
  -- A sequence that eventually equals a constant converges to that constant
  have hlim : Tendsto (fun n => ∑ i ∈ Finset.range n, P.proj (seq i) x)
      Filter.atTop (nhds (P.proj E x + P.proj F x)) := by
    apply tendsto_atTop_of_eventually_const
    exact fun n hn => hsum_stable n hn
  -- By uniqueness of limits
  have huniq := tendsto_nhds_unique hconv hlim
  simp only [ContinuousLinearMap.add_apply]
  exact huniq

/-- P(E)P(F) = P(F)P(E) (projections from a PVM commute) -/
theorem proj_comm (E F : Set ℝ) (hE : MeasurableSet E) (hF : MeasurableSet F) :
    P.proj E ∘L P.proj F = P.proj F ∘L P.proj E := by
  -- P(E)P(F) = P(E ∩ F) = P(F ∩ E) = P(F)P(E)
  have h1 : P.proj E ∘L P.proj F = P.proj (E ∩ F) := (P.inter E F hE hF).symm
  have h2 : P.proj F ∘L P.proj E = P.proj (F ∩ E) := (P.inter F E hF hE).symm
  rw [h1, h2, Set.inter_comm]

/-- ‖P(E)x‖² = ⟨x, P(E)x⟩ (since P(E) is a projection) -/
theorem norm_sq_eq_inner (E : Set ℝ) (hE : MeasurableSet E) (x : H) :
    ‖P.proj E x‖^2 = (@inner ℂ H _ x (P.proj E x)).re := by
  -- P(E)² = P(E) and P(E)* = P(E), so ⟨x, P(E)x⟩ = ⟨P(E)x, P(E)x⟩ = ‖P(E)x‖²
  have hidempotent := P.isIdempotent E hE
  have hselfadj := P.isSelfAdj E hE
  -- ⟨x, P(E)x⟩ = ⟨P(E)x, P(E)x⟩ = ‖P(E)x‖²
  have h1 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    -- adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
    -- Since P(E)* = P(E), we have ⟨x, P(E) y⟩ = ⟨P(E) x, y⟩
    -- With y = P(E)x: ⟨x, P(E)(P(E)x)⟩ = ⟨P(E)x, P(E)x⟩
    -- By idempotence P(E)² = P(E): ⟨x, P(E)x⟩ = ⟨x, P(E)(P(E)x)⟩
    have step1 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ x (P.proj E (P.proj E x)) := by
      conv_rhs => rw [← ContinuousLinearMap.comp_apply, hidempotent]
    -- Using self-adjointness: P(E)* = P(E)
    have step2 : @inner ℂ H _ x (P.proj E (P.proj E x)) =
        @inner ℂ H _ x (ContinuousLinearMap.adjoint (P.proj E) (P.proj E x)) := by
      rw [hselfadj]
    -- adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
    have step3 : @inner ℂ H _ x (ContinuousLinearMap.adjoint (P.proj E) (P.proj E x)) =
        @inner ℂ H _ (P.proj E x) (P.proj E x) :=
      ContinuousLinearMap.adjoint_inner_right (P.proj E) x (P.proj E x)
    rw [step1, step2, step3]
  rw [h1, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- ‖P(E)x‖ ≤ ‖x‖ for any spectral projection.
    This follows from P(E) being an orthogonal projection (idempotent and self-adjoint).
    For non-measurable E, P(E) = 0 so the bound is trivially 0 ≤ ‖x‖.

    Proof: By Pythagoras, ‖x‖² = ‖P(E)x‖² + ‖(1-P(E))x‖² ≥ ‖P(E)x‖² -/
theorem proj_norm_le (E : Set ℝ) (x : H) : ‖P.proj E x‖ ≤ ‖x‖ := by
  by_cases hE : MeasurableSet E
  · by_cases hx : x = 0
    · simp [hx]
    -- Use: ‖P(E)x‖² = ⟨x, P(E)x⟩ and Cauchy-Schwarz
    have hnorm_sq := P.norm_sq_eq_inner E hE x
    -- ‖P(E)x‖² = Re⟨x, P(E)x⟩ ≤ ‖⟨x, P(E)x⟩‖ ≤ ‖x‖ · ‖P(E)x‖ (Cauchy-Schwarz)
    have hCS : ‖@inner ℂ H _ x (P.proj E x)‖ ≤ ‖x‖ * ‖P.proj E x‖ :=
      norm_inner_le_norm x (P.proj E x)
    -- For complex z, z.re ≤ |z.re| ≤ ‖z‖
    have hre_le : (@inner ℂ H _ x (P.proj E x)).re ≤ ‖@inner ℂ H _ x (P.proj E x)‖ := by
      calc (@inner ℂ H _ x (P.proj E x)).re
          ≤ |(@inner ℂ H _ x (P.proj E x)).re| := le_abs_self _
        _ ≤ ‖@inner ℂ H _ x (P.proj E x)‖ := Complex.abs_re_le_norm _
    have h1 : ‖P.proj E x‖^2 ≤ ‖x‖ * ‖P.proj E x‖ := by
      calc ‖P.proj E x‖^2 = (@inner ℂ H _ x (P.proj E x)).re := hnorm_sq
        _ ≤ ‖@inner ℂ H _ x (P.proj E x)‖ := hre_le
        _ ≤ ‖x‖ * ‖P.proj E x‖ := hCS
    by_cases hPx : P.proj E x = 0
    · simp [hPx]
    · have hPx_pos : 0 < ‖P.proj E x‖ := norm_pos_iff.mpr hPx
      calc ‖P.proj E x‖ = ‖P.proj E x‖^2 / ‖P.proj E x‖ := by field_simp
        _ ≤ (‖x‖ * ‖P.proj E x‖) / ‖P.proj E x‖ := by
            apply div_le_div_of_nonneg_right h1 hPx_pos.le
        _ = ‖x‖ := by field_simp
  · -- Non-measurable: P(E) = 0
    rw [P.proj_nonmeasurable E hE, ContinuousLinearMap.zero_apply, norm_zero]
    exact norm_nonneg _

/-- The operator norm of P(E) is at most 1.
    For non-measurable E, P(E) = 0 so ‖P(E)‖ = 0 ≤ 1. -/
theorem proj_opNorm_le_one (E : Set ℝ) : ‖P.proj E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  exact P.proj_norm_le E x

/-- P(E)x and P(F)x are orthogonal when E and F are disjoint.
    This follows from P(E)P(F) = P(E ∩ F) = P(∅) = 0. -/
theorem proj_orthogonal_of_disjoint (E F : Set ℝ) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEF : Disjoint E F) (x : H) :
    @inner ℂ H _ (P.proj E x) (P.proj F x) = 0 := by
  -- ⟨P(E)x, P(F)x⟩ = ⟨x, P(E)* P(F)x⟩ = ⟨x, P(E)P(F)x⟩ (self-adjoint)
  --                = ⟨x, P(E ∩ F)x⟩ = ⟨x, P(∅)x⟩ = ⟨x, 0⟩ = 0
  have hinter : E ∩ F = ∅ := Set.disjoint_iff_inter_eq_empty.mp hEF
  calc @inner ℂ H _ (P.proj E x) (P.proj F x)
      = @inner ℂ H _ x (ContinuousLinearMap.adjoint (P.proj E) (P.proj F x)) :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = @inner ℂ H _ x (P.proj E (P.proj F x)) := by rw [P.isSelfAdj E hE]
    _ = @inner ℂ H _ x ((P.proj E ∘L P.proj F) x) := rfl
    _ = @inner ℂ H _ x (P.proj (E ∩ F) x) := by rw [← P.inter E F hE hF]
    _ = @inner ℂ H _ x (P.proj ∅ x) := by rw [hinter]
    _ = @inner ℂ H _ x 0 := by rw [P.empty]; simp
    _ = 0 := inner_zero_right _

omit [CompleteSpace H] in
/-- Pythagorean theorem for pairwise orthogonal vectors indexed by Fin n. -/
theorem pythag_sum_sq {n : ℕ} (v : Fin n → H)
    (horth : ∀ i j, i ≠ j → @inner ℂ H _ (v i) (v j) = 0) :
    ‖∑ i : Fin n, v i‖^2 = ∑ i : Fin n, ‖v i‖^2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hw_u_orth : @inner ℂ H _ (∑ i : Fin k, v (Fin.castSucc i)) (v (Fin.last k)) = 0 := by
      rw [sum_inner]
      apply Finset.sum_eq_zero
      intro i _
      apply horth
      exact Fin.castSucc_ne_last i
    have hpyth2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hw_u_orth
    simp only [sq]
    rw [hpyth2]
    congr 1
    have horth' : ∀ i j : Fin k, i ≠ j →
        @inner ℂ H _ (v (Fin.castSucc i)) (v (Fin.castSucc j)) = 0 := by
      intro i j hij
      apply horth
      exact Fin.castSucc_injective k |>.ne hij
    have h := ih (v ∘ Fin.castSucc) horth'
    simp only [Function.comp_apply, sq] at h
    exact h

/-- The tight operator norm bound for sums of projections on disjoint sets.
    The tight bound is ‖Σᵢ cᵢ P(Eᵢ)‖ ≤ sup |cᵢ| when the Eᵢ are pairwise disjoint.
    This uses orthogonality: ‖Σᵢ cᵢ P(Eᵢ) x‖² = Σᵢ |cᵢ|² ‖P(Eᵢ) x‖².

    The proof requires the Pythagorean theorem for pairwise orthogonal vectors,
    which we establish using the orthogonality of P(E)x and P(F)x for disjoint E, F. -/
theorem proj_sum_norm_le_sup {n : ℕ} (c : Fin n → ℂ) (E : Fin n → Set ℝ)
    (hE_meas : ∀ i, MeasurableSet (E i))
    (hE_disj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (M : ℝ) (hM : ∀ i, ‖c i‖ ≤ M) (hM_pos : 0 ≤ M) :
    ‖∑ i : Fin n, c i • P.proj (E i)‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM_pos
  intro x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  -- Use Pythagorean theorem for orthogonal vectors
  have hproj_orth : ∀ i j, i ≠ j → @inner ℂ H _ (P.proj (E i) x) (P.proj (E j) x) = 0 := by
    intro i j hij
    exact P.proj_orthogonal_of_disjoint (E i) (E j) (hE_meas i) (hE_meas j) (hE_disj i j hij) x
  have hproj_pythag : ‖∑ i : Fin n, P.proj (E i) x‖^2 = ∑ i : Fin n, ‖P.proj (E i) x‖^2 := by
    exact pythag_sum_sq (fun i => P.proj (E i) x) hproj_orth
  -- Define v and use Pythagorean
  let v : Fin n → H := fun i => c i • P.proj (E i) x
  have hv_orth : ∀ i j, i ≠ j → @inner ℂ H _ (v i) (v j) = 0 := by
    intro i j hij
    simp only [v, inner_smul_left, inner_smul_right]
    rw [P.proj_orthogonal_of_disjoint (E i) (E j) (hE_meas i) (hE_meas j) (hE_disj i j hij) x]
    ring
  have hpythag : ‖∑ i : Fin n, v i‖^2 = ∑ i : Fin n, ‖v i‖^2 := by exact pythag_sum_sq v hv_orth
  -- Bound ∑ᵢ ‖P(Eᵢ) x‖² ≤ ‖x‖²
  have hproj_sum_le : ∑ i : Fin n, ‖P.proj (E i) x‖^2 ≤ ‖x‖^2 := by
    rw [← hproj_pythag]
    have hsum_bound : ‖∑ i : Fin n, P.proj (E i) x‖ ≤ ‖x‖ := by
      have hcalc : ‖∑ i : Fin n, P.proj (E i) x‖^2 ≤ ‖x‖ * ‖∑ i : Fin n, P.proj (E i) x‖ :=
        calc ‖∑ i : Fin n, P.proj (E i) x‖^2 = ∑ i : Fin n, ‖P.proj (E i) x‖^2 := hproj_pythag
          _ = ∑ i : Fin n, (@inner ℂ H _ x (P.proj (E i) x)).re := by
              congr 1; ext i; exact P.norm_sq_eq_inner (E i) (hE_meas i) x
          _ = (∑ i : Fin n, @inner ℂ H _ x (P.proj (E i) x)).re := by rw [← Complex.re_sum]
          _ = (@inner ℂ H _ x (∑ i : Fin n, P.proj (E i) x)).re := by rw [← inner_sum]
          _ ≤ ‖@inner ℂ H _ x (∑ i : Fin n, P.proj (E i) x)‖ := Complex.re_le_norm _
          _ ≤ ‖x‖ * ‖∑ i : Fin n, P.proj (E i) x‖ := norm_inner_le_norm _ _
      by_cases hzero : ∑ i : Fin n, P.proj (E i) x = 0
      · rw [hzero, norm_zero]; exact norm_nonneg x
      · have hpos : 0 < ‖∑ i : Fin n, P.proj (E i) x‖ := norm_pos_iff.mpr hzero
        calc ‖∑ i : Fin n, P.proj (E i) x‖
            = ‖∑ i : Fin n, P.proj (E i) x‖^2 / ‖∑ i : Fin n, P.proj (E i) x‖ := by field_simp
          _ ≤ (‖x‖ * ‖∑ i : Fin n, P.proj (E i) x‖) / ‖∑ i : Fin n, P.proj (E i) x‖ := by
              apply div_le_div_of_nonneg_right hcalc hpos.le
          _ = ‖x‖ := by field_simp
    exact sq_le_sq' (by linarith [norm_nonneg (∑ i : Fin n, P.proj (E i) x)]) hsum_bound
  -- Final calculation
  show ‖∑ i : Fin n, c i • P.proj (E i) x‖ ≤ M * ‖x‖
  calc ‖∑ i : Fin n, c i • P.proj (E i) x‖
      = Real.sqrt (‖∑ i : Fin n, c i • P.proj (E i) x‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (∑ i : Fin n, ‖c i • P.proj (E i) x‖^2) := by rw [hpythag]
    _ = Real.sqrt (∑ i : Fin n, ‖c i‖^2 * ‖P.proj (E i) x‖^2) := by
        congr 1; apply Finset.sum_congr rfl; intro i _
        rw [norm_smul]; ring
    _ ≤ Real.sqrt (∑ i : Fin n, M^2 * ‖P.proj (E i) x‖^2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact sq_le_sq' (by linarith [norm_nonneg (c i)]) (hM i)
    _ = Real.sqrt (M^2 * ∑ i : Fin n, ‖P.proj (E i) x‖^2) := by rw [← Finset.mul_sum]
    _ ≤ Real.sqrt (M^2 * ‖x‖^2) := by
        apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left hproj_sum_le (sq_nonneg M)
    _ = |M| * ‖x‖ := by rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg x)]
    _ = M * ‖x‖ := by rw [abs_of_nonneg hM_pos]

/-! ### Distribution function and diagonal measure -/

/-- ⟨x, P(E)x⟩ is real and non-negative (uses idempotence and self-adjointness). -/
theorem inner_proj_nonneg (E : Set ℝ) (hE : MeasurableSet E) (x : H) :
    0 ≤ (@inner ℂ H _ x (P.proj E x)).re := by
  rw [← P.norm_sq_eq_inner E hE x]; exact sq_nonneg _

/-- ⟨x, P(E)x⟩.re ≤ ‖x‖² for any spectral projection. -/
theorem inner_proj_le_norm_sq (E : Set ℝ) (x : H) :
    (@inner ℂ H _ x (P.proj E x)).re ≤ ‖x‖^2 := by
  by_cases hE : MeasurableSet E
  · rw [← P.norm_sq_eq_inner E hE x]
    exact sq_le_sq' (by linarith [norm_nonneg (P.proj E x), norm_nonneg x]) (P.proj_norm_le E x)
  · rw [P.proj_nonmeasurable E hE, ContinuousLinearMap.zero_apply, inner_zero_right,
        Complex.zero_re]
    exact sq_nonneg _

/-- For decreasing measurable sets with intersection S, P(E_n)x → P(S)x.
    Proof: σ-additivity on the difference sets gives a convergent telescoping sum. -/
theorem proj_decreasing_tendsto_meas (x : H) (E : ℕ → Set ℝ) (S : Set ℝ)
    (hE_meas : ∀ i, MeasurableSet (E i)) (hS_meas : MeasurableSet S)
    (hE_dec : ∀ n, E (n + 1) ⊆ E n) (hS_eq : ⋂ n, E n = S)
    (hS_sub : ∀ n, S ⊆ E n) :
    Tendsto (fun n => P.proj (E n) x) atTop (nhds (P.proj S x)) := by
  -- Define difference sets F_k = E_k \ E_{k+1}
  set F : ℕ → Set ℝ := fun k => E k \ E (k + 1) with hF_def
  have hF_meas : ∀ k, MeasurableSet (F k) := fun k => (hE_meas k).diff (hE_meas (k + 1))
  -- F_k are pairwise disjoint
  have hF_disj : ∀ i j, i ≠ j → Disjoint (F i) (F j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hz hzj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hz.2 (decreasing_chain_le hE_dec (show i + 1 ≤ j by omega) hzj.1)
    · exact hzj.2 (decreasing_chain_le hE_dec (show j + 1 ≤ i by omega) hz.1)
  -- Finite additivity: P(E_k)x = P(E_{k+1})x + P(F_k)x
  have htelesc : ∀ k, P.proj (E k) x = P.proj (E (k + 1)) x + P.proj (F k) x := by
    intro k
    have h := P.additive_disjoint (E (k + 1)) (F k) (hE_meas _) (hF_meas k)
      (Set.disjoint_left.mpr fun z hz ⟨_, hzd⟩ => hzd hz)
    rw [Set.union_diff_cancel (hE_dec k)] at h
    have hx := congrFun (congrArg DFunLike.coe h) x
    simp only [ContinuousLinearMap.add_apply] at hx
    exact hx
  -- Telescoping: ∑_{k<n} P(F_k)x = P(E_0)x - P(E_n)x
  have htelesc_sum : ∀ n, ∑ k ∈ Finset.range n, P.proj (F k) x =
      P.proj (E 0) x - P.proj (E n) x := by
    intro n; induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, (sub_eq_of_eq_add (htelesc m)).symm]
      abel
  -- P(E_n)x = P(E_0)x - ∑_{k<n} P(F_k)x
  have hEn_eq : ∀ n, P.proj (E n) x =
      P.proj (E 0) x - ∑ k ∈ Finset.range n, P.proj (F k) x := by
    intro n; rw [htelesc_sum n]; abel
  -- ⋃_k F_k = E_0 \ S
  have hF_union : ⋃ k, F k = E 0 \ S := by
    ext z; simp only [Set.mem_iUnion, Set.mem_diff]
    constructor
    · rintro ⟨k, hzk, hzk'⟩
      exact ⟨decreasing_chain_le hE_dec (Nat.zero_le k) hzk,
             fun hzS => hzk' (hS_sub (k + 1) hzS)⟩
    · rintro ⟨hz0, hzS⟩
      rw [← hS_eq] at hzS
      simp only [Set.mem_iInter] at hzS
      push_neg at hzS
      obtain ⟨m, hm⟩ := hzS
      haveI : DecidablePred (fun m => z ∉ E m) := Classical.decPred _
      have hexists : ∃ m, z ∉ E m := ⟨m, hm⟩
      set k := Nat.find hexists
      have hk_spec : z ∉ E k := Nat.find_spec hexists
      have hk_pos : k ≠ 0 := fun hk0 => by rw [hk0] at hk_spec; exact hk_spec hz0
      have hk_prev : z ∈ E (k - 1) := by
        by_contra hc; exact Nat.find_min hexists (by omega) hc
      exact ⟨k - 1, hk_prev, by rwa [show k - 1 + 1 = k from by omega]⟩
  -- E_0 = S ∪ (E_0 \ S), so P(E_0)x = P(S)x + P(E_0\S)x
  have hE0_decomp : P.proj (E 0) x = P.proj S x + P.proj (E 0 \ S) x := by
    have h := P.additive_disjoint S (E 0 \ S) hS_meas ((hE_meas 0).diff hS_meas)
      (Set.disjoint_left.mpr fun _ hzS ⟨_, hzd⟩ => hzd hzS)
    rw [Set.union_diff_cancel (hS_sub 0)] at h
    have hx := congrFun (congrArg DFunLike.coe h) x
    simp only [ContinuousLinearMap.add_apply] at hx
    exact hx
  -- σ-additivity: ∑ P(F_k)x → P(E_0 \ S)x
  have hF_sigma := P.sigma_additive F hF_meas hF_disj x
  rw [hF_union] at hF_sigma
  -- P(E_n)x = P(E_0)x - ∑ P(F_k)x → P(E_0)x - P(E_0\S)x = P(S)x
  have h_sub := tendsto_const_nhds (x := P.proj (E 0) x) |>.sub hF_sigma
  have h_eq : P.proj (E 0) x - P.proj (E 0 \ S) x = P.proj S x :=
    sub_eq_iff_eq_add.mpr hE0_decomp
  rw [h_eq] at h_sub
  exact h_sub.congr (fun n => (hEn_eq n).symm)

/-- The spectral distribution function for a SpectralMeasure.
    F_x(t) = ⟨x, P(Iic t) x⟩ = ‖P(Iic t) x‖² -/
def distributionFunction (x : H) : SpectralDistribution where
  toFun := fun t => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
  mono := by
    intro a b hab; dsimp
    rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
    exact sq_le_sq'
      (by linarith [norm_nonneg (P.proj (Set.Iic a) x), norm_nonneg (P.proj (Set.Iic b) x)])
      (P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hab) x)
  right_continuous := by
    intro t
    -- Step 1: Sequential convergence P(Iic(t + 1/(n+1)))x → P(Iic t)x
    set E := fun n : ℕ => Set.Iic (t + 1 / ((↑n : ℝ) + 1))
    have hE_dec : ∀ n, E (n + 1) ⊆ E n := by
      intro n; simp only [E]; apply Set.Iic_subset_Iic.mpr
      have h1 : (0 : ℝ) < (↑n : ℝ) + 1 := by positivity
      linarith [one_div_le_one_div_of_le h1 (by push_cast; linarith : (↑n : ℝ) + 1 ≤ ↑(n + 1) + 1)]
    have hE_inter : ⋂ n, E n = Set.Iic t := by
      ext s; simp only [Set.mem_iInter, Set.mem_Iic, E]
      refine ⟨fun h => ?_, fun hs n => le_add_of_le_of_nonneg hs (by positivity)⟩
      by_contra hst; push_neg at hst
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (s - t))
      have hpos : (0 : ℝ) < s - t := sub_pos.mpr hst
      have h1 : 1 < (↑n : ℝ) * (s - t) := by rwa [div_lt_iff₀ hpos] at hn
      have h2 : (s - t) * ((↑n : ℝ) + 1) ≤ 1 :=
        (le_div_iff₀ (by positivity : (0:ℝ) < ↑n + 1)).mp (by linarith [h n])
      nlinarith [mul_comm (s - t) (↑n : ℝ)]
    have hconv := P.proj_decreasing_tendsto_meas x E (Set.Iic t)
      (fun _ => measurableSet_Iic) measurableSet_Iic hE_dec hE_inter
      (fun n => Set.Iic_subset_Iic.mpr (le_add_of_nonneg_right (by positivity)))
    -- Compose with continuous map y ↦ ⟨x, y⟩.re
    have hcont : Continuous (fun y : H => (@inner ℂ H _ x y).re) := by fun_prop
    have hseq : Tendsto (fun n : ℕ => (@inner ℂ H _ x (P.proj (E n) x)).re)
        atTop (nhds ((@inner ℂ H _ x (P.proj (Set.Iic t) x)).re)) :=
      hcont.continuousAt.tendsto.comp hconv
    -- Step 2: ContinuousWithinAt from monotonicity + sequential convergence
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    rw [Metric.tendsto_atTop] at hseq
    obtain ⟨N, hN⟩ := hseq ε hε
    refine ⟨1 / ((↑N : ℝ) + 1), by positivity, fun s hs hds => ?_⟩
    have hst : t ≤ s := hs
    have hsd : s < t + 1 / ((↑N : ℝ) + 1) := by
      rw [Real.dist_eq, abs_lt] at hds; linarith [hds.2]
    -- f(t) ≤ f(s) ≤ f(t + 1/(N+1)) by monotonicity
    have h_lo : (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re ≤
        (@inner ℂ H _ x (P.proj (Set.Iic s) x)).re := by
      rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
      have := P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hst) x
      nlinarith [norm_nonneg (P.proj (Set.Iic t) x)]
    have h_hi : (@inner ℂ H _ x (P.proj (Set.Iic s) x)).re ≤
        (@inner ℂ H _ x (P.proj (E N) x)).re := by
      rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
      have := P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hsd.le) x
      nlinarith [norm_nonneg (P.proj (Set.Iic s) x)]
    -- |f(s) - f(t)| = f(s) - f(t) ≤ f(N) - f(t) < ε
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    have hNN := hN N le_rfl; rw [Real.dist_eq] at hNN
    have h_nn : 0 ≤ (@inner ℂ H _ x (P.proj (E N) x)).re -
        (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re := by linarith
    rw [abs_of_nonneg h_nn] at hNN
    linarith
  nonneg := fun t => P.inner_proj_nonneg _ measurableSet_Iic x
  bound := ‖x‖^2
  bound_nonneg := sq_nonneg _
  le_bound := fun t => P.inner_proj_le_norm_sq _ x
  tendsto_neg_infty := by
    -- P(Iic(-n))x → P(∅)x = 0 via proj_decreasing_tendsto_meas
    set f := fun t : ℝ => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
    have f_mono : Monotone f := by
      intro a b hab; simp only [f]
      rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
      have := P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hab) x
      nlinarith [norm_nonneg (P.proj (Set.Iic a) x)]
    set E := fun n : ℕ => Set.Iic (-(↑n : ℝ))
    have hE_dec : ∀ n, E (n + 1) ⊆ E n := by
      intro n; simp only [E]; apply Set.Iic_subset_Iic.mpr; push_cast; linarith
    have hE_inter : ⋂ n, E n = ∅ := by
      ext s; simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, E]
      constructor
      · intro h; obtain ⟨n, hn⟩ := exists_nat_gt (-s); linarith [h n]
      · intro h; exact h.elim
    have hconv := P.proj_decreasing_tendsto_meas x E ∅
      (fun _ => measurableSet_Iic) MeasurableSet.empty hE_dec hE_inter
      (fun _ => Set.empty_subset _)
    rw [P.empty, ContinuousLinearMap.zero_apply] at hconv
    have hcont : Continuous (fun y : H => (@inner ℂ H _ x y).re) := by fun_prop
    have hseq : Tendsto (fun n : ℕ => f (-(↑n : ℝ))) atTop (nhds 0) := by
      have := hcont.continuousAt.tendsto.comp hconv
      simp only [inner_zero_right, Complex.zero_re, Function.comp_def] at this
      exact this
    rw [tendsto_order]
    constructor
    · intro a' ha'
      rw [Filter.eventually_atBot]
      exact ⟨0, fun s _ => lt_of_lt_of_le ha' (P.inner_proj_nonneg _ measurableSet_Iic x)⟩
    · intro a' ha'
      rw [Filter.eventually_atBot]
      have hexN : ∃ N : ℕ, f (-(↑N : ℝ)) < a' := by
        by_contra h; push_neg at h
        exact absurd (ge_of_tendsto' hseq h) (not_le.mpr ha')
      obtain ⟨N, hN⟩ := hexN
      exact ⟨-(↑N : ℝ), fun s hs => lt_of_le_of_lt (f_mono hs) hN⟩
  tendsto_pos_infty := by
    -- P(Iic(n))x → P(ℝ)x = x via complement
    set f := fun t : ℝ => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
    have f_mono : Monotone f := by
      intro a b hab; simp only [f]
      rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
      have := P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hab) x
      nlinarith [norm_nonneg (P.proj (Set.Iic a) x)]
    set G := fun n : ℕ => Set.Ioi (↑n : ℝ)
    have hG_dec : ∀ n, G (n + 1) ⊆ G n := by
      intro n; simp only [G]; apply Set.Ioi_subset_Ioi; push_cast; linarith
    have hG_inter : ⋂ n, G n = ∅ := by
      ext s; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, G]
      constructor
      · intro h; obtain ⟨n, hn⟩ := exists_nat_gt s; linarith [h n]
      · intro h; exact h.elim
    have hG_conv := P.proj_decreasing_tendsto_meas x G ∅
      (fun _ => measurableSet_Ioi) MeasurableSet.empty hG_dec hG_inter
      (fun _ => Set.empty_subset _)
    rw [P.empty, ContinuousLinearMap.zero_apply] at hG_conv
    -- P(Iic n)x = x - P(Ioi n)x by finite additivity
    have h_decomp : ∀ n : ℕ, P.proj (Set.Iic (↑n : ℝ)) x + P.proj (Set.Ioi (↑n : ℝ)) x = x := by
      intro n
      have h := P.additive_disjoint (Set.Iic (↑n : ℝ)) (Set.Ioi (↑n : ℝ))
        measurableSet_Iic measurableSet_Ioi
        (Set.disjoint_left.mpr fun z hz hzoi =>
          not_lt.mpr (Set.mem_Iic.mp hz) (Set.mem_Ioi.mp hzoi))
      rw [Set.Iic_union_Ioi, P.univ] at h
      have hx := congrFun (congrArg DFunLike.coe h) x
      simp only [ContinuousLinearMap.add_apply] at hx
      simpa using hx.symm
    -- P(Iic n)x → x
    have hconv : Tendsto (fun n : ℕ => P.proj (Set.Iic (↑n : ℝ)) x) atTop (nhds x) := by
      have heq : (fun (n : ℕ) => P.proj (Set.Iic (↑n : ℝ)) x) = fun n => x - P.proj (G n) x := by
        ext n; simp only [G]; exact eq_sub_iff_add_eq.mpr (h_decomp n)
      rw [heq]; simpa [sub_zero] using tendsto_const_nhds (x := x) |>.sub hG_conv
    -- Compose with continuous inner product to get f(n) → ‖x‖²
    have hcont : Continuous (fun y : H => (@inner ℂ H _ x y).re) := by fun_prop
    have hseq : Tendsto (fun n : ℕ => f (↑n : ℝ)) atTop (nhds (‖x‖^2)) := by
      have h1 := hcont.continuousAt.tendsto.comp hconv
      simp only [Function.comp_def] at h1
      have hlim : (@inner ℂ H _ x x).re = ‖x‖ ^ 2 := by
        have h := P.norm_sq_eq_inner Set.univ MeasurableSet.univ x
        rw [P.univ] at h; simp only [ContinuousLinearMap.one_apply] at h
        exact h.symm
      rwa [hlim] at h1
    rw [tendsto_order]
    constructor
    · intro a' ha'
      rw [Filter.eventually_atTop]
      have hexN : ∃ N : ℕ, a' < f ↑N := by
        by_contra h; push_neg at h
        exact absurd (le_of_tendsto' hseq h) (not_le.mpr ha')
      obtain ⟨N, hN⟩ := hexN
      exact ⟨↑N, fun s hs => lt_of_lt_of_le hN (f_mono hs)⟩
    · intro a' ha'
      rw [Filter.eventually_atTop]
      exact ⟨0, fun s _ => lt_of_le_of_lt (P.inner_proj_le_norm_sq _ x) ha'⟩

open MeasureTheory in
/-- The diagonal spectral measure μ_{x,x} for a vector x. -/
def diagonalMeasure (x : H) : MeasureTheory.Measure ℝ :=
  (P.distributionFunction x).toMeasure

/-! #### Distribution function identities -/

/-- The distribution function of -z equals that of z.
    F_{-z}(t) = ⟨-z, P(Iic t)(-z)⟩.re = ‖P(Iic t)(-z)‖² = ‖P(Iic t)z‖² = F_z(t). -/
theorem distributionFunction_neg (x : H) (t : ℝ) :
    (P.distributionFunction (-x)).toFun t = (P.distributionFunction x).toFun t := by
  simp only [distributionFunction]
  have : P.proj (Set.Iic t) (-x) = -(P.proj (Set.Iic t) x) := map_neg _ _
  rw [this, inner_neg_left, inner_neg_right, neg_neg]

/-- The parallelogram identity for distribution functions:
    F_{x+y}(t) + F_{x-y}(t) = 2F_x(t) + 2F_y(t).
    This follows from the parallelogram law for the inner product ⟨z, P(E)z⟩. -/
theorem distributionFunction_parallelogram (x y : H) (t : ℝ) :
    (P.distributionFunction (x + y)).toFun t + (P.distributionFunction (x - y)).toFun t =
    2 * (P.distributionFunction x).toFun t + 2 * (P.distributionFunction y).toFun t := by
  simp only [distributionFunction]
  -- Let A = P(Iic t), which is self-adjoint
  set A := P.proj (Set.Iic t)
  -- Expand ⟨x+y, A(x+y)⟩ + ⟨x-y, A(x-y)⟩
  have hlin_add : A (x + y) = A x + A y := map_add A x y
  have hlin_sub : A (x - y) = A x - A y := map_sub A x y
  -- ⟨x+y, A(x+y)⟩ = ⟨x+y, Ax+Ay⟩ = ⟨x,Ax⟩ + ⟨x,Ay⟩ + ⟨y,Ax⟩ + ⟨y,Ay⟩
  -- ⟨x-y, A(x-y)⟩ = ⟨x-y, Ax-Ay⟩ = ⟨x,Ax⟩ - ⟨x,Ay⟩ - ⟨y,Ax⟩ + ⟨y,Ay⟩
  -- Sum = 2⟨x,Ax⟩ + 2⟨y,Ay⟩
  have h1 : @inner ℂ H _ (x + y) (A (x + y)) = @inner ℂ H _ x (A x) + @inner ℂ H _ x (A y) +
      @inner ℂ H _ y (A x) + @inner ℂ H _ y (A y) := by
    rw [hlin_add]; simp; ring
  have h2 : @inner ℂ H _ (x - y) (A (x - y)) = @inner ℂ H _ x (A x) - @inner ℂ H _ x (A y) -
      @inner ℂ H _ y (A x) + @inner ℂ H _ y (A y) := by
    rw [hlin_sub]; simp; ring
  have h3 : (@inner ℂ H _ (x + y) (A (x + y))).re + (@inner ℂ H _ (x - y) (A (x - y))).re =
      2 * (@inner ℂ H _ x (A x)).re + 2 * (@inner ℂ H _ y (A y)).re := by
    rw [h1, h2]; simp only [Complex.add_re, Complex.sub_re]; ring
  exact h3

/-- The i-rotation identity for distribution functions:
    F_{x+iy}(t) + F_{x-iy}(t) = 2F_x(t) + 2F_y(t).
    This follows from |i|² = 1 and the parallelogram identity. -/
theorem distributionFunction_irot (x y : H) (t : ℝ) :
    (P.distributionFunction (x + Complex.I • y)).toFun t +
    (P.distributionFunction (x - Complex.I • y)).toFun t =
    2 * (P.distributionFunction x).toFun t + 2 * (P.distributionFunction y).toFun t := by
  -- This is just the parallelogram identity with z = i·y, noting that F_{iz}(t) = F_z(t)
  have h := P.distributionFunction_parallelogram x (Complex.I • y) t
  -- Need: F_{iy}(t) = F_y(t)
  -- ⟨iy, A(iy)⟩ = conj(i)·i·⟨y,Ay⟩ = |i|²⟨y,Ay⟩ = ⟨y,Ay⟩
  have h_iy : (P.distributionFunction (Complex.I • y)).toFun t =
      (P.distributionFunction y).toFun t := by
    simp only [distributionFunction]
    have : P.proj (Set.Iic t) (Complex.I • y) = Complex.I • P.proj (Set.Iic t) y :=
      map_smul _ _ _
    rw [this, inner_smul_left, inner_smul_right]
    simp [Complex.conj_I]
  rw [h_iy] at h; exact h

/-- Diagonal measure of -z equals that of z: μ_{-z} = μ_z. -/
theorem diagonalMeasure_neg (x : H) :
    P.diagonalMeasure (-x) = P.diagonalMeasure x := by
  simp only [diagonalMeasure, SpectralDistribution.toMeasure]
  congr 1
  ext t  -- StieltjesFunction extensionality (has @[ext])
  exact P.distributionFunction_neg x t

/-- The diagonal measure is a finite measure with total mass = ‖x‖². -/
instance diagonalMeasure_isFiniteMeasure (x : H) :
    MeasureTheory.IsFiniteMeasure (P.diagonalMeasure x) :=
  show MeasureTheory.IsFiniteMeasure (P.distributionFunction x).toMeasure from inferInstance

/-- The total mass of the diagonal measure equals ‖x‖². -/
theorem diagonalMeasure_univ (x : H) :
    (P.diagonalMeasure x) Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  simp only [diagonalMeasure, SpectralDistribution.toMeasure, SpectralDistribution.toStieltjes]
  rw [StieltjesFunction.measure_univ _
    (P.distributionFunction x).tendsto_neg_infty
    (P.distributionFunction x).tendsto_pos_infty]
  -- Goal: ofReal(bound - 0) = ofReal(‖x‖^2), where bound = ‖x‖^2
  simp only [sub_zero, distributionFunction]

/-- The total mass of the diagonal measure as a real number. -/
theorem diagonalMeasure_real_univ (x : H) :
    (P.diagonalMeasure x).real Set.univ = ‖x‖ ^ 2 := by
  simp only [MeasureTheory.Measure.real, P.diagonalMeasure_univ x,
    ENNReal.toReal_ofReal (sq_nonneg ‖x‖)]

/-! #### Integral bounds -/

open MeasureTheory in
/-- For bounded f, the integral against the diagonal measure is bounded:
    ‖∫ f dμ_z‖ ≤ M * ‖z‖² when ‖f‖_∞ ≤ M. -/
theorem integral_diagonalMeasure_norm_le (x : H) (f : ℝ → ℂ) (M : ℝ)
    (_hM : 0 ≤ M) (hf : ∀ t, ‖f t‖ ≤ M) :
    ‖∫ t, f t ∂(P.diagonalMeasure x)‖ ≤ M * ‖x‖ ^ 2 := by
  have hfm := P.diagonalMeasure_isFiniteMeasure x
  calc ‖∫ t, f t ∂(P.diagonalMeasure x)‖
      ≤ M * (P.diagonalMeasure x).real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hf)
    _ = M * ‖x‖ ^ 2 := by rw [P.diagonalMeasure_real_univ x]

/-! #### Scalar rotation identities -/

/-- The distribution function is invariant under multiplication by i:
    F_{iz}(t) = F_z(t). This follows from ‖P(E)(iz)‖² = |i|²‖P(E)z‖² = ‖P(E)z‖². -/
theorem distributionFunction_smul_I (x : H) (t : ℝ) :
    (P.distributionFunction (Complex.I • x)).toFun t = (P.distributionFunction x).toFun t := by
  simp only [distributionFunction]
  have : P.proj (Set.Iic t) (Complex.I • x) = Complex.I • P.proj (Set.Iic t) x :=
    map_smul _ _ _
  rw [this, inner_smul_left, inner_smul_right]
  simp [Complex.conj_I]

/-- The diagonal measure is invariant under multiplication by i: μ_{iz} = μ_z. -/
theorem diagonalMeasure_smul_I (x : H) :
    P.diagonalMeasure (Complex.I • x) = P.diagonalMeasure x := by
  simp only [diagonalMeasure, SpectralDistribution.toMeasure]
  congr 1
  ext t
  exact P.distributionFunction_smul_I x t

/-! #### Measure-level parallelogram identity -/

open MeasureTheory in
/-- **Parallelogram identity for diagonal measures:**
    μ_{x+y} + μ_{x-y} = 2 • μ_x + 2 • μ_y.
    Proved via `ext_of_Ioc`: both sides agree on all half-open intervals (a,b],
    using the distribution function parallelogram identity.  -/
theorem diagonalMeasure_parallelogram (x y : H) :
    P.diagonalMeasure (x + y) + P.diagonalMeasure (x - y) =
    (2 : ℝ≥0) • P.diagonalMeasure x + (2 : ℝ≥0) • P.diagonalMeasure y := by
  -- Both sides are finite measures, use ext_of_Ioc
  apply Measure.ext_of_Ioc
  intro a b hab
  -- LHS on (a,b]
  simp only [Measure.coe_add, Pi.add_apply, Measure.smul_apply]
  -- Each μ_z((a,b]) = F_z(b) - F_z(a) via StieltjesFunction.measure_Ioc
  simp only [diagonalMeasure, SpectralDistribution.toMeasure, SpectralDistribution.toStieltjes,
    StieltjesFunction.measure_Ioc]
  have hpb := P.distributionFunction_parallelogram x y b
  have hpa := P.distributionFunction_parallelogram x y a
  have hm1 := (P.distributionFunction (x + y)).mono hab.le
  have hm2 := (P.distributionFunction (x - y)).mono hab.le
  have hm3 := (P.distributionFunction x).mono hab.le
  have hm4 := (P.distributionFunction y).mono hab.le
  -- Convert (2 : ℝ≥0) • a = a + a in ENNReal
  have smul2 : ∀ a : ENNReal, (2 : ℝ≥0) • a = a + a := fun a => by
    change ((2 : ℝ≥0) : ENNReal) * a = a + a; simp [two_mul]
  rw [smul2, smul2,
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
  congr 1; linarith

open MeasureTheory in
/-- **i-rotation identity for diagonal measures:**
    μ_{x+iy} + μ_{x-iy} = 2 • μ_x + 2 • μ_y. -/
theorem diagonalMeasure_irot (x y : H) :
    P.diagonalMeasure (x + Complex.I • y) + P.diagonalMeasure (x - Complex.I • y) =
    (2 : ℝ≥0) • P.diagonalMeasure x + (2 : ℝ≥0) • P.diagonalMeasure y := by
  apply Measure.ext_of_Ioc
  intro a b hab
  simp only [Measure.coe_add, Pi.add_apply, Measure.smul_apply]
  simp only [diagonalMeasure, SpectralDistribution.toMeasure, SpectralDistribution.toStieltjes,
    StieltjesFunction.measure_Ioc]
  have hpb := P.distributionFunction_irot x y b
  have hpa := P.distributionFunction_irot x y a
  have hm1 := (P.distributionFunction (x + Complex.I • y)).mono hab.le
  have hm2 := (P.distributionFunction (x - Complex.I • y)).mono hab.le
  have hm3 := (P.distributionFunction x).mono hab.le
  have hm4 := (P.distributionFunction y).mono hab.le
  have smul2 : ∀ a : ENNReal, (2 : ℝ≥0) • a = a + a := fun a => by
    change ((2 : ℝ≥0) : ENNReal) * a = a + a; simp [two_mul]
  rw [smul2, smul2,
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
  congr 1; linarith

/-- The distribution function scales quadratically: F_{rz}(t) = r² F_z(t) for r : ℝ. -/
theorem distributionFunction_real_smul (r : ℝ) (x : H) (t : ℝ) :
    (P.distributionFunction ((r : ℂ) • x)).toFun t =
    r ^ 2 * (P.distributionFunction x).toFun t := by
  simp only [distributionFunction]
  have : P.proj (Set.Iic t) ((r : ℂ) • x) = (r : ℂ) • P.proj (Set.Iic t) x :=
    map_smul _ _ _
  rw [this, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  -- Goal: (↑r * (↑r * ⟨x, P(Iic t) x⟩)).re = r^2 * (⟨x, P(Iic t) x⟩).re
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]; ring

/-! ### Diagonal measure equals inner product with projection -/

/-- The spectral inner product measure: E ↦ ENNReal.ofReal(⟨z, P(E)z⟩.re).
    This is a σ-additive measure that equals the diagonal spectral measure. -/
noncomputable def spectralInnerMeasure (z : H) : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.ofMeasurable
    (fun E _ => ENNReal.ofReal ((@inner ℂ H _ z (P.proj E z)).re))
    (by simp [P.empty])
    (fun E hE_meas hE_disj => by
      -- Goal (after β-reduction):
      --   ofReal(⟨z, P(⋃ₙ Eₙ)z⟩.re) = ∑' n, ofReal(⟨z, P(Eₙ)z⟩.re)
      show ENNReal.ofReal ((@inner ℂ H _ z (P.proj (⋃ n, E n) z)).re) =
        ∑' n, ENNReal.ofReal ((@inner ℂ H _ z (P.proj (E n) z)).re)
      -- All terms are nonneg
      have h_nonneg : ∀ n, 0 ≤ (@inner ℂ H _ z (P.proj (E n) z)).re :=
        fun n => P.inner_proj_nonneg _ (hE_meas n) z
      -- σ-additivity: P(⋃ₙ Eₙ)z = lim ∑_{n<N} P(Eₙ)z  in H
      have h_sigma := P.sigma_additive E hE_meas
        (fun i j hij => hE_disj hij) z
      -- Compose with continuous (inner z ·).re : H → ℝ
      have h_real : Tendsto (fun N => ∑ i ∈ Finset.range N,
            (@inner ℂ H _ z (P.proj (E i) z)).re)
          atTop (nhds ((@inner ℂ H _ z (P.proj (⋃ n, E n) z)).re)) := by
        have hcont : Continuous (fun y : H => (@inner ℂ H _ z y).re) := by fun_prop
        have h := hcont.continuousAt.tendsto.comp h_sigma
        simp only [Function.comp_def] at h
        exact h.congr (fun N => by
          rw [inner_sum]
          simp only [← Complex.coe_reAddGroupHom, map_sum])
      -- Compose with ENNReal.ofReal : ℝ → ENNReal (continuous)
      have h_ennreal : Tendsto (fun N => ∑ i ∈ Finset.range N,
            ENNReal.ofReal ((@inner ℂ H _ z (P.proj (E i) z)).re))
          atTop (nhds (ENNReal.ofReal ((@inner ℂ H _ z
            (P.proj (⋃ n, E n) z)).re))) := by
        have := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h_real
        simp only [Function.comp_def] at this
        exact this.congr (fun N => by
          exact ENNReal.ofReal_sum_of_nonneg (fun i _ => h_nonneg i))
      -- Partial sums are monotone in ENNReal
      have h_mono : Monotone (fun N => ∑ i ∈ Finset.range N,
            ENNReal.ofReal ((@inner ℂ H _ z (P.proj (E i) z)).re)) :=
        fun _ _ hab => Finset.sum_le_sum_of_subset (Finset.range_mono hab)
      -- tsum = ⨆ of partial sums = limit by monotone convergence
      rw [ENNReal.tsum_eq_iSup_nat, iSup_eq_of_tendsto h_mono h_ennreal])

/-- The spectral inner measure applied to a measurable set. -/
theorem spectralInnerMeasure_apply (z : H) (E : Set ℝ) (hE : MeasurableSet E) :
    P.spectralInnerMeasure z E = ENNReal.ofReal ((@inner ℂ H _ z (P.proj E z)).re) := by
  exact MeasureTheory.Measure.ofMeasurable_apply E hE

/-- The spectral inner measure is a finite measure. -/
instance spectralInnerMeasure_isFiniteMeasure (z : H) :
    MeasureTheory.IsFiniteMeasure (P.spectralInnerMeasure z) := by
  constructor
  rw [P.spectralInnerMeasure_apply z Set.univ MeasurableSet.univ, P.univ,
    ContinuousLinearMap.one_apply]
  exact ENNReal.ofReal_lt_top

open MeasureTheory in
/-- The diagonal measure of Iic t equals the spectral inner measure of Iic t.
    This is the key step for showing the two measures are equal. -/
theorem diagonalMeasure_Iic_eq (z : H) (t : ℝ) :
    P.diagonalMeasure z (Set.Iic t) = P.spectralInnerMeasure z (Set.Iic t) := by
  rw [P.spectralInnerMeasure_apply z _ measurableSet_Iic]
  -- diagonalMeasure = distributionFunction.toMeasure = StieltjesFunction.measure
  simp only [diagonalMeasure, SpectralDistribution.toMeasure]
  -- Apply StieltjesFunction.measure_Iic with the tendsto at -∞
  have h_tendsto : Tendsto (P.distributionFunction z).toStieltjes atBot
      (nhds (0 : ℝ)) :=
    (P.distributionFunction z).tendsto_neg_infty
  have h_eq := (P.distributionFunction z).toStieltjes.measure_Iic h_tendsto t
  rw [h_eq, sub_zero]
  -- Now: ofReal(F_z(t)) = ofReal(⟨z, P(Iic t)z⟩.re)
  -- F_z(t) = (inner z (P(Iic t) z)).re by definition of distributionFunction
  rfl

open MeasureTheory in
/-- **The diagonal measure equals the spectral inner product measure.**
    This is the key infrastructure lemma: for any spectral measure P and vector z,
    μ_z(E) = ‖P(E)z‖² = ⟨z, P(E)z⟩.re for all measurable E. -/
theorem diagonalMeasure_eq_spectralInnerMeasure (z : H) :
    P.diagonalMeasure z = P.spectralInnerMeasure z := by
  -- Both are finite measures on ℝ agreeing on Iic intervals → equal by ext_of_Iic
  exact Measure.ext_of_Iic _ _ (P.diagonalMeasure_Iic_eq z)

/-- **The core connection**: μ_z(E).toReal = ⟨z, P(E)z⟩.re = ‖P(E)z‖² for measurable E.
    This connects the diagonal spectral measure to the spectral projections. -/
theorem diagonalMeasure_apply (z : H) (E : Set ℝ) (hE : MeasurableSet E) :
    (P.diagonalMeasure z E).toReal = (@inner ℂ H _ z (P.proj E z)).re := by
  rw [P.diagonalMeasure_eq_spectralInnerMeasure z, P.spectralInnerMeasure_apply z E hE,
    ENNReal.toReal_ofReal (P.inner_proj_nonneg E hE z)]

/-- Variant: μ_z(E).toReal = ‖P(E)z‖² for measurable E. -/
theorem diagonalMeasure_apply_norm_sq (z : H) (E : Set ℝ) (hE : MeasurableSet E) :
    (P.diagonalMeasure z E).toReal = ‖P.proj E z‖ ^ 2 := by
  rw [P.diagonalMeasure_apply z E hE, ← P.norm_sq_eq_inner E hE z]

end SpectralMeasure

/-! ### Functional calculus -/

/-- A simple function for spectral integrals: a finite linear combination of indicator functions.
    Represents f = Σᵢ cᵢ χ_{Eᵢ} where the Eᵢ are disjoint measurable sets. -/
structure SimpleFunction (n : ℕ) where
  /-- The coefficients -/
  coeffs : Fin n → ℂ
  /-- The sets (should be disjoint for a proper simple function) -/
  sets : Fin n → Set ℝ

namespace SimpleFunction

open Classical in
/-- Evaluate a simple function at a point -/
def eval {n : ℕ} (f : SimpleFunction n) (x : ℝ) : ℂ :=
  ∑ i : Fin n, if x ∈ f.sets i then f.coeffs i else 0

/-- Apply a simple function to a spectral measure: Σᵢ cᵢ P(Eᵢ) -/
def spectralApply {n : ℕ} (f : SimpleFunction n) (P : SpectralMeasure H) : H →L[ℂ] H :=
  ∑ i : Fin n, f.coeffs i • P.proj (f.sets i)

/-- The constant simple function -/
def const (c : ℂ) : SimpleFunction 1 where
  coeffs := fun _ => c
  sets := fun _ => Set.univ

/-- The indicator simple function for a set -/
def indicator (E : Set ℝ) : SimpleFunction 1 where
  coeffs := fun _ => 1
  sets := fun _ => E

end SimpleFunction

/-- A structure representing the functional calculus for a spectral measure.
    This encapsulates the map f ↦ f(T) = ∫ f(λ) dP(λ) together with its properties.

    The functional calculus maps bounded Borel functions f : ℝ → ℂ to bounded operators
    on H, satisfying:
    - Linearity: (αf + g)(T) = αf(T) + g(T)
    - Multiplicativity: (fg)(T) = f(T)g(T)
    - Adjoint: f(T)* = f̄(T) where f̄(λ) = conj(f(λ))
    - Continuity: if fₙ → f uniformly with ‖fₙ‖ ≤ C, then fₙ(T) → f(T) strongly
    - Identity: 1(T) = I
    - Characteristic: χ_E(T) = P(E) for Borel sets E -/
structure FunctionalCalculus (P : SpectralMeasure H) where
  /-- The map from bounded Borel functions to bounded operators -/
  apply : (ℝ → ℂ) → (H →L[ℂ] H)
  /-- Characteristic functions map to projections -/
  characteristic : ∀ E : Set ℝ, apply (Set.indicator E (fun _ => 1)) = P.proj E
  /-- Constant function 1 maps to identity -/
  identity : apply (fun _ => 1) = 1
  /-- Multiplicativity -/
  mul : ∀ f g, apply (f * g) = apply f ∘L apply g
  /-- Adjoint property -/
  adjoint : ∀ f, ContinuousLinearMap.adjoint (apply f) = apply (star ∘ f)

/-- The spectral integral of the constant function 1 is the identity -/
theorem simple_spectralApply_one (P : SpectralMeasure H) :
    (SimpleFunction.const 1).spectralApply P = 1 := by
  unfold SimpleFunction.const SimpleFunction.spectralApply
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_smul]
  exact P.univ

/-- The spectral integral respects scalar multiplication in coefficients -/
theorem simple_spectralApply_smul {n : ℕ} (P : SpectralMeasure H)
    (f : SimpleFunction n) (c : ℂ) :
    -- Scaling all coefficients by c scales the result
    (⟨fun i => c * f.coeffs i, f.sets⟩ : SimpleFunction n).spectralApply P =
    c • f.spectralApply P := by
  unfold SimpleFunction.spectralApply
  simp only [Finset.smul_sum, smul_smul]

/-- Weak bound on the operator norm of a simple function applied to a spectral measure.
    For a simple function f = Σᵢ cᵢ χ_{Eᵢ} with n terms, we have ‖Σᵢ cᵢ P(Eᵢ)‖ ≤ n * sup |cᵢ|.

    This uses the triangle inequality: ‖Σᵢ cᵢ P(Eᵢ)‖ ≤ Σᵢ |cᵢ| ‖P(Eᵢ)‖ ≤ n * M.

    NOTE: The tight bound ‖Σᵢ cᵢ P(Eᵢ)‖ ≤ sup |cᵢ| (independent of n) holds when
    the Eᵢ are disjoint, using orthogonality. See `proj_sum_norm_le_sup`. -/
theorem simple_spectralApply_norm_le {n : ℕ} (P : SpectralMeasure H) (f : SimpleFunction n)
    (M : ℝ) (hM : ∀ i, ‖f.coeffs i‖ ≤ M) :
    ‖f.spectralApply P‖ ≤ n * M := by
  unfold SimpleFunction.spectralApply
  calc ‖∑ i : Fin n, f.coeffs i • P.proj (f.sets i)‖
      ≤ ∑ i : Fin n, ‖f.coeffs i • P.proj (f.sets i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖f.coeffs i‖ * ‖P.proj (f.sets i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_smul_le _ _
    _ ≤ ∑ i : Fin n, ‖f.coeffs i‖ * 1 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (P.proj_opNorm_le_one _) (norm_nonneg _)
    _ = ∑ i : Fin n, ‖f.coeffs i‖ := by simp
    _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum (fun i _ => hM i)
    _ = n * M := by simp [Finset.sum_const]

/-- Approximate a bounded function by a simple function on a partition of [-N, N].
    For n subdivisions, we use intervals [k/n, (k+1)/n) for k = -nN, ..., nN-1. -/
def approximateBySimple (f : ℝ → ℂ) (N : ℕ) (n : ℕ) (_hn : n > 0) : SimpleFunction (2 * N * n) where
  coeffs := fun i =>
    let k : ℤ := i.val - N * n
    f (k / n)
  sets := fun i =>
    let k : ℤ := i.val - N * n
    Set.Ico (k / n) ((k + 1) / n)

/-- The spectral integral of a step function approximation.
    This applies the simple function to the spectral measure. -/
def stepApproximation (P : SpectralMeasure H) (f : ℝ → ℂ) (N n : ℕ) (hn : n > 0) : H →L[ℂ] H :=
  (approximateBySimple f N n hn).spectralApply P

/-! #### Polarization form helpers for functional calculus -/

section PolarizationHelpers

open MeasureTheory

variable (P : SpectralMeasure H) (f : ℝ → ℂ)

/-- The "quadratic form" Q(z) = ∫ f dμ_z underlying the polarization construction. -/
private def Qform (z : H) : ℂ := ∫ t, f t ∂(P.diagonalMeasure z)

/-- The polarization form B(x,y) = (1/4)[Q(x+y) - Q(x-y) - iQ(x+iy) + iQ(x-iy)]. -/
private def Bform (x y : H) : ℂ :=
  (1/4 : ℂ) * (Qform P f (x + y) - Qform P f (x - y)
    - Complex.I * Qform P f (x + Complex.I • y)
    + Complex.I * Qform P f (x - Complex.I • y))

/-- Q(-z) = Q(z) since μ_{-z} = μ_z (‖P(E)(-z)‖² = ‖P(E)z‖²). -/
private theorem Qform_neg (z : H) : Qform P f (-z) = Qform P f z := by
  simp only [Qform, P.diagonalMeasure_neg]

/-- Q(iz) = Q(z) (from diagonalMeasure_smul_I). -/
private theorem Qform_smul_I (z : H) : Qform P f (Complex.I • z) = Qform P f z := by
  simp only [Qform, P.diagonalMeasure_smul_I]

/-- The integral-level parallelogram identity:
    Q(u+v) + Q(u-v) = 2Q(u) + 2Q(v)
    Requires integrability of f against all relevant diagonal measures. -/
private theorem Qform_parallelogram (u v : H)
    (h_int_uv : Integrable f (P.diagonalMeasure (u + v)))
    (h_int_uv' : Integrable f (P.diagonalMeasure (u - v)))
    (h_int_u : Integrable f (P.diagonalMeasure u))
    (h_int_v : Integrable f (P.diagonalMeasure v)) :
    Qform P f (u + v) + Qform P f (u - v) =
    (2 : ℂ) * Qform P f u + (2 : ℂ) * Qform P f v := by
  simp only [Qform]
  -- Step 1: LHS = ∫f d(μ_{u+v} + μ_{u-v})
  rw [← integral_add_measure h_int_uv h_int_uv']
  -- Step 2: By diagonalMeasure_parallelogram, the measures are equal
  rw [P.diagonalMeasure_parallelogram u v]
  -- Step 3: RHS split: ∫f d(2•μ_u + 2•μ_v) = ∫f d(2•μ_u) + ∫f d(2•μ_v)
  --         = 2∫f dμ_u + 2∫f dμ_v
  have h_u2 : Integrable f ((2 : ℝ≥0) • P.diagonalMeasure u) :=
    h_int_u.smul_measure ENNReal.coe_ne_top
  have h_v2 : Integrable f ((2 : ℝ≥0) • P.diagonalMeasure v) :=
    h_int_v.smul_measure ENNReal.coe_ne_top
  rw [integral_add_measure h_u2 h_v2, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp only [Algebra.smul_def, map_ofNat]

/-- Integrability transfers through the parallelogram identity:
    if f is integrable against μ_u and μ_v, it's integrable against μ_{u+v}. -/
private theorem integrable_of_parallelogram (u v : H)
    (h_u : Integrable f (P.diagonalMeasure u))
    (h_v : Integrable f (P.diagonalMeasure v)) :
    Integrable f (P.diagonalMeasure (u + v)) := by
  -- μ_{u+v} ≤ μ_{u+v} + μ_{u-v} = 2•μ_u + 2•μ_v
  exact Integrable.mono_measure
    ((h_u.smul_measure ENNReal.coe_ne_top).add_measure
      (h_v.smul_measure ENNReal.coe_ne_top))
    (calc P.diagonalMeasure (u + v)
        ≤ P.diagonalMeasure (u + v) + P.diagonalMeasure (u - v) :=
          Measure.le_add_right le_rfl
      _ = (2 : ℝ≥0) • P.diagonalMeasure u + (2 : ℝ≥0) • P.diagonalMeasure v :=
        P.diagonalMeasure_parallelogram u v)

/-! ##### Additivity of the polarization form -/

/-- The "difference form" φ_x(y) = Q(x+y) - Q(x-y). -/
private def phi (x y : H) : ℂ := Qform P f (x + y) - Qform P f (x - y)

/-- φ_x(0) = 0. -/
private theorem phi_zero (x : H) : phi P f x 0 = 0 := by
  simp only [phi, add_zero, sub_zero, sub_self]

/-- φ_x(-y) = -φ_x(y). -/
private theorem phi_neg (x y : H) : phi P f x (-y) = -phi P f x y := by
  simp only [phi]
  have h1 : x - -y = x + y := by abel
  have h2 : x + -y = x - y := by abel
  rw [h1, show Qform P f (x + -y) = Qform P f (x - y) from by rw [h2]]
  ring

/-- The parallelogram-derived identity: φ_x(a+b) + φ_x(a-b) = 2φ_x(a).
    This comes from applying the Q-parallelogram to (x+a, b) and (x-a, b). -/
private theorem phi_parallelogram (x a b : H)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    phi P f x (a + b) + phi P f x (a - b) = (2 : ℂ) * phi P f x a := by
  simp only [phi]
  -- Expand: [Q(x+a+b) - Q(x-a-b)] + [Q(x+a-b) - Q(x-a+b)] = 2[Q(x+a) - Q(x-a)]
  -- Use Q-parallelogram with (u, v) = (x+a, b): Q(x+a+b) + Q(x+a-b) = 2Q(x+a) + 2Q(b)
  have h1 := Qform_parallelogram P f (x + a) b (h_int _) (h_int _) (h_int _) (h_int _)
  -- Use Q-parallelogram with (u, v) = (x-a, b): Q(x-a+b) + Q(x-a-b) = 2Q(x-a) + 2Q(b)
  have h2 := Qform_parallelogram P f (x - a) b (h_int _) (h_int _) (h_int _) (h_int _)
  -- Expand the vector arithmetic
  have e1 : x + a + b = x + (a + b) := by abel
  have e2 : x + a - b = x + (a - b) := by abel
  have e3 : x - a + b = x - (a - b) := by abel
  have e4 : x - a - b = x - (a + b) := by abel
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  -- From h1: Q(x+(a+b)) + Q(x+(a-b)) = 2Q(x+a) + 2Q(b)
  -- From h2: Q(x-(a-b)) + Q(x-(a+b)) = 2Q(x-a) + 2Q(b)
  -- Subtract h2 from h1:
  -- [Q(x+(a+b)) - Q(x-(a+b))] + [Q(x+(a-b)) - Q(x-(a-b))] = 2[Q(x+a) - Q(x-a)]
  linear_combination h1 - h2

/-- φ_x(2a) = 2φ_x(a) (doubling). -/
private theorem phi_double (x a : H)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    phi P f x (a + a) = (2 : ℂ) * phi P f x a := by
  have h := phi_parallelogram P f x a a h_int
  simp only [sub_self, phi_zero P f x, add_zero] at h
  exact h

/-- φ_x is additive: φ_x(u+v) = φ_x(u) + φ_x(v).
    Proof: substitute a = (u+v)/2, b = (u-v)/2 in the parallelogram identity,
    then use the doubling formula. -/
private theorem phi_additive (x u v : H)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    phi P f x (u + v) = phi P f x u + phi P f x v := by
  -- From phi_parallelogram with a = (1/2)(u+v), b = (1/2)(u-v):
  -- φ_x(u) + φ_x(v) = 2φ_x((1/2)(u+v))
  -- And φ_x(2·((1/2)(u+v))) = 2φ_x((1/2)(u+v)) = φ_x(u+v) [by doubling]
  let half : ℂ := 1/2
  let a := half • (u + v)
  let b := half • (u - v)
  have hab_sum : a + b = u := by
    show half • (u + v) + half • (u - v) = u
    rw [← smul_add]; simp [half]; module
  have hab_diff : a - b = v := by
    show half • (u + v) - half • (u - v) = v
    rw [← smul_sub]; simp [half]; module
  have h_para := phi_parallelogram P f x a b h_int
  rw [hab_sum, hab_diff] at h_para
  -- h_para : phi x u + phi x v = 2 * phi x a
  -- Also: a + a = u + v (since a = (u+v)/2)
  have h_aa : a + a = u + v := by
    show half • (u + v) + half • (u + v) = u + v
    rw [← add_smul]; simp [half]; module
  -- phi_double: phi x (a+a) = 2 * phi x a
  have h_dbl := phi_double P f x a h_int
  -- So phi x (u+v) = phi x (a+a) = 2 * phi x a = phi x u + phi x v
  rw [h_aa] at h_dbl
  linear_combination h_dbl - h_para

/-- φ is symmetric: φ_x(y) = φ_y(x). Uses Q(-z) = Q(z). -/
private theorem phi_symm (x y : H) : phi P f x y = phi P f y x := by
  simp only [phi]
  have h1 : Qform P f (x + y) = Qform P f (y + x) := by rw [add_comm]
  have h2 : Qform P f (x - y) = Qform P f (y - x) := by
    rw [show x - y = -(y - x) from by abel, Qform_neg]
  rw [h1, h2]

/-! ##### i-multiplication -/

/-- B(x, iy) = i * B(x, y) (purely algebraic from the definition). -/
private theorem Bform_smul_I (x y : H) :
    Bform P f x (Complex.I • y) = Complex.I * Bform P f x y := by
  simp only [Bform, Qform]
  have hIIy : Complex.I • (Complex.I • y) = -y := by
    rw [← mul_smul, Complex.I_mul_I]; simp
  have h1 : P.diagonalMeasure (x + Complex.I • (Complex.I • y)) =
      P.diagonalMeasure (x - y) := by congr 1; rw [hIIy]; abel
  have h2 : P.diagonalMeasure (x - Complex.I • (Complex.I • y)) =
      P.diagonalMeasure (x + y) := by congr 1; rw [hIIy]; abel
  simp_rw [h1, h2]
  ring_nf; simp only [Complex.I_sq]; ring

/-! ##### Additivity of B -/

/-- B is additive in the second argument: B(x, y₁+y₂) = B(x,y₁) + B(x,y₂). -/
private theorem Bform_add_right (x y₁ y₂ : H)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    Bform P f x (y₁ + y₂) = Bform P f x y₁ + Bform P f x y₂ := by
  have h_phi := phi_additive P f x y₁ y₂ h_int
  have h_psi : phi P f x (Complex.I • (y₁ + y₂)) =
      phi P f x (Complex.I • y₁) + phi P f x (Complex.I • y₂) := by
    rw [smul_add]; exact phi_additive P f x _ _ h_int
  -- Unfold everything uniformly in goal AND hypotheses
  simp only [Bform, phi, Qform] at *
  linear_combination (1 / 4 : ℂ) * h_phi - (1 / 4 : ℂ) * Complex.I * h_psi

/-! ##### Real homogeneity via additive + bounded -/

/-- An additive function ℝ → ℂ that is bounded on [0,1] is ℝ-linear: ψ(r) = r * ψ(1).
    Proof: ψ vanishes on ℤ after subtraction of the linear part,
    then bounded on ℝ (via integer shift), then ψ₀(r) = ψ₀(nr)/n → 0. -/
private theorem additive_bounded_linear (ψ : ℝ → ℂ)
    (h_add : ∀ r s, ψ (r + s) = ψ r + ψ s)
    (h_bdd : ∃ C : ℝ, ∀ r, |r| ≤ 1 → ‖ψ r‖ ≤ C) :
    ∀ r, ψ r = r * ψ 1 := by
  obtain ⟨C, hC⟩ := h_bdd
  -- Step 1: ψ(0) = 0
  have h0 : ψ 0 = 0 := by
    have h := h_add 0 0; simp at h; linear_combination h
  -- ψ(-r) = -ψ(r)
  have h_neg : ∀ r, ψ (-r) = -ψ r := by
    intro r; have h := h_add (-r) r; simp [h0] at h; linear_combination -h
  -- Step 2: ψ(n) = n * ψ(1) for n : ℕ
  have h_nat : ∀ n : ℕ, ψ n = n * ψ 1 := by
    intro n; induction n with
    | zero => simp [h0]
    | succ k ih =>
      have : ψ (↑(k + 1) : ℝ) = ψ (↑k + 1) := by push_cast; ring_nf
      rw [this, h_add, ih]; push_cast; ring
  -- ψ(n) = n * ψ(1) for n : ℤ
  have h_int : ∀ n : ℤ, ψ n = n * ψ 1 := by
    intro n
    cases n with
    | ofNat n => exact_mod_cast h_nat n
    | negSucc n =>
      rw [show (Int.negSucc n : ℝ) = -(↑(n + 1) : ℝ) from by push_cast; ring]
      rw [h_neg, h_nat]; push_cast; ring
  -- Step 3: Define ψ₀(r) = ψ(r) - r * ψ(1). Then ψ₀ is additive and ψ₀(n) = 0 for n : ℤ
  let ψ₀ := fun r => ψ r - r * ψ 1
  have hψ₀_def : ∀ r, ψ₀ r = ψ r - r * ψ 1 := fun _ => rfl
  have h0_add : ∀ r s, ψ₀ (r + s) = ψ₀ r + ψ₀ s := by
    intro r s; simp only [hψ₀_def]; rw [h_add]; push_cast; ring
  have h0_int : ∀ n : ℤ, ψ₀ n = 0 := by
    intro n; simp only [hψ₀_def]; rw [h_int]; push_cast; ring
  have h0_zero_val : ψ₀ 0 = 0 := by simpa using h0_int 0
  -- Step 4: ψ₀ bounded on [-1, 1]
  have h0_bdd_unit : ∀ r, |r| ≤ 1 → ‖ψ₀ r‖ ≤ C + ‖ψ 1‖ := by
    intro r hr
    simp only [hψ₀_def]
    calc ‖ψ r - ↑r * ψ 1‖
        ≤ ‖ψ r‖ + ‖↑r * ψ 1‖ := norm_sub_le _ _
      _ ≤ C + ‖↑r * ψ 1‖ := by linarith [hC r hr]
      _ = C + ‖(r : ℂ)‖ * ‖ψ 1‖ := by rw [norm_mul]
      _ = C + |r| * ‖ψ 1‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ C + 1 * ‖ψ 1‖ := by
          have : |r| * ‖ψ 1‖ ≤ 1 * ‖ψ 1‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
          linarith
      _ = C + ‖ψ 1‖ := by ring
  -- Step 5: ψ₀ bounded on all of ℝ
  have h0_bdd : ∀ r, ‖ψ₀ r‖ ≤ C + ‖ψ 1‖ := by
    intro r
    have h := h0_add (↑⌊r⌋) (r - ↑⌊r⌋)
    rw [show (↑⌊r⌋ : ℝ) + (r - ↑⌊r⌋) = r from by ring] at h
    rw [h, h0_int ⌊r⌋, zero_add]
    apply h0_bdd_unit
    rw [abs_le]
    exact ⟨by linarith [Int.floor_le r], by linarith [Int.lt_floor_add_one r]⟩
  -- Step 6: |n * ψ₀(r)| = |ψ₀(n*r)| ≤ C + ‖ψ 1‖, so ψ₀(r) = 0
  have h0_zero : ∀ r, ψ₀ r = 0 := by
    intro r
    by_contra hr
    have hpos : 0 < ‖ψ₀ r‖ := norm_pos_iff.mpr hr
    have h_nat_mul : ∀ n : ℕ, (n : ℂ) * ψ₀ r = ψ₀ (n * r) := by
      intro n; induction n with
      | zero => simp [show ψ₀ 0 = 0 from h0_zero_val]
      | succ k ih =>
        rw [show (↑(k + 1) : ℂ) * ψ₀ r = (↑k : ℂ) * ψ₀ r + ψ₀ r from by push_cast; ring]
        rw [ih, show (↑(k + 1) : ℝ) * r = ↑k * r + r from by push_cast; ring]
        exact (h0_add (↑k * r) r).symm
    have h_contra : ∀ n : ℕ, 0 < n → (n : ℝ) * ‖ψ₀ r‖ ≤ C + ‖ψ 1‖ := by
      intro n hn
      calc (n : ℝ) * ‖ψ₀ r‖ = ‖(n : ℂ) * ψ₀ r‖ := by
            rw [norm_mul, Complex.norm_natCast]
        _ = ‖ψ₀ (n * r)‖ := by rw [h_nat_mul]
        _ ≤ C + ‖ψ 1‖ := h0_bdd _
    -- n * ‖ψ₀ r‖ ≤ C + ‖ψ 1‖ for all n, but LHS → ∞
    obtain ⟨N, hN⟩ := exists_nat_gt ((C + ‖ψ 1‖) / ‖ψ₀ r‖)
    have hC_nn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by simp [abs_of_nonneg]))
    have hN_pos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with rfl | h
      · have h_nn : 0 ≤ (C + ‖ψ 1‖) / ‖ψ₀ r‖ :=
          div_nonneg (by linarith [norm_nonneg (ψ 1)]) hpos.le
        exact absurd (by exact_mod_cast hN : (C + ‖ψ 1‖) / ‖ψ₀ r‖ < (0 : ℝ)) (not_lt.mpr h_nn)
      · exact h
    have h_le := h_contra N hN_pos
    -- hN : (C + ‖ψ 1‖) / ‖ψ₀ r‖ < ↑N, i.e., C + ‖ψ 1‖ < N * ‖ψ₀ r‖
    have h_lt : C + ‖ψ 1‖ < ↑N * ‖ψ₀ r‖ := by
      rwa [div_lt_iff₀ hpos] at hN
    linarith
  -- Conclude: ψ r = r * ψ 1
  intro r
  have h := h0_zero r
  simp only [hψ₀_def] at h
  -- h : ψ r - ↑r * ψ 1 = 0
  linear_combination h

/-- φ_x(r•y) = r * φ_x(y) for r : ℝ (real homogeneity).
    Uses: φ_x is additive + bounded on the unit ball → ℝ-linear. -/
private theorem phi_real_homog (x y : H) (r : ℝ)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ t, ‖f t‖ ≤ M) :
    phi P f x ((r : ℂ) • y) = (r : ℂ) * phi P f x y := by
  -- Define ψ(s) = φ_x(s•y)
  let ψ : ℝ → ℂ := fun s => phi P f x ((s : ℂ) • y)
  -- ψ is additive
  have h_add : ∀ r s, ψ (r + s) = ψ r + ψ s := by
    intro r s
    show phi P f x ((↑(r + s) : ℂ) • y) = phi P f x ((↑r : ℂ) • y) + phi P f x ((↑s : ℂ) • y)
    rw [show (↑(r + s) : ℂ) • y = (↑r : ℂ) • y + (↑s : ℂ) • y from by
      rw [← add_smul]; push_cast; ring_nf]
    exact phi_additive P f x _ _ h_int
  -- ψ is bounded on [-1, 1]: |ψ(s)| ≤ 2M(‖x‖ + ‖y‖)²
  have h_bdd : ∃ C : ℝ, ∀ s, |s| ≤ 1 → ‖ψ s‖ ≤ C := by
    use 2 * M * (‖x‖ + ‖y‖) ^ 2
    intro s hs
    show ‖phi P f x ((s : ℂ) • y)‖ ≤ _
    simp only [phi]
    calc ‖Qform P f (x + (s : ℂ) • y) - Qform P f (x - (s : ℂ) • y)‖
        ≤ ‖Qform P f (x + (s : ℂ) • y)‖ + ‖Qform P f (x - (s : ℂ) • y)‖ := norm_sub_le _ _
      _ ≤ M * ‖x + (s : ℂ) • y‖ ^ 2 + M * ‖x - (s : ℂ) • y‖ ^ 2 := by
          apply add_le_add
          · exact P.integral_diagonalMeasure_norm_le _ f M hM hf
          · exact P.integral_diagonalMeasure_norm_le _ f M hM hf
      _ ≤ M * (‖x‖ + ‖y‖) ^ 2 + M * (‖x‖ + ‖y‖) ^ 2 := by
          have hnorm : ∀ z : H, ‖z‖ ≤ ‖x‖ + ‖y‖ → ‖z‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
            fun z h => pow_le_pow_left₀ (norm_nonneg z) h 2
          have hsy : |s| * ‖y‖ ≤ ‖y‖ := by
            calc |s| * ‖y‖ ≤ 1 * ‖y‖ :=
              mul_le_mul_of_nonneg_right hs (norm_nonneg y)
              _ = ‖y‖ := one_mul _
          have h_add_norm : ‖x + (s : ℂ) • y‖ ≤ ‖x‖ + ‖y‖ := by
            calc ‖x + (s : ℂ) • y‖ ≤ ‖x‖ + ‖(s : ℂ) • y‖ := norm_add_le _ _
              _ = ‖x‖ + |s| * ‖y‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
              _ ≤ ‖x‖ + ‖y‖ := by linarith
          have h_sub_norm : ‖x - (s : ℂ) • y‖ ≤ ‖x‖ + ‖y‖ := by
            calc ‖x - (s : ℂ) • y‖ ≤ ‖x‖ + ‖(s : ℂ) • y‖ := norm_sub_le _ _
              _ = ‖x‖ + |s| * ‖y‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
              _ ≤ ‖x‖ + ‖y‖ := by linarith
          apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ hM <;>
            [exact hnorm _ h_add_norm; exact hnorm _ h_sub_norm]
      _ = 2 * M * (‖x‖ + ‖y‖) ^ 2 := by ring
  -- Apply additive_bounded_linear
  have h_lin := additive_bounded_linear ψ h_add h_bdd r
  -- ψ(r) = r * ψ(1) = r * phi P f x (1 • y) = r * phi P f x y
  rw [show ψ r = phi P f x ((r : ℂ) • y) from rfl] at h_lin
  rw [show ψ 1 = phi P f x y from by show phi P f x ((1 : ℂ) • y) = _; simp] at h_lin
  exact h_lin

/-! ##### Real scalar homogeneity of B -/

/-- B(x, r•y) = r * B(x, y) for real r.
    Proof: Express B in terms of phi, apply phi_real_homog to each phi term, factor. -/
private theorem Bform_real_smul_right (x y : H) (r : ℝ)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ t, ‖f t‖ ≤ M) :
    Bform P f x ((r : ℂ) • y) = (r : ℂ) * Bform P f x y := by
  -- B(x, r•y) = (1/4)[phi(x,r•y) - I*phi(x,I•(r•y))]
  -- phi(x, r•y) = r * phi(x, y) and I•(r•y) = r•(I•y) so
  -- phi(x, r•(I•y)) = r * phi(x, I•y)
  -- Result: B(x,r•y) = r * B(x,y)
  have h1 := phi_real_homog P f x y r h_int M hM hf
  have h2 := phi_real_homog P f x (Complex.I • y) r h_int M hM hf
  have comm : Complex.I • ((r : ℂ) • y) = (r : ℂ) • (Complex.I • y) := smul_comm _ _ _
  simp only [Bform, phi] at h1 h2 ⊢
  rw [comm]
  -- h1: ∫f dμ_{x+(r:ℂ)•y} - ∫f dμ_{x-(r:ℂ)•y} = r * (∫f dμ_{x+y} - ∫f dμ_{x-y})
  -- h2: ∫f dμ_{x+(r:ℂ)•(I•y)} - ∫f dμ_{x-(r:ℂ)•(I•y)} = r * (∫f dμ_{x+I•y} - ∫f dμ_{x-I•y})
  -- Goal follows by ring arithmetic
  linear_combination (1 / 4 : ℂ) * h1 - (1 / 4 : ℂ) * Complex.I * h2

/-! ##### ℂ-homogeneity -/

/-- B is ℂ-linear in the second argument: B(x, c•y) = c * B(x, y).
    Proof: decompose c = c.re + c.im * I and use additivity + real homogeneity + i-mult. -/
private theorem Bform_smul_right (x y : H) (c : ℂ)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ t, ‖f t‖ ≤ M) :
    Bform P f x (c • y) = c * Bform P f x y := by
  -- Decompose c = c.re + c.im * I
  have hc_eq : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hc : c • y = (c.re : ℂ) • y + (c.im : ℂ) • (Complex.I • y) := by
    conv_lhs => rw [hc_eq]
    rw [add_smul, mul_smul]
  rw [hc, Bform_add_right P f x _ _ h_int]
  -- B(x, (re)•y) = re * B(x, y)
  rw [Bform_real_smul_right P f x y c.re h_int M hM hf]
  -- B(x, (im)•(I•y)) = im * B(x, I•y)
  rw [Bform_real_smul_right P f x (Complex.I • y) c.im h_int M hM hf]
  -- B(x, I•y) = I * B(x, y)
  rw [Bform_smul_I]
  -- Goal: ↑c.re * B + ↑c.im * (I * B) = c * B
  -- Rewrite c on RHS only, then ring handles distributivity
  conv_rhs => rw [hc_eq]
  ring

/-! ##### Additivity and conjugate-linearity in x -/

/-- B is additive in the first argument: B(x₁+x₂, y) = B(x₁, y) + B(x₂, y).
    Proof: same parallelogram argument as Bform_add_right but in the x variable. -/
private theorem Bform_add_left (x₁ x₂ y : H)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    Bform P f (x₁ + x₂) y = Bform P f x₁ y + Bform P f x₂ y := by
  -- Define rho_y(x) = Q(x+y) - Q(x-y), then rho_y is additive in x
  -- by the same parallelogram argument used for phi
  -- The "i" terms: Q(x+I•y) - Q(x-I•y) = rho_{I•y}(x), also additive in x
  -- Then B additivity follows from additivity of both rho terms
  let rho := fun z : H => Qform P f (z + y) - Qform P f (z - y)
  let sigma := fun z : H => Qform P f (z + Complex.I • y) - Qform P f (z - Complex.I • y)
  -- rho is additive in z (by parallelogram on z, with y fixed)
  have hrho_add : rho (x₁ + x₂) = rho x₁ + rho x₂ := by
    -- rho z = phi P f z y, and phi is symmetric, so rho z = phi P f y z
    -- phi_additive gives additivity in the second argument
    show phi P f (x₁ + x₂) y = phi P f x₁ y + phi P f x₂ y
    rw [phi_symm P f (x₁ + x₂) y, phi_symm P f x₁ y, phi_symm P f x₂ y]
    exact phi_additive P f y x₁ x₂ h_int
  have hsigma_add : sigma (x₁ + x₂) = sigma x₁ + sigma x₂ := by
    show phi P f (x₁ + x₂) (Complex.I • y) =
      phi P f x₁ (Complex.I • y) + phi P f x₂ (Complex.I • y)
    rw [phi_symm P f (x₁ + x₂) _, phi_symm P f x₁ _, phi_symm P f x₂ _]
    exact phi_additive P f (Complex.I • y) x₁ x₂ h_int
  -- B(x, y) = (1/4)[rho(x) - I*sigma(x)]
  -- B(x₁+x₂, y) = (1/4)[rho(x₁+x₂) - I*sigma(x₁+x₂)]
  --              = (1/4)[rho(x₁)+rho(x₂) - I*(sigma(x₁)+sigma(x₂))]
  --              = (1/4)[rho(x₁) - I*sigma(x₁)] + (1/4)[rho(x₂) - I*sigma(x₂)]
  --              = B(x₁, y) + B(x₂, y)
  -- Bform unfolds to (1/4)(rho - I*sigma), and rho/sigma are let bindings
  simp only [Bform]
  linear_combination (1 / 4 : ℂ) * hrho_add - (1 / 4 : ℂ) * Complex.I * hsigma_add

/-- B(c•x, y) = conj(c) * B(x, y) (conjugate-homogeneity in x).
    Proof: decompose c, use additive + real homog in x + the conjugation of I. -/
private theorem Bform_conj_smul_left (x y : H) (c : ℂ)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ t, ‖f t‖ ≤ M) :
    Bform P f (c • x) y = starRingEnd ℂ c * Bform P f x y := by
  -- Decompose c = re + im * I
  have hc_eq : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hc : c • x = (c.re : ℂ) • x + (c.im : ℂ) • (Complex.I • x) := by
    conv_lhs => rw [hc_eq]; rw [add_smul, mul_smul]
  -- Step 1: B additive in x
  rw [hc, Bform_add_left P f _ _ y h_int]
  -- Step 2: B(r•w, y) = r * B(w,y) for real r and any w, via phi_symm + phi_real_homog
  have hreal_left : ∀ (w : H) (r : ℝ), Bform P f ((r : ℂ) • w) y = (r : ℂ) * Bform P f w y := by
    intro w r; simp only [Bform]
    have h1 : phi P f ((r : ℂ) • w) y = (r : ℂ) * phi P f w y := by
      rw [phi_symm, phi_real_homog P f y w r h_int M hM hf, phi_symm]
    have h2 : phi P f ((r : ℂ) • w) (Complex.I • y) =
        (r : ℂ) * phi P f w (Complex.I • y) := by
      rw [phi_symm, phi_real_homog P f (Complex.I • y) w r h_int M hM hf, phi_symm]
    simp only [phi] at h1 h2 ⊢
    linear_combination (1 / 4 : ℂ) * h1 - (1 / 4 : ℂ) * Complex.I * h2
  rw [hreal_left x c.re]
  -- Step 3: B(I•x, y) = -I * B(x, y)
  -- Key identities: I•x+y = I•(x-I•y), I•x-y = I•(x+I•y), so Q swaps via Qform_smul_I
  have hI_left : Bform P f (Complex.I • x) y = -Complex.I * Bform P f x y := by
    simp only [Bform, Qform]
    have e1 : P.diagonalMeasure (Complex.I • x + y) =
        P.diagonalMeasure (x - Complex.I • y) := by
      conv_lhs => rw [show Complex.I • x + y = Complex.I • (x - Complex.I • y) from by
        rw [smul_sub, ← mul_smul, Complex.I_mul_I]; simp]
      exact P.diagonalMeasure_smul_I _
    have e2 : P.diagonalMeasure (Complex.I • x - y) =
        P.diagonalMeasure (x + Complex.I • y) := by
      conv_lhs => rw [show Complex.I • x - y = Complex.I • (x + Complex.I • y) from by
        rw [smul_add, ← mul_smul, Complex.I_mul_I]; simp [sub_eq_add_neg]]
      exact P.diagonalMeasure_smul_I _
    have e3 : P.diagonalMeasure (Complex.I • x + Complex.I • y) =
        P.diagonalMeasure (x + y) := by
      rw [show Complex.I • x + Complex.I • y = Complex.I • (x + y) from (smul_add _ _ _).symm]
      exact P.diagonalMeasure_smul_I _
    have e4 : P.diagonalMeasure (Complex.I • x - Complex.I • y) =
        P.diagonalMeasure (x - y) := by
      rw [show Complex.I • x - Complex.I • y = Complex.I • (x - y) from (smul_sub _ _ _).symm]
      exact P.diagonalMeasure_smul_I _
    simp_rw [e1, e2, e3, e4]
    ring_nf; simp only [Complex.I_sq]; ring
  -- Combine: B(re•x, y) + B(im•(I•x), y) = re*B(x,y) + im*(-I)*B(x,y)
  rw [hreal_left (Complex.I • x) c.im, hI_left]
  -- Goal: re*B + im*(-I*B) = starRingEnd ℂ c * B
  -- starRingEnd ℂ c = conj c = ↑c.re - ↑c.im * I
  have hstar : (starRingEnd ℂ) c = (↑c.re : ℂ) - ↑c.im * Complex.I := by
    simp only [starRingEnd_apply]
    apply Complex.ext <;> simp
  rw [hstar]; ring

/-! ##### Boundedness -/

/-- The sum-of-squares bound: |B(x,y)| ≤ M(‖x‖² + ‖y‖²) for bounded f. -/
private theorem Bform_sum_bound (x y : H) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ t, ‖f t‖ ≤ M) :
    ‖Bform P f x y‖ ≤ M * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  simp only [Bform, Qform]
  have h1 := P.integral_diagonalMeasure_norm_le (x + y) f M hM hf
  have h2 := P.integral_diagonalMeasure_norm_le (x - y) f M hM hf
  have h3 := P.integral_diagonalMeasure_norm_le (x + Complex.I • y) f M hM hf
  have h4 := P.integral_diagonalMeasure_norm_le (x - Complex.I • y) f M hM hf
  -- Parallelogram law: ‖a+b‖² + ‖a-b‖² = 2(‖a‖² + ‖b‖²)
  have hpara1 : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ x y; nlinarith [sq_nonneg ‖x + y‖, sq_nonneg ‖x - y‖,
      sq_nonneg ‖x‖, sq_nonneg ‖y‖, sq_abs ‖x + y‖, sq_abs ‖x - y‖, sq_abs ‖x‖, sq_abs ‖y‖]
  have hpara2 : ‖x + Complex.I • y‖ ^ 2 + ‖x - Complex.I • y‖ ^ 2 =
      2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ x (Complex.I • y)
    simp only [norm_smul, Complex.norm_I, one_mul] at this
    nlinarith [sq_nonneg ‖x + Complex.I • y‖, sq_nonneg ‖x - Complex.I • y‖,
      sq_nonneg ‖x‖, sq_nonneg ‖y‖]
  -- Triangle inequality: ‖(1/4) * (a - b - I*c + I*d)‖ ≤ (1/4)(‖a‖ + ‖b‖ + ‖c‖ + ‖d‖)
  calc ‖(1 / 4 : ℂ) * (∫ t, f t ∂P.diagonalMeasure (x + y) -
        ∫ t, f t ∂P.diagonalMeasure (x - y) -
        Complex.I * ∫ t, f t ∂P.diagonalMeasure (x + Complex.I • y) +
        Complex.I * ∫ t, f t ∂P.diagonalMeasure (x - Complex.I • y))‖
      ≤ ‖(1 / 4 : ℂ)‖ * ‖∫ t, f t ∂P.diagonalMeasure (x + y) -
        ∫ t, f t ∂P.diagonalMeasure (x - y) -
        Complex.I * ∫ t, f t ∂P.diagonalMeasure (x + Complex.I • y) +
        Complex.I * ∫ t, f t ∂P.diagonalMeasure (x - Complex.I • y)‖ := norm_mul_le _ _
    _ ≤ (1 / 4) * (‖∫ t, f t ∂P.diagonalMeasure (x + y)‖ +
        ‖∫ t, f t ∂P.diagonalMeasure (x - y)‖ +
        ‖∫ t, f t ∂P.diagonalMeasure (x + Complex.I • y)‖ +
        ‖∫ t, f t ∂P.diagonalMeasure (x - Complex.I • y)‖) := by
      have h14 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
      rw [h14]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      -- Use named variables for readability
      set a := ∫ t, f t ∂P.diagonalMeasure (x + y)
      set b := ∫ t, f t ∂P.diagonalMeasure (x - y)
      set c := ∫ t, f t ∂P.diagonalMeasure (x + Complex.I • y)
      set d := ∫ t, f t ∂P.diagonalMeasure (x - Complex.I • y)
      have hIc : ‖Complex.I * c‖ = ‖c‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      have hId : ‖Complex.I * d‖ = ‖d‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      calc ‖a - b - Complex.I * c + Complex.I * d‖
          ≤ ‖a - b - Complex.I * c‖ + ‖Complex.I * d‖ := norm_add_le _ _
        _ ≤ (‖a - b‖ + ‖Complex.I * c‖) + ‖Complex.I * d‖ := by
            linarith [norm_sub_le (a - b) (Complex.I * c)]
        _ ≤ (‖a‖ + ‖b‖ + ‖c‖) + ‖d‖ := by
            rw [hIc, hId]; linarith [norm_sub_le a b]
        _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by ring
    _ ≤ (1 / 4) * (M * ‖x + y‖ ^ 2 + M * ‖x - y‖ ^ 2 +
        M * ‖x + Complex.I • y‖ ^ 2 + M * ‖x - Complex.I • y‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = (1 / 4) * M * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 +
        (‖x + Complex.I • y‖ ^ 2 + ‖x - Complex.I • y‖ ^ 2)) := by ring
    _ = (1 / 4) * M * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by
      rw [hpara1, hpara2]
    _ = M * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by ring

/-- The product bound: |B(x,y)| ≤ 2M‖x‖‖y‖ for bounded f.
    Derivation: from the sum bound using B(0,y)=0, B(x,0)=0, and the scaling trick. -/
private theorem Bform_product_bound (M : ℝ) (hM : 0 ≤ M) (hf : ∀ t, ‖f t‖ ≤ M)
    (h_int : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    ∃ C : ℝ, ∀ x y : H, ‖Bform P f x y‖ ≤ C * ‖x‖ * ‖y‖ := by
  use 2 * M
  intro x y
  -- Strategy: for x≠0, y≠0, normalize to unit vectors using sesquilinearity,
  -- then apply the sum-of-squares bound with ‖x'‖=1, ‖y'‖=1.
  -- B(0,y) = 0 from Bform_conj_smul_left with c=0
  by_cases hx : x = 0
  · subst hx
    have : Bform P f 0 y = 0 := by
      have h := Bform_conj_smul_left P f y y 0 h_int M hM hf
      simp only [zero_smul, map_zero, zero_mul] at h; exact h
    simp [this]
  by_cases hy : y = 0
  · subst hy
    have : Bform P f x 0 = 0 := by
      have h := Bform_smul_right P f x x 0 h_int M hM hf
      simp only [zero_smul, zero_mul] at h; exact h
    simp [this]
  · -- Main case: x ≠ 0, y ≠ 0
    -- Let x' = (1/‖x‖)•x, y' = (1/‖y‖)•y so ‖x'‖ = 1, ‖y'‖ = 1
    have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    have hyn : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
    set x' := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hx'_def
    set y' := ((‖y‖⁻¹ : ℝ) : ℂ) • y with hy'_def
    have hx'_norm : ‖x'‖ = 1 := by
      simp [hx'_def, norm_smul, Complex.norm_real, inv_mul_cancel₀ hxn.ne']
    have hy'_norm : ‖y'‖ = 1 := by
      simp [hy'_def, norm_smul, Complex.norm_real, inv_mul_cancel₀ hyn.ne']
    -- B(x', y') = (1/‖x‖) * (1/‖y‖) * B(x, y) by sesquilinearity
    have hB_scale : Bform P f x' y' =
        ((‖x‖⁻¹ : ℝ) : ℂ) * (((‖y‖⁻¹ : ℝ) : ℂ) * Bform P f x y) := by
      rw [hx'_def, Bform_conj_smul_left P f x y' _ h_int M hM hf]
      congr 1
      · -- star (↑‖x‖⁻¹ : ℂ) = ↑‖x‖⁻¹ (real scalar)
        simp only [Complex.conj_ofReal]
      · rw [hy'_def, Bform_smul_right P f x y _ h_int M hM hf]
    -- From sum bound: ‖B(x', y')‖ ≤ M(‖x'‖² + ‖y'‖²) = M(1+1) = 2M
    have hbound := Bform_sum_bound P f x' y' M hM hf
    rw [hx'_norm, hy'_norm] at hbound
    simp only [one_pow] at hbound
    -- hbound : ‖B(x', y')‖ ≤ M * (1 + 1) = 2M
    -- B(x', y') = ‖x‖⁻¹ * ‖y‖⁻¹ * B(x, y), so ‖B(x,y)‖ ≤ 2M * ‖x‖ * ‖y‖
    rw [hB_scale, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxn), abs_of_pos (inv_pos.mpr hyn)] at hbound
    -- hbound : ‖x‖⁻¹ * (‖y‖⁻¹ * ‖Bform P f x y‖) ≤ M * (1 + 1)
    rw [inv_mul_le_iff₀ hxn] at hbound
    rw [inv_mul_le_iff₀ hyn] at hbound
    -- hbound : ‖Bform P f x y‖ ≤ ‖y‖ * (‖x‖ * (M * (1 + 1)))
    nlinarith

/-- Q_{star∘f}(z) = star(Q_f(z)): conjugating f conjugates the integral. -/
private theorem Qform_star (z : H) : Qform P (star ∘ f) z = star (Qform P f z) := by
  simp only [Qform, Function.comp]
  -- star on ℂ = conjugation commutes with Bochner integral
  exact _root_.integral_conj (f := f) (μ := P.diagonalMeasure z)

/-- The key symmetry identity for Bform under star:
    B_{star∘f}(x,y) = conj(B_f(y,x))
    This follows from:
    - Q_{star∘f}(z) = conj(Q_f(z)) (integral_conj)
    - Q(y+x) = Q(x+y) (add_comm)
    - Q(y-x) = Q(x-y) (Qform_neg)
    - Q(y+ix) = Q(x-iy) (y+ix = i(x-iy), then Qform_smul_I)
    - Q(y-ix) = Q(x+iy) (y-ix = -i(x+iy), then Qform_neg + Qform_smul_I) -/
private theorem Bform_star_swap (x y : H)
    (_hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    Bform P (star ∘ f) x y = starRingEnd ℂ (Bform P f y x) := by
  simp only [Bform]
  -- Step 1: Rewrite Qform (star ∘ f) using Qform_star
  simp_rw [Qform_star P f]
  -- Step 2: Rewrite Qform identities on RHS
  -- Q(y+x) = Q(x+y) by add_comm
  rw [show y + x = x + y from add_comm y x]
  -- Q(y-x) = Q(x-y) by Qform_neg
  rw [show Qform P f (y - x) = Qform P f (x - y) from by
    conv_lhs => rw [show y - x = -(x - y) from neg_sub x y ▸ rfl]; exact Qform_neg P f _]
  -- Q(y + ix) = Q(x - iy): y + ix = i(x - iy), then Qform_smul_I
  rw [show Qform P f (y + Complex.I • x) = Qform P f (x - Complex.I • y) from by
    conv_lhs => rw [show y + Complex.I • x = Complex.I • (x - Complex.I • y) from by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]; abel]
    exact Qform_smul_I P f _]
  -- Q(y - ix) = Q(x + iy): y - ix = -i(x + iy), then Qform_neg + Qform_smul_I
  rw [show Qform P f (y - Complex.I • x) = Qform P f (x + Complex.I • y) from by
    conv_lhs => rw [show y - Complex.I • x = -(Complex.I • (x + Complex.I • y)) from by
      rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]; abel]
    rw [Qform_neg]; exact Qform_smul_I P f _]
  -- Step 3: Now distribute starRingEnd ℂ over the arithmetic and close with ring
  -- RHS = star((1/4) * (Q(x+y) - Q(x-y) - I * Q(x-iy) + I * Q(x+iy)))
  -- After distribution: (1/4) * (star Q(x+y) - star Q(x-y) + I * star Q(x-iy) - I * star Q(x+iy))
  -- LHS = (1/4) * (star Q(x+y) - star Q(x-y) - I * star Q(x+iy) + I * star Q(x-iy))
  -- These are equal by commutativity of addition.
  set a := Qform P f (x + y)
  set b := Qform P f (x - y)
  set c := Qform P f (x + Complex.I • y)
  set d := Qform P f (x - Complex.I • y)
  -- Distribute star over the RHS
  show (1 / 4 : ℂ) * (star a - star b - Complex.I * star c + Complex.I * star d) =
    starRingEnd ℂ ((1 / 4 : ℂ) * (a - b - Complex.I * d + Complex.I * c))
  -- First, distribute starRingEnd ℂ and simplify specific values
  have h_expand : starRingEnd ℂ ((1 / 4 : ℂ) * (a - b - Complex.I * d + Complex.I * c)) =
    (1 / 4 : ℂ) * (star a - star b + Complex.I * star d - Complex.I * star c) := by
    simp only [starRingEnd_apply]
    rw [star_mul', star_add, star_sub, star_sub, star_mul', star_mul']
    have hstarI : star Complex.I = -Complex.I := by
      simp [Complex.conj_I]
    have hstar14 : star (1 / 4 : ℂ) = 1 / 4 := by
      simp
    rw [hstarI, hstar14]
    ring
  rw [h_expand]
  ring

/-! ##### Measure decomposition for Bform_comp_proj -/

/-- Key measure identity: μ_{u+P(F)v}(E) = μ_u(E\F) + μ_{u+v}(E∩F).
    This follows from the Pythagorean theorem:
    P(E)(u + P(F)v) = P(E\F)u + P(E∩F)(u + v)
    and these two terms are orthogonal (disjoint sets → orthogonal ranges). -/
private theorem diagonalMeasure_comp_proj_eq (F : Set ℝ) (hF : MeasurableSet F)
    (u v : H) (E : Set ℝ) (hE : MeasurableSet E) :
    (P.diagonalMeasure (u + P.proj F v) E).toReal =
    (P.diagonalMeasure u (E \ F)).toReal + (P.diagonalMeasure (u + v) (E ∩ F)).toReal := by
  -- Step 1: P(E)(u + P(F)v) = P(E)u + P(E∩F)v
  have hPE_decomp : P.proj E (u + P.proj F v) = P.proj E u + P.proj (E ∩ F) v := by
    rw [map_add, ← ContinuousLinearMap.comp_apply, P.inter E F hE hF]
  -- Step 2: P(E)u = P(E\F)u + P(E∩F)u (decompose E = (E\F) ∪ (E∩F))
  have hEdiff : E \ F ∪ (E ∩ F) = E := Set.diff_union_inter E F
  have hEdisj : Disjoint (E \ F) (E ∩ F) :=
    Set.disjoint_sdiff_left.mono_right Set.inter_subset_right
  have hPE_u : P.proj E u = P.proj (E \ F) u + P.proj (E ∩ F) u := by
    have h := P.additive_disjoint (E \ F) (E ∩ F) (hE.diff hF) (hE.inter hF) hEdisj
    rw [hEdiff] at h; rw [h]; simp
  -- Step 3: P(E)(u + P(F)v) = P(E\F)u + (P(E∩F)u + P(E∩F)v)
  --                          = P(E\F)u + P(E∩F)(u+v)
  have hPE_sum : P.proj E (u + P.proj F v) = P.proj (E \ F) u + P.proj (E ∩ F) (u + v) := by
    rw [hPE_decomp, hPE_u, map_add]; abel
  -- Step 4: These two terms are orthogonal (E\F and E∩F are disjoint)
  have horth : @inner ℂ H _ (P.proj (E \ F) u) (P.proj (E ∩ F) (u + v)) = 0 := by
    -- ⟨P(E\F)u, P(E∩F)(u+v)⟩ = ⟨u, P(E\F)* P(E∩F)(u+v)⟩ = ⟨u, P(E\F)P(E∩F)(u+v)⟩
    -- P(E\F)P(E∩F) = P((E\F)∩(E∩F)) = P(∅) = 0
    have hinter_empty : (E \ F) ∩ (E ∩ F) = ∅ :=
      (Set.disjoint_sdiff_left.mono_right Set.inter_subset_right).inter_eq
    calc @inner ℂ H _ (P.proj (E \ F) u) (P.proj (E ∩ F) (u + v))
        = @inner ℂ H _ u ((P.proj (E \ F)).adjoint (P.proj (E ∩ F) (u + v))) :=
          (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = @inner ℂ H _ u (P.proj (E \ F) (P.proj (E ∩ F) (u + v))) := by
          rw [P.isSelfAdj _ (hE.diff hF)]
      _ = @inner ℂ H _ u ((P.proj (E \ F) ∘L P.proj (E ∩ F)) (u + v)) := rfl
      _ = @inner ℂ H _ u (P.proj ((E \ F) ∩ (E ∩ F)) (u + v)) := by
          rw [← P.inter _ _ (hE.diff hF) (hE.inter hF)]
      _ = 0 := by rw [hinter_empty, P.empty]; simp
  -- Step 5: Pythagorean theorem: ‖a + b‖² = ‖a‖² + ‖b‖² when ⟨a,b⟩ = 0
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  -- Step 6: Convert to diagonal measure
  rw [P.diagonalMeasure_apply_norm_sq _ E hE, hPE_sum]
  rw [show ‖P.proj (E \ F) u + P.proj (E ∩ F) (u + v)‖ ^ 2 =
    ‖P.proj (E \ F) u‖ ^ 2 + ‖P.proj (E ∩ F) (u + v)‖ ^ 2 from by rw [sq, sq, sq, hpyth]]
  rw [← P.diagonalMeasure_apply_norm_sq u (E \ F) (hE.diff hF),
      ← P.diagonalMeasure_apply_norm_sq (u + v) (E ∩ F) (hE.inter hF)]

/-- The Qform integral decomposes: ∫f dμ_{u+P(F)v} = ∫_{ℝ\F} f dμ_u + ∫_F f dμ_{u+v}.
    This is the integral-level consequence of diagonalMeasure_comp_proj_eq. -/
private theorem Qform_comp_proj_eq (F : Set ℝ) (hF : MeasurableSet F)
    (u v : H) (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    Qform P f (u + P.proj F v) =
    ∫ t in (Set.univ \ F), f t ∂(P.diagonalMeasure u) +
    ∫ t in F, f t ∂(P.diagonalMeasure (u + v)) := by
  simp only [Qform]
  -- The measures agree on all measurable sets by diagonalMeasure_comp_proj_eq
  -- So the integrals agree
  -- μ_{u+P(F)v} = μ_u|_{ℝ\F} + μ_{u+v}|_F  (as measures)
  -- We prove this by showing the measures are equal, then use integral equality
  have h_meas_eq : P.diagonalMeasure (u + P.proj F v) =
      (P.diagonalMeasure u).restrict (Set.univ \ F) +
      (P.diagonalMeasure (u + v)).restrict F := by
    ext E hE
    simp only [MeasureTheory.Measure.add_apply,
        MeasureTheory.Measure.restrict_apply hE]
    -- Both sides are ENNReal, use toReal injectivity (all values finite)
    haveI := P.diagonalMeasure_isFiniteMeasure (u + P.proj F v)
    haveI := P.diagonalMeasure_isFiniteMeasure u
    haveI := P.diagonalMeasure_isFiniteMeasure (u + v)
    have h_finite_lhs := MeasureTheory.measure_lt_top (P.diagonalMeasure (u + P.proj F v)) E
    have h_finite_rhs1 := MeasureTheory.measure_lt_top (P.diagonalMeasure u) (E ∩ (Set.univ \ F))
    have h_finite_rhs2 := MeasureTheory.measure_lt_top (P.diagonalMeasure (u + v)) (E ∩ F)
    rw [← ENNReal.toReal_eq_toReal_iff' h_finite_lhs.ne (ENNReal.add_lt_top.mpr
        ⟨h_finite_rhs1, h_finite_rhs2⟩).ne,
        ENNReal.toReal_add h_finite_rhs1.ne h_finite_rhs2.ne]
    have h_sets : E ∩ (Set.univ \ F) = E \ F := by ext t; simp [Set.mem_diff]
    rw [h_sets, diagonalMeasure_comp_proj_eq P F hF u v E hE]
  rw [h_meas_eq]
  exact integral_add_measure ((hf_int _).restrict) ((hf_int _).restrict)

/-- **Key lemma for functionalCalculus_mul**: Bform P f x (P(F)y) = Bform P (f · χ_F) x y.
    Proof: Each of the 4 polarization terms has a common "remainder" ∫_{ℝ\F} f dμ_x,
    and the polarization coefficients (1, -1, -i, +i) sum to 0. -/
private theorem Bform_comp_proj (F : Set ℝ) (hF : MeasurableSet F)
    (x y : H) (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    Bform P f x (P.proj F y) = Bform P (fun t => f t * F.indicator (fun _ => 1) t) x y := by
  simp only [Bform]
  -- Apply Qform_comp_proj_eq to each of the 4 terms
  -- For the substitutions: P(F)y, P(F)(-y) = -(P(F)y), P(F)(iy), P(F)(-iy) = -(P(F)(iy))
  have h1 := Qform_comp_proj_eq P f F hF x y hf_int
  have h2 : Qform P f (x + P.proj F (-y)) =
      ∫ t in (Set.univ \ F), f t ∂(P.diagonalMeasure x) +
      ∫ t in F, f t ∂(P.diagonalMeasure (x + (-y))) :=
    Qform_comp_proj_eq P f F hF x (-y) hf_int
  have h3 : Qform P f (x + P.proj F (Complex.I • y)) =
      ∫ t in (Set.univ \ F), f t ∂(P.diagonalMeasure x) +
      ∫ t in F, f t ∂(P.diagonalMeasure (x + Complex.I • y)) :=
    Qform_comp_proj_eq P f F hF x (Complex.I • y) hf_int
  have h4 : Qform P f (x + P.proj F (-(Complex.I • y))) =
      ∫ t in (Set.univ \ F), f t ∂(P.diagonalMeasure x) +
      ∫ t in F, f t ∂(P.diagonalMeasure (x + -(Complex.I • y))) :=
    Qform_comp_proj_eq P f F hF x (-(Complex.I • y)) hf_int
  -- Rewrite: P(F)(-y) = -(P(F)y), etc.
  rw [map_neg] at h2; rw [map_neg] at h4
  -- Rewrite goal to match h1-h4 and eliminate Qform terms
  have e1 : x - P.proj F y = x + -(P.proj F y) := sub_eq_add_neg _ _
  have e2 : Complex.I • P.proj F y = P.proj F (Complex.I • y) := (map_smul _ _ _).symm
  -- First rewrite goal structure, then substitute the decompositions
  conv_lhs => rw [e1, e2]
  -- After e2, the 4th term is x - P.proj F (Complex.I • y); rewrite sub to add neg
  have e3 : x - P.proj F (Complex.I • y) = x + -(P.proj F (Complex.I • y)) := sub_eq_add_neg _ _
  conv_lhs => rw [e3]
  rw [h1, h2, h3, h4]
  -- Rewrite: x + (-y) = x - y, x + -(I•y) = x - I•y
  have : x + -y = x - y := by abel
  rw [this]
  have : x + -(Complex.I • y) = x - Complex.I • y := by abel
  rw [this]
  -- The remainders ∫_{ℝ\F} f dμ_x cancel via (1 - 1 - i + i) = 0
  -- And the set integrals equal indicator integrals
  have h_ind : ∀ z : H, ∫ t in F, f t ∂(P.diagonalMeasure z) =
      ∫ t, (fun t => f t * F.indicator (fun _ => 1) t) t ∂(P.diagonalMeasure z) := by
    intro z
    rw [← MeasureTheory.integral_indicator hF]
    congr 1; ext t
    simp only [Set.indicator]; split_ifs <;> ring
  simp_rw [h_ind]
  -- Unfold Qform on the RHS so ring can match
  simp only [Qform]
  ring

end PolarizationHelpers

/-! ### Indicator-Projection Lemmas -/

/-- For a spectral measure, ⟨z, P(F)z⟩ has zero imaginary part.
    Proof: P(F) self-adjoint + idempotent gives ⟨z, P(F)z⟩ = ⟨P(F)z, P(F)z⟩ = ‖P(F)z‖² ∈ ℝ. -/
theorem SpectralMeasure.inner_proj_real (P : SpectralMeasure H)
    (z : H) (F : Set ℝ) (hF : MeasurableSet F) :
    (@inner ℂ H _ z (P.proj F z)).im = 0 := by
  -- conj ⟨z, P(F)z⟩ = ⟨P(F)z, z⟩ = ⟨P(F)†z, z⟩ = ⟨z, P(F)z⟩
  -- So conj w = w, hence im w = 0
  suffices hconj : starRingEnd ℂ (@inner ℂ H _ z (P.proj F z)) =
      @inner ℂ H _ z (P.proj F z) by
    exact Complex.conj_eq_iff_im.mp hconj
  rw [inner_conj_symm]  -- Goal: ⟨P(F)z, z⟩ = ⟨z, P(F)z⟩
  have h := ContinuousLinearMap.adjoint_inner_left (P.proj F) z z
  -- h : ⟨P(F)†z, z⟩ = ⟨z, P(F)z⟩
  rw [P.isSelfAdj F hF] at h
  -- h : ⟨P(F)z, z⟩ = ⟨z, P(F)z⟩
  exact h

open MeasureTheory in
/-- For an indicator function, the Qform equals the inner product with the projection.
    Proof: ∫ χ_F dμ_z = μ_z(F).toReal = ⟨z, P(F)z⟩.re = ⟨z, P(F)z⟩ (since P(F) self-adjoint). -/
theorem SpectralMeasure.Qform_indicator_eq_inner (P : SpectralMeasure H)
    (F : Set ℝ) (hF : MeasurableSet F) (z : H) :
    Qform P (Set.indicator F (fun _ => (1 : ℂ))) z = @inner ℂ H _ z (P.proj F z) := by
  simp only [Qform]
  -- Step 1: ∫ χ_F dμ_z = ↑(μ_z(F).toReal) via integral_indicator_const
  have h_eq : ∫ t, Set.indicator F (fun _ => (1 : ℂ)) t ∂(P.diagonalMeasure z) =
      ↑(P.diagonalMeasure z F).toReal := by
    rw [integral_indicator_const _ hF, Measure.real]
    simp [Algebra.smul_def]
  rw [h_eq]
  -- Step 2: μ_z(F).toReal = ⟨z, P(F)z⟩.re
  rw [P.diagonalMeasure_apply z F hF]
  -- Step 3: ↑(⟨z, P(F)z⟩.re) = ⟨z, P(F)z⟩ (P(F) self-adjoint → inner product is real)
  apply Complex.ext
  · exact Complex.ofReal_re _
  · rw [Complex.ofReal_im]; exact (P.inner_proj_real z F hF).symm

omit [CompleteSpace H] in
/-- The polarization identity for a continuous linear map A on a Hilbert space:
    (1/4)(⟨x+y, A(x+y)⟩ - ⟨x-y, A(x-y)⟩ - i⟨x+iy, A(x+iy)⟩ + i⟨x-iy, A(x-iy)⟩) = ⟨x, Ay⟩.
    This is the standard identity relating quadratic forms to sesquilinear forms. -/
theorem inner_polarization_clm (A : H →L[ℂ] H) (x y : H) :
    (1/4 : ℂ) * (@inner ℂ H _ (x + y) (A (x + y)) - @inner ℂ H _ (x - y) (A (x - y))
      - Complex.I * @inner ℂ H _ (x + Complex.I • y) (A (x + Complex.I • y))
      + Complex.I * @inner ℂ H _ (x - Complex.I • y) (A (x - Complex.I • y))) =
    @inner ℂ H _ x (A y) := by
  -- Introduce abbreviations
  set a := @inner ℂ H _ x (A x)
  set b := @inner ℂ H _ x (A y)
  set c := @inner ℂ H _ y (A x)
  set d := @inner ℂ H _ y (A y)
  -- Expand each of the 4 inner products
  have h1 : @inner ℂ H _ (x + y) (A (x + y)) = a + b + c + d := by
    rw [map_add]; simp only [inner_add_left, inner_add_right]; ring
  have h2 : @inner ℂ H _ (x - y) (A (x - y)) = a - b - c + d := by
    rw [map_sub]; simp only [inner_sub_left, inner_sub_right]; ring
  -- For the Complex.I terms, expand and simplify conj(I) = -I, I² = -1
  have hI_sq : Complex.I ^ 2 = (-1 : ℂ) := Complex.I_sq
  have h3 : @inner ℂ H _ (x + Complex.I • y) (A (x + Complex.I • y)) =
      a + Complex.I * b - Complex.I * c + d := by
    rw [map_add, map_smul]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I]
    ring_nf; rw [hI_sq]; ring
  have h4 : @inner ℂ H _ (x - Complex.I • y) (A (x - Complex.I • y)) =
      a - Complex.I * b + Complex.I * c + d := by
    rw [map_sub, map_smul]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
    ring_nf; rw [hI_sq]; ring
  rw [h1, h2, h3, h4]; ring_nf; rw [hI_sq]; ring

open MeasureTheory in
/-- For an indicator function, the Bform equals the inner product with the projection:
    Bform P χ_F x y = ⟨x, P(F) y⟩.
    This combines `Qform_indicator_eq_inner` with the polarization identity. -/
theorem SpectralMeasure.Bform_indicator_eq_inner (P : SpectralMeasure H)
    (F : Set ℝ) (hF : MeasurableSet F) (x y : H) :
    Bform P (Set.indicator F (fun _ => (1 : ℂ))) x y = @inner ℂ H _ x (P.proj F y) := by
  -- Substitute Qform = inner product with projection
  simp only [Bform, P.Qform_indicator_eq_inner F hF]
  -- Now the goal is the polarization identity for A = P.proj F
  exact inner_polarization_clm (P.proj F) x y

/-! ### Spectral Integral -/

open MeasureTheory in
/-- The spectral integral `∫ f(λ) d⟨x, P(dλ)y⟩` for a spectral measure P,
    defined via polarization of diagonal measures:

    `∫ f d⟨x, Py⟩ = (1/4)[∫f dμ_{x+y} - ∫f dμ_{x-y} - i∫f dμ_{x+iy} + i∫f dμ_{x-iy}]`

    where `μ_z(E) = ‖P(E)z‖²` is the diagonal spectral measure. -/
noncomputable def SpectralMeasure.spectralIntegral (P : SpectralMeasure H)
    (f : ℝ → ℂ) (x y : H) : ℂ :=
  (1/4 : ℂ) * (∫ t, f t ∂(P.diagonalMeasure (x + y))
    - ∫ t, f t ∂(P.diagonalMeasure (x - y))
    - Complex.I * ∫ t, f t ∂(P.diagonalMeasure (x + Complex.I • y))
    + Complex.I * ∫ t, f t ∂(P.diagonalMeasure (x - Complex.I • y)))

open MeasureTheory in
/-- For a spectral measure, construct the functional calculus via sesquilinear form.
    f(T) = ∫ f(λ) dP(λ) is constructed using the Riesz representation theorem:

    The sesquilinear form B_f(x,y) = ∫ f dμ_{x,y} (where μ_{x,y} is the complex spectral
    measure, constructed via polarization of diagonal measures) is bounded:
      |B_f(x,y)| ≤ ‖f‖_∞ · ‖x‖ · ‖y‖
    By `sesquilinearToOperator`, there exists a unique operator f(T) with
      ⟨x, f(T) y⟩ = B_f(x,y) = ∫ f(λ) d⟨x, P(·)y⟩(λ)

    Requires: f is integrable against all diagonal spectral measures, and
    f is bounded (for the operator norm bound).

    Key properties:
    1. ∫ χ_E dP = P(E) for measurable E (characteristic property)
    2. ‖∫ f dP‖ ≤ sup |f| (operator norm bound)
    3. ∫ fg dP = (∫ f dP)(∫ g dP) (multiplicativity, Reed-Simon VIII.5b)
    4. (∫ f dP)* = ∫ f̄ dP (adjoint property, Reed-Simon VIII.5c) -/
def functionalCalculus (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M) : H →L[ℂ] H :=
  sesquilinearToOperator (Bform P f)
    (fun x => {
      map_add := fun y₁ y₂ => Bform_add_right P f x y₁ y₂ hf_int
      map_smul := fun c y => by
        rw [smul_eq_mul]
        exact Bform_smul_right P f x y c hf_int
          hf_bdd.choose hf_bdd.choose_spec.1 hf_bdd.choose_spec.2 })
    (fun y c x₁ x₂ => by
      rw [show Bform P f (c • x₁ + x₂) y = Bform P f (c • x₁) y + Bform P f x₂ y
        from Bform_add_left P f _ _ y hf_int]
      congr 1
      exact Bform_conj_smul_left P f x₁ y c hf_int
        hf_bdd.choose hf_bdd.choose_spec.1 hf_bdd.choose_spec.2)
    (Bform_product_bound P f hf_bdd.choose hf_bdd.choose_spec.1
      hf_bdd.choose_spec.2 hf_int)

open MeasureTheory in
/-- The defining property of functionalCalculus: B_f(x,y) = ⟨x, f(T) y⟩. -/
theorem functionalCalculus_inner (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (x y : H) :
    Bform P f x y = @inner ℂ H _ x (functionalCalculus P f hf_int hf_bdd y) := by
  unfold functionalCalculus
  exact sesquilinearToOperator_inner (Bform P f) _ _ _ x y

open MeasureTheory in
/-- **Polarization diagonal identity**: ⟨x, f(T)x⟩ = ∫ f dμ_x.

    This is the key bridge between the inner product with the functional calculus
    and the diagonal spectral integral. The proof uses the polarization formula
    B(x,x) = Q(x), which holds because Q is a genuine quadratic form:
    - Q(0) = 0 (integral against zero measure)
    - Q(2x) = 4Q(x) (parallelogram with u = v = x)
    - Q(x+ix) = Q(x-ix) = 2Q(x) (from Q(ix) = Q(x) and parallelogram)
    So B(x,x) = (1/4)[4Q(x) - 0 - i·2Q(x) + i·2Q(x)] = Q(x). -/
theorem functionalCalculus_inner_self (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (x : H) :
    @inner ℂ H _ x (functionalCalculus P f hf_int hf_bdd x) =
    ∫ t, f t ∂(P.diagonalMeasure x) := by
  rw [← functionalCalculus_inner P f hf_int hf_bdd x x]
  -- Goal: Bform P f x x = Qform P f x
  -- Only unfold Bform, keep Qform opaque so Qform_smul_I etc. apply
  simp only [Bform]
  -- Q(0) = 0: from parallelogram with u = v = 0, we get 2Q(0) = 4Q(0)
  have hQ0 : Qform P f (0 : H) = 0 := by
    have hpar := Qform_parallelogram P f 0 0 (hf_int _) (hf_int _) (hf_int _) (hf_int _)
    simp only [add_zero, sub_self] at hpar
    linear_combination (-1/2 : ℂ) * hpar
  -- Q(2x) = 4Q(x): from parallelogram with u = v = x
  have hQ2x : Qform P f (x + x) = (4 : ℂ) * Qform P f x := by
    have hpar := Qform_parallelogram P f x x (hf_int _) (hf_int _) (hf_int _) (hf_int _)
    simp only [sub_self] at hpar
    rw [hQ0, add_zero] at hpar
    linear_combination hpar
  -- Q(x+ix) = Q(x-ix): since i·(x-ix) = x+ix, by Qform_smul_I
  have hQsym : Qform P f (x + Complex.I • x) = Qform P f (x - Complex.I • x) := by
    have key : Complex.I • (x - Complex.I • x) = x + Complex.I • x := by
      simp [smul_sub, smul_smul, Complex.I_mul_I]; abel
    rw [show x + Complex.I • x = Complex.I • (x - Complex.I • x) from key.symm]
    exact Qform_smul_I P f (x - Complex.I • x)
  -- Q(x+ix) + Q(x-ix) = 4Q(x): parallelogram with v = ix, plus Q(ix) = Q(x)
  have hQsum : Qform P f (x + Complex.I • x) + Qform P f (x - Complex.I • x) =
      (4 : ℂ) * Qform P f x := by
    have hpar := Qform_parallelogram P f x (Complex.I • x)
      (hf_int _) (hf_int _) (hf_int _) (hf_int _)
    rw [Qform_smul_I P f x] at hpar
    linear_combination hpar
  -- Therefore Q(x+ix) = 2Q(x)
  have hQix : Qform P f (x + Complex.I • x) = (2 : ℂ) * Qform P f x := by
    linear_combination (1/2 : ℂ) * hQsum + (1/2 : ℂ) * hQsym
  -- B(x,x) = (1/4)[Q(2x) - Q(0) - iQ(x+ix) + iQ(x-ix)]
  --   = (1/4)[4Q(x) - 0 - i·2Q(x) + i·2Q(x)] = Q(x)
  rw [show x - x = (0 : H) from sub_self x, hQ0, hQ2x, ← hQsym, hQix]
  simp only [Qform]
  ring

/-! ### Functional Calculus Helper Lemmas -/

open MeasureTheory in
/-- The functional calculus of an indicator function equals the spectral projection. -/
theorem functionalCalculus_indicator (P : SpectralMeasure H) (F : Set ℝ) (hF : MeasurableSet F)
    (hint : ∀ z : H, Integrable (F.indicator (fun _ => (1 : ℂ))) (P.diagonalMeasure z))
    (hbdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖F.indicator (fun _ => (1 : ℂ)) t‖ ≤ M) :
    functionalCalculus P (F.indicator (fun _ => (1 : ℂ))) hint hbdd = P.proj F := by
  apply ContinuousLinearMap.ext; intro y
  apply ext_inner_left ℂ; intro x
  rw [← functionalCalculus_inner]
  exact P.Bform_indicator_eq_inner F hF x y

open MeasureTheory in
/-- Linearity of Bform in f (addition): B_{f₁+f₂}(x,y) = B_{f₁}(x,y) + B_{f₂}(x,y). -/
private theorem Bform_add_f (P : SpectralMeasure H) (f₁ f₂ : ℝ → ℂ) (x y : H)
    (h1 : ∀ z : H, Integrable f₁ (P.diagonalMeasure z))
    (h2 : ∀ z : H, Integrable f₂ (P.diagonalMeasure z)) :
    Bform P (f₁ + f₂) x y = Bform P f₁ x y + Bform P f₂ x y := by
  simp only [Bform, Qform, Pi.add_apply]
  simp_rw [integral_add (h1 _) (h2 _)]
  ring

open MeasureTheory in
/-- Linearity of Bform in f (scalar): B_{c·f}(x,y) = c · B_f(x,y). -/
private theorem Bform_smul_f (P : SpectralMeasure H) (c : ℂ) (f : ℝ → ℂ) (x y : H)
    (_hf : ∀ z : H, Integrable f (P.diagonalMeasure z)) :
    Bform P (fun t => c * f t) x y = c * Bform P f x y := by
  simp only [Bform, Qform]
  have hI : ∀ z, ∫ t, c * f t ∂(P.diagonalMeasure z) =
      c * ∫ t, f t ∂(P.diagonalMeasure z) := by
    intro z
    have : (fun t => c * f t) = fun t => c • f t := funext (fun t => (smul_eq_mul c (f t)).symm)
    rw [this, integral_smul, smul_eq_mul]
  simp_rw [hI]
  ring

open MeasureTheory in
/-- Key multiplicative identity for indicators: Bform P (f · 1_F) x y = Bform P 1_F (fT†x) y.
    Chain: Bform_comp_proj → functionalCalculus_inner → adjoint → Bform_indicator_eq_inner. -/
private theorem Bform_mul_indicator (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (F : Set ℝ) (hF : MeasurableSet F) (x y : H) :
    Bform P (fun t => f t * F.indicator (fun _ => (1 : ℂ)) t) x y =
    Bform P (F.indicator (fun _ => (1 : ℂ)))
      ((functionalCalculus P f hf_int hf_bdd).adjoint x) y := by
  calc Bform P (fun t => f t * F.indicator (fun _ => (1 : ℂ)) t) x y
      = Bform P f x (P.proj F y) :=
        (Bform_comp_proj P f F hF x y hf_int).symm
    _ = @inner ℂ H _ x (functionalCalculus P f hf_int hf_bdd (P.proj F y)) :=
        functionalCalculus_inner P f hf_int hf_bdd x (P.proj F y)
    _ = @inner ℂ H _ ((functionalCalculus P f hf_int hf_bdd).adjoint x) (P.proj F y) :=
        (ContinuousLinearMap.adjoint_inner_left _ (P.proj F y) x).symm
    _ = Bform P (F.indicator (fun _ => (1 : ℂ)))
          ((functionalCalculus P f hf_int hf_bdd).adjoint x) y :=
        (P.Bform_indicator_eq_inner F hF _ y).symm

open MeasureTheory in
/-- The functional calculus is multiplicative: (fg)(T) = f(T)g(T)

    **Reference:** Reed-Simon Theorem VIII.5(b)

    **Proof strategy:**
    1. Reduce to showing Bform P (f*g) x y = Bform P f x (g(T)y) for all x, y.
    2. For g = χ_F (indicator): follows from `Bform_comp_proj`.
    3. For general g: approximate by simple gₙ → g pointwise (|gₙ| ≤ M).
       - For each simple gₙ: decompose gₙ = Σ cⱼ χ_{Eⱼ}, use indicator case + linearity.
       - LHS: Bform P (f·gₙ) x y → Bform P (f·g) x y by DCT.
       - RHS: ⟨f(T)*x, gₙ(T)y⟩ → ⟨f(T)*x, g(T)y⟩ by DCT (weak convergence). -/
theorem functionalCalculus_mul (P : SpectralMeasure H) (f g : ℝ → ℂ)
    (hf_int : ∀ z : H, MeasureTheory.Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hg_int : ∀ z : H, MeasureTheory.Integrable g (P.diagonalMeasure z))
    (hg_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖g t‖ ≤ M)
    (hfg_int : ∀ z : H, MeasureTheory.Integrable (f * g) (P.diagonalMeasure z))
    (hfg_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(f * g) t‖ ≤ M)
    (hg_meas : Measurable g) :
    functionalCalculus P (f * g) hfg_int hfg_bdd =
    functionalCalculus P f hf_int hf_bdd ∘L functionalCalculus P g hg_int hg_bdd := by
  apply ContinuousLinearMap.ext; intro y
  apply ext_inner_left ℂ; intro x
  rw [ContinuousLinearMap.comp_apply,
      ← functionalCalculus_inner P (f * g), ← functionalCalculus_inner P f]
  -- Goal: Bform P (f * g) x y = Bform P f x (g(T)y)
  -- Proof chain: Bform P (f*g) x y = Bform P g u y = ⟨u, g(T)y⟩ = ⟨x, f(T)(g(T)y)⟩
  --   = Bform P f x (g(T)y), where u = f(T)†x.
  -- The first step uses DCT + simple function approximation.
  let fT := functionalCalculus P f hf_int hf_bdd
  let gT := functionalCalculus P g hg_int hg_bdd
  let u := fT.adjoint x
  calc Bform P (f * g) x y
      = Bform P g u y := by
        -- Approximate g by simple functions sₙ → g, prove for each sₙ, take limits.
        obtain ⟨Mg, hMg_pos, hMg⟩ := hg_bdd
        let sn := fun n => SimpleFunc.approxOn g hg_meas
          Set.univ 0 (Set.mem_univ 0) n
        -- sₙ → g pointwise
        have hs_tend : ∀ t, Filter.Tendsto (fun n => (sn n : ℝ → ℂ) t)
            Filter.atTop (𝓝 (g t)) := fun t =>
          SimpleFunc.tendsto_approxOn hg_meas (Set.mem_univ 0)
            (subset_closure (Set.mem_univ _))
        -- Bound on ‖sₙ(t)‖ ≤ 2Mg from edist_approxOn_le + triangle inequality
        have h_sn_norm_le : ∀ n t, ‖(sn n : ℝ → ℂ) t‖ ≤ 2 * Mg := by
          intro n t
          have h_ed := SimpleFunc.edist_approxOn_le
            hg_meas (Set.mem_univ 0) t n
          -- edist (sn n t) (g t) ≤ edist 0 (g t), convert to nndist then norm
          rw [edist_nndist, edist_nndist] at h_ed
          have h_nn := ENNReal.coe_le_coe.mp h_ed
          rw [nndist_eq_nnnorm, nndist_eq_nnnorm, zero_sub, nnnorm_neg] at h_nn
          have h_le : ‖(sn n : ℝ → ℂ) t - g t‖ ≤ ‖g t‖ := by exact_mod_cast h_nn
          linarith [norm_le_insert' ((sn n : ℝ → ℂ) t) (g t), hMg t]
        -- For each n: Bform P (f * sₙ) x y = Bform P sₙ u y
        -- Proved by SimpleFunc.induction: indicator case uses Bform_mul_indicator
        have h_eq_n : ∀ n, Bform P (f * (sn n : ℝ → ℂ)) x y =
            Bform P (sn n : ℝ → ℂ) u y := by
          intro n
          -- Prove for ALL simple functions, then specialize to sn n
          suffices ∀ (s : SimpleFunc ℝ ℂ),
              Bform P (f * ↑s) x y = Bform P (↑s) u y from this _
          intro s
          induction s using SimpleFunc.induction with
          | const c hS =>
            rename_i S
            -- Goal: Bform P (f * ↑(piecewise S hS (const c) (const 0))) x y =
            --       Bform P ↑(piecewise S hS (const c) (const 0)) u y
            -- The coercion is definitionally S.indicator (fun _ => c), so use convert
            have h_coe : ∀ t, (↑(SimpleFunc.piecewise S hS
                (SimpleFunc.const ℝ c) (SimpleFunc.const ℝ 0)) : ℝ → ℂ) t =
                S.indicator (fun _ => c) t := fun t => by
              simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
                Function.const_apply, Set.piecewise, Set.indicator_apply]
            -- Rewrite coercions using funext + h_coe
            have h_eq : (↑(SimpleFunc.piecewise S hS (SimpleFunc.const ℝ c)
                (SimpleFunc.const ℝ 0)) : ℝ → ℂ) =
                S.indicator (fun _ => c) := funext h_coe
            rw [h_eq]
            -- Now: Bform P (f * S.indicator (fun _ => c)) x y =
            --      Bform P (S.indicator (fun _ => c)) u y
            -- Factor out c: indicator(c) = c • indicator(1)
            have h_ind_c : S.indicator (fun _ => c) =
                (fun t => c * S.indicator (fun _ => (1 : ℂ)) t) := by
              ext t; by_cases ht : t ∈ S
              · simp [Set.indicator_of_mem ht]
              · simp [Set.indicator_of_notMem ht]
            have h_f_ind_c : f * S.indicator (fun _ => c) =
                (fun t => c * (f t * S.indicator (fun _ => (1 : ℂ)) t)) := by
              ext t; by_cases ht : t ∈ S
              · simp [Pi.mul_apply, Set.indicator_of_mem ht]; ring
              · simp [Pi.mul_apply, Set.indicator_of_notMem ht, mul_zero]
            rw [h_f_ind_c, h_ind_c]
            -- Now use Bform_smul_f on both sides
            have h_int_f1 : ∀ z : H, Integrable
                (fun t => f t * S.indicator (fun _ => (1 : ℂ)) t)
                (P.diagonalMeasure z) := fun z => by
              haveI := P.diagonalMeasure_isFiniteMeasure z
              have : (fun t => f t * S.indicator (fun _ => (1 : ℂ)) t) =
                  S.indicator f := by
                ext t; by_cases ht : t ∈ S
                · simp [Set.indicator_of_mem ht]
                · simp [Set.indicator_of_notMem ht]
              rw [this]; exact (hf_int z).indicator hS
            have h_int_1 : ∀ z : H, Integrable
                (S.indicator (fun _ => (1 : ℂ)))
                (P.diagonalMeasure z) := fun z => by
              haveI := P.diagonalMeasure_isFiniteMeasure z
              exact (integrable_const (1 : ℂ)).indicator hS
            rw [Bform_smul_f P c _ x y h_int_f1,
                Bform_mul_indicator P f hf_int hf_bdd S hS x y,
                Bform_smul_f P c _ u y h_int_1]
          | add hDisj ihf ihg =>
            rename_i sf sg
            -- Goal: Bform P (f * ↑(sf + sg)) x y = Bform P ↑(sf + sg) u y
            -- Rewrite coe(sf + sg) = ↑sf + ↑sg
            have h_coe_add : (↑(sf + sg) : ℝ → ℂ) = (↑sf : ℝ → ℂ) + (↑sg : ℝ → ℂ) :=
              SimpleFunc.coe_add sf sg
            rw [h_coe_add]
            -- Rewrite f * (↑sf + ↑sg) = f * ↑sf + f * ↑sg
            have h_mul_add : f * ((↑sf : ℝ → ℂ) + (↑sg : ℝ → ℂ)) =
                f * (↑sf : ℝ → ℂ) + f * (↑sg : ℝ → ℂ) :=
              mul_add f ↑sf ↑sg
            rw [h_mul_add]
            -- Integrability: f * sf and f * sg on finite spectral measures
            have simpleFunc_integrable : ∀ (s : SimpleFunc ℝ ℂ) (z : H),
                Integrable (↑s : ℝ → ℂ) (P.diagonalMeasure z) := fun s z => by
              haveI := P.diagonalMeasure_isFiniteMeasure z
              have hne : s.range.Nonempty :=
                ⟨s 0, SimpleFunc.mem_range.mpr ⟨0, rfl⟩⟩
              exact (integrable_const (s.range.sup' hne (fun c => ‖c‖))).mono'
                s.stronglyMeasurable.aestronglyMeasurable
                (Eventually.of_forall (fun t =>
                  Finset.le_sup' _ (SimpleFunc.mem_range.mpr ⟨t, rfl⟩)))
            have f_simpleFunc_integrable : ∀ (s : SimpleFunc ℝ ℂ) (z : H),
                Integrable (f * (↑s : ℝ → ℂ)) (P.diagonalMeasure z) := fun s z => by
              haveI := P.diagonalMeasure_isFiniteMeasure z
              obtain ⟨Mf, hMf_nn, hMf⟩ := hf_bdd
              have hne : s.range.Nonempty :=
                ⟨s 0, SimpleFunc.mem_range.mpr ⟨0, rfl⟩⟩
              exact (integrable_const (Mf * s.range.sup' hne (fun c => ‖c‖))).mono'
                ((hf_int z).aestronglyMeasurable.mul
                  s.stronglyMeasurable.aestronglyMeasurable)
                (Eventually.of_forall (fun t => by
                  rw [Pi.mul_apply, norm_mul]
                  exact mul_le_mul (hMf t)
                    (Finset.le_sup' _ (SimpleFunc.mem_range.mpr ⟨t, rfl⟩))
                    (norm_nonneg _) hMf_nn))
            rw [Bform_add_f P _ _ x y (fun z => f_simpleFunc_integrable sf z)
                (fun z => f_simpleFunc_integrable sg z), ihf, ihg]
            exact (Bform_add_f P _ _ u y (fun z => simpleFunc_integrable sf z)
                (fun z => simpleFunc_integrable sg z)).symm
        -- LHS: Bform P (f * sₙ) x y → Bform P (f * g) x y by DCT
        have h_lhs : Filter.Tendsto (fun n => Bform P (f * (sn n : ℝ → ℂ)) x y)
            Filter.atTop (𝓝 (Bform P (f * g) x y)) := by
          simp only [Bform]
          obtain ⟨Mf, hMf_nn, hMf⟩ := hf_bdd
          have hQ : ∀ z, Filter.Tendsto
              (fun n => Qform P (f * (sn n : ℝ → ℂ)) z)
              Filter.atTop (𝓝 (Qform P (f * g) z)) := by
            intro z; simp only [Qform]
            haveI := P.diagonalMeasure_isFiniteMeasure z
            exact tendsto_integral_of_dominated_convergence
              (fun _ => Mf * (2 * Mg))
              (fun n => (hf_int z).aestronglyMeasurable.mul
                (sn n).stronglyMeasurable.aestronglyMeasurable)
              (integrable_const _)
              (fun n => ae_of_all _ (fun t => by
                rw [Pi.mul_apply, norm_mul]
                exact mul_le_mul (hMf t) (h_sn_norm_le n t)
                  (norm_nonneg _) hMf_nn))
              (ae_of_all _ (fun t => tendsto_const_nhds.mul (hs_tend t)))
          exact tendsto_const_nhds.mul
            ((((hQ (x + y)).sub (hQ (x - y))).sub
              (tendsto_const_nhds.mul (hQ (x + Complex.I • y)))).add
              (tendsto_const_nhds.mul (hQ (x - Complex.I • y))))
        -- RHS: Bform P sₙ u y → Bform P g u y by DCT
        have h_rhs : Filter.Tendsto (fun n => Bform P (sn n : ℝ → ℂ) u y)
            Filter.atTop (𝓝 (Bform P g u y)) := by
          simp only [Bform]
          have hQ : ∀ z, Filter.Tendsto
              (fun n => Qform P (sn n : ℝ → ℂ) z)
              Filter.atTop (𝓝 (Qform P g z)) := by
            intro z; simp only [Qform]
            haveI := P.diagonalMeasure_isFiniteMeasure z
            exact tendsto_integral_of_dominated_convergence
              (fun _ => 2 * Mg)
              (fun n => (sn n).stronglyMeasurable.aestronglyMeasurable)
              (integrable_const _)
              (fun n => ae_of_all _ (fun t => h_sn_norm_le n t))
              (ae_of_all _ hs_tend)
          exact tendsto_const_nhds.mul
            ((((hQ (u + y)).sub (hQ (u - y))).sub
              (tendsto_const_nhds.mul (hQ (u + Complex.I • y)))).add
              (tendsto_const_nhds.mul (hQ (u - Complex.I • y))))
        -- Both sequences are equal (h_eq_n), limits agree by uniqueness
        exact tendsto_nhds_unique
          (by rwa [show (fun n => Bform P (f * (sn n : ℝ → ℂ)) x y) =
              (fun n => Bform P (sn n : ℝ → ℂ) u y) from funext h_eq_n] at h_lhs) h_rhs
    _ = @inner ℂ H _ u (gT y) :=
        functionalCalculus_inner P g hg_int hg_bdd u y
    _ = @inner ℂ H _ x (fT (gT y)) :=
        ContinuousLinearMap.adjoint_inner_left fT (gT y) x
    _ = Bform P f x (gT y) :=
        (functionalCalculus_inner P f hf_int hf_bdd x (gT y)).symm

/-- The functional calculus respects adjoints: f(T)* = f̄(T)

    **Reference:** Reed-Simon Theorem VIII.5(c)

    The proof uses that P(E)* = P(E) (self-adjointness of projections):
    - For simple f = Σᵢ cᵢ χ_{Eᵢ}: f(T)* = (Σᵢ cᵢ P(Eᵢ))* = Σᵢ c̄ᵢ P(Eᵢ) = f̄(T)
    - Extending to bounded Borel f uses continuity of the adjoint operation. -/
theorem functionalCalculus_star (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, MeasureTheory.Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hsf_int : ∀ z : H, MeasureTheory.Integrable (star ∘ f) (P.diagonalMeasure z))
    (hsf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(star ∘ f) t‖ ≤ M) :
    ContinuousLinearMap.adjoint (functionalCalculus P f hf_int hf_bdd) =
    functionalCalculus P (star ∘ f) hsf_int hsf_bdd := by
  -- Proof: Equality of bounded operators by equality on all inner products.
  -- ⟨y, f(T)* x⟩ = ⟨f(T) y, x⟩ = conj ⟨x, f(T) y⟩ = conj(B_f(x,y))
  --              = B_{star∘f}(y,x) = ⟨y, (star∘f)(T) x⟩
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  -- Chain: ⟨y, f(T)*x⟩ = ⟨f(T)y, x⟩ = conj⟨x, f(T)y⟩ = conj(B_f(x,y))
  --      = B_{sf}(y,x) = ⟨y, (sf)(T)x⟩
  calc @inner ℂ H _ y (ContinuousLinearMap.adjoint (functionalCalculus P f hf_int hf_bdd) x)
      = @inner ℂ H _ (functionalCalculus P f hf_int hf_bdd y) x :=
        ContinuousLinearMap.adjoint_inner_right _ y x
    _ = starRingEnd ℂ (@inner ℂ H _ x (functionalCalculus P f hf_int hf_bdd y)) :=
        (inner_conj_symm (functionalCalculus P f hf_int hf_bdd y) x).symm
    _ = starRingEnd ℂ (Bform P f x y) := by
        congr 1; exact (functionalCalculus_inner P f hf_int hf_bdd x y).symm
    _ = Bform P (star ∘ f) y x :=
        (Bform_star_swap P f y x hf_int).symm
    _ = @inner ℂ H _ y (functionalCalculus P (star ∘ f) hsf_int hsf_bdd x) :=
        functionalCalculus_inner P (star ∘ f) hsf_int hsf_bdd y x


/-! ### The Spectral Theorem -/

/-- **The PVM Construction for Unbounded Self-Adjoint Operators (sorry-free)**

    For every densely defined self-adjoint operator T on a Hilbert space H,
    there exists a spectral measure P (projection-valued measure) and a
    Cayley transform C such that P.proj agrees with spectralMeasureFromRMK
    on all measurable sets.

    This is the core sorry-free construction. The spectral measure P is:
    - P(E) = spectralMeasureFromRMK T hT hsa C E hE for measurable E
    - P(E) = 0 for non-measurable E

    All PVM properties (empty, univ, idempotent, self-adjoint, multiplicative,
    monotone, σ-additive) are proven from the RMK chain.

    References: Reed-Simon Theorem VIII.4, Rudin Theorem 13.30 -/
theorem spectral_theorem_pvm (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ (P : SpectralMeasure H) (C : CayleyTransform T hT hsa),
      ∀ E (hE : MeasurableSet E), P.proj E = spectralMeasureFromRMK T hT hsa C E hE := by
  -- Step 1: Get the Cayley transform and PVM properties from spectralMeasure_isPVM_via_RMK
  -- The RMK approach proves: empty=0, univ=1, idempotent, selfAdjoint, multiplicative
  -- All of these are sorry-free!
  -- Note: This only proves P is a PVM; the T-P connection (final sorry below) is separate.
  obtain ⟨C, hP_empty, hP_univ, hP_idem, hP_sa, hP_inter⟩ :=
    spectralMeasure_isPVM_via_RMK T hT hsa
  -- Define P_raw from the RMK spectral measure
  -- For non-measurable sets, we define P(E) = 0
  let P_raw : Set ℝ → (H →L[ℂ] H) := fun E =>
    if hE : MeasurableSet E then spectralMeasureFromRMK T hT hsa C E hE else 0
  -- Step 2: Prove the SpectralMeasure properties for P_raw
  -- empty: P(∅) = 0
  have hP_raw_empty : P_raw ∅ = 0 := by
    simp only [P_raw, MeasurableSet.empty, ↓reduceDIte]
    exact hP_empty
  -- univ: P(ℝ) = 1
  have hP_raw_univ : P_raw Set.univ = 1 := by
    simp only [P_raw, MeasurableSet.univ, ↓reduceDIte]
    exact hP_univ
  -- isIdempotent: P(E)² = P(E) (for measurable E)
  have hP_raw_idem : ∀ E, MeasurableSet E → P_raw E ∘L P_raw E = P_raw E := by
    intro E hE
    simp only [P_raw, hE, ↓reduceDIte]
    exact hP_idem E hE
  -- isSelfAdj: P(E)* = P(E) (for measurable E)
  have hP_raw_sa : ∀ E, MeasurableSet E → (P_raw E).adjoint = P_raw E := by
    intro E hE
    simp only [P_raw, hE, ↓reduceDIte]
    exact hP_sa E hE
  -- inter: P(E ∩ F) = P(E) ∘L P(F) (for measurable E, F)
  have hP_raw_inter : ∀ E F, MeasurableSet E → MeasurableSet F →
      P_raw (E ∩ F) = P_raw E ∘L P_raw F := by
    intro E F hE hF
    simp only [P_raw, hE, hF, hE.inter hF, ↓reduceDIte]
    exact hP_inter E F hE hF
  -- monotone: E ⊆ F implies ‖P(E)x‖ ≤ ‖P(F)x‖ (for measurable E, F)
  have hP_raw_mono : ∀ E F, MeasurableSet E → MeasurableSet F → E ⊆ F →
      ∀ x : H, ‖P_raw E x‖ ≤ ‖P_raw F x‖ := by
    intro E F hE hF hEF x
    -- Both measurable: use the contraction property P(E) = P(E∩F) = P(E)∘P(F)
    have hEF_inter : E ∩ F = E := Set.inter_eq_left.mpr hEF
    have hPE_eq : P_raw E = P_raw E ∘L P_raw F := by
      rw [← hP_raw_inter E F hE hF, hEF_inter]
    have hPEx : P_raw E x = P_raw E (P_raw F x) := by
      calc P_raw E x = (P_raw E ∘L P_raw F) x := by rw [← hPE_eq]
        _ = P_raw E (P_raw F x) := rfl
    rw [hPEx]
    -- Projections are contractions: ‖P(E)y‖ ≤ ‖y‖
    by_cases hy : P_raw E (P_raw F x) = 0
    · rw [hy, norm_zero]; exact norm_nonneg _
    · have h1 : ‖P_raw E (P_raw F x)‖^2 =
          RCLike.re (@inner ℂ H _ (P_raw E (P_raw F x)) (P_raw E (P_raw F x))) :=
        (inner_self_eq_norm_sq _).symm
      have h2 : @inner ℂ H _ (P_raw E (P_raw F x)) (P_raw E (P_raw F x)) =
          @inner ℂ H _ (P_raw F x) ((P_raw E).adjoint (P_raw E (P_raw F x))) :=
        (ContinuousLinearMap.adjoint_inner_right (P_raw E) (P_raw F x) _).symm
      have h3 : (P_raw E).adjoint (P_raw E (P_raw F x)) = P_raw E (P_raw E (P_raw F x)) := by
        rw [hP_raw_sa E hE]
      have h5 : P_raw E (P_raw E (P_raw F x)) = P_raw E (P_raw F x) := by
        have := hP_raw_idem E hE
        simp only [] at this
        exact congrFun (congrArg DFunLike.coe this) (P_raw F x)
      have h_inner_eq : @inner ℂ H _ (P_raw E (P_raw F x)) (P_raw E (P_raw F x)) =
          @inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x)) := by rw [h2, h3, h5]
      have hcs : ‖@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))‖ ≤
          ‖P_raw F x‖ * ‖P_raw E (P_raw F x)‖ := norm_inner_le_norm _ _
      have hre_le : RCLike.re (@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))) ≤
          ‖@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))‖ := by
        have h := Complex.abs_re_le_norm (@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x)))
        exact le_trans (le_abs_self _) h
      have h6 : ‖P_raw E (P_raw F x)‖^2 ≤ ‖P_raw F x‖ * ‖P_raw E (P_raw F x)‖ := by
        calc ‖P_raw E (P_raw F x)‖^2 =
            RCLike.re (@inner ℂ H _ (P_raw E (P_raw F x)) (P_raw E (P_raw F x))) := h1
          _ = RCLike.re (@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))) := by rw [h_inner_eq]
          _ ≤ ‖@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))‖ := hre_le
          _ ≤ ‖P_raw F x‖ * ‖P_raw E (P_raw F x)‖ := hcs
      have hpos : 0 < ‖P_raw E (P_raw F x)‖ := norm_pos_iff.mpr hy
      calc ‖P_raw E (P_raw F x)‖ =
          ‖P_raw E (P_raw F x)‖^2 / ‖P_raw E (P_raw F x)‖ := by field_simp
        _ ≤ (‖P_raw F x‖ * ‖P_raw E (P_raw F x)‖) / ‖P_raw E (P_raw F x)‖ := by
          apply div_le_div_of_nonneg_right h6 hpos.le
        _ = ‖P_raw F x‖ := by field_simp
  -- sigma_additive: For disjoint measurable E_i, P(⋃ E_i)x = Σ P(E_i)x
  -- This requires transferring σ-additivity from the RMK construction.
  have hP_raw_sigma : ∀ (E : ℕ → Set ℝ), (∀ i, MeasurableSet (E i)) →
      (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
      ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P_raw (E i) x)
        Filter.atTop (nhds (P_raw (⋃ i, E i) x)) := by
    intro E hE_meas hE_disj x
    -- For measurable E_i, P_raw (E i) = spectralMeasureFromRMK ...
    have hP_raw_eq : ∀ i, P_raw (E i) = spectralMeasureFromRMK T hT hsa C (E i) (hE_meas i) := by
      intro i; simp only [P_raw, hE_meas i, ↓reduceDIte]
    have hP_raw_union : P_raw (⋃ i, E i) =
        spectralMeasureFromRMK T hT hsa C (⋃ i, E i) (MeasurableSet.iUnion hE_meas) := by
      simp only [P_raw, MeasurableSet.iUnion hE_meas, ↓reduceDIte]
    -- Use the sigma-additivity theorem from SigmaAdditivity.lean
    have h := spectralProjection_sigma_additive T hT hsa C E hE_meas hE_disj x
    simp only [hP_raw_eq] at *
    rw [hP_raw_union]
    exact h
  -- proj_nonmeasurable: P(E) = 0 for non-measurable E
  have hP_raw_nonmeas : ∀ E, ¬MeasurableSet E → P_raw E = 0 := by
    intro E hE; simp only [P_raw, hE, ↓reduceDIte]
  -- Step 3: Construct the SpectralMeasure
  let P : SpectralMeasure H := {
    proj := P_raw
    empty := hP_raw_empty
    univ := hP_raw_univ
    isIdempotent := hP_raw_idem
    isSelfAdj := hP_raw_sa
    inter := hP_raw_inter
    monotone := hP_raw_mono
    sigma_additive := hP_raw_sigma
    proj_nonmeasurable := hP_raw_nonmeas
  }
  -- Step 4: The conclusion - P.proj agrees with spectralMeasureFromRMK on measurable sets
  use P, C
  intro E hE
  -- For measurable E, P_raw E = spectralMeasureFromRMK T hT hsa C E hE by construction
  show P_raw E = spectralMeasureFromRMK T hT hsa C E hE
  exact dif_pos hE

/-- The spectral measure of a self-adjoint operator, extracted from `spectral_theorem_pvm`.
    This definition is sorry-free: the PVM is fully constructed from the RMK chain.
    For measurable E: `P.proj E = spectralMeasureFromRMK T hT hsa C E hE`. -/
def UnboundedOperator.spectralMeasure (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) : SpectralMeasure H :=
  (spectral_theorem_pvm T hT hsa).choose

/-- The Cayley transform associated with the spectral measure.
    This definition is sorry-free. -/
def UnboundedOperator.spectralCayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) : CayleyTransform T hT hsa :=
  (spectral_theorem_pvm T hT hsa).choose_spec.choose

/-- The core sorry-free property: spectral measure agrees with RMK construction.
    For all measurable E, `P.proj E = spectralMeasureFromRMK T hT hsa C E hE`. -/
theorem UnboundedOperator.spectralMeasure_eq_RMK (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (T.spectralMeasure hT hsa).proj E =
    spectralMeasureFromRMK T hT hsa (T.spectralCayley hT hsa) E hE :=
  (spectral_theorem_pvm T hT hsa).choose_spec.choose_spec E hE

/-- **The Spectral Theorem** (Reed-Simon Theorem VIII.4).

    For every densely defined self-adjoint operator T on a Hilbert space H,
    there exists a unique projection-valued measure P (constructed sorry-free
    by `spectral_theorem_pvm`) such that for all bounded measurable f : ℝ → ℂ:

    `⟨x, f(T) y⟩ = ∫ f(λ) d⟨x, P(dλ) y⟩`

    where `f(T) = functionalCalculus P f` is the spectral integral operator
    and `P.spectralIntegral f x y` is the polarized spectral integral
    `(1/4)[∫f dμ_{x+y} - ∫f dμ_{x-y} - i∫f dμ_{x+iy} + i∫f dμ_{x-iy}]`
    with `μ_z(E) = ‖P(E) z‖²`.

    References: Reed-Simon Theorem VIII.4, Rudin Theorem 13.30 -/
theorem spectral_theorem (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    let P := T.spectralMeasure hT hsa
    ∀ (f : ℝ → ℂ) (hf_int : ∀ z : H, MeasureTheory.Integrable f (P.diagonalMeasure z))
      (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M) (x y : H),
      @inner ℂ H _ x (functionalCalculus P f hf_int hf_bdd y) =
      P.spectralIntegral f x y := by
  intro P f hf_int hf_bdd x y
  -- functionalCalculus_inner: Bform P f x y = ⟨x, functionalCalculus P f y⟩
  -- P.spectralIntegral = Bform (both expand to the same polarized integral)
  have h := functionalCalculus_inner P f hf_int hf_bdd x y
  rw [← h]
  -- Goal: Bform P f x y = P.spectralIntegral f x y
  -- Both expand to the same polarized integral expression
  unfold Bform Qform SpectralMeasure.spectralIntegral; rfl

/-! ### Powers of positive self-adjoint operators -/

/-- For a positive self-adjoint operator T and s ∈ ℂ with Re(s) = 0, define T^s.
    This uses functional calculus: T^s = ∫ λ^s dP(λ).
    The hypothesis Re(s) = 0 ensures the integrand |λ^s| = 1 is bounded. -/
def UnboundedOperator.power (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (_hpos : T.IsPositive) (s : ℂ) (hs : s.re = 0) :
    H →L[ℂ] H :=
  let P := T.spectralMeasure hT hsa
  let f := fun x : ℝ => if x > 0 then Complex.exp (s * Complex.log x) else 0
  functionalCalculus P f
    (by -- Integrability: |f(x)| ≤ 1 (since Re(s) = 0) and μ_z is finite → integrable
      intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
      have hf_bdd : ∀ x, ‖f x‖ ≤ 1 := by
        intro x; simp only [f]
        split_ifs with hx
        · rw [Complex.norm_exp,
              show Complex.log (↑x : ℂ) = ↑(Real.log x) from
                (Complex.ofReal_log (le_of_lt hx)).symm]
          have hre : (s * ↑(Real.log x)).re = 0 := by
            simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hs]
          rw [hre, Real.exp_zero]
        · simp
      exact (MeasureTheory.integrable_const (1 : ℂ)).mono
        (Measurable.aestronglyMeasurable (by
          apply Measurable.ite measurableSet_Ioi
          · exact Complex.continuous_exp.measurable.comp
              (measurable_const.mul
                (Complex.measurable_log.comp Complex.continuous_ofReal.measurable))
          · exact measurable_const))
        (by filter_upwards with x; simp only [norm_one]; exact hf_bdd x))
    (by -- Boundedness: |exp(s * log x)| = exp(Re(s * log x)) = exp(0) = 1
      refine ⟨1, zero_le_one, fun x => ?_⟩
      simp only [f]
      split_ifs with hx
      · rw [Complex.norm_exp,
            show Complex.log (↑x : ℂ) = ↑(Real.log x) from
              (Complex.ofReal_log (le_of_lt hx)).symm]
        have hre : (s * ↑(Real.log x)).re = 0 := by
          simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hs]
        rw [hre, Real.exp_zero]
      · simp)

/-- T^0 = 1 for strictly positive T.

    **Note:** This requires strict positivity (T injective), not just positivity.
    For a merely positive T, `power 0` gives `P((0,∞))` (the projection onto ker(T)⊥),
    which equals 1 only when T has trivial kernel. Counterexample: T = 0.
    See Issue #4.

    **Proof:** The function f(λ) = λ^0 = 1 for λ > 0 (and 0 elsewhere).
    For strictly positive T, P({0}) = 0 (since 0 is not an eigenvalue),
    so P((0,∞)) = P([0,∞)) = P(ℝ) = 1, giving ∫ f dP = 1.
    Depends on: spectral support argument (P((-∞, 0]) = 0 for positive T). -/
theorem UnboundedOperator.power_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive)
    (hstrict : T.IsStrictlyPositive) :
    T.power hT hsa hpos 0 (by simp [Complex.zero_re]) = 1 := by
  /-
  PROOF STRUCTURE:

  1. The power function is: f(λ) = if λ > 0 then exp(0 * log λ) else 0
  2. For λ > 0: exp(0 * log λ) = exp(0) = 1
  3. So f(λ) = χ_{(0,∞)}(λ) (indicator of positive reals)

  For a strictly positive operator T:
  - The spectrum is contained in [0, ∞) (by positivity)
  - P({0}) = 0 (by strict positivity / injectivity)
  - Therefore P((0, ∞)) = P([0, ∞)) = P(ℝ) = 1
  - And ∫ χ_{(0,∞)} dP = P((0,∞)) = 1

  FOUNDATIONAL: Requires showing P((-∞, 0]) = 0 for strictly positive T
  and that the functional calculus of the constant 1 on support is the identity.
  -/
  sorry

/-- T^(s+t) = T^s ∘ T^t

    **Proof:** Uses `functionalCalculus_mul`. The function λ^(s+t) = λ^s · λ^t pointwise,
    so ∫ λ^(s+t) dP = ∫ (λ^s · λ^t) dP = (∫ λ^s dP)(∫ λ^t dP) = T^s ∘ T^t.
    Depends on: `functionalCalculus_mul`. -/
theorem UnboundedOperator.power_add (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (s t : ℂ)
    (hs : s.re = 0) (ht : t.re = 0) :
    T.power hT hsa hpos (s + t) (by simp [Complex.add_re, hs, ht]) =
    T.power hT hsa hpos s hs ∘L T.power hT hsa hpos t ht := by
  set P := T.spectralMeasure hT hsa
  -- The power functions
  let f_s : ℝ → ℂ := fun x => if x > 0 then Complex.exp (s * Complex.log x) else 0
  let f_t : ℝ → ℂ := fun x => if x > 0 then Complex.exp (t * Complex.log x) else 0
  -- Norm bound: |exp(u * log x)| ≤ 1 when Re(u) = 0
  have power_norm_le : ∀ (u : ℂ), u.re = 0 → ∀ x : ℝ,
      ‖(if x > 0 then Complex.exp (u * Complex.log ↑x) else 0 : ℂ)‖ ≤ 1 := by
    intro u hu x
    split_ifs with hx
    · rw [Complex.norm_exp,
          show Complex.log (↑x : ℂ) = ↑(Real.log x) from (Complex.ofReal_log (le_of_lt hx)).symm]
      have : (u * ↑(Real.log x)).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hu]
      rw [this, Real.exp_zero]
    · simp
  -- Measurability
  have power_meas : ∀ (u : ℂ), Measurable (fun x : ℝ =>
      if x > 0 then Complex.exp (u * Complex.log ↑x) else (0 : ℂ)) := by
    intro u
    apply Measurable.ite measurableSet_Ioi
    · exact Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.measurable_log.comp Complex.continuous_ofReal.measurable))
    · exact measurable_const
  -- Integrability
  have power_int : ∀ (u : ℂ), u.re = 0 → ∀ z : H,
      MeasureTheory.Integrable (fun (x : ℝ) => if x > 0 then Complex.exp (u * Complex.log ↑x) else 0)
        (P.diagonalMeasure z) := by
    intro u hu z
    haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const (1 : ℂ)).mono
      ((power_meas u).aestronglyMeasurable)
      (by filter_upwards with x; simp only [norm_one]; exact power_norm_le u hu x)
  -- Key pointwise identity: f_{s+t} = f_s * f_t
  have h_eq : (fun x : ℝ => if x > 0 then Complex.exp ((s + t) * Complex.log ↑x) else (0 : ℂ)) =
      f_s * f_t := by
    ext x; simp only [Pi.mul_apply, f_s, f_t]
    split_ifs with hx
    · rw [add_mul, Complex.exp_add]
    · simp
  -- Product norm bound
  have hfg_bdd : ∃ M, 0 ≤ M ∧ ∀ x, ‖(f_s * f_t) x‖ ≤ M :=
    ⟨1, zero_le_one, fun x => by
      simp only [Pi.mul_apply, f_s, f_t]; rw [norm_mul]
      calc ‖(if x > 0 then Complex.exp (s * Complex.log ↑x) else 0 : ℂ)‖ *
            ‖(if x > 0 then Complex.exp (t * Complex.log ↑x) else 0 : ℂ)‖
          ≤ 1 * 1 := by
            exact mul_le_mul (power_norm_le s hs x) (power_norm_le t ht x)
              (norm_nonneg _) zero_le_one
        _ = 1 := mul_one 1⟩
  -- Product integrability
  have hfg_int : ∀ z : H, MeasureTheory.Integrable (f_s * f_t) (P.diagonalMeasure z) := by
    rw [← h_eq]; exact power_int (s + t) (by simp [Complex.add_re, hs, ht])
  -- Get the functionalCalculus_mul result
  have hmul := functionalCalculus_mul P f_s f_t
    (power_int s hs) ⟨1, zero_le_one, power_norm_le s hs⟩
    (power_int t ht) ⟨1, zero_le_one, power_norm_le t ht⟩
    hfg_int hfg_bdd (power_meas t)
  -- Use calc: power(s+t) = fc(f_s*f_t) = fc(f_s) ∘L fc(f_t) = power(s) ∘L power(t)
  have h_st_re : (s + t).re = 0 := by simp [Complex.add_re, hs, ht]
  calc T.power hT hsa hpos (s + t) _
      = functionalCalculus P (f_s * f_t) hfg_int hfg_bdd := by
          -- power(s+t) = fc(f_{s+t}) definitionally, and f_{s+t} = f_s * f_t
          show functionalCalculus P
            (fun x : ℝ => if x > 0 then Complex.exp ((s + t) * Complex.log ↑x) else 0)
            (power_int (s + t) h_st_re) ⟨1, zero_le_one, power_norm_le (s + t) h_st_re⟩ =
            functionalCalculus P (f_s * f_t) hfg_int hfg_bdd
          congr 1
    _ = functionalCalculus P f_s (power_int s hs) ⟨1, zero_le_one, power_norm_le s hs⟩ ∘L
        functionalCalculus P f_t (power_int t ht) ⟨1, zero_le_one, power_norm_le t ht⟩ := hmul
    _ = T.power hT hsa hpos s hs ∘L T.power hT hsa hpos t ht := rfl

/-- For real t, T^{it} is unitary (requires strict positivity).

    **Note:** Like `power_zero`, this requires strict positivity (T injective).
    For a merely positive T, T^0 = P((0,∞)) ≠ 1, so u* ∘ u = T^0 ≠ 1.
    Counterexample: T = 0 gives T^{it} = 0 for all t, which is not unitary.

    **Proof:** Uses `functionalCalculus_star`. For real t:
    - (T^{it})* = ∫ conj(λ^{it}) dP = ∫ λ^{-it} dP = T^{-it}
    - T^{it} ∘ T^{-it} = T^0 = 1 (by `power_add` and `power_zero`)
    Depends on: `functionalCalculus_star`, `power_add`, `power_zero`. -/
theorem UnboundedOperator.power_imaginary_unitary (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive)
    (hstrict : T.IsStrictlyPositive) (t : ℝ) :
    let hs : (Complex.I * ↑t).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    let u := T.power hT hsa hpos (Complex.I * t) hs
    ContinuousLinearMap.adjoint u ∘L u = 1 ∧ u ∘L ContinuousLinearMap.adjoint u = 1 := by
  /-
  PROOF STRUCTURE:

  Let u = T^{it} where the power function is:
    f_{it}(x) = if x > 0 then exp(it * log x) else 0

  **Step 1: Compute u* using functionalCalculus_star**
  u* = (∫ f_{it} dP)* = ∫ (star ∘ f_{it}) dP
  where (star ∘ f_{it})(x) = conj(f_{it}(x))

  For x > 0:
    conj(exp(it * log x)) = exp(conj(it * log x))
                          = exp(-it * log x)  [since log x ∈ ℝ for x > 0]
                          = exp((-it) * log x)

  So (star ∘ f_{it}) = f_{-it}, hence u* = T^{-it}

  **Step 2: Use power_add and power_zero**
  u* ∘ u = T^{-it} ∘ T^{it} = T^{-it + it} = T^0 = 1
  u ∘ u* = T^{it} ∘ T^{-it} = T^{it + (-it)} = T^0 = 1
  -/
  -- Depends on functionalCalculus_star (proven), power_add (proven), power_zero (sorry'd).
  -- Inherits the bug from power_zero: false for non-injective positive operators.
  -- For T = 0: u = T^{it} = functionalCalculus P (indicator_Ioi) = P(Ioi 0) = 0,
  -- so u* ∘ u = 0 ≠ 1. Fix power definition first (see power_zero comment).
  sorry

/-! ### One-parameter unitary groups

The one-parameter unitary group U(t) = e^{itA} = ∫ exp(itλ) dP(λ) is defined using
the exponential function directly, not through the `power` function. This is important:
- `power` uses λ^{it} = exp(it·log λ), which requires positivity and fails at λ = 0
- The exponential exp(itλ) is defined for all λ ∈ ℝ, works for any self-adjoint operator
- No positivity hypothesis is needed
-/

/-- Norm bound: ‖exp(itx)‖ ≤ 1 for real t, x. -/
private lemma expI_norm_le (t : ℝ) (x : ℝ) :
    ‖Complex.exp (Complex.I * ↑t * ↑x)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have : (Complex.I * ↑t * ↑x).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [this, Real.exp_zero]

/-- Measurability of exp(itx) in x for fixed t. -/
private lemma expI_measurable (t : ℝ) :
    Measurable (fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x)) :=
  Complex.continuous_exp.measurable.comp
    ((continuous_const.mul Complex.continuous_ofReal).measurable)

open MeasureTheory in
/-- Integrability of exp(itx) against spectral diagonal measures. -/
private lemma expI_integrable (P : SpectralMeasure H) (t : ℝ) (z : H) :
    Integrable (fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x))
      (P.diagonalMeasure z) := by
  haveI := P.diagonalMeasure_isFiniteMeasure z
  exact (integrable_const (1 : ℂ)).mono
    (expI_measurable t).aestronglyMeasurable
    (by filter_upwards with x; simp only [norm_one]; exact expI_norm_le t x)

/-- The functional calculus is proof-irrelevant: it depends only on the function f. -/
private lemma functionalCalculus_congr (P : SpectralMeasure H) {f g : ℝ → ℂ}
    (hfg : f = g)
    (hf_int : ∀ z : H, MeasureTheory.Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hg_int : ∀ z : H, MeasureTheory.Integrable g (P.diagonalMeasure z))
    (hg_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖g t‖ ≤ M) :
    functionalCalculus P f hf_int hf_bdd = functionalCalculus P g hg_int hg_bdd := by
  subst hfg; rfl

/-- The one-parameter unitary group generated by a self-adjoint operator.
    U(t) = e^{itA} = ∫ exp(itλ) dP(λ) where P is the spectral measure of T.

    This uses the exponential function directly (not through `power`),
    so no positivity hypothesis is needed. -/
def unitaryGroup (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (t : ℝ) : H →L[ℂ] H :=
  let P := T.spectralMeasure hT hsa
  functionalCalculus P (fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x))
    (fun z => expI_integrable P t z)
    ⟨1, zero_le_one, expI_norm_le t⟩

set_option maxHeartbeats 400000 in
open MeasureTheory in
/-- U(0) = 1. Since exp(i·0·λ) = 1 for all λ, the functional calculus gives
    the integral of the constant 1, which equals P(ℝ) = 1. -/
theorem unitaryGroup_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    unitaryGroup T hT hsa 0 = 1 := by
  set P := T.spectralMeasure hT hsa
  -- exp(I * 0 * x) = 1 for all x, matching Set.univ indicator
  have hfg : (fun x : ℝ => Complex.exp (Complex.I * ↑(0 : ℝ) * ↑x)) =
      Set.univ.indicator (fun _ => (1 : ℂ)) := by
    funext x; simp [Complex.exp_zero]
  show functionalCalculus P (fun x : ℝ => Complex.exp (Complex.I * ↑(0 : ℝ) * ↑x))
    (fun z => expI_integrable P 0 z) ⟨1, zero_le_one, expI_norm_le 0⟩ = 1
  apply ContinuousLinearMap.ext; intro y
  apply ext_inner_left ℂ; intro x
  rw [← functionalCalculus_inner, ContinuousLinearMap.one_apply, hfg,
    P.Bform_indicator_eq_inner Set.univ MeasurableSet.univ, P.univ,
    ContinuousLinearMap.one_apply]

set_option maxHeartbeats 400000 in
open MeasureTheory in
/-- The group law: U(s) ∘ U(t) = U(s+t).

    **Proof:** Uses `functionalCalculus_mul`. The pointwise identity
    exp(isλ) · exp(itλ) = exp(i(s+t)λ) gives the result. -/
theorem unitaryGroup_mul (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (s t : ℝ) :
    unitaryGroup T hT hsa s ∘L unitaryGroup T hT hsa t =
    unitaryGroup T hT hsa (s + t) := by
  set P := T.spectralMeasure hT hsa
  set f_s := fun x : ℝ => Complex.exp (Complex.I * ↑s * ↑x)
  set f_t := fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x)
  -- Pointwise identity: exp(isλ) · exp(itλ) = exp(i(s+t)λ)
  have h_eq : (fun x : ℝ => Complex.exp (Complex.I * ↑(s + t) * ↑x)) = f_s * f_t := by
    ext x; simp only [Pi.mul_apply, f_s, f_t]
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  -- Product norm bound
  have hfg_bdd : ∃ M, 0 ≤ M ∧ ∀ x, ‖(f_s * f_t) x‖ ≤ M :=
    ⟨1, zero_le_one, fun x => by
      simp only [Pi.mul_apply, f_s, f_t, norm_mul]
      calc ‖Complex.exp (Complex.I * ↑s * ↑x)‖ * ‖Complex.exp (Complex.I * ↑t * ↑x)‖
          ≤ 1 * 1 := mul_le_mul (expI_norm_le s x) (expI_norm_le t x)
            (norm_nonneg _) zero_le_one
        _ = 1 := mul_one 1⟩
  -- Product integrability
  have hfg_int : ∀ z : H, Integrable (f_s * f_t) (P.diagonalMeasure z) := by
    rw [← h_eq]; exact fun z => expI_integrable P (s + t) z
  -- Apply functionalCalculus_mul
  have hmul := functionalCalculus_mul P f_s f_t
    (fun z => expI_integrable P s z) ⟨1, zero_le_one, expI_norm_le s⟩
    (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩
    hfg_int hfg_bdd (expI_measurable t)
  -- Use show + congr 1 pattern (same as power_add):
  -- U(s) ∘L U(t) = fc(f_s * f_t) = U(s+t)
  have h_eq_sym := h_eq.symm
  calc unitaryGroup T hT hsa s ∘L unitaryGroup T hT hsa t
      = functionalCalculus P (f_s * f_t) hfg_int hfg_bdd := by
          show functionalCalculus P f_s
            (fun z => expI_integrable P s z) ⟨1, zero_le_one, expI_norm_le s⟩ ∘L
            functionalCalculus P f_t
            (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩ =
            functionalCalculus P (f_s * f_t) hfg_int hfg_bdd
          exact hmul.symm
    _ = unitaryGroup T hT hsa (s + t) := by
          show functionalCalculus P (f_s * f_t) hfg_int hfg_bdd =
            functionalCalculus P (fun x : ℝ => Complex.exp (Complex.I * ↑(s + t) * ↑x))
            (fun z => expI_integrable P (s + t) z) ⟨1, zero_le_one, expI_norm_le (s + t)⟩
          congr 1

set_option maxHeartbeats 400000 in
open MeasureTheory in
/-- U(t)* = U(-t)

    **Proof:** Uses `functionalCalculus_star`:
    U(t)* = (∫ exp(itλ) dP)* = ∫ conj(exp(itλ)) dP = ∫ exp(-itλ) dP = U(-t) -/
theorem unitaryGroup_inv (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (t : ℝ) :
    ContinuousLinearMap.adjoint (unitaryGroup T hT hsa t) =
    unitaryGroup T hT hsa (-t) := by
  set P := T.spectralMeasure hT hsa
  set f_t := fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x)
  set f_neg := fun x : ℝ => Complex.exp (Complex.I * ↑(-t) * ↑x)
  -- Key identity: star ∘ f_t = f_neg
  have hsfg : star ∘ f_t = f_neg := by
    funext x
    simp only [Function.comp, f_t, f_neg]
    have star_exp : ∀ z : ℂ, star (Complex.exp z) = Complex.exp (star z) := by
      intro z; simp [Complex.exp_conj]
    rw [star_exp]
    congr 1
    simp only [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  -- Norm bound for star ∘ f_t
  have hsf_norm_le : ∀ x, ‖(star ∘ f_t) x‖ ≤ 1 := by
    intro x; simp only [Function.comp, norm_star]; exact expI_norm_le t x
  -- Measurability of star ∘ f_t
  have hsf_meas : Measurable (star ∘ f_t) :=
    continuous_star.measurable.comp (expI_measurable t)
  -- Integrability of star ∘ f_t
  have hsf_int : ∀ z : H, Integrable (star ∘ f_t) (P.diagonalMeasure z) := by
    intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (integrable_const (1 : ℂ)).mono hsf_meas.aestronglyMeasurable
      (by filter_upwards with x; simp only [norm_one]; exact hsf_norm_le x)
  have hsf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(star ∘ f_t) t‖ ≤ M :=
    ⟨1, zero_le_one, hsf_norm_le⟩
  -- Apply functionalCalculus_star
  have h_star := functionalCalculus_star P f_t
    (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩
    hsf_int hsf_bdd
  -- U(t)* = fc(star ∘ f_t) = fc(f_neg) = U(-t)
  calc ContinuousLinearMap.adjoint (unitaryGroup T hT hsa t)
      = functionalCalculus P (star ∘ f_t) hsf_int hsf_bdd := by
          show ContinuousLinearMap.adjoint (functionalCalculus P f_t
            (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩) =
            functionalCalculus P (star ∘ f_t) hsf_int hsf_bdd
          exact h_star
    _ = unitaryGroup T hT hsa (-t) := by
          show functionalCalculus P (star ∘ f_t) hsf_int hsf_bdd =
            functionalCalculus P f_neg
            (fun z => expI_integrable P (-t) z) ⟨1, zero_le_one, expI_norm_le (-t)⟩
          congr 1

/-- U(-t) ∘ U(t) = 1 (left inverse) -/
theorem unitaryGroup_neg_comp (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (t : ℝ) :
    unitaryGroup T hT hsa (-t) ∘L unitaryGroup T hT hsa t = 1 := by
  rw [unitaryGroup_mul, neg_add_cancel, unitaryGroup_zero]

/-- U(t) ∘ U(-t) = 1 (right inverse) -/
theorem unitaryGroup_comp_neg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (t : ℝ) :
    unitaryGroup T hT hsa t ∘L unitaryGroup T hT hsa (-t) = 1 := by
  rw [unitaryGroup_mul, add_neg_cancel, unitaryGroup_zero]

/-- The integral ∫ exp(its) dμ(s) is continuous in t for any finite measure μ.
    Uses Lebesgue dominated convergence with constant bound 1. -/
private lemma continuous_integral_cexp (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ] :
    Continuous (fun t : ℝ => ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂μ) := by
  apply continuous_iff_continuousAt.mpr; intro t₀
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  · -- AEStronglyMeasurable for each t near t₀
    filter_upwards with t
    exact (expI_measurable t).aestronglyMeasurable
  · -- Norm bound: ‖exp(its)‖ ≤ 1
    filter_upwards with t
    filter_upwards with s using expI_norm_le t s
  · -- Bound integrable on finite measure
    exact MeasureTheory.integrable_const 1
  · -- Pointwise limit: exp(its) → exp(it₀s) as t → t₀ for each fixed s
    filter_upwards with s
    exact (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).continuousAt

-- Strong continuity: t ↦ U(t)x is continuous for all x
-- Reference: Reed-Simon Theorem VIII.8
-- Proof: weak continuity (DCT) + isometry (U(t)*U(t)=I) → strong continuity
set_option maxHeartbeats 800000 in
open MeasureTheory in
theorem unitaryGroup_continuous (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : H) :
    Continuous (fun t => unitaryGroup T hT hsa t x) := by
  set P := T.spectralMeasure hT hsa
  -- Step 1: Each ∫ exp(its) dμ_z(s) is continuous in t
  have h_int_cont : ∀ z : H, Continuous (fun t : ℝ =>
      ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂(P.diagonalMeasure z)) :=
    fun z => continuous_integral_cexp (P.diagonalMeasure z)
  -- Step 2: spectralIntegral of exp(it·) is continuous in t
  have h_si_cont : ∀ y : H, Continuous (fun t : ℝ =>
      P.spectralIntegral (fun s => Complex.exp (Complex.I * ↑t * ↑s)) y x) := by
    intro y; unfold SpectralMeasure.spectralIntegral
    exact continuous_const.mul
      ((((h_int_cont (y + x)).sub (h_int_cont (y - x))).sub
        (continuous_const.mul (h_int_cont (y + Complex.I • x)))).add
        (continuous_const.mul (h_int_cont (y - Complex.I • x))))
  -- Step 3: ⟨y, U(t)x⟩ is continuous in t (weak continuity)
  have h_weak : ∀ y : H, Continuous (fun t =>
      @inner ℂ H _ y (unitaryGroup T hT hsa t x)) := by
    intro y; convert h_si_cont y using 1; ext t
    show @inner ℂ H _ y (functionalCalculus P
      (fun s => Complex.exp (Complex.I * ↑t * ↑s))
      (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩ x) = _
    exact spectral_theorem T hT hsa _ _ _ y x
  -- Step 4: U(t) is isometric: ‖U(t)x‖ = ‖x‖
  have h_iso : ∀ t, ‖unitaryGroup T hT hsa t x‖ = ‖x‖ := by
    intro t
    have h_adj_comp : ContinuousLinearMap.adjoint (unitaryGroup T hT hsa t) ∘L
        unitaryGroup T hT hsa t = 1 := by
      rw [unitaryGroup_inv, unitaryGroup_neg_comp]
    have h_inner_eq : @inner ℂ H _ (unitaryGroup T hT hsa t x)
        (unitaryGroup T hT hsa t x) = @inner ℂ H _ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_right (unitaryGroup T hT hsa t) x
        (unitaryGroup T hT hsa t x), ← ContinuousLinearMap.comp_apply,
        h_adj_comp, ContinuousLinearMap.one_apply]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_inner_eq
    have h_sq : ‖unitaryGroup T hT hsa t x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h_inner_eq
    calc ‖unitaryGroup T hT hsa t x‖
        = Real.sqrt (‖unitaryGroup T hT hsa t x‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖x‖ ^ 2) := by rw [h_sq]
      _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)
  -- Step 5: Strong continuity from weak continuity + isometry
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- Re⟨U(t₀)x, U(t)x⟩ is continuous at t = t₀
  have h_re_cont : ContinuousAt (fun t =>
      (@inner ℂ H _ (unitaryGroup T hT hsa t₀ x)
        (unitaryGroup T hT hsa t x)).re) t₀ :=
    Complex.continuous_re.continuousAt.comp
      (h_weak (unitaryGroup T hT hsa t₀ x)).continuousAt
  -- At t = t₀: Re⟨U(t₀)x, U(t₀)x⟩ = ‖x‖²
  have h_at_t₀ : (@inner ℂ H _ (unitaryGroup T hT hsa t₀ x)
      (unitaryGroup T hT hsa t₀ x)).re = ‖x‖ ^ 2 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (unitaryGroup T hT hsa t₀ x)
    rw [this, h_iso t₀]; norm_cast
  -- Find δ such that |Re⟨U(t₀)x, U(t)x⟩ - ‖x‖²| < ε²/4 when dist t t₀ < δ
  have hε2 : (0 : ℝ) < ε ^ 2 / 4 := by positivity
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp h_re_cont (ε ^ 2 / 4) hε2
  refine ⟨δ, hδ, fun t ht => ?_⟩
  -- ‖U(t)x - U(t₀)x‖² < ε², hence ‖U(t)x - U(t₀)x‖ < ε
  have h_re_close : |(@inner ℂ H _ (unitaryGroup T hT hsa t₀ x)
      (unitaryGroup T hT hsa t x)).re - ‖x‖ ^ 2| < ε ^ 2 / 4 := by
    have := hδε ht; rw [Real.dist_eq, h_at_t₀] at this; exact this
  -- ‖U(t)x - U(t₀)x‖² = 2‖x‖² - 2*Re⟨U(t)x, U(t₀)x⟩
  have h_ns := @norm_sub_sq ℂ H _ _ _ (unitaryGroup T hT hsa t x)
    (unitaryGroup T hT hsa t₀ x)
  rw [h_iso t, h_iso t₀] at h_ns
  -- Bridge: RCLike.re and .re are definitionally equal for ℂ
  change ‖unitaryGroup T hT hsa t x - unitaryGroup T hT hsa t₀ x‖ ^ 2 =
    ‖x‖ ^ 2 - 2 * (@inner ℂ H _ (unitaryGroup T hT hsa t x)
      (unitaryGroup T hT hsa t₀ x)).re + ‖x‖ ^ 2 at h_ns
  -- Re⟨U(t)x, U(t₀)x⟩ = Re⟨U(t₀)x, U(t)x⟩ (from conjugate symmetry)
  have h_re_sym : (@inner ℂ H _ (unitaryGroup T hT hsa t x)
      (unitaryGroup T hT hsa t₀ x)).re =
      (@inner ℂ H _ (unitaryGroup T hT hsa t₀ x)
        (unitaryGroup T hT hsa t x)).re := by
    have h := inner_conj_symm (𝕜 := ℂ) (unitaryGroup T hT hsa t₀ x)
      (unitaryGroup T hT hsa t x)
    -- h : conj ⟪U(t)x, U(t₀)x⟫ = ⟪U(t₀)x, U(t)x⟫
    have conj_re_eq : ∀ z : ℂ, ((starRingEnd ℂ) z).re = z.re := fun z => by simp
    rw [← conj_re_eq]; exact congr_arg Complex.re h
  rw [h_re_sym] at h_ns
  -- h_ns : ‖...‖² = ‖x‖² - 2 * Re⟪U(t₀)x, U(t)x⟫ + ‖x‖²
  -- h_re_close : |Re⟪U(t₀)x, U(t)x⟫ - ‖x‖²| < ε²/4
  have h_bound : ‖unitaryGroup T hT hsa t x - unitaryGroup T hT hsa t₀ x‖ ^ 2 <
      ε ^ 2 := by linarith [(abs_lt.mp h_re_close).1]
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt hε) h_bound

end
