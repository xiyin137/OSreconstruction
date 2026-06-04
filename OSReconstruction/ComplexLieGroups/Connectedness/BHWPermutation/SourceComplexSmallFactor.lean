import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexGlobalIdentity

/-!
# Quantitative complex symmetric factorization support

This file isolates the finite entry-size estimates used to turn an
entry-controlled complex symmetric dot-factorization into the small-factor
statement needed by the Euclidean tail realization route.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator ComplexOrder

namespace BHW

/-- Entrywise `ℓ¹` size of a finite square complex matrix.  This avoids
choosing a matrix norm while proving the small-factor estimate. -/
noncomputable def matrixEntryL1Bound
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ∑ p : Fin m × Fin m, ‖S p.1 p.2‖

theorem matrixEntryL1Bound_nonneg
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) :
    0 ≤ matrixEntryL1Bound m S := by
  unfold matrixEntryL1Bound
  exact Finset.sum_nonneg (fun p _hp => norm_nonneg (S p.1 p.2))

/-- If every matrix entry is bounded by `δ`, then the finite entry-`ℓ¹`
bound is bounded by `((m*m)+1) δ`.  The `+1` keeps the empty case painless. -/
theorem matrixEntryL1Bound_lt_of_entry_bound
    (m : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ i j, ‖S i j‖ < δ) :
    matrixEntryL1Bound m S < (((m * m : ℕ) : ℝ) + 1) * δ := by
  unfold matrixEntryL1Bound
  have hle : (∑ p : Fin m × Fin m, ‖S p.1 p.2‖) ≤
      ∑ _p : Fin m × Fin m, δ := by
    exact Finset.sum_le_sum (fun p _hp => le_of_lt (hS p.1 p.2))
  have hsum : (∑ _p : Fin m × Fin m, δ) = ((m * m : ℕ) : ℝ) * δ := by
    simp
  calc
    (∑ p : Fin m × Fin m, ‖S p.1 p.2‖)
        ≤ ∑ _p : Fin m × Fin m, δ := hle
    _ = ((m * m : ℕ) : ℝ) * δ := hsum
    _ < (((m * m : ℕ) : ℝ) + 1) * δ := by
      nlinarith [hδ]

/-- Choose a positive entry bound whose square-root-scaled size is below the
target `ε`. -/
theorem exists_pos_mul_sqrt_lt
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ Real.sqrt (C * δ) < ε := by
  refine ⟨ε ^ 2 / (4 * C), ?_, ?_⟩
  · positivity
  · have hmul : C * (ε ^ 2 / (4 * C)) = (ε / 2) ^ 2 := by
      field_simp [ne_of_gt hC]
      ring
    rw [hmul]
    rw [Real.sqrt_sq]
    · linarith
    · linarith

theorem real_sqrt_lt_of_lt_mul_bound
    {x C δ ε : ℝ}
    (hx : 0 ≤ x)
    (hxlt : x < C * δ)
    (hsmall : Real.sqrt (C * δ) < ε) :
    Real.sqrt x < ε := by
  exact (Real.sqrt_lt_sqrt hx hxlt).trans hsmall

/-- The conjugate-linear map `v ↦ S *ᵥ star v` used in the
Autonne-Takagi construction. -/
def takagiConjugateLinearMap
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) :
    (Fin m → ℂ) → (Fin m → ℂ) :=
  fun v => S *ᵥ star v

theorem takagiConjugateLinearMap_add
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (v w : Fin m → ℂ) :
    takagiConjugateLinearMap m S (v + w) =
      takagiConjugateLinearMap m S v + takagiConjugateLinearMap m S w := by
  ext i
  simp [takagiConjugateLinearMap, Matrix.mulVec, dotProduct, Finset.sum_add_distrib,
    mul_add]

theorem takagiConjugateLinearMap_smul
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (c : ℂ) (v : Fin m → ℂ) :
    takagiConjugateLinearMap m S (c • v) =
      star c • takagiConjugateLinearMap m S v := by
  ext i
  simp [takagiConjugateLinearMap, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_left_comm]

/-- Under symmetry, the square of the conjugate-linear Takagi map is the
positive Hermitian square `S * Sᴴ`. -/
theorem takagiConjugateLinearMap_sq
    (m : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    (hSym : S.transpose = S) :
    (fun v : Fin m → ℂ =>
      takagiConjugateLinearMap m S
        (takagiConjugateLinearMap m S v)) =
    fun v => (S * Sᴴ) *ᵥ v := by
  have hSym_apply : ∀ a b : Fin m, S a b = S b a := by
    intro a b
    simpa [Matrix.transpose_apply] using congrFun (congrFun hSym b) a
  funext v
  ext i
  simp only [takagiConjugateLinearMap, Matrix.mulVec, dotProduct, Pi.star_apply, star_sum,
    StarMul.star_mul, star_star, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hSym_apply j k]
  ring_nf

theorem takagiConjugateLinearMap_commutes_square
    (m : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    (hSym : S.transpose = S) :
    (fun v : Fin m → ℂ =>
      takagiConjugateLinearMap m S ((S * Sᴴ) *ᵥ v)) =
    fun v =>
      (S * Sᴴ) *ᵥ (takagiConjugateLinearMap m S v) := by
  have hsq := takagiConjugateLinearMap_sq (m := m) (S := S) hSym
  funext v
  rw [← congrFun hsq v]
  rw [← congrFun hsq (takagiConjugateLinearMap m S v)]

theorem takagiConjugateLinearMap_mem_eigenspace
    (m : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    (hSym : S.transpose = S)
    {lambda : ℝ} {v : Fin m → ℂ}
    (hv : (S * Sᴴ) *ᵥ v = (lambda : ℂ) • v) :
    (S * Sᴴ) *ᵥ (takagiConjugateLinearMap m S v) =
      (lambda : ℂ) • takagiConjugateLinearMap m S v := by
  have hcomm :=
    congrFun (takagiConjugateLinearMap_commutes_square (m := m) (S := S) hSym) v
  rw [← hcomm, hv]
  rw [takagiConjugateLinearMap_smul]
  simp

theorem takagiConjugateLinearMap_conjTranspose_mulVec_eq_star
    (m : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    (hSym : S.transpose = S)
    (v : Fin m → ℂ) :
    Sᴴ *ᵥ v = star (takagiConjugateLinearMap m S v) := by
  have hSym_apply : ∀ a b : Fin m, S a b = S b a := by
    intro a b
    simpa [Matrix.transpose_apply] using congrFun (congrFun hSym b) a
  ext i
  simp only [takagiConjugateLinearMap, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Pi.star_apply, star_sum, StarMul.star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hSym_apply j i]
  ring_nf

theorem takagiConjugateLinearMap_zero_eigenspace_eq_zero
    (m : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    (hSym : S.transpose = S)
    {v : Fin m → ℂ}
    (hv : (S * Sᴴ) *ᵥ v = 0) :
    takagiConjugateLinearMap m S v = 0 := by
  have hker : Sᴴ *ᵥ v = 0 := by
    exact (Matrix.self_mul_conjTranspose_mulVec_eq_zero S v).mp hv
  have hstar : star (takagiConjugateLinearMap m S v) = 0 := by
    rw [← takagiConjugateLinearMap_conjTranspose_mulVec_eq_star
      (m := m) (S := S) hSym v]
    exact hker
  exact star_eq_zero.mp hstar

theorem takagiHermitianSquare_isHermitian
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) :
    (S * Sᴴ).IsHermitian := by
  exact Matrix.isHermitian_mul_conjTranspose_self S

/-- Spectral theorem for the positive Hermitian square in the exact unitary
matrix form used as the input to the Takagi construction. -/
theorem takagiHermitianSquare_spectralTheorem
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) :
    let hH := Matrix.isHermitian_mul_conjTranspose_self S
    let U := Matrix.IsHermitian.eigenvectorUnitary hH
    S * Sᴴ =
      (U : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.diagonal (fun a => ((hH.eigenvalues a : ℝ) : ℂ)) *
        star (U : Matrix (Fin m) (Fin m) ℂ) := by
  intro hH U
  have hs := hH.spectral_theorem
  simpa [U, hH, Unitary.conjStarAlgAut_apply, Function.comp_def] using hs

theorem takagiHermitianSquare_eigenvalue_nonneg
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) :
    0 ≤ (Matrix.isHermitian_mul_conjTranspose_self S).eigenvalues a := by
  exact Matrix.eigenvalues_self_mul_conjTranspose_nonneg S a

theorem takagiHermitianSquare_singularValue_nonneg
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) :
    0 ≤ Real.sqrt ((Matrix.isHermitian_mul_conjTranspose_self S).eigenvalues a) := by
  exact Real.sqrt_nonneg _

theorem takagiHermitianSquare_eigenvalue_rankSupport
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) :
    Fintype.card
        {a : Fin m // (Matrix.isHermitian_mul_conjTranspose_self S).eigenvalues a ≠ 0} =
      Matrix.rank S := by
  have hH := Matrix.isHermitian_mul_conjTranspose_self S
  have hcard : Matrix.rank (S * Sᴴ) =
      Fintype.card {a : Fin m // hH.eigenvalues a ≠ 0} :=
    hH.rank_eq_card_non_zero_eigs
  rw [← hcard]
  exact Matrix.rank_self_mul_conjTranspose S

theorem takagiHermitianSquare_singularValue_rankSupport
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) :
    Fintype.card
        {a : Fin m //
          Real.sqrt ((Matrix.isHermitian_mul_conjTranspose_self S).eigenvalues a) ≠ 0} =
      Matrix.rank S := by
  have hnonneg :
      ∀ a : Fin m, 0 ≤ (Matrix.isHermitian_mul_conjTranspose_self S).eigenvalues a := by
    intro a
    exact takagiHermitianSquare_eigenvalue_nonneg m S a
  have hcard :
      Fintype.card
          {a : Fin m //
            Real.sqrt ((Matrix.isHermitian_mul_conjTranspose_self S).eigenvalues a) ≠ 0} =
        Fintype.card
          {a : Fin m // (Matrix.isHermitian_mul_conjTranspose_self S).eigenvalues a ≠ 0} := by
    apply Fintype.card_congr
    refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
    · intro a
      refine ⟨a.1, ?_⟩
      intro hz
      apply a.2
      simp [hz]
    · intro a
      refine ⟨a.1, ?_⟩
      intro hsqrtz
      apply a.2
      have hsq :
          (Real.sqrt
            ((Matrix.isHermitian_mul_conjTranspose_self S).eigenvalues a.1)) ^ 2 = 0 := by
        simp [hsqrtz]
      have hval :
          (Matrix.isHermitian_mul_conjTranspose_self S).eigenvalues a.1 = 0 := by
        rw [← Real.sq_sqrt (hnonneg a.1), hsq]
      exact hval
    · intro a
      rfl
    · intro a
      rfl
  rw [hcard]
  exact takagiHermitianSquare_eigenvalue_rankSupport m S

/-- Entries of a unitary matrix have norm at most one. -/
theorem matrix_unitary_entry_norm_le_one
    (m : ℕ)
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (i a : Fin m) :
    ‖(U : Matrix (Fin m) (Fin m) ℂ) i a‖ ≤ 1 := by
  exact entry_norm_bound_of_unitary U.2 i a

/-- Unit-entry bound combined with a real square-root column scaling. -/
theorem matrix_unitary_entry_mul_real_sqrt_norm_le_sqrt
    (m : ℕ)
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (i a : Fin m)
    {σ L : ℝ}
    (hσ_le : σ ≤ L) :
    ‖(U : Matrix (Fin m) (Fin m) ℂ) i a * (Real.sqrt σ : ℂ)‖ ≤
      Real.sqrt L := by
  have hentry := matrix_unitary_entry_norm_le_one m U i a
  have hsqrtnorm : ‖(Real.sqrt σ : ℂ)‖ = Real.sqrt σ :=
    RCLike.norm_of_nonneg (K := ℂ) (Real.sqrt_nonneg σ)
  calc
    ‖(U : Matrix (Fin m) (Fin m) ℂ) i a * (Real.sqrt σ : ℂ)‖
        = ‖(U : Matrix (Fin m) (Fin m) ℂ) i a‖ *
            ‖(Real.sqrt σ : ℂ)‖ := by
          rw [norm_mul]
    _ = ‖(U : Matrix (Fin m) (Fin m) ℂ) i a‖ * Real.sqrt σ := by
          rw [hsqrtnorm]
    _ ≤ 1 * Real.sqrt σ := by
          exact mul_le_mul_of_nonneg_right hentry (Real.sqrt_nonneg σ)
    _ = Real.sqrt σ := by ring
    _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hσ_le

/-- Given a Takagi-style diagonalization and an embedding of the nonzero
singular directions into `Fin k`, construct the rectangular `m × k` factor.

The same statement also carries the entry estimate used downstream: if all
singular values are bounded by `L`, then all entries of the rectangular factor
are bounded by `sqrt L`. -/
theorem complexSymmetric_takagi_factor_from_supportEmbedding
    (m k : ℕ)
    {U : Matrix.unitaryGroup (Fin m) ℂ}
    {σ : Fin m → ℝ}
    (hσ_nonneg : ∀ a, 0 ≤ σ a)
    (e : {a : Fin m // σ a ≠ 0} ↪ Fin k)
    (S : Matrix (Fin m) (Fin m) ℂ)
    (hTakagi :
      S =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose) :
    ∃ A : Matrix (Fin m) (Fin k) ℂ,
      S = A * A.transpose ∧
      ∀ {L : ℝ}, 0 ≤ L → (∀ a, σ a ≤ L) →
        ∀ i b, ‖A i b‖ ≤ Real.sqrt L := by
  let nz := {a : Fin m // σ a ≠ 0}
  let A : Matrix (Fin m) (Fin k) ℂ := fun i b =>
    if hb : b ∈ Set.range e then
      (U : Matrix (Fin m) (Fin m) ℂ) i (Classical.choose hb).1 *
        (Real.sqrt (σ (Classical.choose hb).1) : ℂ)
    else 0
  refine ⟨A, ?_, ?_⟩
  · ext i j
    rw [hTakagi]
    have hdiag :
        (((U : Matrix (Fin m) (Fin m) ℂ) *
            Matrix.diagonal (fun a => (σ a : ℂ)) *
            (U : Matrix (Fin m) (Fin m) ℂ).transpose) i j) =
          ∑ a : Fin m,
            (U : Matrix (Fin m) (Fin m) ℂ) i a * (σ a : ℂ) *
              (U : Matrix (Fin m) (Fin m) ℂ) j a := by
      simp [Matrix.mul_apply, Matrix.diagonal]
    rw [hdiag]
    have hright :
        ((A * A.transpose) i j) =
          ∑ a : nz,
            ((U : Matrix (Fin m) (Fin m) ℂ) i a.1 *
                (Real.sqrt (σ a.1) : ℂ)) *
              ((U : Matrix (Fin m) (Fin m) ℂ) j a.1 *
                (Real.sqrt (σ a.1) : ℂ)) := by
      have hsum :=
        sum_mul_indicator_embedding e
          (fun a : nz =>
            (U : Matrix (Fin m) (Fin m) ℂ) i a.1 *
              (Real.sqrt (σ a.1) : ℂ))
          (fun a : nz =>
            (U : Matrix (Fin m) (Fin m) ℂ) j a.1 *
              (Real.sqrt (σ a.1) : ℂ))
      simpa [A, Matrix.mul_apply, Matrix.transpose_apply] using hsum
    rw [hright]
    let F : Fin m → ℂ := fun a =>
      (U : Matrix (Fin m) (Fin m) ℂ) i a * (σ a : ℂ) *
        (U : Matrix (Fin m) (Fin m) ℂ) j a
    have hdrop :
        (∑ a : Fin m, F a) = ∑ a : nz, F a.1 := by
      calc
        (∑ a : Fin m, F a)
            = ∑ a : Fin m, if σ a ≠ 0 then F a else 0 := by
              apply Finset.sum_congr rfl
              intro a _ha
              by_cases hσa : σ a ≠ 0
              · simp [hσa]
              · have hzero : σ a = 0 := not_ne_iff.mp hσa
                simp [F, hzero]
        _ = ∑ a ∈ Finset.univ.filter (fun a : Fin m => σ a ≠ 0), F a := by
              rw [Finset.sum_filter]
        _ = ∑ a : nz, F a.1 := by
              simpa [nz] using
                (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
                  (p := fun a : Fin m => σ a ≠ 0) (f := F)).symm
    rw [hdrop]
    apply Finset.sum_congr rfl
    intro a _ha
    simp [F]
    have hs :
        (Real.sqrt (σ a.1) : ℂ) * (Real.sqrt (σ a.1) : ℂ) =
          (σ a.1 : ℂ) := by
      have hreal : Real.sqrt (σ a.1) * Real.sqrt (σ a.1) = σ a.1 := by
        rw [← sq]
        exact Real.sq_sqrt (hσ_nonneg a.1)
      exact_mod_cast hreal
    rw [← hs]
    ring
  · intro L _hL_nonneg hσ_le i b
    by_cases hb : b ∈ Set.range e
    · dsimp [A]
      rw [dif_pos hb]
      exact
        matrix_unitary_entry_mul_real_sqrt_norm_le_sqrt
          m U i (Classical.choose hb).1 (hσ_le (Classical.choose hb).1)
    · dsimp [A]
      rw [dif_neg hb]
      rw [norm_zero]
      exact Real.sqrt_nonneg L

/-- A Takagi diagonalization with bounded nonzero support and singular values
bounded by the entry-`ℓ¹` size gives the entry-controlled rectangular factor. -/
theorem complexSymmetric_entryL1_of_takagiDiagonalData
    (m k : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    {U : Matrix.unitaryGroup (Fin m) ℂ}
    {σ : Fin m → ℝ}
    (hσ_nonneg : ∀ a, 0 ≤ σ a)
    (hTakagi :
      S =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose)
    (hcard : Fintype.card {a : Fin m // σ a ≠ 0} ≤ k)
    (hσ_bound : ∀ a, σ a ≤ matrixEntryL1Bound m S) :
    ∃ A : Matrix (Fin m) (Fin k) ℂ,
      S = A * A.transpose ∧
      ∀ i a, ‖A i a‖ ≤ Real.sqrt (matrixEntryL1Bound m S) := by
  let nz := {a : Fin m // σ a ≠ 0}
  have hnzEmb : Nonempty (nz ↪ Fin k) := by
    rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_fin]
    exact hcard
  let e : nz ↪ Fin k := Classical.choice hnzEmb
  rcases complexSymmetric_takagi_factor_from_supportEmbedding
      (m := m) (k := k) (U := U) (σ := σ) hσ_nonneg e S hTakagi with
    ⟨A, hA_factor, hA_bound⟩
  refine ⟨A, hA_factor, ?_⟩
  intro i a
  exact hA_bound (matrixEntryL1Bound_nonneg m S) hσ_bound i a

/-- Same as `complexSymmetric_entryL1_of_takagiDiagonalData`, with the support
bound supplied by the rank-support identity and the requested rank bound. -/
theorem complexSymmetric_entryL1_of_takagiDiagonalData_rankSupport
    (m k : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    {U : Matrix.unitaryGroup (Fin m) ℂ}
    {σ : Fin m → ℝ}
    (hσ_nonneg : ∀ a, 0 ≤ σ a)
    (hTakagi :
      S =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose)
    (hrankSupport : Fintype.card {a : Fin m // σ a ≠ 0} = S.rank)
    (hRank : S.rank ≤ k)
    (hσ_bound : ∀ a, σ a ≤ matrixEntryL1Bound m S) :
    ∃ A : Matrix (Fin m) (Fin k) ℂ,
      S = A * A.transpose ∧
      ∀ i a, ‖A i a‖ ≤ Real.sqrt (matrixEntryL1Bound m S) := by
  exact complexSymmetric_entryL1_of_takagiDiagonalData
    (m := m) (k := k) (S := S) (U := U) (σ := σ)
    hσ_nonneg hTakagi (by simpa [hrankSupport] using hRank) hσ_bound

/-- An entry-controlled complex symmetric factorization immediately gives the
small-entry factorization needed by the tail realization theorem. -/
theorem complexSymmetric_factorSmall_rankLE_of_entryL1
    (m k : ℕ)
    (hentry :
      ∀ {S : Matrix (Fin m) (Fin m) ℂ},
        S.transpose = S →
        S.rank ≤ k →
        ∃ A : Matrix (Fin m) (Fin k) ℂ,
          S = A * A.transpose ∧
          ∀ i a, ‖A i a‖ ≤ Real.sqrt (matrixEntryL1Bound m S))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ S : Matrix (Fin m) (Fin m) ℂ,
        S.transpose = S →
        S.rank ≤ k →
        (∀ i j, ‖S i j‖ < δ) →
        ∃ A : Matrix (Fin m) (Fin k) ℂ,
          (∀ i a, ‖A i a‖ < ε) ∧
          S = A * A.transpose := by
  let C : ℝ := (((m * m : ℕ) : ℝ) + 1)
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  rcases exists_pos_mul_sqrt_lt hε hC_pos with ⟨δ, hδ_pos, hδ_small⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro S hSym hRank hSmall
  rcases hentry hSym hRank with ⟨A, hA_factor, hA_bound⟩
  have hL1 : matrixEntryL1Bound m S < C * δ := by
    simpa [C] using matrixEntryL1Bound_lt_of_entry_bound (m := m) hδ_pos hSmall
  have hsqrt : Real.sqrt (matrixEntryL1Bound m S) < ε :=
    real_sqrt_lt_of_lt_mul_bound
      (matrixEntryL1Bound_nonneg m S) hL1 hδ_small
  refine ⟨A, ?_, hA_factor⟩
  intro i a
  exact lt_of_le_of_lt (hA_bound i a) hsqrt

/-- Source-coordinate version of `complexSymmetric_factorSmall_rankLE_of_entryL1`. -/
theorem sourceComplexSymmetric_factorSmall_rankLE_of_entryL1
    (m k : ℕ)
    (hentry :
      ∀ {S : Matrix (Fin m) (Fin m) ℂ},
        S.transpose = S →
        S.rank ≤ k →
        ∃ A : Matrix (Fin m) (Fin k) ℂ,
          S = A * A.transpose ∧
          ∀ i a, ‖A i a‖ ≤ Real.sqrt (matrixEntryL1Bound m S))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ S : Fin m → Fin m → ℂ,
        S ∈ sourceSymmetricMatrixSpace m →
        (Matrix.of fun i j : Fin m => S i j).rank ≤ k →
        (∀ i j, ‖S i j‖ < δ) →
        ∃ q : Fin m → Fin k → ℂ,
          (∀ i a, ‖q i a‖ < ε) ∧
          sourceComplexDotGram k m q = S := by
  rcases complexSymmetric_factorSmall_rankLE_of_entryL1
      (m := m) (k := k) hentry hε with
    ⟨δ, hδ_pos, hfactor⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro S hSym hRank hSmall
  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j : Fin m => S i j
  have hM_sym : M.transpose = M := by
    ext i j
    exact hSym j i
  have hM_small : ∀ i j, ‖M i j‖ < δ := by
    intro i j
    exact hSmall i j
  rcases hfactor M hM_sym hRank hM_small with ⟨A, hA_small, hA_factor⟩
  refine ⟨fun i a => A i a, hA_small, ?_⟩
  ext i j
  have hij := congrFun (congrFun hA_factor i) j
  simp [sourceComplexDotGram, M, Matrix.mul_apply] at hij ⊢
  exact hij.symm

end BHW
