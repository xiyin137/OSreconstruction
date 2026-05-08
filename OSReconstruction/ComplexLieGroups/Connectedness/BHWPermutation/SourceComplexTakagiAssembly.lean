import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTakagiEntry

/-!
# Algebraic assembly for Autonne-Takagi columns

This file proves the purely matrix-algebraic endpoint of the Takagi assembly:
if the columns of a unitary matrix satisfy the conjugate-linear Takagi
eigenvector equation, then the corresponding matrix diagonalization is
`S = U * diagonal σ * Uᵀ`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator ComplexOrder ComplexConjugate

namespace BHW

/-- The unitary matrix whose columns are a complex orthonormal basis of
`EuclideanSpace ℂ (Fin m)`. -/
noncomputable def matrixUnitaryOfOrthonormalBasis
    (m : ℕ) (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) :
    Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin m) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin m) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

@[simp]
theorem matrixUnitaryOfOrthonormalBasis_apply
    (m : ℕ) (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (i a : Fin m) :
    ((matrixUnitaryOfOrthonormalBasis m b : Matrix.unitaryGroup (Fin m) ℂ) :
      Matrix (Fin m) (Fin m) ℂ) i a = (b a : EuclideanSpace ℂ (Fin m)) i :=
  rfl

/-- The transpose of a unitary complex matrix also has the needed left inverse. -/
theorem matrix_unitary_star_transpose_mul_transpose
    (m : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ) :
    star ((U : Matrix (Fin m) (Fin m) ℂ).transpose) *
      ((U : Matrix (Fin m) (Fin m) ℂ).transpose) = 1 := by
  ext i j
  have h := congrFun (congrFun U.2.2 j) i
  by_cases hij : i = j
  · subst j
    simpa [Matrix.mul_apply, mul_comm] using h
  · have hji : j ≠ i := by
      exact fun h => hij h.symm
    simpa [Matrix.mul_apply, hij, hji, mul_comm] using h

/-- If the unitary columns are Takagi eigenvectors for the conjugate-linear map
`v ↦ S *ᵥ star v`, then they assemble into the Takagi matrix identity. -/
theorem complexSymmetric_takagi_matrix_eq_of_col_eigen
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (U : Matrix.unitaryGroup (Fin m) ℂ) (σ : Fin m → ℝ)
    (hcol : ∀ a : Fin m,
      takagiConjugateLinearMap m S (fun i => (U : Matrix (Fin m) (Fin m) ℂ) i a) =
        (σ a : ℂ) • fun i => (U : Matrix (Fin m) (Fin m) ℂ) i a) :
    S =
      (U : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.diagonal (fun a => (σ a : ℂ)) *
        (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
  have hright := matrix_unitary_star_transpose_mul_transpose m U
  have hSU :
      S * star ((U : Matrix (Fin m) (Fin m) ℂ).transpose) =
        (U : Matrix (Fin m) (Fin m) ℂ) * Matrix.diagonal (fun a => (σ a : ℂ)) := by
    ext i a
    have h := congrFun (hcol a) i
    simpa [takagiConjugateLinearMap, Matrix.mul_apply, Matrix.diagonal, dotProduct, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  calc
    S = S * 1 := by
      rw [mul_one]
    _ = S * (star ((U : Matrix (Fin m) (Fin m) ℂ).transpose) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose) := by
      rw [hright]
    _ = (S * star ((U : Matrix (Fin m) (Fin m) ℂ).transpose)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
      rw [Matrix.mul_assoc]
    _ = ((U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ))) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
      rw [hSU]
    _ = (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
      rw [Matrix.mul_assoc]

/-- An orthonormal basis satisfying the Takagi conjugate-linear eigenvector
equation produces the corresponding unitary Takagi matrix identity. -/
theorem complexSymmetric_takagi_exists_unitary_of_orthonormalBasis_col_eigen
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (σ : Fin m → ℝ)
    (hcol : ∀ a : Fin m,
      takagiConjugateLinearEuclideanMap m S (b a) = (σ a : ℂ) • b a) :
    ∃ U : Matrix.unitaryGroup (Fin m) ℂ,
      S =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
  let U := matrixUnitaryOfOrthonormalBasis m b
  refine ⟨U, ?_⟩
  apply complexSymmetric_takagi_matrix_eq_of_col_eigen
  intro a
  ext i
  have h := congrArg (fun v : EuclideanSpace ℂ (Fin m) => (v : Fin m → ℂ) i) (hcol a)
  simpa [U, takagiConjugateLinearEuclideanMap, smul_eq_mul] using h

/-- A Hermitian-square orthonormal eigenbasis whose positive eigenspace
components are fixed by the normalized Takagi conjugation assembles to an
Autonne-Takagi unitary.  This isolates the remaining global basis-construction
problem from the matrix-algebra endpoint. -/
theorem complexSymmetric_takagi_exists_unitary_of_fixedHermitianEigenbasis
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (lambda : Fin m → ℝ)
    (hlambda_nonneg : ∀ a, 0 ≤ lambda a)
    (heig : ∀ a,
      (S * Sᴴ) *ᵥ ((b a : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) =
        (lambda a : ℂ) • ((b a : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ))
    (hfixed : ∀ a (ha : 0 < lambda a),
      takagiPositiveEigenspaceConjugation (m := m) (S := S) hSym ha
          (⟨b a, heig a⟩ : takagiHermitianEigenspace m S (lambda a)) =
        (⟨b a, heig a⟩ : takagiHermitianEigenspace m S (lambda a))) :
    ∃ U : Matrix.unitaryGroup (Fin m) ℂ,
      S =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (Real.sqrt (lambda a) : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
  apply complexSymmetric_takagi_exists_unitary_of_orthonormalBasis_col_eigen
  intro a
  by_cases ha : 0 < lambda a
  · have hcol :=
      takagiConjugateLinearEuclideanMap_eq_sqrt_smul_of_positive_fixed
        (m := m) (S := S) (lambda := lambda a) hSym ha
        (x := (⟨b a, heig a⟩ : takagiHermitianEigenspace m S (lambda a)))
        (hfixed a ha)
    simpa using hcol
  · have hlambda_le : lambda a ≤ 0 := le_of_not_gt ha
    have hlambda_zero : lambda a = 0 :=
      le_antisymm hlambda_le (hlambda_nonneg a)
    have hv0 : (S * Sᴴ) *ᵥ ((b a : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) = 0 := by
      have h := heig a
      simpa [hlambda_zero] using h
    have hzero :=
      takagiConjugateLinearEuclideanMap_zero_eigenspace_eq_zero
        (m := m) (S := S) hSym (v := b a) hv0
    simp [hzero, hlambda_zero]

/-- Entry-controlled rectangular factorization once the fixed Hermitian
eigenbasis and the rank-support identity are available. -/
theorem complexSymmetric_entryL1_of_fixedHermitianEigenbasis
    (m k : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (lambda : Fin m → ℝ)
    (hlambda_nonneg : ∀ a, 0 ≤ lambda a)
    (heig : ∀ a,
      (S * Sᴴ) *ᵥ ((b a : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) =
        (lambda a : ℂ) • ((b a : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ))
    (hfixed : ∀ a (ha : 0 < lambda a),
      takagiPositiveEigenspaceConjugation (m := m) (S := S) hSym ha
          (⟨b a, heig a⟩ : takagiHermitianEigenspace m S (lambda a)) =
        (⟨b a, heig a⟩ : takagiHermitianEigenspace m S (lambda a)))
    (hrankSupport :
      Fintype.card {a : Fin m // Real.sqrt (lambda a) ≠ 0} = S.rank)
    (hRank : S.rank ≤ k) :
    ∃ A : Matrix (Fin m) (Fin k) ℂ,
      S = A * A.transpose ∧
      ∀ i a, ‖A i a‖ ≤ Real.sqrt (matrixEntryL1Bound m S) := by
  rcases complexSymmetric_takagi_exists_unitary_of_fixedHermitianEigenbasis
      (m := m) (S := S) hSym b lambda hlambda_nonneg heig hfixed with
    ⟨U, hTakagi⟩
  exact complexSymmetric_entryL1_of_autonneTakagiDiagonalization
    (m := m) (k := k) (S := S) (U := U)
    (σ := fun a => Real.sqrt (lambda a))
    (fun a => Real.sqrt_nonneg (lambda a)) hTakagi hrankSupport hRank

end BHW
