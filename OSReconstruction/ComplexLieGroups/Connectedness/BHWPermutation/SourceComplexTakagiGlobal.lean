import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTakagiAssembly

/-!
# Global fixed-eigenbasis support for Autonne-Takagi

This file starts the final finite-dimensional collection step in the
Autonne-Takagi route.  The local positive-eigenspace fixed bases and the
matrix-algebra assembly theorem are already checked; here we connect the
custom Takagi eigenspaces to Mathlib's Hermitian-square eigenspace
decomposition.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open DirectSum
open scoped Matrix.Norms.Operator ComplexOrder ComplexConjugate

namespace BHW

/-- The Hermitian-square eigenspace family indexed by Mathlib's eigenvalue
subtype. -/
abbrev takagiHermitianSquareEigenSubspace
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (mu : Module.End.Eigenvalues ((S * Sᴴ).toEuclideanLin)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
  Module.End.eigenspace ((S * Sᴴ).toEuclideanLin) (mu : ℂ)

/-- Sigma index for the collected Hermitian-square eigenspace basis. -/
abbrev takagiHermitianSquareFixedEigenbasisIndex
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) : Type :=
  Σ mu : Module.End.Eigenvalues ((S * Sᴴ).toEuclideanLin),
    Fin (Module.finrank ℂ (takagiHermitianSquareEigenSubspace m S mu))

/-- The custom Takagi Hermitian-square eigenspace is the standard eigenspace
of the Euclidean linear map associated to `S * Sᴴ`. -/
theorem takagiHermitianEigenspace_eq_eigenspace_toEuclideanLin
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) (lambda : ℝ) :
    takagiHermitianEigenspace m S lambda =
      Module.End.eigenspace ((S * Sᴴ).toEuclideanLin) (lambda : ℂ) := by
  ext v
  constructor
  · intro hv
    rw [Module.End.mem_eigenspace_iff]
    change (S * Sᴴ).toEuclideanLin v = (lambda : ℂ) • v
    ext i
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin, Matrix.toLin'_apply]
      using congrFun hv i
  · intro hv
    rw [Module.End.mem_eigenspace_iff] at hv
    change (S * Sᴴ).toEuclideanLin v = (lambda : ℂ) • v at hv
    ext i
    have hi := congrArg (fun w : EuclideanSpace ℂ (Fin m) => (w : Fin m → ℂ) i) hv
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin, Matrix.toLin'_apply] using hi

/-- Each eigenvalue of the Hermitian square `S * Sᴴ`, viewed through Mathlib's
Euclidean linear map, is real. -/
theorem takagiHermitianSquare_eigenvalue_real
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (mu : Module.End.Eigenvalues ((S * Sᴴ).toEuclideanLin)) :
    ((RCLike.re (mu : ℂ) : ℝ) : ℂ) = (mu : ℂ) := by
  let T : Module.End ℂ (EuclideanSpace ℂ (Fin m)) := (S * Sᴴ).toEuclideanLin
  have hH : (S * Sᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self S
  have hT : T.IsSymmetric := by
    simpa [T] using (Matrix.isHermitian_iff_isSymmetric.mp hH)
  have hmu : Module.End.HasEigenvalue T (mu : ℂ) := by
    simpa [T] using mu.property
  exact RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hmu)

/-- Each eigenvalue of the Hermitian square `S * Sᴴ` is nonnegative. -/
theorem takagiHermitianSquare_eigenvalue_nonneg_of_eigenvalue
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (mu : Module.End.Eigenvalues ((S * Sᴴ).toEuclideanLin)) :
    0 ≤ RCLike.re (mu : ℂ) := by
  let T : Module.End ℂ (EuclideanSpace ℂ (Fin m)) := (S * Sᴴ).toEuclideanLin
  have hmu : Module.End.HasEigenvalue T (mu : ℂ) := by
    simpa [T] using mu.property
  have hreal : ((RCLike.re (mu : ℂ) : ℝ) : ℂ) = (mu : ℂ) :=
    takagiHermitianSquare_eigenvalue_real m S mu
  have hmu_real :
      Module.End.HasEigenvalue T (((RCLike.re (mu : ℂ) : ℝ) : ℂ)) := by
    rw [hreal]
    exact hmu
  have hnn : ∀ x : EuclideanSpace ℂ (Fin m), 0 ≤ RCLike.re (inner ℂ x (T x)) := by
    intro x
    have hpsd : (S * Sᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose S
    simpa [T, Matrix.toEuclideanLin, Matrix.toLpLin, Matrix.toLin'_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      hpsd.re_dotProduct_nonneg (x : Fin m → ℂ)
  exact eigenvalue_nonneg_of_nonneg
    (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin m)) hmu_real hnn

/-- The prescribed orthonormal basis on a Hermitian-square eigenspace: on
positive eigenspaces it is the checked fixed Takagi basis transported to
Mathlib's eigenspace, while on the zero eigenspace it is an arbitrary standard
orthonormal basis. -/
noncomputable def takagiHermitianSquareEigenvalueFixedBasis
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    (mu : Module.End.Eigenvalues ((S * Sᴴ).toEuclideanLin)) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ (takagiHermitianSquareEigenSubspace m S mu))) ℂ
      (takagiHermitianSquareEigenSubspace m S mu) := by
  classical
  let V := takagiHermitianSquareEigenSubspace m S mu
  let lambda : ℝ := RCLike.re (mu : ℂ)
  by_cases hpos : 0 < lambda
  · have hspace : takagiHermitianEigenspace m S lambda = V := by
      dsimp [V, takagiHermitianSquareEigenSubspace, lambda]
      rw [takagiHermitianEigenspace_eq_eigenspace_toEuclideanLin]
      exact congrArg
        (fun z : ℂ => Module.End.eigenspace ((S * Sᴴ).toEuclideanLin) z)
        (takagiHermitianSquare_eigenvalue_real m S mu)
    let L : takagiHermitianEigenspace m S lambda ≃ₗᵢ[ℂ] V :=
      LinearIsometryEquiv.ofEq
        (takagiHermitianEigenspace m S lambda) V hspace
    have hfin :
        Module.finrank ℂ (takagiHermitianEigenspace m S lambda) =
          Module.finrank ℂ V :=
      LinearEquiv.finrank_eq L.toLinearEquiv
    exact
      ((takagiPositiveEigenspaceFixedBasis
          (m := m) (S := S) hSym hpos).map L).reindex (finCongr hfin)
  · exact stdOrthonormalBasis ℂ V

/-- Each vector of the prescribed per-eigenvalue basis satisfies the Takagi
column equation with singular value `sqrt (re mu)`. -/
theorem takagiHermitianSquareEigenvalueFixedBasis_col_eigen
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    (mu : Module.End.Eigenvalues ((S * Sᴴ).toEuclideanLin))
    (i : Fin (Module.finrank ℂ (takagiHermitianSquareEigenSubspace m S mu))) :
    let lambda : ℝ := RCLike.re (mu : ℂ)
    takagiConjugateLinearEuclideanMap m S
        ((takagiHermitianSquareEigenvalueFixedBasis
          (m := m) (S := S) hSym mu i :
          takagiHermitianSquareEigenSubspace m S mu) :
          EuclideanSpace ℂ (Fin m)) =
      (Real.sqrt lambda : ℂ) •
        ((takagiHermitianSquareEigenvalueFixedBasis
          (m := m) (S := S) hSym mu i :
          takagiHermitianSquareEigenSubspace m S mu) :
          EuclideanSpace ℂ (Fin m)) := by
  intro lambda
  classical
  by_cases hpos : 0 < lambda
  · have hpos' : 0 < (mu : ℂ).re := by
      simpa [lambda] using hpos
    unfold takagiHermitianSquareEigenvalueFixedBasis
    simp [hpos', lambda]
    apply takagiPositiveEigenspace_fixedBasis_col_eigen
  · have hlambda_nonneg : 0 ≤ lambda := by
      simpa [lambda] using
        takagiHermitianSquare_eigenvalue_nonneg_of_eigenvalue m S mu
    have hlambda_zero : lambda = 0 := le_antisymm (le_of_not_gt hpos) hlambda_nonneg
    let v : EuclideanSpace ℂ (Fin m) :=
      ((takagiHermitianSquareEigenvalueFixedBasis
        (m := m) (S := S) hSym mu i :
        takagiHermitianSquareEigenSubspace m S mu) :
        EuclideanSpace ℂ (Fin m))
    change takagiConjugateLinearEuclideanMap m S v = (Real.sqrt lambda : ℂ) • v
    have hmu_zero : (mu : ℂ) = 0 := by
      rw [← takagiHermitianSquare_eigenvalue_real m S mu]
      simp [lambda, hlambda_zero]
    have hvT :
        (S * Sᴴ).toEuclideanLin v = (mu : ℂ) • v := by
      have hv_mem :
          v ∈ Module.End.eigenspace ((S * Sᴴ).toEuclideanLin) (mu : ℂ) :=
        (takagiHermitianSquareEigenvalueFixedBasis
          (m := m) (S := S) hSym mu i).2
      rwa [Module.End.mem_eigenspace_iff] at hv_mem
    have hv0_euclidean : (S * Sᴴ).toEuclideanLin v = 0 := by
      simpa [hmu_zero] using hvT
    have hv0 : (S * Sᴴ) *ᵥ (v : Fin m → ℂ) = 0 := by
      ext j
      have hj := congrArg
        (fun w : EuclideanSpace ℂ (Fin m) => (w : Fin m → ℂ) j) hv0_euclidean
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin, Matrix.toLin'_apply] using hj
    have hkill :=
      takagiConjugateLinearEuclideanMap_zero_eigenspace_eq_zero
        (m := m) (S := S) hSym (v := v) hv0
    simp [hkill, hlambda_zero]

/-- The collected orthonormal basis obtained from the fixed bases on positive
Hermitian-square eigenspaces and the standard basis on the zero eigenspace. -/
noncomputable def takagiHermitianSquareFixedEigenbasisSigma
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S) :
    OrthonormalBasis (takagiHermitianSquareFixedEigenbasisIndex m S) ℂ
      (EuclideanSpace ℂ (Fin m)) := by
  let T : Module.End ℂ (EuclideanSpace ℂ (Fin m)) := (S * Sᴴ).toEuclideanLin
  let V : Module.End.Eigenvalues T → Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
    fun mu => Module.End.eigenspace T (mu : ℂ)
  have hH : (S * Sᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self S
  have hT : T.IsSymmetric := by
    simpa [T] using (Matrix.isHermitian_iff_isSymmetric.mp hH)
  have hInt : DirectSum.IsInternal V := by
    simpa [V] using hT.direct_sum_isInternal
  have hOrth : OrthogonalFamily ℂ (fun mu => V mu) fun mu => (V mu).subtypeₗᵢ := by
    simpa [V] using hT.orthogonalFamily_eigenspaces'
  exact hInt.collectedOrthonormalBasis hOrth
    (fun mu => takagiHermitianSquareEigenvalueFixedBasis (m := m) (S := S) hSym mu)

/-- The collected Sigma-indexed fixed eigenbasis satisfies the Takagi column
equation. -/
theorem takagiHermitianSquareFixedEigenbasisSigma_col_eigen
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    (idx : takagiHermitianSquareFixedEigenbasisIndex m S) :
    let lambda : ℝ := RCLike.re (idx.1 : ℂ)
    takagiConjugateLinearEuclideanMap m S
        (takagiHermitianSquareFixedEigenbasisSigma
          (m := m) (S := S) hSym idx) =
      (Real.sqrt lambda : ℂ) •
        takagiHermitianSquareFixedEigenbasisSigma
          (m := m) (S := S) hSym idx := by
  cases idx with
  | mk mu i =>
      intro lambda
      dsimp [takagiHermitianSquareFixedEigenbasisSigma]
      rw [DirectSum.IsInternal.collectedOrthonormalBasis]
      simp [DirectSum.IsInternal.collectedBasis_coe]
      simpa [lambda] using
        takagiHermitianSquareEigenvalueFixedBasis_col_eigen
          (m := m) (S := S) hSym mu i

/-- The collected Sigma index has cardinality `m`; packaged as the reindexing
equivalence used by the final Euclidean basis. -/
noncomputable def takagiHermitianSquareFixedEigenbasisIndexEquivFin
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S) :
    takagiHermitianSquareFixedEigenbasisIndex m S ≃ Fin m := by
  let b := takagiHermitianSquareFixedEigenbasisSigma (m := m) (S := S) hSym
  have hcard : Fintype.card (takagiHermitianSquareFixedEigenbasisIndex m S) = m := by
    have hb := Module.finrank_eq_card_basis b.toBasis
    simpa [b, takagiHermitianSquareFixedEigenbasisIndex, finrank_euclideanSpace_fin]
      using hb.symm
  exact Fintype.equivFinOfCardEq hcard

/-- The collected fixed Hermitian-square eigenbasis reindexed by `Fin m`. -/
noncomputable def takagiHermitianSquareFixedEigenbasis
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S) :
    OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) := by
  let b := takagiHermitianSquareFixedEigenbasisSigma (m := m) (S := S) hSym
  exact b.reindex
    (takagiHermitianSquareFixedEigenbasisIndexEquivFin
      (m := m) (S := S) hSym)

/-- Eigenvalue labels on the final `Fin m` fixed Hermitian-square basis. -/
noncomputable def takagiHermitianSquareFixedEigenbasisLambda
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S) :
    Fin m → ℝ :=
  fun a =>
    RCLike.re
      (((takagiHermitianSquareFixedEigenbasisIndexEquivFin
        (m := m) (S := S) hSym).symm a).1 : ℂ)

theorem takagiHermitianSquareFixedEigenbasisLambda_nonneg
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S) :
    ∀ a, 0 ≤ takagiHermitianSquareFixedEigenbasisLambda
      (m := m) (S := S) hSym a := by
  intro a
  unfold takagiHermitianSquareFixedEigenbasisLambda
  exact takagiHermitianSquare_eigenvalue_nonneg_of_eigenvalue m S
    ((takagiHermitianSquareFixedEigenbasisIndexEquivFin
      (m := m) (S := S) hSym).symm a).1

/-- The final `Fin m` fixed Hermitian-square basis satisfies the Takagi column
equation. -/
theorem takagiHermitianSquareFixedEigenbasis_col_eigen
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    (a : Fin m) :
    takagiConjugateLinearEuclideanMap m S
        (takagiHermitianSquareFixedEigenbasis (m := m) (S := S) hSym a) =
      (Real.sqrt
        (takagiHermitianSquareFixedEigenbasisLambda
          (m := m) (S := S) hSym a) : ℂ) •
        takagiHermitianSquareFixedEigenbasis (m := m) (S := S) hSym a := by
  let e := takagiHermitianSquareFixedEigenbasisIndexEquivFin
    (m := m) (S := S) hSym
  change takagiConjugateLinearEuclideanMap m S
        ((takagiHermitianSquareFixedEigenbasisSigma
          (m := m) (S := S) hSym).reindex e a) =
      (Real.sqrt
        (RCLike.re ((e.symm a).1 : ℂ)) : ℂ) •
        (takagiHermitianSquareFixedEigenbasisSigma
          (m := m) (S := S) hSym).reindex e a
  simpa [e, takagiHermitianSquareFixedEigenbasisLambda] using
    takagiHermitianSquareFixedEigenbasisSigma_col_eigen
      (m := m) (S := S) hSym (e.symm a)

/-- In a unitary Takagi diagonalization, the number of nonzero singular
directions is the matrix rank. -/
theorem takagi_rankSupport_of_unitary_diagonalization
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ}
    {U : Matrix.unitaryGroup (Fin m) ℂ} {σ : Fin m → ℝ}
    (hTakagi :
      S =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose) :
    Fintype.card {a : Fin m // σ a ≠ 0} = S.rank := by
  have hUunit : IsUnit (U : Matrix (Fin m) (Fin m) ℂ).det :=
    Matrix.UnitaryGroup.det_isUnit U
  have hUtunit : IsUnit ((U : Matrix (Fin m) (Fin m) ℂ).transpose).det :=
    Matrix.isUnit_det_transpose (U : Matrix (Fin m) (Fin m) ℂ) hUunit
  have hrankeq : S.rank = (Matrix.diagonal (fun a => (σ a : ℂ))).rank := by
    calc
      S.rank =
          ((U : Matrix (Fin m) (Fin m) ℂ) *
            Matrix.diagonal (fun a => (σ a : ℂ)) *
            (U : Matrix (Fin m) (Fin m) ℂ).transpose).rank := by
        rw [hTakagi]
      _ =
          ((U : Matrix (Fin m) (Fin m) ℂ) *
            Matrix.diagonal (fun a => (σ a : ℂ))).rank := by
        rw [Matrix.rank_mul_eq_left_of_isUnit_det
          ((U : Matrix (Fin m) (Fin m) ℂ).transpose)
          ((U : Matrix (Fin m) (Fin m) ℂ) *
            Matrix.diagonal (fun a => (σ a : ℂ))) hUtunit]
      _ = (Matrix.diagonal (fun a => (σ a : ℂ))).rank := by
        rw [Matrix.rank_mul_eq_right_of_isUnit_det
          (U : Matrix (Fin m) (Fin m) ℂ)
          (Matrix.diagonal (fun a => (σ a : ℂ))) hUunit]
  rw [hrankeq, Matrix.rank_diagonal]
  simp

/-- Autonne-Takagi with the explicit entry-`ℓ¹` rectangular factor. -/
theorem complexSymmetric_autonneTakagi_entryL1
    (m k : ℕ) {S : Matrix (Fin m) (Fin m) ℂ}
    (hSym : S.transpose = S) (hRank : S.rank ≤ k) :
    ∃ A : Matrix (Fin m) (Fin k) ℂ,
      S = A * A.transpose ∧
      ∀ i a, ‖A i a‖ ≤ Real.sqrt (matrixEntryL1Bound m S) := by
  let b := takagiHermitianSquareFixedEigenbasis (m := m) (S := S) hSym
  let σ := fun a : Fin m =>
    Real.sqrt (takagiHermitianSquareFixedEigenbasisLambda
      (m := m) (S := S) hSym a)
  have hcol : ∀ a : Fin m,
      takagiConjugateLinearEuclideanMap m S (b a) = (σ a : ℂ) • b a := by
    intro a
    simpa [b, σ] using
      takagiHermitianSquareFixedEigenbasis_col_eigen
        (m := m) (S := S) hSym a
  rcases complexSymmetric_takagi_exists_unitary_of_orthonormalBasis_col_eigen
      (m := m) (S := S) b σ hcol with
    ⟨U, hTakagi⟩
  have hσ_nonneg : ∀ a, 0 ≤ σ a := by
    intro a
    exact Real.sqrt_nonneg _
  have hrankSupport : Fintype.card {a : Fin m // σ a ≠ 0} = S.rank :=
    takagi_rankSupport_of_unitary_diagonalization
      (m := m) (S := S) (U := U) (σ := σ) hTakagi
  exact complexSymmetric_entryL1_of_autonneTakagiDiagonalization
    (m := m) (k := k) (S := S) (U := U) (σ := σ)
    hσ_nonneg hTakagi hrankSupport hRank

/-- Small-entry complex symmetric factorization, with the Autonne-Takagi
entry theorem discharged. -/
theorem complexSymmetric_factorSmall_rankLE
    (m k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ S : Matrix (Fin m) (Fin m) ℂ,
        S.transpose = S →
        S.rank ≤ k →
        (∀ i j, ‖S i j‖ < δ) →
        ∃ A : Matrix (Fin m) (Fin k) ℂ,
          (∀ i a, ‖A i a‖ < ε) ∧
          S = A * A.transpose := by
  exact complexSymmetric_factorSmall_rankLE_of_entryL1
    (m := m) (k := k)
    (fun {_S} hSym hRank =>
      complexSymmetric_autonneTakagi_entryL1
        (m := m) (k := k) hSym hRank)
    hε

/-- Source-coordinate small-entry same-Gram factorization, with the
Autonne-Takagi entry theorem discharged. -/
theorem sourceComplexSymmetric_factorSmall_rankLE
    (m k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ S : Fin m → Fin m → ℂ,
        S ∈ sourceSymmetricMatrixSpace m →
        (Matrix.of fun i j : Fin m => S i j).rank ≤ k →
        (∀ i j, ‖S i j‖ < δ) →
        ∃ q : Fin m → Fin k → ℂ,
          (∀ i a, ‖q i a‖ < ε) ∧
          sourceComplexDotGram k m q = S := by
  exact sourceComplexSymmetric_factorSmall_rankLE_of_entryL1
    (m := m) (k := k)
    (fun {_S} hSym hRank =>
      complexSymmetric_autonneTakagi_entryL1
        (m := m) (k := k) hSym hRank)
    hε

end BHW
