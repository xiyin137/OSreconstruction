import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurPatch

/-!
# Cone support for source symmetric rank strata

This file records the elementary cone algebra used by the local
Hall-Wightman source-variety connectedness proof.  The harder topological
Stiefel-space connectedness and small-cone contraction lemmas are kept for the
next layer.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator

namespace BHW

/-- Nonzero scalar multiplication does not change matrix rank. -/
theorem matrix_rank_smul_of_ne_zero
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (c : ℂ) (hc : c ≠ 0) (A : Matrix m n ℂ) :
    (c • A).rank = A.rank := by
  have hdet : IsUnit ((c • (1 : Matrix m m ℂ)).det) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc)
  have hmul : (c • (1 : Matrix m m ℂ)) * A = c • A := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [← hmul]
  exact Matrix.rank_mul_eq_right_of_isUnit_det
    (c • (1 : Matrix m m ℂ)) A hdet

/-- Rank-exact symmetric strata are cones under nonzero complex scalar
multiplication. -/
theorem sourceSymmetricRankExactStratum_smul_mem
    {n r : ℕ} {Z : Fin n → Fin n → ℂ}
    (hZ : Z ∈ sourceSymmetricRankExactStratum n r)
    {c : ℂ} (hc : c ≠ 0) :
    (c • Z) ∈ sourceSymmetricRankExactStratum n r := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp [Pi.smul_apply, hZ.1 i j]
  · let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
    have hM :
        (Matrix.of fun i j : Fin n => (c • Z) i j) = c • M := by
      ext i j
      simp [M]
    rw [hM]
    simpa [M] using
      (matrix_rank_smul_of_ne_zero
        (m := Fin n) (n := Fin n) c hc M).trans hZ.2

/-- Scaling source configurations scales their ordinary complex dot-Gram matrix
by the square of the scalar. -/
theorem sourceComplexDotGram_smul
    (D n : ℕ) (a : ℂ) (z : Fin n → Fin D → ℂ) :
    sourceComplexDotGram D n (a • z) =
      (a * a) • sourceComplexDotGram D n z := by
  ext i j
  simp [sourceComplexDotGram, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _hμ
  ring

/-- Scaling a source configuration by the chosen square root scales its
ordinary complex dot-Gram matrix by the original scalar. -/
theorem sourceComplexDotGram_smul_sqrt
    (D n : ℕ) (c : ℂ) (z : Fin n → Fin D → ℂ) :
    sourceComplexDotGram D n ((complexSquareRootChoice c) • z) =
      c • sourceComplexDotGram D n z := by
  rw [sourceComplexDotGram_smul]
  rw [complexSquareRootChoice_mul_self]

/-- The ordinary complex dot-Gram map is continuous. -/
theorem continuous_sourceComplexDotGram
    (D n : ℕ) :
    Continuous (sourceComplexDotGram D n) := by
  unfold sourceComplexDotGram
  exact continuous_pi fun i => continuous_pi fun j =>
    continuous_finset_sum _ fun μ _ =>
      (continuous_apply_apply i μ).mul (continuous_apply_apply j μ)

/-- Full-rank complex source configurations for the ordinary dot-Gram
parametrization. -/
def sourceFullRankConfigurations
    (m r : ℕ) :
    Set (Fin m → Fin r → ℂ) :=
  {A | (Matrix.of fun (i : Fin m) (a : Fin r) => A i a).rank = r}

/-- The coordinate frame associated to an injective selection of `r` rows. -/
def selectedFullRankFrame
    {m r : ℕ} (I : Fin r → Fin m) :
    Fin m → Fin r → ℂ :=
  fun i a => if i = I a then 1 else 0

/-- The standard full-rank coordinate frame. -/
def standardFullRankConfiguration
    (m r : ℕ) (hr : r ≤ m) :
    Fin m → Fin r → ℂ :=
  selectedFullRankFrame (fun a : Fin r => Fin.castLE hr a)

/-- An injectively selected coordinate frame is a full-rank configuration. -/
theorem selectedFullRankFrame_mem_sourceFullRankConfigurations
    {m r : ℕ} {I : Fin r → Fin m} (hI : Function.Injective I) :
    selectedFullRankFrame I ∈ sourceFullRankConfigurations m r := by
  let P : Matrix (Fin m) (Fin r) ℂ :=
    Matrix.of fun i a => selectedFullRankFrame I i a
  have hle : P.rank ≤ r := by
    simpa using Matrix.rank_le_width P
  have hminor : Matrix.det (fun a b : Fin r => P (I a) b) ≠ 0 := by
    have hmat :
        (fun a b : Fin r => P (I a) b) =
          (1 : Matrix (Fin r) (Fin r) ℂ) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [P, selectedFullRankFrame]
      · have hne : I a ≠ I b := fun h => hab (hI h)
        simp [P, selectedFullRankFrame, hne, hab]
    rw [hmat, Matrix.det_one]
    exact one_ne_zero
  have hge : r ≤ P.rank :=
    matrix_rank_ge_of_nondegenerate_square_submatrix
      (A := P) (I := I) (J := id) (by simpa using hminor)
  simpa [sourceFullRankConfigurations, P] using le_antisymm hle hge

/-- The standard coordinate frame is a full-rank configuration. -/
theorem standardFullRankConfiguration_mem_sourceFullRankConfigurations
    {m r : ℕ} (hr : r ≤ m) :
    standardFullRankConfiguration m r hr ∈ sourceFullRankConfigurations m r := by
  apply selectedFullRankFrame_mem_sourceFullRankConfigurations
  intro a b h
  exact Fin.castLE_injective hr h

/-- Left multiplication by an invertible square matrix preserves full-rank
source configurations. -/
theorem sourceFullRankConfigurations_left_mul_isUnit_mem
    {m r : ℕ} {G : Matrix (Fin m) (Fin m) ℂ}
    (hG : IsUnit G.det)
    {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r) :
    (fun i a =>
      (G * (Matrix.of fun (j : Fin m) (b : Fin r) => A j b)) i a) ∈
      sourceFullRankConfigurations m r := by
  let P : Matrix (Fin m) (Fin r) ℂ :=
    Matrix.of fun (j : Fin m) (b : Fin r) => A j b
  have hrank : (G * P).rank = r := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det G P hG]
    simpa [sourceFullRankConfigurations, P] using hA
  simpa [sourceFullRankConfigurations, P] using hrank

/-- Right multiplication by an invertible square matrix preserves full-rank
source configurations. -/
theorem sourceFullRankConfigurations_right_mul_isUnit_mem
    {m r : ℕ} {R : Matrix (Fin r) (Fin r) ℂ}
    (hR : IsUnit R.det)
    {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r) :
    (fun i a =>
      ((Matrix.of fun (j : Fin m) (b : Fin r) => A j b) * R) i a) ∈
      sourceFullRankConfigurations m r := by
  let P : Matrix (Fin m) (Fin r) ℂ :=
    Matrix.of fun (j : Fin m) (b : Fin r) => A j b
  have hrank : (P * R).rank = r := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det R P hR]
    simpa [sourceFullRankConfigurations, P] using hA
  simpa [sourceFullRankConfigurations, P] using hrank

/-- A full-rank source configuration maps to the exact symmetric rank stratum
under the ordinary complex dot-Gram map. -/
theorem sourceComplexDotGram_mem_rankExact_of_fullRank
    {m r : ℕ} {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r) :
    sourceComplexDotGram r m A ∈
      sourceSymmetricRankExactStratum m r := by
  refine ⟨sourceComplexDotGram_mem_sourceSymmetricMatrixSpace r m A, ?_⟩
  let P : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i a => A i a
  let M : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun i j : Fin m => sourceComplexDotGram r m A i j
  have hM_eq : M = P * Pᵀ := by
    ext i j
    simp [M, P, sourceComplexDotGram, Matrix.mul_apply]
  have hP_rank : P.rank = r := by
    simpa [sourceFullRankConfigurations, P] using hA
  have hle : M.rank ≤ r := by
    have hmul_le : (P * Pᵀ).rank ≤ P.rank :=
      Matrix.rank_mul_le_left P Pᵀ
    rw [hM_eq]
    exact hmul_le.trans_eq hP_rank
  have hP_rank_ge : r ≤ P.rank := by
    rw [hP_rank]
  rcases exists_nondegenerate_square_submatrix_of_rank_ge P hP_rank_ge with
    ⟨I, J, hdetIJ⟩
  let PI : Matrix (Fin r) (Fin r) ℂ := fun a b => A (I a) b
  have hJinj : Function.Injective J := by
    intro a b hab
    by_contra hne
    have hzero : Matrix.det (fun x y : Fin r => P (I x) (J y)) = 0 :=
      Matrix.det_zero_of_column_eq hne (by
        intro x
        simp [hab])
    exact hdetIJ (by simpa using hzero)
  let σ : Equiv.Perm (Fin r) :=
    Equiv.ofBijective J
      ((Fintype.bijective_iff_injective_and_card J).mpr ⟨hJinj, by simp⟩)
  have hdet_perm_ne : (PI.submatrix id σ).det ≠ 0 := by
    simpa [PI, P, σ] using hdetIJ
  have hPI_det_ne : PI.det ≠ 0 := by
    have hperm := Matrix.det_permute' σ PI
    rw [hperm] at hdet_perm_ne
    intro hzero
    exact hdet_perm_ne (by simp [hzero])
  have hminor_ne :
      sourceMatrixMinor m r I I (sourceComplexDotGram r m A) ≠ 0 := by
    have hminor_eq :
        sourceMatrixMinor m r I I (sourceComplexDotGram r m A) =
          (PI * PIᵀ).det := by
      have hmatrix :
          (fun a b : Fin r => sourceComplexDotGram r m A (I a) (I b)) =
            PI * PIᵀ := by
        ext a b
        simp [sourceComplexDotGram, PI, Matrix.mul_apply]
      rw [sourceMatrixMinor, hmatrix]
    rw [hminor_eq, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hPI_det_ne hPI_det_ne
  have hge : r ≤ M.rank := by
    exact matrix_rank_ge_of_nondegenerate_square_submatrix
      (A := M) (I := I) (J := I) (by
        simpa [sourceMatrixMinor, M] using hminor_ne)
  exact le_antisymm hle hge

/-- Every exact-rank symmetric source matrix has a full-rank ordinary
dot-Gram representative in exactly that rank. -/
theorem exists_fullRank_sourceComplexDotGram_of_rankExact
    {m r : ℕ} {Z : Fin m → Fin m → ℂ}
    (hZ : Z ∈ sourceSymmetricRankExactStratum m r) :
    ∃ A : Fin m → Fin r → ℂ,
      A ∈ sourceFullRankConfigurations m r ∧
        sourceComplexDotGram r m A = Z := by
  rcases complex_symmetric_matrix_factorization_of_rank_le m r hZ.1
      (by rw [hZ.2]) with
    ⟨A, hAeq⟩
  refine ⟨A, ?_, hAeq.symm⟩
  let P : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i a => A i a
  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j : Fin m => Z i j
  have hM_eq : M = P * Pᵀ := by
    ext i j
    change Z i j = (P * Pᵀ) i j
    rw [hAeq]
    simp [P, sourceComplexDotGram, Matrix.mul_apply]
  have hM_rank : M.rank = r := by
    simpa [M] using hZ.2
  have hle : P.rank ≤ r := by
    simpa using Matrix.rank_le_width P
  have hge : r ≤ P.rank := by
    have hmul_le : (P * Pᵀ).rank ≤ P.rank :=
      Matrix.rank_mul_le_left P Pᵀ
    have hmul_rank : (P * Pᵀ).rank = r := by
      rw [← hM_eq]
      exact hM_rank
    exact hmul_rank.ge.trans hmul_le
  exact le_antisymm hle hge

/-- The exact symmetric rank stratum is the dot-Gram image of the full-rank
configuration space of the same rank. -/
theorem sourceSymmetricRankExactStratum_eq_sourceComplexDotGram_image_fullRank
    (m r : ℕ) :
    sourceSymmetricRankExactStratum m r =
      sourceComplexDotGram r m '' sourceFullRankConfigurations m r := by
  ext Z
  constructor
  · intro hZ
    rcases exists_fullRank_sourceComplexDotGram_of_rankExact hZ with
      ⟨A, hA, hAZ⟩
    exact ⟨A, hA, hAZ⟩
  · rintro ⟨A, hA, rfl⟩
    exact sourceComplexDotGram_mem_rankExact_of_fullRank hA

/-- Once the full-rank source-configuration space is path-connected, the
exact symmetric rank stratum is path-connected by the dot-Gram map. -/
theorem sourceSymmetricRankExactStratum_isPathConnected_of_fullRank
    (m r : ℕ)
    (hfull : IsPathConnected (sourceFullRankConfigurations m r)) :
    IsPathConnected (sourceSymmetricRankExactStratum m r) := by
  rw [sourceSymmetricRankExactStratum_eq_sourceComplexDotGram_image_fullRank]
  exact hfull.image (continuous_sourceComplexDotGram r m)

end BHW
