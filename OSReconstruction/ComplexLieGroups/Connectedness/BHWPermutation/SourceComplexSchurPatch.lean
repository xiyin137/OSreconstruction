import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexGlobalIdentity

/-!
# Schur-complement patches for the source complex Gram variety

This file packages the checked Schur-complement algebra from
`SourceComplexGlobalIdentity.lean` as rectangular and principal graph
descriptions of the rank stratum and the source complex Gram variety.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator

namespace BHW

/-- Rectangular Schur complement after independent row and column reindexings. -/
def reindexedRectSchurComplement
    {ι κ r q₁ q₂ : Type*} [Fintype r] [DecidableEq r]
    (Z : Matrix ι κ ℂ)
    (er : ι ≃ r ⊕ q₁) (ec : κ ≃ r ⊕ q₂) :
    Matrix q₁ q₂ ℂ :=
  let M : Matrix (r ⊕ q₁) (r ⊕ q₂) ℂ := Z.reindex er ec
  M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂

/-- Complement of a selected finite index map. -/
abbrev selectedIndexComplement
    {r n : ℕ} (I : Fin r → Fin n) : Type :=
  {j : Fin n // j ∉ Set.range I}

/-- A nonzero selected minor has no repeated selected rows. -/
theorem sourceMatrixMinor_ne_zero_left_injective
    {n r : ℕ} {I J : Fin r → Fin n}
    {Z : Fin n → Fin n → ℂ}
    (hdet : sourceMatrixMinor n r I J Z ≠ 0) :
    Function.Injective I := by
  intro a b hab
  by_contra hne
  have hzero :
      Matrix.det (fun x y : Fin r => Z (I x) (J y)) = 0 := by
    exact Matrix.det_zero_of_row_eq hne (by
      ext y
      simp [hab])
  exact hdet (by simpa [sourceMatrixMinor] using hzero)

/-- A nonzero selected minor has no repeated selected columns. -/
theorem sourceMatrixMinor_ne_zero_right_injective
    {n r : ℕ} {I J : Fin r → Fin n}
    {Z : Fin n → Fin n → ℂ}
    (hdet : sourceMatrixMinor n r I J Z ≠ 0) :
    Function.Injective J := by
  intro a b hab
  by_contra hne
  have hzero :
      Matrix.det (fun x y : Fin r => Z (I x) (J y)) = 0 := by
    exact Matrix.det_zero_of_column_eq hne (by
      intro x
      simp [hab])
  exact hdet (by simpa [sourceMatrixMinor] using hzero)

/-- Reindex `Fin n` as selected indices followed by their complement. -/
noncomputable def selectedIndexSumEquiv
    {r n : ℕ} (I : Fin r → Fin n) (hI : Function.Injective I) :
    Fin n ≃ Fin r ⊕ selectedIndexComplement I :=
  (Equiv.sumCompl (fun j : Fin n => j ∈ Set.range I)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective I hI).symm (Equiv.refl _))

@[simp]
theorem selectedIndexSumEquiv_apply_selected
    {r n : ℕ} (I : Fin r → Fin n) (hI : Function.Injective I)
    (a : Fin r) :
    selectedIndexSumEquiv I hI (I a) = Sum.inl a := by
  simp [selectedIndexSumEquiv, Equiv.sumCompl_symm_apply_of_pos,
    Equiv.ofInjective_symm_apply]

/-- The upper-left block after selected/complement reindexing is exactly the
selected square submatrix. -/
theorem selectedIndexSumEquiv_toBlocks₁₁
    {r n : ℕ} {I J : Fin r → Fin n}
    (hI : Function.Injective I) (hJ : Function.Injective J)
    (Z : Fin n → Fin n → ℂ) :
    (((Matrix.of fun i j : Fin n => Z i j).reindex
        (selectedIndexSumEquiv I hI) (selectedIndexSumEquiv J hJ)).toBlocks₁₁) =
      (fun a b : Fin r => Z (I a) (J b)) := by
  ext a b
  have hIa : (selectedIndexSumEquiv I hI).symm (Sum.inl a) = I a := by
    rw [Equiv.symm_apply_eq]
    exact (selectedIndexSumEquiv_apply_selected I hI a).symm
  have hJb : (selectedIndexSumEquiv J hJ).symm (Sum.inl b) = J b := by
    rw [Equiv.symm_apply_eq]
    exact (selectedIndexSumEquiv_apply_selected J hJ b).symm
  change Z ((selectedIndexSumEquiv I hI).symm (Sum.inl a))
      ((selectedIndexSumEquiv J hJ).symm (Sum.inl b)) =
    Z (I a) (J b)
  rw [hIa, hJb]

/-- A nonzero selected minor gives an invertible upper-left block after
selected/complement reindexing. -/
theorem isUnit_selectedIndexSumEquiv_toBlocks₁₁_det
    {r n : ℕ} {I J : Fin r → Fin n}
    (hI : Function.Injective I) (hJ : Function.Injective J)
    {Z : Fin n → Fin n → ℂ}
    (hdet : sourceMatrixMinor n r I J Z ≠ 0) :
    IsUnit
      ((((Matrix.of fun i j : Fin n => Z i j).reindex
        (selectedIndexSumEquiv I hI) (selectedIndexSumEquiv J hJ)).toBlocks₁₁).det) := by
  apply isUnit_iff_ne_zero.mpr
  simpa [sourceMatrixMinor, selectedIndexSumEquiv_toBlocks₁₁ hI hJ Z] using hdet

/-- A rectangular block matrix with only the upper-left block possibly nonzero
has rank at most the size of that block. -/
theorem rank_fromBlocks_zero₂₂_le_card_left_rect
    {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
    [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
    (A : Matrix r r ℂ) :
    (Matrix.fromBlocks A (0 : Matrix r q₂ ℂ) (0 : Matrix q₁ r ℂ)
      (0 : Matrix q₁ q₂ ℂ)).rank ≤ Fintype.card r := by
  let M : Matrix (r ⊕ q₁) (r ⊕ q₂) ℂ :=
    Matrix.fromBlocks A (0 : Matrix r q₂ ℂ) (0 : Matrix q₁ r ℂ)
      (0 : Matrix q₁ q₂ ℂ)
  let rowVec : r → (r ⊕ q₂ → ℂ) := fun i => M.row (Sum.inl i)
  have hrow_mem :
      ∀ x : r ⊕ q₁,
        M.row x ∈ Submodule.span ℂ (Set.range rowVec) := by
    intro x
    cases x with
    | inl i =>
        exact Submodule.subset_span ⟨i, rfl⟩
    | inr j =>
        have hzero : M.row (Sum.inr j) = 0 := by
          ext y
          cases y <;> rfl
        rw [hzero]
        exact Submodule.zero_mem _
  have hspan_le :
      Submodule.span ℂ (Set.range fun x : r ⊕ q₁ => M.row x) ≤
        Submodule.span ℂ (Set.range rowVec) := by
    exact Submodule.span_le.mpr (by
      rintro v ⟨x, rfl⟩
      exact hrow_mem x)
  rw [Matrix.rank_eq_finrank_span_row]
  calc
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun x : r ⊕ q₁ => M.row x))
        ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range rowVec)) :=
          Submodule.finrank_mono hspan_le
    _ ≤ Fintype.card r := by
          simpa using finrank_range_le_card (R := ℂ) rowVec

/-- Rectangular Schur-complement obstruction: if the upper-left block is
invertible and the whole block matrix has rank at most that block size, the
Schur complement vanishes. -/
theorem schur_complement_entry_eq_zero_of_rank_le_rect
    {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
    [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
    (A : Matrix r r ℂ) (B : Matrix r q₂ ℂ)
    (D : Matrix q₁ r ℂ) (C : Matrix q₁ q₂ ℂ)
    (hA : IsUnit A.det)
    (hrank : (Matrix.fromBlocks A B D C).rank ≤ Fintype.card r)
    (u : q₁) (v : q₂) :
    (C - D * A⁻¹ * B) u v = 0 := by
  by_contra hne
  let rowSel : r ⊕ Unit → r ⊕ q₁ := Sum.elim Sum.inl (fun _ => Sum.inr u)
  let colSel : r ⊕ Unit → r ⊕ q₂ := Sum.elim Sum.inl (fun _ => Sum.inr v)
  let S : Matrix (r ⊕ Unit) (r ⊕ Unit) ℂ :=
    (Matrix.fromBlocks A B D C).submatrix rowSel colSel
  have hS_eq :
      S = Matrix.fromBlocks A (fun i _ => B i v)
        (fun _ j => D u j) (fun _ _ : Unit => C u v) := by
    ext x y
    cases x <;> cases y <;> rfl
  have hdetS :
      S.det = A.det * ((C - D * A⁻¹ * B) u v) := by
    classical
    cases ((Matrix.isUnit_iff_isUnit_det A).mpr hA).nonempty_invertible
    rw [hS_eq]
    rw [Matrix.det_fromBlocks₁₁]
    simp [Matrix.det_unique, Matrix.mul_apply]
  have hdetS_ne : S.det ≠ 0 := by
    rw [hdetS]
    exact mul_ne_zero hA.ne_zero hne
  have hge :
      Fintype.card (r ⊕ Unit) ≤
        (Matrix.fromBlocks A B D C).rank :=
    matrix_rank_ge_card_of_nondegenerate_square_submatrix
      (A := Matrix.fromBlocks A B D C)
      (I := rowSel) (J := colSel)
      (by simpa [S] using hdetS_ne)
  have hcard : Fintype.card (r ⊕ Unit) = Fintype.card r + 1 := by
    simp
  omega

/-- Rectangular graph-to-rank theorem: on an invertible upper-left block,
Schur-complement zero forces rank at most the block size. -/
theorem rank_fromBlocks_le_of_schur_complement_eq_zero_rect
    {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
    [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
    (A : Matrix r r ℂ) (B : Matrix r q₂ ℂ)
    (D : Matrix q₁ r ℂ) (C : Matrix q₁ q₂ ℂ)
    (hA : IsUnit A.det)
    (hschur : C - D * A⁻¹ * B = 0) :
    (Matrix.fromBlocks A B D C).rank ≤ Fintype.card r := by
  classical
  cases ((Matrix.isUnit_iff_isUnit_det A).mpr hA).nonempty_invertible
  have hschur' : C - D * ⅟A * B = 0 := by
    simpa [Matrix.invOf_eq_nonsing_inv] using hschur
  rw [Matrix.fromBlocks_eq_of_invertible₁₁ (A := A) (B := B) (C := D) (D := C)]
  calc
    (Matrix.fromBlocks 1 0 (D * ⅟A) 1 *
          Matrix.fromBlocks A 0 0 (C - D * ⅟A * B) *
          Matrix.fromBlocks 1 (⅟A * B) 0 1).rank
        ≤ (Matrix.fromBlocks 1 0 (D * ⅟A) 1 *
          Matrix.fromBlocks A 0 0 (C - D * ⅟A * B)).rank :=
          Matrix.rank_mul_le_left _ _
    _ ≤ (Matrix.fromBlocks A 0 0 (C - D * ⅟A * B)).rank :=
          Matrix.rank_mul_le_right _ _
    _ = (Matrix.fromBlocks A (0 : Matrix r q₂ ℂ) (0 : Matrix q₁ r ℂ)
          (0 : Matrix q₁ q₂ ℂ)).rank := by
          rw [hschur']
    _ ≤ Fintype.card r :=
          rank_fromBlocks_zero₂₂_le_card_left_rect A

/-- Rectangular Schur chart for an arbitrary selected nonzero minor: exact rank
equal to the selected block size is equivalent to Schur-complement zero after
independent row and column reindexings. -/
theorem rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero
    {ι κ r q₁ q₂ : Type*} [Fintype ι] [Fintype κ] [Fintype r]
    [Fintype q₁] [Fintype q₂]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq r]
    [DecidableEq q₁] [DecidableEq q₂]
    (Z : Matrix ι κ ℂ)
    (er : ι ≃ r ⊕ q₁) (ec : κ ≃ r ⊕ q₂)
    (hA : IsUnit ((Z.reindex er ec).toBlocks₁₁.det)) :
    Z.rank = Fintype.card r ↔
      reindexedRectSchurComplement Z er ec = 0 := by
  constructor
  · intro hrank
    let M : Matrix (r ⊕ q₁) (r ⊕ q₂) ℂ := Z.reindex er ec
    let A : Matrix r r ℂ := M.toBlocks₁₁
    let B : Matrix r q₂ ℂ := M.toBlocks₁₂
    let D : Matrix q₁ r ℂ := M.toBlocks₂₁
    let C : Matrix q₁ q₂ ℂ := M.toBlocks₂₂
    have hA' : IsUnit A.det := by
      simpa [M, A] using hA
    have hrankM : M.rank ≤ Fintype.card r := by
      have hMrank : M.rank = Z.rank := by
        simp [M]
      rw [hMrank, hrank]
    have hblock : Matrix.fromBlocks A B D C = M := by
      rw [← Matrix.fromBlocks_toBlocks M]
    have hrankBlock : (Matrix.fromBlocks A B D C).rank ≤ Fintype.card r := by
      rw [hblock]
      exact hrankM
    change C - D * A⁻¹ * B = 0
    ext u v
    exact schur_complement_entry_eq_zero_of_rank_le_rect
      (A := A) (B := B) (D := D) (C := C) hA' hrankBlock u v
  · intro hschur
    let M : Matrix (r ⊕ q₁) (r ⊕ q₂) ℂ := Z.reindex er ec
    let A : Matrix r r ℂ := M.toBlocks₁₁
    let B : Matrix r q₂ ℂ := M.toBlocks₁₂
    let D : Matrix q₁ r ℂ := M.toBlocks₂₁
    let C : Matrix q₁ q₂ ℂ := M.toBlocks₂₂
    have hA' : IsUnit A.det := by
      simpa [M, A] using hA
    have hschur' :
        C - D * A⁻¹ * B = 0 := by
      simpa [reindexedRectSchurComplement, M, A, B, C, D] using hschur
    have hMle : M.rank ≤ Fintype.card r :=
      by
        have hblock : Matrix.fromBlocks A B D C = M := by
          rw [← Matrix.fromBlocks_toBlocks M]
        have hblock_le : (Matrix.fromBlocks A B D C).rank ≤ Fintype.card r :=
          rank_fromBlocks_le_of_schur_complement_eq_zero_rect
            (A := A) (B := B) (D := D) (C := C) hA' hschur'
        rw [hblock] at hblock_le
        exact hblock_le
    have hle : Z.rank ≤ Fintype.card r := by
      have hMrank : M.rank = Z.rank := by
        simp [M]
      simpa [hMrank] using hMle
    have hge : Fintype.card r ≤ Z.rank := by
      have hdet :
          Matrix.det (fun a b : r => M (Sum.inl a) (Sum.inl b)) ≠ 0 := by
        simpa [M] using hA.ne_zero
      have hMge : Fintype.card r ≤ M.rank :=
        matrix_rank_ge_card_of_nondegenerate_square_submatrix
          (A := M) (I := Sum.inl) (J := Sum.inl) hdet
      have hMrank : M.rank = Z.rank := by
        simp [M]
      simpa [hMrank] using hMge
    exact le_antisymm hle hge

/-- Rectangular Schur-chart form of the rank-exact symmetric stratum.  Unlike
the principal-patch theorem below, this version covers the regular rank stratum
directly from an arbitrary nonzero rank minor. -/
theorem sourceSymmetricRankExactStratum_iff_reindexed_rect_schur_complement_eq_zero
    (n : ℕ) {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
    [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
    (er : Fin n ≃ r ⊕ q₁) (ec : Fin n ≃ r ⊕ q₂)
    {Z : Fin n → Fin n → ℂ}
    (hA : IsUnit
      (((Matrix.of fun i j : Fin n => Z i j).reindex er ec).toBlocks₁₁.det)) :
    Z ∈ sourceSymmetricRankExactStratum n (Fintype.card r) ↔
      Z ∈ sourceSymmetricMatrixSpace n ∧
        reindexedRectSchurComplement
          (Matrix.of fun i j : Fin n => Z i j) er ec = 0 := by
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
  have hA' : IsUnit ((M.reindex er ec).toBlocks₁₁.det) := by
    simpa [M] using hA
  constructor
  · intro hZ
    refine ⟨hZ.1, ?_⟩
    have hschur :=
      (rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero
        (Z := M) (er := er) (ec := ec) hA').mp (by
          simpa [M] using hZ.2)
    simpa [M] using hschur
  · rintro ⟨hZsym, hschur⟩
    refine ⟨hZsym, ?_⟩
    have hrank :=
      (rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero
        (Z := M) (er := er) (ec := ec) hA').mpr (by
          simpa [M] using hschur)
    simpa [M] using hrank

/-- Rectangular Schur-chart form of the source complex Gram variety on an
arbitrary nonzero selected `(d+1) × (d+1)` minor. -/
theorem sourceComplexGramVariety_iff_reindexed_rect_schur_complement_eq_zero
    (d n : ℕ) {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
    [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
    (er : Fin n ≃ r ⊕ q₁) (ec : Fin n ≃ r ⊕ q₂)
    (hcard : Fintype.card r = d + 1)
    {Z : Fin n → Fin n → ℂ}
    (hA : IsUnit
      (((Matrix.of fun i j : Fin n => Z i j).reindex er ec).toBlocks₁₁.det)) :
    Z ∈ sourceComplexGramVariety d n ↔
      Z ∈ sourceSymmetricMatrixSpace n ∧
        reindexedRectSchurComplement
          (Matrix.of fun i j : Fin n => Z i j) er ec = 0 := by
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
  have hA' : IsUnit ((M.reindex er ec).toBlocks₁₁.det) := by
    simpa [M] using hA
  constructor
  · intro hZ
    rw [sourceComplexGramVariety_eq_rank_le] at hZ
    refine ⟨hZ.1, ?_⟩
    have hge : Fintype.card r ≤ M.rank := by
      let N : Matrix (r ⊕ q₁) (r ⊕ q₂) ℂ := M.reindex er ec
      have hdet :
          Matrix.det (fun a b : r => N (Sum.inl a) (Sum.inl b)) ≠ 0 := by
        simpa [N] using hA'.ne_zero
      have hNge : Fintype.card r ≤ N.rank :=
        matrix_rank_ge_card_of_nondegenerate_square_submatrix
          (A := N) (I := Sum.inl) (J := Sum.inl) hdet
      have hNrank : N.rank = M.rank := by
        simp [N]
      simpa [hNrank] using hNge
    have hle : M.rank ≤ Fintype.card r := by
      simpa [M, hcard] using hZ.2
    have hrank : M.rank = Fintype.card r := le_antisymm hle hge
    have hschur :=
      (rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero
        (Z := M) (er := er) (ec := ec) hA').mp hrank
    simpa [M] using hschur
  · rintro ⟨hZsym, hschur⟩
    rw [sourceComplexGramVariety_eq_rank_le]
    refine ⟨hZsym, ?_⟩
    have hrank :
        M.rank = Fintype.card r :=
      (rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero
        (Z := M) (er := er) (ec := ec) hA').mpr (by
          simpa [M] using hschur)
    rw [hrank, hcard]

/-- Selected-minor version of the rectangular Schur chart for the source complex
Gram variety.  The row and column complements are supplied canonically by
`selectedIndexSumEquiv`. -/
theorem sourceComplexGramVariety_iff_selected_rect_schur_complement_eq_zero
    (d n r : ℕ) {I J : Fin r → Fin n}
    (hI : Function.Injective I) (hJ : Function.Injective J)
    (hr : r = d + 1)
    {Z : Fin n → Fin n → ℂ}
    (hdet : sourceMatrixMinor n r I J Z ≠ 0) :
    Z ∈ sourceComplexGramVariety d n ↔
      Z ∈ sourceSymmetricMatrixSpace n ∧
        reindexedRectSchurComplement
          (Matrix.of fun i j : Fin n => Z i j)
          (selectedIndexSumEquiv I hI) (selectedIndexSumEquiv J hJ) = 0 := by
  have hA :
      IsUnit
        ((((Matrix.of fun i j : Fin n => Z i j).reindex
          (selectedIndexSumEquiv I hI) (selectedIndexSumEquiv J hJ)).toBlocks₁₁).det) :=
    isUnit_selectedIndexSumEquiv_toBlocks₁₁_det hI hJ hdet
  exact
    sourceComplexGramVariety_iff_reindexed_rect_schur_complement_eq_zero
      (d := d) (n := n)
      (er := selectedIndexSumEquiv I hI)
      (ec := selectedIndexSumEquiv J hJ)
      (hcard := by simpa using hr) hA

/-- Every point of the rank-exact source symmetric stratum has a nonzero
selected square minor of that rank. -/
theorem exists_sourceMatrixMinor_ne_zero_of_sourceSymmetricRankExactStratum
    {n r : ℕ} {Z : Fin n → Fin n → ℂ}
    (hZ : Z ∈ sourceSymmetricRankExactStratum n r) :
    ∃ I : Fin r → Fin n, ∃ J : Fin r → Fin n,
      sourceMatrixMinor n r I J Z ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
  have hrank : r ≤ M.rank := by
    rw [hZ.2]
  rcases exists_nondegenerate_square_submatrix_of_rank_ge M hrank with
    ⟨I, J, hdet⟩
  refine ⟨I, J, ?_⟩
  simpa [sourceMatrixMinor, M] using hdet

/-- The selected rectangular Schur charts cover the rank-exact symmetric
source stratum. -/
theorem exists_selected_rect_schur_chart_of_sourceSymmetricRankExactStratum
    {n r : ℕ} {Z : Fin n → Fin n → ℂ}
    (hZ : Z ∈ sourceSymmetricRankExactStratum n r) :
    ∃ I : Fin r → Fin n, ∃ hI : Function.Injective I,
    ∃ J : Fin r → Fin n, ∃ hJ : Function.Injective J,
      sourceMatrixMinor n r I J Z ≠ 0 ∧
      Z ∈ sourceSymmetricMatrixSpace n ∧
        reindexedRectSchurComplement
          (Matrix.of fun i j : Fin n => Z i j)
          (selectedIndexSumEquiv I hI) (selectedIndexSumEquiv J hJ) = 0 := by
  rcases exists_sourceMatrixMinor_ne_zero_of_sourceSymmetricRankExactStratum hZ with
    ⟨I, J, hdet⟩
  let hI : Function.Injective I := sourceMatrixMinor_ne_zero_left_injective hdet
  let hJ : Function.Injective J := sourceMatrixMinor_ne_zero_right_injective hdet
  have hA :
      IsUnit
        ((((Matrix.of fun i j : Fin n => Z i j).reindex
          (selectedIndexSumEquiv I hI) (selectedIndexSumEquiv J hJ)).toBlocks₁₁).det) :=
    isUnit_selectedIndexSumEquiv_toBlocks₁₁_det hI hJ hdet
  have hchart :
      Z ∈ sourceSymmetricMatrixSpace n ∧
        reindexedRectSchurComplement
          (Matrix.of fun i j : Fin n => Z i j)
          (selectedIndexSumEquiv I hI) (selectedIndexSumEquiv J hJ) = 0 := by
    have hiff :=
      sourceSymmetricRankExactStratum_iff_reindexed_rect_schur_complement_eq_zero
        (n := n) (r := Fin r)
        (er := selectedIndexSumEquiv I hI)
        (ec := selectedIndexSumEquiv J hJ) hA
    exact hiff.mp (by simpa using hZ)
  exact ⟨I, hI, J, hJ, hdet, hchart⟩

/-- On the regular rank-`d+1` stratum, the selected rectangular Schur charts
give the local graph form of the source complex Gram variety. -/
theorem exists_selected_rect_schur_chart_of_sourceComplexGramVariety_rankExact
    {d n : ℕ} {Z : Fin n → Fin n → ℂ}
    (hZ : Z ∈ sourceSymmetricRankExactStratum n (d + 1)) :
    ∃ I : Fin (d + 1) → Fin n, ∃ hI : Function.Injective I,
    ∃ J : Fin (d + 1) → Fin n, ∃ hJ : Function.Injective J,
      sourceMatrixMinor n (d + 1) I J Z ≠ 0 ∧
      (Z ∈ sourceComplexGramVariety d n ↔
        Z ∈ sourceSymmetricMatrixSpace n ∧
          reindexedRectSchurComplement
            (Matrix.of fun i j : Fin n => Z i j)
            (selectedIndexSumEquiv I hI) (selectedIndexSumEquiv J hJ) = 0) ∧
      Z ∈ sourceComplexGramVariety d n ∧
        reindexedRectSchurComplement
          (Matrix.of fun i j : Fin n => Z i j)
          (selectedIndexSumEquiv I hI) (selectedIndexSumEquiv J hJ) = 0 := by
  rcases exists_selected_rect_schur_chart_of_sourceSymmetricRankExactStratum hZ with
    ⟨I, hI, J, hJ, hdet, hsym, hschur⟩
  have hiff :=
    sourceComplexGramVariety_iff_selected_rect_schur_complement_eq_zero
      (d := d) (n := n) (r := d + 1)
      (I := I) (J := J) hI hJ rfl hdet
  have hvar : Z ∈ sourceComplexGramVariety d n :=
    sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
      d n (d + 1) (by omega) hZ
  exact ⟨I, hI, J, hJ, hdet, hiff, hvar, hschur⟩

/-- A determinant-nonzero selected source-matrix-minor locus is open. -/
theorem isOpen_sourceMatrixMinor_ne_zero
    (n r : ℕ) (I J : Fin r → Fin n) :
    IsOpen {Z : Fin n → Fin n → ℂ |
      sourceMatrixMinor n r I J Z ≠ 0} := by
  exact isOpen_ne_fun (continuous_sourceMatrixMinor n r I J) continuous_const

/-- A determinant-nonzero selected source-matrix-minor patch is relatively open
inside the source complex Gram variety. -/
theorem sourceMatrixMinor_ne_zero_relOpenInSourceComplexGramVariety
    (d n r : ℕ) (I J : Fin r → Fin n) :
    IsRelOpenInSourceComplexGramVariety d n
      ({Z : Fin n → Fin n → ℂ | sourceMatrixMinor n r I J Z ≠ 0} ∩
        sourceComplexGramVariety d n) := by
  refine ⟨{Z : Fin n → Fin n → ℂ | sourceMatrixMinor n r I J Z ≠ 0},
    isOpen_sourceMatrixMinor_ne_zero n r I J, rfl⟩

/-- The regular rank-`d+1` stratum restricted to a determinant-nonzero selected
minor is a relatively open source-variety patch. -/
theorem sourceComplexGramVariety_regularSelectedMinorPatch_relOpen
    (d n : ℕ) (I J : Fin (d + 1) → Fin n) :
    IsRelOpenInSourceComplexGramVariety d n
      (sourceSymmetricRankExactStratum n (d + 1) ∩
        {Z : Fin n → Fin n → ℂ |
          sourceMatrixMinor n (d + 1) I J Z ≠ 0}) := by
  rcases sourceSymmetricRankExactStratum_relOpenIn_sourceComplexGramVariety d n with
    ⟨U0, hU0, hreg⟩
  let V0 : Set (Fin n → Fin n → ℂ) :=
    {Z | sourceMatrixMinor n (d + 1) I J Z ≠ 0}
  refine ⟨U0 ∩ V0,
    hU0.inter (isOpen_sourceMatrixMinor_ne_zero n (d + 1) I J), ?_⟩
  ext Z
  constructor
  · intro h
    rcases h with ⟨hZreg, hminor⟩
    have hZvar : Z ∈ sourceComplexGramVariety d n :=
      sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
        d n (d + 1) (by omega) hZreg
    have hZU0 : Z ∈ U0 := by
      have : Z ∈ U0 ∩ sourceComplexGramVariety d n := by
        simpa [hreg] using hZreg
      exact this.1
    exact ⟨⟨hZU0, hminor⟩, hZvar⟩
  · intro h
    rcases h with ⟨⟨hZU0, hminor⟩, hZvar⟩
    refine ⟨?_, hminor⟩
    simpa [hreg] using ⟨hZU0, hZvar⟩

/-- On a symmetric matrix with an invertible reindexed principal block, exact
rank equal to the block size is equivalent to Schur-complement zero. -/
theorem rank_eq_card_iff_reindexed_schur_complement_eq_zero
    {ι r q : Type*} [Fintype ι] [Fintype r] [Fintype q]
    [DecidableEq ι] [DecidableEq r] [DecidableEq q]
    (Z : Matrix ι ι ℂ)
    (e : ι ≃ r ⊕ q)
    (hZsym : ∀ i j, Z i j = Z j i)
    (hA : IsUnit ((Z.reindex e e).toBlocks₁₁.det)) :
    Z.rank = Fintype.card r ↔
      (Z.reindex e e).toBlocks₂₂ -
          (Z.reindex e e).toBlocks₁₂ᵀ *
            (Z.reindex e e).toBlocks₁₁⁻¹ *
            (Z.reindex e e).toBlocks₁₂ = 0 := by
  constructor
  · intro hrank
    ext u v
    exact
      schur_complement_entry_eq_zero_of_rank_le_reindex
        (Z := Z) (e := e) hZsym hA hrank.le u v
  · intro hschur
    have hle : Z.rank ≤ Fintype.card r :=
      rank_le_of_reindexed_schur_complement_eq_zero
        (Z := Z) (e := e) hZsym hA hschur
    have hge : Fintype.card r ≤ Z.rank := by
      let M : Matrix (r ⊕ q) (r ⊕ q) ℂ := Z.reindex e e
      have hdet :
          Matrix.det (fun a b : r => M (Sum.inl a) (Sum.inl b)) ≠ 0 := by
        simpa [M] using hA.ne_zero
      have hMge : Fintype.card r ≤ M.rank :=
        matrix_rank_ge_card_of_nondegenerate_square_submatrix
          (A := M) (I := Sum.inl) (J := Sum.inl) hdet
      have hMrank : M.rank = Z.rank := by
        simp [M]
      simpa [hMrank] using hMge
    exact le_antisymm hle hge

/-- On an invertible reindexed principal block, the rank-exact symmetric stratum
is exactly the Schur-complement graph. -/
theorem sourceSymmetricRankExactStratum_iff_reindexed_schur_complement_eq_zero
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {Z : Fin n → Fin n → ℂ}
    (hA : IsUnit
      (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁.det)) :
    Z ∈ sourceSymmetricRankExactStratum n (Fintype.card r) ↔
      Z ∈ sourceSymmetricMatrixSpace n ∧
        ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₂₂ -
            ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂ᵀ *
              ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁⁻¹ *
              ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂ = 0 := by
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
  have hA' : IsUnit ((M.reindex e e).toBlocks₁₁.det) := by
    simpa [M] using hA
  constructor
  · intro hZ
    refine ⟨hZ.1, ?_⟩
    have hMsym : ∀ i j, M i j = M j i := by
      intro i j
      simpa [M] using hZ.1 i j
    have hschur :=
      (rank_eq_card_iff_reindexed_schur_complement_eq_zero
        (Z := M) (e := e) hMsym hA').mp (by
          simpa [M] using hZ.2)
    simpa [M] using hschur
  · rintro ⟨hZsym, hschur⟩
    refine ⟨hZsym, ?_⟩
    have hMsym : ∀ i j, M i j = M j i := by
      intro i j
      simpa [M] using hZsym i j
    have hrank :=
      (rank_eq_card_iff_reindexed_schur_complement_eq_zero
        (Z := M) (e := e) hMsym hA').mpr (by
          simpa [M] using hschur)
    simpa [M] using hrank

/-- On an invertible principal block of size `d + 1`, the source complex Gram
variety itself is exactly the Schur-complement graph inside the symmetric matrix
space. -/
theorem sourceComplexGramVariety_iff_reindexed_schur_complement_eq_zero
    (d n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    (hcard : Fintype.card r = d + 1)
    {Z : Fin n → Fin n → ℂ}
    (hA : IsUnit
      (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁.det)) :
    Z ∈ sourceComplexGramVariety d n ↔
      Z ∈ sourceSymmetricMatrixSpace n ∧
        ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₂₂ -
            ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂ᵀ *
              ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁⁻¹ *
              ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂ = 0 := by
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
  have hA' : IsUnit ((M.reindex e e).toBlocks₁₁.det) := by
    simpa [M] using hA
  constructor
  · intro hZ
    rw [sourceComplexGramVariety_eq_rank_le] at hZ
    refine ⟨hZ.1, ?_⟩
    have hMsym : ∀ i j, M i j = M j i := by
      intro i j
      simpa [M] using hZ.1 i j
    have hge : Fintype.card r ≤ M.rank := by
      let N : Matrix (r ⊕ q) (r ⊕ q) ℂ := M.reindex e e
      have hdet :
          Matrix.det (fun a b : r => N (Sum.inl a) (Sum.inl b)) ≠ 0 := by
        simpa [N] using hA'.ne_zero
      have hNge : Fintype.card r ≤ N.rank :=
        matrix_rank_ge_card_of_nondegenerate_square_submatrix
          (A := N) (I := Sum.inl) (J := Sum.inl) hdet
      have hNrank : N.rank = M.rank := by
        simp [N]
      simpa [hNrank] using hNge
    have hle : M.rank ≤ Fintype.card r := by
      simpa [M, hcard] using hZ.2
    have hrank : M.rank = Fintype.card r := le_antisymm hle hge
    have hschur :=
      (rank_eq_card_iff_reindexed_schur_complement_eq_zero
        (Z := M) (e := e) hMsym hA').mp hrank
    simpa [M] using hschur
  · rintro ⟨hZsym, hschur⟩
    rw [sourceComplexGramVariety_eq_rank_le]
    refine ⟨hZsym, ?_⟩
    have hMsym : ∀ i j, M i j = M j i := by
      intro i j
      simpa [M] using hZsym i j
    have hrank :
        M.rank = Fintype.card r :=
      (rank_eq_card_iff_reindexed_schur_complement_eq_zero
        (Z := M) (e := e) hMsym hA').mpr (by
          simpa [M] using hschur)
    rw [hrank, hcard]

end BHW
