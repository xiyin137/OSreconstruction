import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurPatch
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceRank

/-!
# Selected-span projections for Hall-Wightman low-rank source data

This file contains the first finite-algebra step in the Lemma-2/Lemma-3
low-rank route: given an invertible selected principal Gram block, the inverse
block coefficients project source vectors to the selected span, and the
residuals are orthogonal to the selected vectors.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Principal Gram block selected by `I`. -/
def sourcePrincipalGramMatrix
    (n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun a b => G (I a) (I b)

@[simp]
theorem sourcePrincipalGramMatrix_apply
    (n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ)
    (a b : Fin r) :
    sourcePrincipalGramMatrix n r I G a b = G (I a) (I b) := by
  rfl

/-- The determinant of the selected principal Gram block is the corresponding
source matrix minor. -/
theorem sourcePrincipalGramMatrix_det_eq_sourceMatrixMinor
    (n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ) :
    (sourcePrincipalGramMatrix n r I G).det =
      sourceMatrixMinor n r I I G := by
  rfl

/-- A nonzero selected principal minor makes the selected Gram block
invertible. -/
theorem sourcePrincipalGramMatrix_det_isUnit_of_sourceMatrixMinor_ne_zero
    (n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ)
    (hminor : sourceMatrixMinor n r I I G ≠ 0) :
    IsUnit (sourcePrincipalGramMatrix n r I G).det := by
  apply isUnit_iff_ne_zero.mpr
  simpa [sourcePrincipalGramMatrix_det_eq_sourceMatrixMinor] using hminor

/-- Coefficients of the selected-span projection, `row_i * A⁻¹`, where
`A` is the selected principal Gram block. -/
def hw_selectedSpanCoeff
    (n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ)
    (i : Fin n) :
    Fin r → ℂ :=
  fun a =>
    ∑ b : Fin r,
      G i (I b) * (sourcePrincipalGramMatrix n r I G)⁻¹ b a

/-- Multiplying the selected-span coefficient row by the selected Gram block
recovers the original mixed row. -/
theorem hw_selectedSpanCoeff_projection_eq
    (n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ)
    (hminor : sourceMatrixMinor n r I I G ≠ 0)
    (i : Fin n)
    (a : Fin r) :
    (∑ b : Fin r,
        hw_selectedSpanCoeff n r I G i b *
          sourcePrincipalGramMatrix n r I G b a) =
      G i (I a) := by
  let A := sourcePrincipalGramMatrix n r I G
  let row : Matrix (Fin 1) (Fin r) ℂ := fun _ b => G i (I b)
  have hAunit : IsUnit A.det := by
    simpa [A] using
      sourcePrincipalGramMatrix_det_isUnit_of_sourceMatrixMinor_ne_zero
        n r I G hminor
  have hcancel : row * A⁻¹ * A = row :=
    Matrix.nonsing_inv_mul_cancel_right (A := A) row hAunit
  have happ := congrFun (congrFun hcancel (0 : Fin 1)) a
  simpa [Matrix.mul_apply, hw_selectedSpanCoeff, A, row]
    using happ

/-- On selected source labels the selected-span coefficient row is the
corresponding standard basis row. -/
theorem hw_selectedSpanCoeff_selected
    (n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ)
    (hminor : sourceMatrixMinor n r I I G ≠ 0)
    (a b : Fin r) :
    hw_selectedSpanCoeff n r I G (I a) b = if a = b then 1 else 0 := by
  let A := sourcePrincipalGramMatrix n r I G
  have hAunit : IsUnit A.det := by
    simpa [A] using
      sourcePrincipalGramMatrix_det_isUnit_of_sourceMatrixMinor_ne_zero
        n r I G hminor
  have hcancel : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv (A := A) hAunit
  have happ := congrFun (congrFun hcancel a) b
  simpa [Matrix.mul_apply, hw_selectedSpanCoeff, A, Matrix.one_apply]
    using happ

/-- Projection of a source tuple to the selected span using the inverse
principal-block coefficients. -/
def hwLemma3_selectedProjection
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ)
    (z0 : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i =>
    ∑ a : Fin r,
      hw_selectedSpanCoeff n r I G i a • z0 (I a)

/-- Residual after subtracting the selected-span projection. -/
def hwLemma3_selectedResidual
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ)
    (z0 : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i => z0 i - hwLemma3_selectedProjection d n r I G z0 i

/-- The selected-span projection fixes selected source labels. -/
theorem hwLemma3_selectedProjection_selected
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (a : Fin r) :
    hwLemma3_selectedProjection d n r I
        (sourceMinkowskiGram d n z0) z0 (I a) =
      z0 (I a) := by
  ext μ
  rw [hwLemma3_selectedProjection]
  simp only [
    hw_selectedSpanCoeff_selected n r I (sourceMinkowskiGram d n z0)
      hminor]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _hb hba
    simp [hba.symm]
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

/-- The selected residual vanishes on selected source labels. -/
theorem hwLemma3_selectedResidual_selected
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (a : Fin r) :
    hwLemma3_selectedResidual d n r I
        (sourceMinkowskiGram d n z0) z0 (I a) = 0 := by
  rw [hwLemma3_selectedResidual]
  rw [hwLemma3_selectedProjection_selected d n r I z0 hminor a]
  simp

/-- The selected-span projection has the same pairings with selected vectors
as the original vector. -/
theorem hwLemma3_selectedProjection_inner_head
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (i : Fin n)
    (a : Fin r) :
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedProjection d n r I
          (sourceMinkowskiGram d n z0) z0 i)
        (z0 (I a)) =
      sourceMinkowskiGram d n z0 i (I a) := by
  rw [hwLemma3_selectedProjection]
  rw [sourceComplexMinkowskiInner_sum_smul_left]
  have hrow :=
    hw_selectedSpanCoeff_projection_eq
      n r I (sourceMinkowskiGram d n z0) hminor i a
  simpa [sourceMinkowskiGram_apply_eq_complexInner]
    using hrow

/-- The residual is orthogonal to every selected vector. -/
theorem hwLemma3_selectedResidual_inner_head
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (i : Fin n)
    (a : Fin r) :
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedResidual d n r I
          (sourceMinkowskiGram d n z0) z0 i)
        (z0 (I a)) = 0 := by
  rw [hwLemma3_selectedResidual]
  rw [sourceComplexMinkowskiInner_sub_left]
  rw [hwLemma3_selectedProjection_inner_head d n r I z0 hminor i a]
  rw [sourceMinkowskiGram_apply_eq_complexInner]
  ring

/-- Orthogonality in the symmetric order, by symmetry of the complex
Minkowski pairing. -/
theorem hwLemma3_selectedResidual_head_inner
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (a : Fin r)
    (i : Fin n) :
    sourceComplexMinkowskiInner d
        (z0 (I a))
        (hwLemma3_selectedResidual d n r I
          (sourceMinkowskiGram d n z0) z0 i) = 0 := by
  rw [sourceComplexMinkowskiInner_comm]
  exact hwLemma3_selectedResidual_inner_head d n r I z0 hminor i a

/-- A selected-span projection is orthogonal to every selected residual. -/
theorem hwLemma3_selectedProjection_inner_residual
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (i j : Fin n) :
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedProjection d n r I
          (sourceMinkowskiGram d n z0) z0 i)
        (hwLemma3_selectedResidual d n r I
          (sourceMinkowskiGram d n z0) z0 j) = 0 := by
  rw [hwLemma3_selectedProjection]
  rw [sourceComplexMinkowskiInner_sum_smul_left]
  apply Finset.sum_eq_zero
  intro a _ha
  rw [hwLemma3_selectedResidual_head_inner d n r I z0 hminor a j]
  simp

/-- A selected residual is orthogonal to every selected-span projection. -/
theorem hwLemma3_selectedResidual_inner_projection
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (i j : Fin n) :
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedResidual d n r I
          (sourceMinkowskiGram d n z0) z0 i)
        (hwLemma3_selectedProjection d n r I
          (sourceMinkowskiGram d n z0) z0 j) = 0 := by
  rw [sourceComplexMinkowskiInner_comm]
  exact hwLemma3_selectedProjection_inner_residual d n r I z0 hminor j i

/-- On complementary indices, the residual-residual pairing is the indexed
Schur complement of the selected principal Gram block. -/
theorem hwLemma3_selectedComplement_residual_inner_residual_eq_schur
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hI : Function.Injective I)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (u v : selectedIndexComplement I) :
    let e := selectedIndexSumEquiv I hI
    let G : Fin n → Fin n → ℂ := sourceMinkowskiGram d n z0
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedResidual d n r I G z0 (e.symm (Sum.inr u)))
        (hwLemma3_selectedResidual d n r I G z0 (e.symm (Sum.inr v))) =
      reindexedRectSchurComplement
        (Matrix.of fun i j : Fin n => G i j) e e u v := by
  classical
  intro e G
  let i : Fin n := e.symm (Sum.inr u)
  let j : Fin n := e.symm (Sum.inr v)
  have hsymm_inl : ∀ a : Fin r, e.symm (Sum.inl a) = I a := by
    intro a
    rw [Equiv.symm_apply_eq]
    exact (selectedIndexSumEquiv_apply_selected I hI a).symm
  have hAeq :
      sourcePrincipalGramMatrix n r I (sourceMinkowskiGram d n z0) =
        Matrix.of fun a b : Fin r =>
          sourceComplexMinkowskiInner d (z0 (I a)) (z0 (I b)) := by
    ext a b
    simp [sourcePrincipalGramMatrix, sourceMinkowskiGram_apply_eq_complexInner]
  have hproj :
      sourceComplexMinkowskiInner d
          (hwLemma3_selectedResidual d n r I G z0 i)
          (hwLemma3_selectedProjection d n r I G z0 j) = 0 := by
    simpa [G, i, j] using
      hwLemma3_selectedResidual_inner_projection d n r I z0 hminor i j
  calc
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedResidual d n r I G z0 (e.symm (Sum.inr u)))
        (hwLemma3_selectedResidual d n r I G z0 (e.symm (Sum.inr v)))
        =
      sourceComplexMinkowskiInner d
        (hwLemma3_selectedResidual d n r I G z0 i)
        (z0 j) := by
          rw [show e.symm (Sum.inr u) = i from rfl,
            show e.symm (Sum.inr v) = j from rfl]
          change
            sourceComplexMinkowskiInner d
                (hwLemma3_selectedResidual d n r I G z0 i)
                (z0 j - hwLemma3_selectedProjection d n r I G z0 j) =
              sourceComplexMinkowskiInner d
                (hwLemma3_selectedResidual d n r I G z0 i)
                (z0 j)
          rw [sourceComplexMinkowskiInner_sub_right]
          rw [hproj]
          ring
    _ =
      reindexedRectSchurComplement
        (Matrix.of fun i j : Fin n => G i j) e e u v := by
          rw [hwLemma3_selectedResidual]
          rw [sourceComplexMinkowskiInner_sub_left]
          rw [hwLemma3_selectedProjection]
          rw [sourceComplexMinkowskiInner_sum_smul_left]
          simp [reindexedRectSchurComplement, Matrix.mul_apply,
            Matrix.reindex, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
            Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
            hw_selectedSpanCoeff, hAeq,
            sourceMinkowskiGram_apply_eq_complexInner,
            G, i, j, hsymm_inl]

/-- If the selected principal block has the full Gram rank, every selected
residual pairing vanishes. -/
theorem hwLemma3_selectedResidual_inner_residual_eq_zero
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hrank :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z0) = r)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (i j : Fin n) :
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedResidual d n r I
          (sourceMinkowskiGram d n z0) z0 i)
        (hwLemma3_selectedResidual d n r I
          (sourceMinkowskiGram d n z0) z0 j) = 0 := by
  classical
  let G : Fin n → Fin n → ℂ := sourceMinkowskiGram d n z0
  have hI : Function.Injective I :=
    sourceMatrixMinor_ne_zero_left_injective
      (I := I) (J := I) (Z := sourceMinkowskiGram d n z0) hminor
  let e := selectedIndexSumEquiv I hI
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a b => G a b
  have hA : IsUnit ((M.reindex e e).toBlocks₁₁.det) := by
    simpa [M, G, e] using
      isUnit_selectedIndexSumEquiv_toBlocks₁₁_det
        (I := I) (J := I) hI hI hminor
  have hrankM : M.rank = Fintype.card (Fin r) := by
    simpa [M, G, sourceGramMatrixRank] using hrank
  have hschur :
      reindexedRectSchurComplement M e e = 0 :=
    (rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero
      (Z := M) (er := e) (ec := e) hA).1 hrankM
  rcases hi : e i with a | u
  · have hi_eq : i = I a := by
      calc
        i = e.symm (e i) := (e.symm_apply_apply i).symm
        _ = e.symm (Sum.inl a) := by rw [hi]
        _ = I a := by
          rw [Equiv.symm_apply_eq]
          exact (selectedIndexSumEquiv_apply_selected I hI a).symm
    subst i
    rw [hwLemma3_selectedResidual_selected d n r I z0 hminor a]
    simp [sourceComplexMinkowskiInner]
  · rcases hj : e j with b | v
    · have hj_eq : j = I b := by
        calc
          j = e.symm (e j) := (e.symm_apply_apply j).symm
          _ = e.symm (Sum.inl b) := by rw [hj]
          _ = I b := by
            rw [Equiv.symm_apply_eq]
            exact (selectedIndexSumEquiv_apply_selected I hI b).symm
      subst j
      rw [hwLemma3_selectedResidual_selected d n r I z0 hminor b]
      simp [sourceComplexMinkowskiInner]
    · have hi_eq : i = e.symm (Sum.inr u) := by
        calc
          i = e.symm (e i) := (e.symm_apply_apply i).symm
          _ = e.symm (Sum.inr u) := by rw [hi]
      have hj_eq : j = e.symm (Sum.inr v) := by
        calc
          j = e.symm (e j) := (e.symm_apply_apply j).symm
          _ = e.symm (Sum.inr v) := by rw [hj]
      have hpair :=
        hwLemma3_selectedComplement_residual_inner_residual_eq_schur
          d n r I z0 hI hminor u v
      have hentry :
          reindexedRectSchurComplement M e e u v = 0 := by
        simpa [M, e] using congrFun (congrFun hschur u) v
      rw [hi_eq, hj_eq]
      simpa [M, G, e] using hpair.trans hentry

/-- The projection plus residual decomposition recovers the original source
vector. -/
theorem hwLemma3_selectedProjection_add_residual
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (G : Fin n → Fin n → ℂ)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (i : Fin n) :
    hwLemma3_selectedProjection d n r I G z0 i +
        hwLemma3_selectedResidual d n r I G z0 i =
      z0 i := by
  ext μ
  simp [hwLemma3_selectedResidual]

/-- At rank `r`, selected residuals are orthogonal to every original source
vector. -/
theorem hwLemma3_selectedResidual_inner_original_eq_zero
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hrank :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z0) = r)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (i j : Fin n) :
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedResidual d n r I
          (sourceMinkowskiGram d n z0) z0 i)
        (z0 j) = 0 := by
  rw [← hwLemma3_selectedProjection_add_residual
    d n r I (sourceMinkowskiGram d n z0) z0 j]
  rw [sourceComplexMinkowskiInner_add_right]
  rw [hwLemma3_selectedResidual_inner_projection d n r I z0 hminor i j]
  rw [hwLemma3_selectedResidual_inner_residual_eq_zero
    d n r I z0 hrank hminor i j]
  simp

/-- At rank `r`, every original source vector is orthogonal to selected
residuals. -/
theorem hwLemma3_original_inner_selectedResidual_eq_zero
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hrank :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z0) = r)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (i j : Fin n) :
    sourceComplexMinkowskiInner d
        (z0 i)
        (hwLemma3_selectedResidual d n r I
          (sourceMinkowskiGram d n z0) z0 j) = 0 := by
  rw [← hwLemma3_selectedProjection_add_residual
    d n r I (sourceMinkowskiGram d n z0) z0 i]
  rw [sourceComplexMinkowskiInner_add_left]
  rw [hwLemma3_selectedProjection_inner_residual d n r I z0 hminor i j]
  rw [hwLemma3_selectedResidual_inner_residual_eq_zero
    d n r I z0 hrank hminor i j]
  simp

/-- The selected-span projection preserves the full scalar source Gram matrix
when the selected principal block realizes the full rank. -/
theorem hwLemma3_selectedProjection_gram_eq
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hrank :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z0) = r)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0)
    (i j : Fin n) :
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedProjection d n r I
          (sourceMinkowskiGram d n z0) z0 i)
        (hwLemma3_selectedProjection d n r I
          (sourceMinkowskiGram d n z0) z0 j) =
      sourceMinkowskiGram d n z0 i j := by
  calc
    sourceComplexMinkowskiInner d
        (hwLemma3_selectedProjection d n r I
          (sourceMinkowskiGram d n z0) z0 i)
        (hwLemma3_selectedProjection d n r I
          (sourceMinkowskiGram d n z0) z0 j)
        =
      sourceComplexMinkowskiInner d
        (hwLemma3_selectedProjection d n r I
          (sourceMinkowskiGram d n z0) z0 i)
        (z0 j) := by
          rw [← hwLemma3_selectedProjection_add_residual
            d n r I (sourceMinkowskiGram d n z0) z0 j]
          rw [sourceComplexMinkowskiInner_add_right]
          rw [hwLemma3_selectedProjection_inner_residual
            d n r I z0 hminor i j]
          simp
    _ =
      sourceComplexMinkowskiInner d (z0 i) (z0 j) := by
          rw [← hwLemma3_selectedProjection_add_residual
            d n r I (sourceMinkowskiGram d n z0) z0 i]
          rw [sourceComplexMinkowskiInner_add_left]
          rw [hwLemma3_selectedResidual_inner_original_eq_zero
            d n r I z0 hrank hminor i j]
          simp
    _ = sourceMinkowskiGram d n z0 i j := by
          rw [sourceMinkowskiGram_apply_eq_complexInner]

/-- The selected projection tuple has source-span dimension exactly the
selected Gram rank. -/
theorem hwLemma3_selectedProjection_span_finrank_eq_rank
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hrank :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z0) = r)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0) :
    Module.finrank ℂ
        (LinearMap.range
          (sourceCoefficientEval d n
            (hwLemma3_selectedProjection d n r I
              (sourceMinkowskiGram d n z0) z0))) =
      r := by
  classical
  let ξ : Fin n → Fin (d + 1) → ℂ :=
    hwLemma3_selectedProjection d n r I
      (sourceMinkowskiGram d n z0) z0
  let S : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range fun a : Fin r => z0 (I a))
  have hrange_le :
      LinearMap.range (sourceCoefficientEval d n ξ) ≤ S := by
    rintro y ⟨coeff, rfl⟩
    change (∑ i : Fin n, coeff i • ξ i) ∈ S
    apply Submodule.sum_mem
    intro i _hi
    change
      coeff i •
          (∑ a : Fin r,
            hw_selectedSpanCoeff n r I (sourceMinkowskiGram d n z0) i a •
              z0 (I a)) ∈ S
    rw [Finset.smul_sum]
    apply Submodule.sum_mem
    intro a _ha
    rw [smul_smul]
    exact Submodule.smul_mem S _ (Submodule.subset_span ⟨a, rfl⟩)
  have hspan_le : Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n ξ)) ≤ r := by
    calc
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n ξ))
          ≤ Module.finrank ℂ S := Submodule.finrank_mono hrange_le
      _ ≤ Fintype.card (Fin r) := by
            simpa [S] using
              finrank_range_le_card (R := ℂ)
                (fun a : Fin r => z0 (I a))
      _ = r := Fintype.card_fin r
  have hgramξ :
      sourceMinkowskiGram d n ξ = sourceMinkowskiGram d n z0 := by
    ext i j
    rw [sourceMinkowskiGram_apply_eq_complexInner]
    rw [sourceMinkowskiGram_apply_eq_complexInner]
    exact hwLemma3_selectedProjection_gram_eq d n r I z0 hrank hminor i j
  have hrankξ :
      sourceGramMatrixRank n (sourceMinkowskiGram d n ξ) = r := by
    simpa [hgramξ] using hrank
  have hrank_le_span :
      r ≤ Module.finrank ℂ
          (LinearMap.range (sourceCoefficientEval d n ξ)) := by
    have hle :
        sourceGramMatrixRank n (sourceMinkowskiGram d n ξ) ≤
          Module.finrank ℂ
            (LinearMap.range (sourceCoefficientEval d n ξ)) := by
      rw [sourceGramMatrixRank_eq_restrictedMinkowskiRank_range]
      simp [restrictedMinkowskiRank]
    simpa [hrankξ] using hle
  exact le_antisymm hspan_le hrank_le_span

/-- A vector in the span of a finite frame has explicit coordinates on that
frame. -/
theorem exists_coefficients_of_mem_span_finite_frame
    {d s : ℕ}
    {q : Fin s → Fin (d + 1) → ℂ}
    {v : Fin (d + 1) → ℂ}
    (hv : v ∈ Submodule.span ℂ (Set.range q)) :
    ∃ a : Fin s → ℂ, v = ∑ c : Fin s, a c • q c := by
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℂ) (v := q)).1 hv with
    ⟨a, ha⟩
  exact ⟨a, ha.symm⟩

/-- The selected residuals span a finite totally isotropic frame orthogonal to
the selected projection tuple. -/
theorem hwLemma3_selectedResidual_isotropicFrameData
    (d n r : ℕ)
    (I : Fin r → Fin n)
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hrank :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z0) = r)
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z0) ≠ 0) :
    ∃ (s : ℕ)
      (q : Fin s → Fin (d + 1) → ℂ)
      (a : Fin n → Fin s → ℂ),
      LinearIndependent ℂ q ∧
      (∀ c e,
        sourceComplexMinkowskiInner d (q c) (q e) = 0) ∧
      (∀ c i,
        sourceComplexMinkowskiInner d (q c)
          (hwLemma3_selectedProjection d n r I
            (sourceMinkowskiGram d n z0) z0 i) = 0) ∧
      (∀ i μ,
        hwLemma3_selectedResidual d n r I
          (sourceMinkowskiGram d n z0) z0 i μ =
        ∑ c : Fin s, a i c * q c μ) ∧
      (fun i μ =>
        hwLemma3_selectedProjection d n r I
          (sourceMinkowskiGram d n z0) z0 i μ +
        ∑ c : Fin s, a i c * q c μ) = z0 := by
  classical
  let G : Fin n → Fin n → ℂ := sourceMinkowskiGram d n z0
  let ξ : Fin n → Fin (d + 1) → ℂ :=
    hwLemma3_selectedProjection d n r I G z0
  let ρ : Fin n → Fin (d + 1) → ℂ :=
    hwLemma3_selectedResidual d n r I G z0
  let R : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range ρ)
  rcases Submodule.exists_fun_fin_finrank_span_eq
      (K := ℂ) (s := Set.range ρ) with
    ⟨q, hq_mem, hq_span, hq_li⟩
  have hres_mem :
      ∀ i : Fin n, ρ i ∈ Submodule.span ℂ (Set.range q) := by
    intro i
    rw [hq_span]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcoef_exists :
      ∀ i : Fin n,
        ∃ coeff :
            Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range ρ))) → ℂ,
          ρ i = ∑ c, coeff c • q c := by
    intro i
    exact exists_coefficients_of_mem_span_finite_frame (hres_mem i)
  choose a ha using hcoef_exists
  refine ⟨Module.finrank ℂ R, q, a, hq_li, ?_, ?_, ?_, ?_⟩
  · intro c e
    rcases hq_mem c with ⟨i, hi⟩
    rcases hq_mem e with ⟨j, hj⟩
    rw [← hi, ← hj]
    exact hwLemma3_selectedResidual_inner_residual_eq_zero
      d n r I z0 hrank hminor i j
  · intro c i
    rcases hq_mem c with ⟨j, hj⟩
    rw [← hj]
    exact hwLemma3_selectedResidual_inner_projection d n r I z0 hminor j i
  · intro i μ
    have hcoord := congrFun (ha i) μ
    simpa [Pi.smul_apply, smul_eq_mul] using hcoord
  · ext i μ
    have hcoord := congrFun (ha i) μ
    have hadd :=
      congrFun (hwLemma3_selectedProjection_add_residual d n r I G z0 i) μ
    calc
      ξ i μ + ∑ c : Fin (Module.finrank ℂ R), a i c * q c μ
          =
        ξ i μ + ρ i μ := by
          simpa [R, Pi.smul_apply, smul_eq_mul] using
            congrArg (fun x => ξ i μ + x) hcoord.symm
      _ = z0 i μ := by
          simpa [ξ, ρ, G] using hadd

end BHW
