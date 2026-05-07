import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurPatch

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

end BHW
