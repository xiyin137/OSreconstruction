import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWSingularLimit

/-!
# Hall-Wightman low-rank selected-span alignment data

This file records the finite-dimensional data surfaces immediately below the
low-rank singular normal form.  The producer of these structures is still the
hard Hall-Wightman geometry; the checked theorem here packages the residual
subspaces once the selected-span alignment fields are available.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Linear algebra inside the low-rank branch: after choosing a nonzero
principal scalar block, the equal Gram data determine the same selected
coefficients and residual radical pairings. -/
structure HWLowRankSelectedSpanFrame
    (d n r : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ)
    (I : Fin r → Fin n) where
  I_injective : Function.Injective I
  principal_minor_ne :
    sourceMatrixMinor n r I I (sourceMinkowskiGram d n z) ≠ 0
  selected_gram_eq :
    ∀ a b,
      sourceMinkowskiGram d n z (I a) (I b) =
        sourceMinkowskiGram d n w (I a) (I b)
  coeff : Fin n → Fin r → ℂ
  left_residual_orth :
    ∀ i a,
      sourceComplexMinkowskiInner d
        (z i - ∑ b : Fin r, coeff i b • z (I b))
        (z (I a)) = 0
  right_residual_orth :
    ∀ i a,
      sourceComplexMinkowskiInner d
        (w i - ∑ b : Fin r, coeff i b • w (I b))
        (w (I a)) = 0
  residual_pairing_eq :
    ∀ i j,
      sourceComplexMinkowskiInner d
        (z i - ∑ b : Fin r, coeff i b • z (I b))
        (z j - ∑ b : Fin r, coeff j b • z (I b)) =
      sourceComplexMinkowskiInner d
        (w i - ∑ b : Fin r, coeff i b • w (I b))
        (w j - ∑ b : Fin r, coeff j b • w (I b))
  left_residual_pair_zero :
    ∀ i j,
      sourceComplexMinkowskiInner d
        (z i - ∑ b : Fin r, coeff i b • z (I b))
        (z j - ∑ b : Fin r, coeff j b • z (I b)) = 0
  right_residual_pair_zero :
    ∀ i j,
      sourceComplexMinkowskiInner d
        (w i - ∑ b : Fin r, coeff i b • w (I b))
        (w j - ∑ b : Fin r, coeff j b • w (I b)) = 0

/-- Data obtained after the selected nondegenerate spans have been matched by
a determinant-one complex Lorentz transformation.  The common selected span is
the target span; only after applying `Λsel` to the left endpoint do the two
residual families live in the same orthogonal complement. -/
structure HWLowRankSelectedSpanAlignment
    (d n r : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ)
    (I : Fin r → Fin n)
    (S : HWLowRankSelectedSpanFrame d n r z w I) where
  M : Submodule ℂ (Fin (d + 1) → ℂ)
  Λsel : ComplexLorentzGroup d
  ξ : Fin n → Fin (d + 1) → ℂ
  leftResidual : Fin n → Fin (d + 1) → ℂ
  rightResidual : Fin n → Fin (d + 1) → ℂ
  M_eq : M = Submodule.span ℂ (Set.range fun a : Fin r => w (I a))
  M_nondeg : ComplexMinkowskiNondegenerateSubspace d M
  selected_mem : ∀ a, w (I a) ∈ M
  Λsel_selected :
    ∀ a, complexLorentzVectorAction Λsel (z (I a)) = w (I a)
  ξ_eq : ∀ i, ξ i = ∑ b : Fin r, S.coeff i b • w (I b)
  ξ_mem : ∀ i, ξ i ∈ M
  leftResidual_eq :
    ∀ i, leftResidual i = complexLorentzVectorAction Λsel (z i) - ξ i
  rightResidual_eq : ∀ i, rightResidual i = w i - ξ i
  left_decomp :
    ∀ i, complexLorentzVectorAction Λsel (z i) = ξ i + leftResidual i
  right_decomp : ∀ i, w i = ξ i + rightResidual i
  left_residual_orth_M :
    ∀ i (m : M),
      sourceComplexMinkowskiInner d (leftResidual i)
        (m : Fin (d + 1) → ℂ) = 0
  right_residual_orth_M :
    ∀ i (m : M),
      sourceComplexMinkowskiInner d (rightResidual i)
        (m : Fin (d + 1) → ℂ) = 0
  left_residual_pair_zero :
    ∀ i j,
      sourceComplexMinkowskiInner d (leftResidual i) (leftResidual j) = 0
  right_residual_pair_zero :
    ∀ i j,
      sourceComplexMinkowskiInner d (rightResidual i) (rightResidual j) = 0

/-- Once the selected spans are aligned, the left and right residual families
span totally isotropic subspaces in the orthogonal complement of the common
selected span. -/
theorem hw_lowRank_residualSubspaces_after_selectedAlignment
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) :
    ∃ (Rleft Rright : Submodule ℂ (Fin (d + 1) → ℂ)),
      Rleft = Submodule.span ℂ (Set.range A.leftResidual) ∧
      Rright = Submodule.span ℂ (Set.range A.rightResidual) ∧
      (∀ x : Rleft, ∀ m : A.M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0) ∧
      (∀ x : Rright, ∀ m : A.M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0) ∧
      ComplexMinkowskiTotallyIsotropicSubspace d Rleft ∧
      ComplexMinkowskiTotallyIsotropicSubspace d Rright := by
  refine
    ⟨Submodule.span ℂ (Set.range A.leftResidual),
      Submodule.span ℂ (Set.range A.rightResidual), rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro x m
    exact
      span_frame_orthogonal_to_subspace
        (d := d) (s := n) (M := A.M) (q := A.leftResidual)
        A.left_residual_orth_M x.2 m
  · intro x m
    exact
      span_frame_orthogonal_to_subspace
        (d := d) (s := n) (M := A.M) (q := A.rightResidual)
        A.right_residual_orth_M x.2 m
  · exact
      complexMinkowskiTotallyIsotropic_span_range
        d n A.leftResidual A.left_residual_pair_zero
  · exact
      complexMinkowskiTotallyIsotropic_span_range
        d n A.rightResidual A.right_residual_pair_zero

end BHW
