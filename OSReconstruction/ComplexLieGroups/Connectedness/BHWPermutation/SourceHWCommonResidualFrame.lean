import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWLowRankAlignment

/-!
# Hall-Wightman common residual-frame support

This file contains the first mechanical subspace facts needed by the
low-rank common residual-frame theorem.  Once the selected spans are aligned,
the residual spans lie in the common orthogonal complement; nondegeneracy of
the selected span then makes the sums with that selected span disjoint.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- A subspace whose vectors are pointwise orthogonal to `M` is contained in
the Minkowski orthogonal complement of `M`. -/
theorem subspace_le_complexMinkowskiOrthogonalSubmodule
    {d : ℕ} {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0) :
    R ≤ complexMinkowskiOrthogonalSubmodule d M := by
  intro x hx
  rw [mem_complexMinkowskiOrthogonalSubmodule_iff]
  intro m
  exact hR_orth ⟨x, hx⟩ m

/-- If `M` is nondegenerate and `R` is orthogonal to `M`, then the selected
span and the residual span intersect trivially. -/
theorem complexMinkowski_disjoint_of_nondegenerate_orthogonal
    {d : ℕ} {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0) :
    Disjoint M R := by
  rw [Submodule.disjoint_def]
  intro x hxM hxR
  have hx0_sub : (⟨x, hxM⟩ : M) = 0 := by
    apply hM
    intro m
    exact hR_orth ⟨x, hxR⟩ m
  exact show x = 0 from congrArg Subtype.val hx0_sub

/-- The checked selected-span alignment yields residual spans in the common
Minkowski orthogonal complement, disjoint from the selected span, and totally
isotropic.  This is the exact packet consumed by the common residual-frame
Witt-extension step. -/
theorem hw_lowRank_residualSubspaces_orthogonalComplement_after_selectedAlignment
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) :
    ∃ (Rleft Rright : Submodule ℂ (Fin (d + 1) → ℂ)),
      Rleft = Submodule.span ℂ (Set.range A.leftResidual) ∧
      Rright = Submodule.span ℂ (Set.range A.rightResidual) ∧
      Rleft ≤ complexMinkowskiOrthogonalSubmodule d A.M ∧
      Rright ≤ complexMinkowskiOrthogonalSubmodule d A.M ∧
      Disjoint A.M Rleft ∧
      Disjoint A.M Rright ∧
      ComplexMinkowskiTotallyIsotropicSubspace d Rleft ∧
      ComplexMinkowskiTotallyIsotropicSubspace d Rright := by
  rcases hw_lowRank_residualSubspaces_after_selectedAlignment
      (d := d) (n := n) (r := r) (z := z) (w := w)
      (I := I) (S := S) A with
    ⟨Rleft, Rright, hRleft_eq, hRright_eq,
      hRleft_orth, hRright_orth, hRleft_iso, hRright_iso⟩
  refine ⟨Rleft, Rright, hRleft_eq, hRright_eq, ?_, ?_, ?_, ?_,
    hRleft_iso, hRright_iso⟩
  · exact subspace_le_complexMinkowskiOrthogonalSubmodule hRleft_orth
  · exact subspace_le_complexMinkowskiOrthogonalSubmodule hRright_orth
  · exact
      complexMinkowski_disjoint_of_nondegenerate_orthogonal
        A.M_nondeg hRleft_orth
  · exact
      complexMinkowski_disjoint_of_nondegenerate_orthogonal
        A.M_nondeg hRright_orth

end BHW
