import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicFinal
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWResidualWittExtension

/-!
# Residual frame-extension bridge

This file packages the checked proper residual hyperbolic block extension into
the final low-rank residual frame-extension data surface.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- If the determinant-one residual hyperbolic block data has been constructed
for the left residual span and a compatible maximal frame whose span contains
the right residual span, then the final low-rank residual frame-extension packet
is mechanical. -/
noncomputable def hw_lowRank_residualFrameExtensionData_of_blockExtensionData
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    {A : HWLowRankSelectedSpanAlignment d n r z w I S}
    {Rleft Rright : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hRleft_eq :
      Rleft = Submodule.span ℂ (Set.range A.leftResidual))
    (hRright_eq :
      Rright = Submodule.span ℂ (Set.range A.rightResidual))
    (F : ComplexMinkowskiMaximalIsotropicFrameIn d
      (complexMinkowskiOrthogonalSubmodule d A.M))
    (hRright_span : Rright ≤ Submodule.span ℂ (Set.range F.q))
    (D : HWSelectedResidualHyperbolicBlockExtensionData
      (d := d) (M := A.M) (Rleft := Rleft) F.q) :
    HWLowRankResidualFrameExtensionData A :=
  let h :=
    complexMinkowski_selectedResidualHyperbolicExtension_of_blockExtensionData
      (d := d) (M := A.M) (Rleft := Rleft) (q := F.q) D
  let Λfix := Classical.choose h
  let hΛfix_M := (Classical.choose_spec h).1
  let hΛfix_left_span := (Classical.choose_spec h).2
  { F := F
    Λfix := Λfix
    Λfix_M := hΛfix_M
    left_span := by
      intro i
      have hi : A.leftResidual i ∈ Rleft := by
        simpa [hRleft_eq] using
          (Submodule.subset_span (R := ℂ) ⟨i, rfl⟩ :
            A.leftResidual i ∈
              Submodule.span ℂ (Set.range A.leftResidual))
      exact hΛfix_left_span ⟨A.leftResidual i, hi⟩
    right_span := by
      intro i
      have hi : A.rightResidual i ∈ Rright := by
        simpa [hRright_eq] using
          (Submodule.subset_span (R := ℂ) ⟨i, rfl⟩ :
            A.rightResidual i ∈
              Submodule.span ℂ (Set.range A.rightResidual))
      exact hRright_span hi }

end BHW
