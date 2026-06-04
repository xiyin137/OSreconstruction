import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicExtension

/-!
# Final maximal isotropic extension wrapper

This file keeps the small final wrapper separate from the quotient-preimage
support file so Lean can use those support theorems as imported declarations.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

set_option maxHeartbeats 800000

local instance sourceHWMaximalIsotropicFinal_hasQuotient
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) :
    HasQuotient (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)
      (Submodule ℂ (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)) :=
  Submodule.hasQuotient (R := ℂ)
    (M := complexMinkowskiRelativeOrthogonalIn (d := d) N RN)

/-- A totally isotropic subspace `R ≤ N` extends to a globally maximal
isotropic subspace of `N`. -/
theorem complexMinkowski_maximalIsotropicSubspaceIn_extending
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    ∃ F : ComplexMinkowskiMaximalIsotropicSubspaceIn d N,
      R ≤ F.Q := by
  let M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R) :=
    complexMinkowskiRelativeOrthogonalQuotient_maximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R)
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) :=
    complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N
      (complexMinkowskiSubmoduleIn (d := d) N R) M.Q
  have hR_le_Q : R ≤ Q :=
    complexMinkowskiSubmodule_le_relativeOrthogonalQuotientPreimage
      (d := d) (N := N) (R := R) hR_le hR_iso M.Q
  have hQ_le : Q ≤ N :=
    complexMinkowskiRelativeOrthogonalQuotientPreimage_le
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R) M.Q
  have hQ_iso : ComplexMinkowskiTotallyIsotropicSubspace d Q :=
    complexMinkowskiRelativeOrthogonalQuotientPreimage_isotropic
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R) M.Q M.Q_iso
  have hQ_fin :
      Module.finrank ℂ
          (complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N
            (complexMinkowskiSubmoduleIn (d := d) N R) M.Q) =
        Module.finrank ℂ R + Module.finrank ℂ M.Q := by
    exact
      complexMinkowskiRelativeOrthogonalQuotientPreimage_finrank_eq_add
        (d := d) (N := N) (R := R) hR_le hR_iso M.Q
  have hQ_fin' :
      Module.finrank ℂ Q = Module.finrank ℂ R + Module.finrank ℂ M.Q := by
    exact hQ_fin
  have hQ_global_max :
      ∀ S : Submodule ℂ (Fin (d + 1) → ℂ),
        S ≤ N →
        ComplexMinkowskiTotallyIsotropicSubspace d S →
        Module.finrank ℂ S ≤ Module.finrank ℂ Q :=
    complexMinkowskiSubspace_global_maximal_of_quotient_maximal
      (d := d) (N := N) (R := R) (Q := Q) hR_le hR_iso M hQ_fin'
  exact ⟨{ Q := Q, Q_le := hQ_le, Q_iso := hQ_iso, maximal := hQ_global_max },
    hR_le_Q⟩

/-- A totally isotropic subspace `R ≤ N` extends to a globally maximal
isotropic frame of `N` whose span contains `R`. -/
theorem complexMinkowski_maximalIsotropicFrameIn_extending
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    ∃ F : ComplexMinkowskiMaximalIsotropicFrameIn d N,
      R ≤ Submodule.span ℂ (Set.range F.q) := by
  rcases complexMinkowski_maximalIsotropicSubspaceIn_extending
    (d := d) (N := N) (R := R) hR_le hR_iso with ⟨F, hR_le_F⟩
  exact
    complexMinkowski_maximalIsotropicFrameIn_of_subspace_containing
      (d := d) (N := N) (R := R) F hR_le_F

end BHW
