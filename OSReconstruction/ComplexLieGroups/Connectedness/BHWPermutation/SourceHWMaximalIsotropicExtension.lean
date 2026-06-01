import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicQuotient

/-!
# Compatible maximal isotropic extension

This file keeps the final wrapper for extending a fixed totally isotropic
subspace to a globally maximal one separate from the quotient/rank-nullity
support file.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

set_option maxHeartbeats 800000

local instance sourceHWMaximalIsotropicExtension_hasQuotient
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) :
    HasQuotient (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)
      (Submodule ℂ (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)) :=
  Submodule.hasQuotient (R := ℂ)
    (M := complexMinkowskiRelativeOrthogonalIn (d := d) N RN)

/-- The named quotient-preimage candidate contains the original isotropic
subspace. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal_contains
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R)) :
    R ≤ complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal
      (d := d) (N := N) (R := R) M := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  rw [complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal]
  exact
    complexMinkowskiSubmodule_le_relativeOrthogonalQuotientPreimage
      (d := d) (N := N) (R := R) hR_le hR_iso M.Q

/-- The named quotient-preimage candidate remains inside `N`. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal_le
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R)) :
    complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal
      (d := d) (N := N) (R := R) M ≤ N := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  rw [complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal]
  exact
    complexMinkowskiRelativeOrthogonalQuotientPreimage_le
      (d := d) (N := N) RN M.Q

/-- The named quotient-preimage candidate is totally isotropic. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal_isotropic
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R)) :
    ComplexMinkowskiTotallyIsotropicSubspace d
      (complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal
        (d := d) (N := N) (R := R) M) := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  rw [complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal]
  exact
    complexMinkowskiRelativeOrthogonalQuotientPreimage_isotropic
      (d := d) (N := N) RN M.Q M.Q_iso

/-- Assemble a globally maximal isotropic subspace from the named quotient
preimage candidate once its finrank formula has been supplied. -/
theorem complexMinkowski_maximalIsotropicSubspaceIn_extending_of_finrank
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R))
    (hQ_fin :
      Module.finrank ℂ
          (complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal
            (d := d) (N := N) (R := R) M) =
        Module.finrank ℂ R + Module.finrank ℂ M.Q) :
    ∃ F : ComplexMinkowskiMaximalIsotropicSubspaceIn d N,
      R ≤ F.Q := by
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) :=
    complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal
      (d := d) (N := N) (R := R) M
  have hR_le_Q : R ≤ Q :=
    complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal_contains
      (d := d) (N := N) (R := R) hR_le hR_iso M
  have hQ_le : Q ≤ N :=
    complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal_le
      (d := d) (N := N) (R := R) M
  have hQ_iso : ComplexMinkowskiTotallyIsotropicSubspace d Q :=
    complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal_isotropic
      (d := d) (N := N) (R := R) M
  have hQ_fin' :
      Module.finrank ℂ Q = Module.finrank ℂ R + Module.finrank ℂ M.Q :=
    hQ_fin
  have hQ_global_max :
      ∀ S : Submodule ℂ (Fin (d + 1) → ℂ),
        S ≤ N →
        ComplexMinkowskiTotallyIsotropicSubspace d S →
        Module.finrank ℂ S ≤ Module.finrank ℂ Q :=
    complexMinkowskiSubspace_global_maximal_of_quotient_maximal
      (d := d) (N := N) (R := R) (Q := Q) hR_le hR_iso M hQ_fin'
  exact ⟨{ Q := Q, Q_le := hQ_le, Q_iso := hQ_iso, maximal := hQ_global_max },
    hR_le_Q⟩

end BHW
