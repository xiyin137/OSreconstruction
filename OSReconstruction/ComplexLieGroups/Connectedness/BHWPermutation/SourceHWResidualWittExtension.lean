import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicFrame

/-!
# Nondegenerate block extension for Hall-Wightman residual Witt geometry

This file isolates the nondegenerate part of the remaining low-rank residual
extension theorem.  After the future construction adjoins hyperbolic duals to
the degenerate residual blocks, the resulting pairing-preserving equivalence is
between nondegenerate subspaces.  The theorems below extend that equivalence to
the full ambient complex Minkowski space by matching orthogonal complements.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Nondegenerate orthogonal complements of same-finrank nondegenerate
subspaces are linearly isometric for the complex Minkowski form. -/
theorem exists_complexMinkowskiOrthogonalComplementIsometry_of_finrank_eq
    {d : ℕ}
    {K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hK : ComplexMinkowskiNondegenerateSubspace d K)
    (hL : ComplexMinkowskiNondegenerateSubspace d L)
    (hfin : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ C :
        complexMinkowskiOrthogonalSubmodule d K ≃ₗ[ℂ]
          complexMinkowskiOrthogonalSubmodule d L,
      ∀ x y,
        sourceComplexMinkowskiInner d
          ((C x : complexMinkowskiOrthogonalSubmodule d L) :
            Fin (d + 1) → ℂ)
          ((C y : complexMinkowskiOrthogonalSubmodule d L) :
            Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) := by
  let B := sourceComplexMinkowskiBilinForm d
  have hB_nd : B.Nondegenerate :=
    sourceComplexMinkowskiBilinForm_nondegenerate d
  have hB_symm : B.IsSymm :=
    sourceComplexMinkowskiBilinForm_isSymm d
  have hOK_nd :
      (B.restrict (complexMinkowskiOrthogonalSubmodule d K)).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict
      d _
      (complexMinkowskiOrthogonalSubmodule_nondegenerate d hK)
  have hOL_nd :
      (B.restrict (complexMinkowskiOrthogonalSubmodule d L)).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict
      d _
      (complexMinkowskiOrthogonalSubmodule_nondegenerate d hL)
  have hfin_comp :
      Module.finrank ℂ (complexMinkowskiOrthogonalSubmodule d K) =
        Module.finrank ℂ (complexMinkowskiOrthogonalSubmodule d L) := by
    have hK_orth :=
      LinearMap.BilinForm.finrank_orthogonal (B := B) hB_nd K
    have hL_orth :=
      LinearMap.BilinForm.finrank_orthogonal (B := B) hB_nd L
    rw [
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d K] at hK_orth
    rw [
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d L] at hL_orth
    omega
  rcases
    nondegenerate_complexSymmetricBilinForm_linearEquiv_of_finrank_eq
      (B.restrict (complexMinkowskiOrthogonalSubmodule d K))
      (B.restrict (complexMinkowskiOrthogonalSubmodule d L))
      (restrict_isSymm_of_isSymm hB_symm _)
      (restrict_isSymm_of_isSymm hB_symm _)
      hOK_nd hOL_nd hfin_comp with
  ⟨C, hC⟩
  exact ⟨C, by
    intro x y
    simpa [LinearMap.BilinForm.restrict, B,
      sourceComplexMinkowskiBilinForm] using hC x y⟩

/-- A pairing-preserving equivalence between nondegenerate complex-Minkowski
subspaces extends to a pairing-preserving ambient linear equivalence. -/
theorem complexMinkowski_nondegenerateSubspaceEquiv_ambientExtension
    {d : ℕ}
    {K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hK : ComplexMinkowskiNondegenerateSubspace d K)
    (hL : ComplexMinkowskiNondegenerateSubspace d L)
    (T : K ≃ₗ[ℂ] L)
    (hT :
      ∀ x y,
        sourceComplexMinkowskiInner d
          (T x : Fin (d + 1) → ℂ)
          (T y : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ)) :
    ∃ E : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ),
      (∀ x y,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d x y) ∧
      ∀ x : K, E (x : Fin (d + 1) → ℂ) = (T x : Fin (d + 1) → ℂ) := by
  rcases
    exists_complexMinkowskiOrthogonalComplementIsometry_of_finrank_eq
      (d := d) hK hL T.finrank_eq with
  ⟨C, hC⟩
  let B := sourceComplexMinkowskiBilinForm d
  have hK_rest : (B.restrict K).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict d K hK
  have hL_rest : (B.restrict L).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict d L hL
  have hK_compl0 : IsCompl K (B.orthogonal K) :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := B) (W := K)
      (sourceComplexMinkowskiBilinForm_isRefl d)).mp hK_rest
  have hL_compl0 : IsCompl L (B.orthogonal L) :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := B) (W := L)
      (sourceComplexMinkowskiBilinForm_isRefl d)).mp hL_rest
  have hK_compl :
      IsCompl K (complexMinkowskiOrthogonalSubmodule d K) := by
    simpa [B,
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d K] using hK_compl0
  have hL_compl :
      IsCompl L (complexMinkowskiOrthogonalSubmodule d L) := by
    simpa [B,
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d L] using hL_compl0
  let OK := complexMinkowskiOrthogonalSubmodule d K
  let OL := complexMinkowskiOrthogonalSubmodule d L
  let eK : (K × OK) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    Submodule.prodEquivOfIsCompl K OK hK_compl
  let eL : (L × OL) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    Submodule.prodEquivOfIsCompl L OL hL_compl
  let P : (K × OK) ≃ₗ[ℂ] (L × OL) :=
    T.prodCongr C
  let E : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    eK.symm.trans (P.trans eL)
  refine ⟨E, ?_, ?_⟩
  · intro x y
    let xu : K × OK := eK.symm x
    let yv : K × OK := eK.symm y
    calc
      sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d (eL (P xu)) (eL (P yv)) := by
            simp [E, xu, yv]
      _ =
          sourceComplexMinkowskiInner d
            ((P xu).1 : Fin (d + 1) → ℂ)
            ((P yv).1 : Fin (d + 1) → ℂ) +
          sourceComplexMinkowskiInner d
            ((P xu).2 : Fin (d + 1) → ℂ)
            ((P yv).2 : Fin (d + 1) → ℂ) := by
            exact sourceInner_prodEquivOfIsCompl L hL_compl (P xu) (P yv)
      _ =
          sourceComplexMinkowskiInner d
            (xu.1 : Fin (d + 1) → ℂ)
            (yv.1 : Fin (d + 1) → ℂ) +
          sourceComplexMinkowskiInner d
            (xu.2 : Fin (d + 1) → ℂ)
            (yv.2 : Fin (d + 1) → ℂ) := by
            simp [P, hT, hC]
      _ = sourceComplexMinkowskiInner d (eK xu) (eK yv) := by
            rw [sourceInner_prodEquivOfIsCompl K hK_compl xu yv]
      _ = sourceComplexMinkowskiInner d x y := by
            simp [xu, yv]
  · intro x
    have hx :
        eK.symm (x : Fin (d + 1) → ℂ) = (x, (0 : OK)) := by
      exact Submodule.prodEquivOfIsCompl_symm_apply_left K OK hK_compl x
    calc
      E (x : Fin (d + 1) → ℂ) =
          eL (P (eK.symm (x : Fin (d + 1) → ℂ))) := by
            rfl
      _ = eL (P (x, (0 : OK))) := by
            rw [hx]
      _ = eL (T x, (0 : OL)) := by
            simp [P]
      _ = (T x : Fin (d + 1) → ℂ) := by
            simp [eL]

/-- A proper nondegenerate source subspace admits a determinant-`-1` full
complex Lorentz reflection fixing it pointwise. -/
theorem fullComplexLorentz_det_neg_reflection_fixing_nondegenerate_subspace
    {d : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hproper : Module.finrank ℂ M < d + 1) :
    ∃ R : HallWightmanFullComplexLorentzGroup d,
      hallWightmanFullComplexLorentzDet R = -1 ∧
      ∀ x : M,
        hallWightmanFullComplexLorentzVectorAction R
            (x : Fin (d + 1) → ℂ) =
          x := by
  have hcomp_ne :
      complexMinkowskiOrthogonalSubmodule d M ≠ ⊥ :=
    complexMinkowskiOrthogonalSubmodule_ne_bot_of_finrank_lt d hproper
  letI : Nontrivial (complexMinkowskiOrthogonalSubmodule d M) :=
    (Submodule.nontrivial_iff_ne_bot).2 hcomp_ne
  rcases
    exists_nonisotropic_in_nondegenerate_subspace d
      (complexMinkowskiOrthogonalSubmodule d M)
      (complexMinkowskiOrthogonalSubmodule_nondegenerate d hM) with
  ⟨u, hu⟩
  refine
    ⟨fullComplexLorentzReflection u hu,
      fullComplexLorentzReflection_det u hu,
      ?_⟩
  intro x
  exact fullComplexLorentzReflection_fix_subspace u hu x

/-- A pairing-preserving equivalence between nondegenerate subspaces extends to
a determinant-one proper complex Lorentz transformation, provided the target
subspace is proper.  If the raw ambient extension has determinant `-1`, a
Householder reflection fixing the target subspace repairs the determinant
without changing the prescribed action on the source block. -/
theorem complexMinkowski_nondegenerateSubspaceEquiv_detOne_orbitExtension
    {d : ℕ}
    {K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hK : ComplexMinkowskiNondegenerateSubspace d K)
    (hL : ComplexMinkowskiNondegenerateSubspace d L)
    (hLproper : Module.finrank ℂ L < d + 1)
    (T : K ≃ₗ[ℂ] L)
    (hT :
      ∀ x y,
        sourceComplexMinkowskiInner d
          (T x : Fin (d + 1) → ℂ)
          (T y : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ)) :
    ∃ Λ : ComplexLorentzGroup d,
      ∀ x : K,
        complexLorentzVectorAction Λ (x : Fin (d + 1) → ℂ) =
          (T x : Fin (d + 1) → ℂ) := by
  rcases
    complexMinkowski_nondegenerateSubspaceEquiv_ambientExtension
      (d := d) hK hL T hT with
  ⟨E, hE_pres, hE_apply⟩
  let A : HallWightmanFullComplexLorentzGroup d :=
    HallWightmanFullComplexLorentzGroup.ofLinearMap E.toLinearMap hE_pres
  have hA_action :
      ∀ v,
        hallWightmanFullComplexLorentzVectorAction A v = E v := by
    intro v
    simpa [A] using
      HallWightmanFullComplexLorentzGroup.ofLinearMap_vectorAction
        E.toLinearMap hE_pres v
  by_cases hdetA : hallWightmanFullComplexLorentzDet A = 1
  · rcases fullComplexLorentz_to_complexLorentzGroup_of_det_one A hdetA with
    ⟨Λ, hΛ⟩
    refine ⟨Λ, ?_⟩
    intro x
    calc
      complexLorentzVectorAction Λ (x : Fin (d + 1) → ℂ) =
          hallWightmanFullComplexLorentzVectorAction A
            (x : Fin (d + 1) → ℂ) := hΛ _
      _ = E (x : Fin (d + 1) → ℂ) := hA_action _
      _ = (T x : Fin (d + 1) → ℂ) := hE_apply x
  · have hA_neg : hallWightmanFullComplexLorentzDet A = -1 :=
      det_eq_neg_one_of_sq_one_of_ne_one
        (hallWightmanFullComplexLorentz_det_sq_eq_one A) hdetA
    rcases
      fullComplexLorentz_det_neg_reflection_fixing_nondegenerate_subspace
        (d := d) hL hLproper with
    ⟨R, hRdet, hRfix⟩
    let RA : HallWightmanFullComplexLorentzGroup d :=
      hallWightmanFullComplexLorentzMul R A
    have hRAdet : hallWightmanFullComplexLorentzDet RA = 1 := by
      simp [RA, fullComplexLorentz_mul_det, hRdet, hA_neg]
    rcases fullComplexLorentz_to_complexLorentzGroup_of_det_one RA hRAdet with
    ⟨Λ, hΛ⟩
    refine ⟨Λ, ?_⟩
    intro x
    have hEx : E (x : Fin (d + 1) → ℂ) = (T x : Fin (d + 1) → ℂ) :=
      hE_apply x
    calc
      complexLorentzVectorAction Λ (x : Fin (d + 1) → ℂ) =
          hallWightmanFullComplexLorentzVectorAction RA
            (x : Fin (d + 1) → ℂ) := hΛ _
      _ =
          hallWightmanFullComplexLorentzVectorAction R
            (hallWightmanFullComplexLorentzVectorAction A
              (x : Fin (d + 1) → ℂ)) := by
            simpa [RA] using
              fullComplexLorentz_mul_vectorAction R A
                (x : Fin (d + 1) → ℂ)
      _ =
          hallWightmanFullComplexLorentzVectorAction R
            (E (x : Fin (d + 1) → ℂ)) := by
            rw [hA_action]
      _ = hallWightmanFullComplexLorentzVectorAction R
            (T x : Fin (d + 1) → ℂ) := by
            rw [hEx]
      _ = (T x : Fin (d + 1) → ℂ) := hRfix (T x)

/-- The nondegenerate block data needed after adjoining compatible hyperbolic
duals to the degenerate residual source and target blocks.  The producer of this
structure is the remaining hard finite-dimensional step for the selected
residual hyperbolic extension. -/
structure HWSelectedResidualHyperbolicBlockExtensionData
    {d s : ℕ}
    {M Rleft : Submodule ℂ (Fin (d + 1) → ℂ)}
    (q : Fin s → Fin (d + 1) → ℂ) where
  K : Submodule ℂ (Fin (d + 1) → ℂ)
  L : Submodule ℂ (Fin (d + 1) → ℂ)
  K_nondeg : ComplexMinkowskiNondegenerateSubspace d K
  L_nondeg : ComplexMinkowskiNondegenerateSubspace d L
  L_proper : Module.finrank ℂ L < d + 1
  K_M : M ≤ K
  K_left : Rleft ≤ K
  Tblock : K ≃ₗ[ℂ] L
  Tblock_preserves :
    ∀ x y : K,
      sourceComplexMinkowskiInner d
        (Tblock x : Fin (d + 1) → ℂ)
        (Tblock y : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ)
        (y : Fin (d + 1) → ℂ)
  Tblock_M :
    ∀ m : M,
      (Tblock ⟨(m : Fin (d + 1) → ℂ), K_M m.2⟩ :
        Fin (d + 1) → ℂ) =
      (m : Fin (d + 1) → ℂ)
  Tblock_left_span :
    ∀ x : Rleft,
      (Tblock ⟨(x : Fin (d + 1) → ℂ), K_left x.2⟩ :
        Fin (d + 1) → ℂ) ∈
      Submodule.span ℂ (Set.range q)

/-- Once the compatible residual hyperbolic block extension data is available,
the selected residual hyperbolic extension output is mechanical. -/
theorem complexMinkowski_selectedResidualHyperbolicExtension_of_blockExtensionData
    {d s : ℕ}
    {M Rleft : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (D : HWSelectedResidualHyperbolicBlockExtensionData (d := d)
      (M := M) (Rleft := Rleft) q) :
    ∃ Λfix : ComplexLorentzGroup d,
      (∀ m : M,
        complexLorentzVectorAction Λfix
          (m : Fin (d + 1) → ℂ) =
        (m : Fin (d + 1) → ℂ)) ∧
      ∀ x : Rleft,
        complexLorentzVectorAction Λfix
          (x : Fin (d + 1) → ℂ) ∈
        Submodule.span ℂ (Set.range q) := by
  rcases
    complexMinkowski_nondegenerateSubspaceEquiv_detOne_orbitExtension
      (d := d) D.K_nondeg D.L_nondeg D.L_proper D.Tblock
      D.Tblock_preserves with
  ⟨Λfix, hΛfix⟩
  refine ⟨Λfix, ?_, ?_⟩
  · intro m
    calc
      complexLorentzVectorAction Λfix (m : Fin (d + 1) → ℂ) =
          complexLorentzVectorAction Λfix
            ((⟨(m : Fin (d + 1) → ℂ), D.K_M m.2⟩ : D.K) :
              Fin (d + 1) → ℂ) := rfl
      _ =
          (D.Tblock ⟨(m : Fin (d + 1) → ℂ), D.K_M m.2⟩ :
            Fin (d + 1) → ℂ) := hΛfix _
      _ = (m : Fin (d + 1) → ℂ) := D.Tblock_M m
  · intro x
    rw [hΛfix (⟨(x : Fin (d + 1) → ℂ), D.K_left x.2⟩ : D.K)]
    exact D.Tblock_left_span x

end BHW
