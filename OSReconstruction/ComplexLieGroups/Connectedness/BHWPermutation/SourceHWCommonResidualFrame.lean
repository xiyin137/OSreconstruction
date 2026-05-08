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

/-- Inside the span `M ⊔ R`, the two pulled-back summands are complementary
as soon as `M` and `R` are disjoint in the ambient source space. -/
theorem isCompl_comap_sup_subtype_of_disjoint
    {d : ℕ} {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hdisj : Disjoint M R) :
    IsCompl
      (M.comap (M ⊔ R).subtype)
      (R.comap (M ⊔ R).subtype) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxM hxR
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hdisj
      (x : Fin (d + 1) → ℂ) hxM hxR
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [Submodule.mem_sup]
    have hxSup : (x : Fin (d + 1) → ℂ) ∈ M ⊔ R := x.2
    rw [Submodule.mem_sup] at hxSup
    rcases hxSup with ⟨m, hm, r, hr, hsum⟩
    refine ⟨⟨m, ?_⟩, hm, ⟨r, ?_⟩, hr, ?_⟩
    · exact Submodule.mem_sup_left hm
    · exact Submodule.mem_sup_right hr
    · apply Subtype.ext
      simpa using hsum

/-- The direct sum of the identity on the selected nondegenerate span with an
injective residual embedding, viewed as a linear equivalence between the two
ambient sup submodules.  Pairing preservation is proved separately from the
block formulas and the residual embedding's preservation field. -/
noncomputable def directSum_identity_sum_isotropicEmbedding
    {d : ℕ}
    (M R : Submodule ℂ (Fin (d + 1) → ℂ))
    (E : R →ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0)
    (hE_inj : Function.Injective E)
    (hE_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (E x)
          (m : Fin (d + 1) → ℂ) = 0) :
    ↥(M ⊔ R) ≃ₗ[ℂ] ↥(M ⊔ (LinearMap.range E)) := by
  let Sdom : Submodule ℂ (Fin (d + 1) → ℂ) := M ⊔ R
  let Scod : Submodule ℂ (Fin (d + 1) → ℂ) :=
    M ⊔ (LinearMap.range E)
  let Mdom : Submodule ℂ Sdom := M.comap Sdom.subtype
  let Rdom : Submodule ℂ Sdom := R.comap Sdom.subtype
  let Mcod : Submodule ℂ Scod := M.comap Scod.subtype
  let Rcod : Submodule ℂ Scod := (LinearMap.range E).comap Scod.subtype
  have hdom : IsCompl Mdom Rdom := by
    simpa [Sdom, Mdom, Rdom] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := R)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hR_orth)
  have hRange_orth :
      ∀ x : LinearMap.range E, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0 := by
    intro x m
    rcases x.2 with ⟨r, hr⟩
    rw [← hr]
    exact hE_orth r m
  have hcod : IsCompl Mcod Rcod := by
    simpa [Scod, Mcod, Rcod] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := LinearMap.range E)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hRange_orth)
  let eMdom : Mdom ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Sdom from le_sup_left)
  let eMcod : Mcod ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Scod from le_sup_left)
  let eRdom : Rdom ≃ₗ[ℂ] R :=
    Submodule.comapSubtypeEquivOfLe (show R ≤ Sdom from le_sup_right)
  let eRcod : Rcod ≃ₗ[ℂ] LinearMap.range E :=
    Submodule.comapSubtypeEquivOfLe
      (show LinearMap.range E ≤ Scod from le_sup_right)
  let eRange : R ≃ₗ[ℂ] LinearMap.range E :=
    LinearEquiv.ofInjective E hE_inj
  let eM : Mdom ≃ₗ[ℂ] Mcod := eMdom.trans eMcod.symm
  let eR : Rdom ≃ₗ[ℂ] Rcod := eRdom.trans (eRange.trans eRcod.symm)
  exact (Submodule.prodEquivOfIsCompl Mdom Rdom hdom).symm.trans
    ((eM.prodCongr eR).trans
      (Submodule.prodEquivOfIsCompl Mcod Rcod hcod))

/-- The direct-sum equivalence sends a vector in the residual summand to its
chosen embedded residual vector. -/
theorem directSum_identity_sum_isotropicEmbedding_maps_right
    {d : ℕ}
    {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    {E : R →ₗ[ℂ] (Fin (d + 1) → ℂ)}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0)
    (hE_inj : Function.Injective E)
    (hE_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (E x)
          (m : Fin (d + 1) → ℂ) = 0)
    (x : R) :
    ((directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth)
      ⟨(x : Fin (d + 1) → ℂ), Submodule.mem_sup_right x.2⟩ :
        Fin (d + 1) → ℂ) = E x := by
  let Sdom : Submodule ℂ (Fin (d + 1) → ℂ) := M ⊔ R
  let Scod : Submodule ℂ (Fin (d + 1) → ℂ) :=
    M ⊔ (LinearMap.range E)
  let Mdom : Submodule ℂ Sdom := M.comap Sdom.subtype
  let Rdom : Submodule ℂ Sdom := R.comap Sdom.subtype
  let Mcod : Submodule ℂ Scod := M.comap Scod.subtype
  let Rcod : Submodule ℂ Scod := (LinearMap.range E).comap Scod.subtype
  have hdom : IsCompl Mdom Rdom := by
    simpa [Sdom, Mdom, Rdom] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := R)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hR_orth)
  have hRange_orth :
      ∀ x : LinearMap.range E, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0 := by
    intro x m
    rcases x.2 with ⟨r, hr⟩
    rw [← hr]
    exact hE_orth r m
  have hcod : IsCompl Mcod Rcod := by
    simpa [Scod, Mcod, Rcod] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := LinearMap.range E)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hRange_orth)
  let eMdom : Mdom ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Sdom from le_sup_left)
  let eMcod : Mcod ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Scod from le_sup_left)
  let eRdom : Rdom ≃ₗ[ℂ] R :=
    Submodule.comapSubtypeEquivOfLe (show R ≤ Sdom from le_sup_right)
  let eRcod : Rcod ≃ₗ[ℂ] LinearMap.range E :=
    Submodule.comapSubtypeEquivOfLe
      (show LinearMap.range E ≤ Scod from le_sup_right)
  let eRange : R ≃ₗ[ℂ] LinearMap.range E :=
    LinearEquiv.ofInjective E hE_inj
  let eM : Mdom ≃ₗ[ℂ] Mcod := eMdom.trans eMcod.symm
  let eR : Rdom ≃ₗ[ℂ] Rcod := eRdom.trans (eRange.trans eRcod.symm)
  let T : Sdom ≃ₗ[ℂ] Scod :=
    (Submodule.prodEquivOfIsCompl Mdom Rdom hdom).symm.trans
      ((eM.prodCongr eR).trans
        (Submodule.prodEquivOfIsCompl Mcod Rcod hcod))
  have hTdef :
      directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth = T := by
    rfl
  rw [hTdef]
  let y : Sdom :=
    ⟨(x : Fin (d + 1) → ℂ), Submodule.mem_sup_right x.2⟩
  let xr : Rdom := ⟨y, x.2⟩
  have hsymm :
      (Submodule.prodEquivOfIsCompl Mdom Rdom hdom).symm y =
        (0, xr) := by
    simpa [y, xr] using
      Submodule.prodEquivOfIsCompl_symm_apply_right Mdom Rdom hdom xr
  have heR_val : ((eR xr : Rcod) : Fin (d + 1) → ℂ) = E x := by
    rfl
  have heM_zero : ((eM (0 : Mdom) : Mcod) : Fin (d + 1) → ℂ) = 0 := by
    rfl
  calc
    ((T y : Scod) : Fin (d + 1) → ℂ)
        = (((Submodule.prodEquivOfIsCompl Mcod Rcod hcod)
            ((eM.prodCongr eR) (0, xr)) : Scod) :
              Fin (d + 1) → ℂ) := by
            dsimp [T]
            rw [hsymm]
    _ = ((eM (0 : Mdom) : Mcod) : Fin (d + 1) → ℂ) +
          ((eR xr : Rcod) : Fin (d + 1) → ℂ) := by
            rfl
    _ = E x := by
            rw [heM_zero, heR_val, zero_add]

end BHW
