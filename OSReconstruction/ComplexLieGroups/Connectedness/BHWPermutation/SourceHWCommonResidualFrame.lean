import Mathlib.LinearAlgebra.Dual.Lemmas
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

/-- The direct-sum equivalence fixes the selected nondegenerate span. -/
theorem directSum_identity_sum_isotropicEmbedding_maps_left
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
    (m : M) :
    ((directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth)
      ⟨(m : Fin (d + 1) → ℂ), Submodule.mem_sup_left m.2⟩ :
        Fin (d + 1) → ℂ) = m := by
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
    ⟨(m : Fin (d + 1) → ℂ), Submodule.mem_sup_left m.2⟩
  let xm : Mdom := ⟨y, m.2⟩
  have hsymm :
      (Submodule.prodEquivOfIsCompl Mdom Rdom hdom).symm y =
        (xm, 0) := by
    simpa [y, xm] using
      Submodule.prodEquivOfIsCompl_symm_apply_left Mdom Rdom hdom xm
  have heM_val : ((eM xm : Mcod) : Fin (d + 1) → ℂ) = m := by
    rfl
  have heR_zero : ((eR (0 : Rdom) : Rcod) : Fin (d + 1) → ℂ) = 0 := by
    have hz : eR (0 : Rdom) = 0 := map_zero eR
    exact congrArg (fun y : Rcod => (y : Fin (d + 1) → ℂ)) hz
  calc
    ((T y : Scod) : Fin (d + 1) → ℂ)
        = (((Submodule.prodEquivOfIsCompl Mcod Rcod hcod)
            ((eM.prodCongr eR) (xm, 0)) : Scod) :
              Fin (d + 1) → ℂ) := by
            dsimp [T]
            rw [hsymm]
    _ = ((eM xm : Mcod) : Fin (d + 1) → ℂ) +
          ((eR (0 : Rdom) : Rcod) : Fin (d + 1) → ℂ) := by
            rfl
    _ = m := by
            rw [heM_val, heR_zero, add_zero]

/-- The direct-sum equivalence preserves the complex Minkowski pairing when
the residual embedding preserves residual pairings. -/
theorem directSum_identity_sum_isotropicEmbedding_preserves
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
    (hE_preserves :
      ∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ)
            (y : Fin (d + 1) → ℂ)) :
    let T :=
      directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth
    ∀ x y : ↥(M ⊔ R),
      sourceComplexMinkowskiInner d
        ((T x : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ)
        ((T y : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ)
        (y : Fin (d + 1) → ℂ) := by
  intro T x y
  have hfour :
      ∀ a b c e : Fin (d + 1) → ℂ,
        sourceComplexMinkowskiInner d (a + b) (c + e) =
          sourceComplexMinkowskiInner d a c +
            sourceComplexMinkowskiInner d a e +
            sourceComplexMinkowskiInner d b c +
            sourceComplexMinkowskiInner d b e := by
    intro a b c e
    rw [sourceComplexMinkowskiInner_add_left]
    rw [sourceComplexMinkowskiInner_add_right]
    rw [sourceComplexMinkowskiInner_add_right]
    ring
  rcases (Submodule.mem_sup.mp x.2) with ⟨mx0, hmx0, rx0, hrx0, hxsum⟩
  rcases (Submodule.mem_sup.mp y.2) with ⟨my0, hmy0, ry0, hry0, hysum⟩
  let mx : M := ⟨mx0, hmx0⟩
  let rx : R := ⟨rx0, hrx0⟩
  let my : M := ⟨my0, hmy0⟩
  let ry : R := ⟨ry0, hry0⟩
  let xM : ↥(M ⊔ R) :=
    ⟨(mx : Fin (d + 1) → ℂ), Submodule.mem_sup_left mx.2⟩
  let xR : ↥(M ⊔ R) :=
    ⟨(rx : Fin (d + 1) → ℂ), Submodule.mem_sup_right rx.2⟩
  let yM : ↥(M ⊔ R) :=
    ⟨(my : Fin (d + 1) → ℂ), Submodule.mem_sup_left my.2⟩
  let yR : ↥(M ⊔ R) :=
    ⟨(ry : Fin (d + 1) → ℂ), Submodule.mem_sup_right ry.2⟩
  have hx_decomp : x = xM + xR := by
    apply Subtype.ext
    simpa [xM, xR, mx, rx] using hxsum.symm
  have hy_decomp : y = yM + yR := by
    apply Subtype.ext
    simpa [yM, yR, my, ry] using hysum.symm
  have hTx :
      ((T x : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) =
        (mx : Fin (d + 1) → ℂ) + E rx := by
    calc
      ((T x : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ)
          = ((T (xM + xR) : ↥(M ⊔ LinearMap.range E)) :
              Fin (d + 1) → ℂ) := by rw [hx_decomp]
      _ = ((T xM : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) +
            ((T xR : ↥(M ⊔ LinearMap.range E)) :
              Fin (d + 1) → ℂ) := by
              exact congrArg
                (fun z : ↥(M ⊔ LinearMap.range E) =>
                  (z : Fin (d + 1) → ℂ))
                (map_add T xM xR)
      _ = (mx : Fin (d + 1) → ℂ) + E rx := by
              rw [directSum_identity_sum_isotropicEmbedding_maps_left
                    (d := d) (M := M) (R := R) (E := E)
                    hM hR_orth hE_inj hE_orth mx,
                  directSum_identity_sum_isotropicEmbedding_maps_right
                    (d := d) (M := M) (R := R) (E := E)
                    hM hR_orth hE_inj hE_orth rx]
  have hTy :
      ((T y : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) =
        (my : Fin (d + 1) → ℂ) + E ry := by
    calc
      ((T y : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ)
          = ((T (yM + yR) : ↥(M ⊔ LinearMap.range E)) :
              Fin (d + 1) → ℂ) := by rw [hy_decomp]
      _ = ((T yM : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) +
            ((T yR : ↥(M ⊔ LinearMap.range E)) :
              Fin (d + 1) → ℂ) := by
              exact congrArg
                (fun z : ↥(M ⊔ LinearMap.range E) =>
                  (z : Fin (d + 1) → ℂ))
                (map_add T yM yR)
      _ = (my : Fin (d + 1) → ℂ) + E ry := by
              rw [directSum_identity_sum_isotropicEmbedding_maps_left
                    (d := d) (M := M) (R := R) (E := E)
                    hM hR_orth hE_inj hE_orth my,
                  directSum_identity_sum_isotropicEmbedding_maps_right
                    (d := d) (M := M) (R := R) (E := E)
                    hM hR_orth hE_inj hE_orth ry]
  have hx_val :
      (x : Fin (d + 1) → ℂ) =
        (mx : Fin (d + 1) → ℂ) + (rx : Fin (d + 1) → ℂ) := by
    simpa [mx, rx] using hxsum.symm
  have hy_val :
      (y : Fin (d + 1) → ℂ) =
        (my : Fin (d + 1) → ℂ) + (ry : Fin (d + 1) → ℂ) := by
    simpa [my, ry] using hysum.symm
  have h_mx_Ery :
      sourceComplexMinkowskiInner d (mx : Fin (d + 1) → ℂ) (E ry) = 0 := by
    rw [sourceComplexMinkowskiInner_comm]
    exact hE_orth ry mx
  have h_Erx_my :
      sourceComplexMinkowskiInner d (E rx) (my : Fin (d + 1) → ℂ) = 0 :=
    hE_orth rx my
  have h_mx_ry :
      sourceComplexMinkowskiInner d
        (mx : Fin (d + 1) → ℂ) (ry : Fin (d + 1) → ℂ) = 0 := by
    rw [sourceComplexMinkowskiInner_comm]
    exact hR_orth ry mx
  have h_rx_my :
      sourceComplexMinkowskiInner d
        (rx : Fin (d + 1) → ℂ) (my : Fin (d + 1) → ℂ) = 0 :=
    hR_orth rx my
  rw [hTx, hTy, hx_val, hy_val]
  rw [hfour, hfour]
  rw [h_mx_Ery, h_Erx_my, h_mx_ry, h_rx_my, hE_preserves rx ry]

/-- A totally isotropic subspace embeds injectively into the span of an
independent totally isotropic frame once its finrank is no larger than the
frame length.  Pairing preservation is automatic because both source and
target residual blocks are totally isotropic. -/
theorem complexMinkowski_totallyIsotropic_embedding_into_frame
    {d s : ℕ}
    {R : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (hq_independent : LinearIndependent ℂ q)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (hdim : Module.finrank ℂ R ≤ s) :
    ∃ E : R →ₗ[ℂ] (Fin (d + 1) → ℂ),
      Function.Injective E ∧
      (∀ x : R, E x ∈ Submodule.span ℂ (Set.range q)) ∧
      ∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ)
            (y : Fin (d + 1) → ℂ) := by
  let k := Module.finrank ℂ R
  let b := Module.finBasis ℂ R
  let ι : Fin k → Fin s := Fin.castLE hdim
  let L : (Fin k → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ) := {
    toFun := fun a => ∑ i : Fin k, a i • q (ι i)
    map_add' := by
      intro a b'
      ext μ
      simp [Pi.add_apply, Finset.sum_add_distrib, add_smul]
    map_smul' := by
      intro c a
      ext μ
      simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  let E : R →ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    L.comp b.equivFunL.toLinearMap
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x y hxy
    apply b.equivFunL.injective
    ext i
    have hli_sub : LinearIndependent ℂ (fun i : Fin k => q (ι i)) :=
      hq_independent.comp ι (Fin.castLE_injective hdim)
    have hsum :
        (∑ i : Fin k,
          (b.equivFunL x - b.equivFunL y) i • q (ι i)) = 0 := by
      have hdiff : E (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      simpa [E, L, sub_eq_add_neg, Pi.sub_apply] using hdiff
    have hcoeff := Fintype.linearIndependent_iff.mp hli_sub
      (fun i : Fin k => (b.equivFunL x - b.equivFunL y) i) hsum
    have hi := hcoeff i
    exact sub_eq_zero.mp (by simpa [Pi.sub_apply] using hi)
  · intro x
    change (∑ i : Fin k, b.equivFunL x i • q (ι i)) ∈
      Submodule.span ℂ (Set.range q)
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (b.equivFunL x i)
        (Submodule.subset_span ⟨ι i, rfl⟩)
  · intro x y
    have hQiso :=
      complexMinkowskiTotallyIsotropic_span_range d s q hq_pair_zero
    have hEx_mem : E x ∈ Submodule.span ℂ (Set.range q) := by
      change (∑ i : Fin k, b.equivFunL x i • q (ι i)) ∈
        Submodule.span ℂ (Set.range q)
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (b.equivFunL x i)
          (Submodule.subset_span ⟨ι i, rfl⟩)
    have hEy_mem : E y ∈ Submodule.span ℂ (Set.range q) := by
      change (∑ i : Fin k, b.equivFunL y i • q (ι i)) ∈
        Submodule.span ℂ (Set.range q)
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (b.equivFunL y i)
          (Submodule.subset_span ⟨ι i, rfl⟩)
    rw [hQiso ⟨E x, hEx_mem⟩ ⟨E y, hEy_mem⟩, hR_iso x y]

/-- Given an independent totally isotropic frame orthogonal to `M`, a
totally isotropic residual subspace of no larger finrank produces the
injective residual embedding and the associated pairing-preserving direct-sum
equivalence. -/
theorem directSum_identity_sum_isotropicFrameEmbedding
    {d s : ℕ}
    {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0)
    (hq_independent : LinearIndependent ℂ q)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hq_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d (q c)
          (m : Fin (d + 1) → ℂ) = 0)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (hdim : Module.finrank ℂ R ≤ s) :
    ∃ (E : R →ₗ[ℂ] (Fin (d + 1) → ℂ))
      (hE_inj : Function.Injective E)
      (hE_orth :
        ∀ x : R, ∀ m : M,
          sourceComplexMinkowskiInner d (E x)
            (m : Fin (d + 1) → ℂ) = 0),
      (∀ x : R, E x ∈ Submodule.span ℂ (Set.range q)) ∧
      (∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ)
            (y : Fin (d + 1) → ℂ)) ∧
      let T := directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth
      ∀ x y : ↥(M ⊔ R),
        sourceComplexMinkowskiInner d
          ((T x : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ)
          ((T y : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) := by
  rcases complexMinkowski_totallyIsotropic_embedding_into_frame
      (d := d) (s := s) (R := R) (q := q)
      hq_independent hq_pair_zero hR_iso hdim with
    ⟨E, hE_inj, hE_mem, hE_preserves⟩
  have hE_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d (E x)
          (m : Fin (d + 1) → ℂ) = 0 := by
    intro x m
    exact span_frame_orthogonal_to_subspace
      (d := d) (s := s) (M := M) (q := q)
      hq_orth_M (hE_mem x) m
  refine ⟨E, hE_inj, hE_orth, hE_mem, hE_preserves, ?_⟩
  exact directSum_identity_sum_isotropicEmbedding_preserves
    (d := d) (M := M) (R := R) (E := E)
    hM hR_orth hE_inj hE_orth hE_preserves

/-- A finite family whose values lie in the span of a finite frame has
coefficient functions on that frame. -/
theorem coefficients_of_family_mem_span_finite_frame
    {d n s : ℕ}
    {q : Fin s → Fin (d + 1) → ℂ}
    {v : Fin n → Fin (d + 1) → ℂ}
    (hv : ∀ i, v i ∈ Submodule.span ℂ (Set.range q)) :
    ∃ a : Fin n → Fin s → ℂ,
      ∀ i, v i = ∑ c : Fin s, a i c • q c := by
  choose a ha using fun i =>
    exists_coefficients_of_mem_span_finite_frame (hv i)
  exact ⟨a, ha⟩

/-- A Kronecker dual frame reads off coefficients, hence the left frame is
linearly independent. -/
theorem complexMinkowski_dualPair_linearIndependent_left
    {d s : ℕ}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0) :
    LinearIndependent ℂ q := by
  rw [Fintype.linearIndependent_iff]
  intro a hsum c
  have hcoeff :=
    sourceComplexMinkowskiInner_sum_smul_dual_left
      (d := d) (m := s) (u := q) (e := qDual) hdual a c
  rw [hsum] at hcoeff
  simpa [sourceComplexMinkowskiInner] using hcoeff.symm

/-- A Kronecker dual frame also makes the dual frame linearly independent. -/
theorem complexMinkowski_dualPair_linearIndependent_right
    {d s : ℕ}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0) :
    LinearIndependent ℂ qDual := by
  have hdual' :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (q c') =
        if c = c' then (1 : ℂ) else 0 := by
    intro c c'
    rw [sourceComplexMinkowskiInner_comm d (qDual c) (q c'), hdual c' c]
    by_cases h : c = c'
    · subst c'
      simp
    · simp [h, eq_comm]
  rw [Fintype.linearIndependent_iff]
  intro a hsum c
  have hcoeff :=
    sourceComplexMinkowskiInner_sum_smul_dual_left
      (d := d) (m := s) (u := qDual) (e := q) hdual' a c
  rw [hsum] at hcoeff
  simpa [sourceComplexMinkowskiInner] using hcoeff.symm

/-- The residual frame span meets the selected block trivially once the dual
frame is orthogonal to the selected block. -/
theorem complexMinkowski_span_frame_disjoint_selected_of_dual_orthogonal
    {d s : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hqDual_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d (qDual c)
          (m : Fin (d + 1) → ℂ) = 0)
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0) :
    Disjoint (Submodule.span ℂ (Set.range q)) M := by
  rw [Submodule.disjoint_def]
  intro x hxQ hxM
  rcases exists_coefficients_of_mem_span_finite_frame
      (d := d) (s := s) (q := q) hxQ with
    ⟨a, ha⟩
  have hzero_a : ∀ c, a c = 0 := by
    intro c
    have hcoeff :=
      sourceComplexMinkowskiInner_sum_smul_dual_left
        (d := d) (m := s) (u := q) (e := qDual) hdual a c
    have hxpair : sourceComplexMinkowskiInner d x (qDual c) = 0 := by
      rw [sourceComplexMinkowskiInner_comm d x (qDual c)]
      exact hqDual_orth_M c ⟨x, hxM⟩
    have hcoeff_x : sourceComplexMinkowskiInner d x (qDual c) = a c := by
      rw [ha]
      exact hcoeff
    rw [hxpair] at hcoeff_x
    exact hcoeff_x.symm
  calc
    x = ∑ c : Fin s, a c • q c := ha
    _ = 0 := by simp [hzero_a]

/-- The dual residual frame span meets the selected block plus residual frame
span trivially.  This is the second direct-sum fact for the hyperbolic block
`M ⊔ span q ⊔ span qDual`. -/
theorem complexMinkowski_span_dualFrame_disjoint_selected_sup_frame
    {d s : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hq_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d (q c)
          (m : Fin (d + 1) → ℂ) = 0)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0) :
    Disjoint (Submodule.span ℂ (Set.range qDual))
      (M ⊔ Submodule.span ℂ (Set.range q)) := by
  have hdual' :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (q c') =
        if c = c' then (1 : ℂ) else 0 := by
    intro c c'
    rw [sourceComplexMinkowskiInner_comm d (qDual c) (q c'), hdual c' c]
    by_cases h : c = c'
    · subst c'
      simp
    · simp [h, eq_comm]
  rw [Submodule.disjoint_def]
  intro x hxQd hxSup
  rcases exists_coefficients_of_mem_span_finite_frame
      (d := d) (s := s) (q := qDual) hxQd with
    ⟨a, ha⟩
  rcases Submodule.mem_sup.mp hxSup with ⟨m, hm, qx, hqx, hxsum⟩
  rcases exists_coefficients_of_mem_span_finite_frame
      (d := d) (s := s) (q := q) hqx with
    ⟨b, hb⟩
  have hzero_a : ∀ c, a c = 0 := by
    intro c
    have hcoeff :=
      sourceComplexMinkowskiInner_sum_smul_dual_left
        (d := d) (m := s) (u := qDual) (e := q) hdual' a c
    have hx_pair : sourceComplexMinkowskiInner d x (q c) = 0 := by
      rw [hxsum.symm]
      rw [sourceComplexMinkowskiInner_add_left]
      have hm_pair : sourceComplexMinkowskiInner d m (q c) = 0 := by
        rw [sourceComplexMinkowskiInner_comm d m (q c)]
        exact hq_orth_M c ⟨m, hm⟩
      have hqx_pair : sourceComplexMinkowskiInner d qx (q c) = 0 := by
        rw [hb]
        rw [sourceComplexMinkowskiInner_sum_smul_left]
        simp [hq_pair_zero]
      rw [hm_pair, hqx_pair, add_zero]
    have hcoeff_x : sourceComplexMinkowskiInner d x (q c) = a c := by
      rw [ha]
      exact hcoeff
    rw [hx_pair] at hcoeff_x
    exact hcoeff_x.symm
  calc
    x = ∑ c : Fin s, a c • qDual c := ha
    _ = 0 := by simp [hzero_a]

/-- The two halves of a hyperbolic residual frame have disjoint spans. -/
theorem complexMinkowski_span_frame_disjoint_dualFrame
    {d s : ℕ}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0) :
    Disjoint (Submodule.span ℂ (Set.range q))
      (Submodule.span ℂ (Set.range qDual)) := by
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  have hQd_iso : ComplexMinkowskiTotallyIsotropicSubspace d Qd := by
    simpa [Qd] using
      complexMinkowskiTotallyIsotropic_span_range d s qDual hqDual_pair_zero
  have hqDual_orth_Qd :
      ∀ c (m : Qd),
        sourceComplexMinkowskiInner d (qDual c)
          (m : Fin (d + 1) → ℂ) = 0 := by
    intro c m
    exact hQd_iso ⟨qDual c, Submodule.subset_span ⟨c, rfl⟩⟩ m
  simpa [Qd] using
    complexMinkowski_span_frame_disjoint_selected_of_dual_orthogonal
      (d := d) (s := s) (M := Qd) (q := q) (qDual := qDual)
      hqDual_orth_Qd hdual

/-- Scaling a submodule by a nonzero scalar as a linear equivalence of that
submodule with itself. -/
noncomputable def submoduleScaleLinearEquiv
    {d : ℕ}
    (S : Submodule ℂ (Fin (d + 1) → ℂ))
    (α : ℂ) (hα : α ≠ 0) :
    S ≃ₗ[ℂ] S where
  toFun x := ⟨α • (x : Fin (d + 1) → ℂ), S.smul_mem α x.2⟩
  invFun x := ⟨α⁻¹ • (x : Fin (d + 1) → ℂ), S.smul_mem α⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    ext μ
    simp [Pi.smul_apply, hα]
  right_inv x := by
    apply Subtype.ext
    ext μ
    simp [Pi.smul_apply, hα]
  map_add' x y := by
    apply Subtype.ext
    ext μ
    simp [Pi.smul_apply, mul_add]
  map_smul' c x := by
    apply Subtype.ext
    ext μ
    simp [Pi.smul_apply, mul_left_comm]

/-- The submodule scaling equivalence acts by scalar multiplication after
forgetting the subtype. -/
theorem submoduleScaleLinearEquiv_apply
    {d : ℕ}
    (S : Submodule ℂ (Fin (d + 1) → ℂ))
    (α : ℂ) (hα : α ≠ 0) (x : S) :
    ((submoduleScaleLinearEquiv S α hα x : S) : Fin (d + 1) → ℂ) =
      α • (x : Fin (d + 1) → ℂ) :=
  rfl

/-- Determinant of the scalar multiplication equivalence on a finite
submodule. -/
theorem submoduleScaleLinearEquiv_det
    {d : ℕ}
    (S : Submodule ℂ (Fin (d + 1) → ℂ))
    (α : ℂ) (hα : α ≠ 0) :
    LinearMap.det (submoduleScaleLinearEquiv S α hα).toLinearMap =
      α ^ Module.finrank ℂ S := by
  have hlin :
      (submoduleScaleLinearEquiv S α hα).toLinearMap =
        α • (LinearMap.id : S →ₗ[ℂ] S) := by
    ext x μ
    simp [submoduleScaleLinearEquiv, Pi.smul_apply]
  rw [hlin, LinearMap.det_smul]
  simp

/-- The complex scalar used to contract a null frame is nonzero. -/
theorem complex_exp_neg_ne_zero (t : ℝ) :
    ((Real.exp (-t) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast Real.exp_ne_zero (-t)

/-- The complex scalar used to expand the dual null frame is nonzero. -/
theorem complex_exp_pos_ne_zero (t : ℝ) :
    ((Real.exp t : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast Real.exp_ne_zero t

/-- The two null-boost scale factors are reciprocal. -/
theorem complex_exp_neg_mul_exp (t : ℝ) :
    ((Real.exp (-t) : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul]
  norm_num [← Real.exp_add]

/-- The determinant contribution of equally many contracted and expanded
null directions is one. -/
theorem complex_exp_neg_pow_mul_exp_pow (t : ℝ) (s : ℕ) :
    (((Real.exp (-t) : ℝ) : ℂ) ^ s) *
      (((Real.exp t : ℝ) : ℂ) ^ s) = 1 := by
  rw [← mul_pow]
  rw [complex_exp_neg_mul_exp t]
  simp

/-- Scale two complementary summands inside their supremum. -/
noncomputable def directSum_scale_sup_equiv
    {d : ℕ}
    {A B : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hdisj : Disjoint A B)
    (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    ↥(A ⊔ B) ≃ₗ[ℂ] ↥(A ⊔ B) := by
  let S : Submodule ℂ (Fin (d + 1) → ℂ) := A ⊔ B
  let As : Submodule ℂ S := A.comap S.subtype
  let Bs : Submodule ℂ S := B.comap S.subtype
  have hcompl : IsCompl As Bs := by
    simpa [S, As, Bs] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := A) (R := B) hdisj
  let eA : As ≃ₗ[ℂ] A :=
    Submodule.comapSubtypeEquivOfLe (show A ≤ S from le_sup_left)
  let eB : Bs ≃ₗ[ℂ] B :=
    Submodule.comapSubtypeEquivOfLe (show B ≤ S from le_sup_right)
  let scaleA : As ≃ₗ[ℂ] As :=
    eA.trans ((submoduleScaleLinearEquiv A α hα).trans eA.symm)
  let scaleB : Bs ≃ₗ[ℂ] Bs :=
    eB.trans ((submoduleScaleLinearEquiv B β hβ).trans eB.symm)
  exact (Submodule.prodEquivOfIsCompl As Bs hcompl).symm.trans
    ((scaleA.prodCongr scaleB).trans
      (Submodule.prodEquivOfIsCompl As Bs hcompl))

/-- The two-summand scaling equivalence scales the left summand. -/
theorem directSum_scale_sup_equiv_maps_left
    {d : ℕ}
    {A B : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hdisj : Disjoint A B)
    (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (a : A) :
    ((directSum_scale_sup_equiv (d := d) (A := A) (B := B)
        hdisj α β hα hβ
      ⟨(a : Fin (d + 1) → ℂ), Submodule.mem_sup_left a.2⟩ :
        ↥(A ⊔ B)) : Fin (d + 1) → ℂ) =
      α • (a : Fin (d + 1) → ℂ) := by
  let S : Submodule ℂ (Fin (d + 1) → ℂ) := A ⊔ B
  let As : Submodule ℂ S := A.comap S.subtype
  let Bs : Submodule ℂ S := B.comap S.subtype
  have hcompl : IsCompl As Bs := by
    simpa [S, As, Bs] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := A) (R := B) hdisj
  let eA : As ≃ₗ[ℂ] A :=
    Submodule.comapSubtypeEquivOfLe (show A ≤ S from le_sup_left)
  let eB : Bs ≃ₗ[ℂ] B :=
    Submodule.comapSubtypeEquivOfLe (show B ≤ S from le_sup_right)
  let scaleA : As ≃ₗ[ℂ] As :=
    eA.trans ((submoduleScaleLinearEquiv A α hα).trans eA.symm)
  let scaleB : Bs ≃ₗ[ℂ] Bs :=
    eB.trans ((submoduleScaleLinearEquiv B β hβ).trans eB.symm)
  let T : S ≃ₗ[ℂ] S :=
    (Submodule.prodEquivOfIsCompl As Bs hcompl).symm.trans
      ((scaleA.prodCongr scaleB).trans
        (Submodule.prodEquivOfIsCompl As Bs hcompl))
  have hTdef :
      directSum_scale_sup_equiv (d := d) (A := A) (B := B)
        hdisj α β hα hβ = T := by
    rfl
  rw [hTdef]
  let y : S := ⟨(a : Fin (d + 1) → ℂ), Submodule.mem_sup_left a.2⟩
  let xa : As := ⟨y, a.2⟩
  have hsymm :
      (Submodule.prodEquivOfIsCompl As Bs hcompl).symm y = (xa, 0) := by
    simpa [y, xa] using
      Submodule.prodEquivOfIsCompl_symm_apply_left As Bs hcompl xa
  have hscaleA : ((scaleA xa : As) : Fin (d + 1) → ℂ) =
      α • (a : Fin (d + 1) → ℂ) := by
    rfl
  have hscaleB_zero : ((scaleB (0 : Bs) : Bs) :
      Fin (d + 1) → ℂ) = 0 := by
    have hz : scaleB (0 : Bs) = 0 := map_zero scaleB
    exact congrArg (fun z : Bs => (z : Fin (d + 1) → ℂ)) hz
  calc
    ((T y : S) : Fin (d + 1) → ℂ)
        = (((Submodule.prodEquivOfIsCompl As Bs hcompl)
            ((scaleA.prodCongr scaleB) (xa, 0)) : S) :
              Fin (d + 1) → ℂ) := by
            dsimp [T]
            rw [hsymm]
    _ = ((scaleA xa : As) : Fin (d + 1) → ℂ) +
          ((scaleB (0 : Bs) : Bs) : Fin (d + 1) → ℂ) := by
            rfl
    _ = α • (a : Fin (d + 1) → ℂ) := by
            rw [hscaleA, hscaleB_zero, add_zero]

/-- The two-summand scaling equivalence scales the right summand. -/
theorem directSum_scale_sup_equiv_maps_right
    {d : ℕ}
    {A B : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hdisj : Disjoint A B)
    (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (b : B) :
    ((directSum_scale_sup_equiv (d := d) (A := A) (B := B)
        hdisj α β hα hβ
      ⟨(b : Fin (d + 1) → ℂ), Submodule.mem_sup_right b.2⟩ :
        ↥(A ⊔ B)) : Fin (d + 1) → ℂ) =
      β • (b : Fin (d + 1) → ℂ) := by
  let S : Submodule ℂ (Fin (d + 1) → ℂ) := A ⊔ B
  let As : Submodule ℂ S := A.comap S.subtype
  let Bs : Submodule ℂ S := B.comap S.subtype
  have hcompl : IsCompl As Bs := by
    simpa [S, As, Bs] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := A) (R := B) hdisj
  let eA : As ≃ₗ[ℂ] A :=
    Submodule.comapSubtypeEquivOfLe (show A ≤ S from le_sup_left)
  let eB : Bs ≃ₗ[ℂ] B :=
    Submodule.comapSubtypeEquivOfLe (show B ≤ S from le_sup_right)
  let scaleA : As ≃ₗ[ℂ] As :=
    eA.trans ((submoduleScaleLinearEquiv A α hα).trans eA.symm)
  let scaleB : Bs ≃ₗ[ℂ] Bs :=
    eB.trans ((submoduleScaleLinearEquiv B β hβ).trans eB.symm)
  let T : S ≃ₗ[ℂ] S :=
    (Submodule.prodEquivOfIsCompl As Bs hcompl).symm.trans
      ((scaleA.prodCongr scaleB).trans
        (Submodule.prodEquivOfIsCompl As Bs hcompl))
  have hTdef :
      directSum_scale_sup_equiv (d := d) (A := A) (B := B)
        hdisj α β hα hβ = T := by
    rfl
  rw [hTdef]
  let y : S := ⟨(b : Fin (d + 1) → ℂ), Submodule.mem_sup_right b.2⟩
  let xb : Bs := ⟨y, b.2⟩
  have hsymm :
      (Submodule.prodEquivOfIsCompl As Bs hcompl).symm y = (0, xb) := by
    simpa [y, xb] using
      Submodule.prodEquivOfIsCompl_symm_apply_right As Bs hcompl xb
  have hscaleA_zero : ((scaleA (0 : As) : As) :
      Fin (d + 1) → ℂ) = 0 := by
    have hz : scaleA (0 : As) = 0 := map_zero scaleA
    exact congrArg (fun z : As => (z : Fin (d + 1) → ℂ)) hz
  have hscaleB : ((scaleB xb : Bs) : Fin (d + 1) → ℂ) =
      β • (b : Fin (d + 1) → ℂ) := by
    rfl
  calc
    ((T y : S) : Fin (d + 1) → ℂ)
        = (((Submodule.prodEquivOfIsCompl As Bs hcompl)
            ((scaleA.prodCongr scaleB) (0, xb)) : S) :
              Fin (d + 1) → ℂ) := by
            dsimp [T]
            rw [hsymm]
    _ = ((scaleA (0 : As) : As) : Fin (d + 1) → ℂ) +
          ((scaleB xb : Bs) : Fin (d + 1) → ℂ) := by
            rfl
    _ = β • (b : Fin (d + 1) → ℂ) := by
            rw [hscaleA_zero, hscaleB, zero_add]

/-- If a vector in `A ⊔ B` is written as `a + b`, the two-summand scaling
equivalence sends it to `α a + β b`. -/
theorem directSum_scale_sup_equiv_apply_of_eq_add
    {d : ℕ}
    {A B : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hdisj : Disjoint A B)
    (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    {x : ↥(A ⊔ B)} {a : A} {b : B}
    (hx : (a : Fin (d + 1) → ℂ) + (b : Fin (d + 1) → ℂ) =
      (x : Fin (d + 1) → ℂ)) :
    ((directSum_scale_sup_equiv (d := d) (A := A) (B := B)
        hdisj α β hα hβ x : ↥(A ⊔ B)) : Fin (d + 1) → ℂ) =
      α • (a : Fin (d + 1) → ℂ) + β • (b : Fin (d + 1) → ℂ) := by
  let T := directSum_scale_sup_equiv (d := d) (A := A) (B := B)
    hdisj α β hα hβ
  let xA : ↥(A ⊔ B) :=
    ⟨(a : Fin (d + 1) → ℂ), Submodule.mem_sup_left a.2⟩
  let xB : ↥(A ⊔ B) :=
    ⟨(b : Fin (d + 1) → ℂ), Submodule.mem_sup_right b.2⟩
  have hx_decomp : x = xA + xB := by
    apply Subtype.ext
    simpa [xA, xB] using hx.symm
  calc
    ((T x : ↥(A ⊔ B)) : Fin (d + 1) → ℂ)
        = ((T (xA + xB) : ↥(A ⊔ B)) : Fin (d + 1) → ℂ) := by
            rw [hx_decomp]
    _ = ((T xA : ↥(A ⊔ B)) : Fin (d + 1) → ℂ) +
          ((T xB : ↥(A ⊔ B)) : Fin (d + 1) → ℂ) := by
            exact congrArg (fun z : ↥(A ⊔ B) =>
              (z : Fin (d + 1) → ℂ)) (map_add T xA xB)
    _ = α • (a : Fin (d + 1) → ℂ) +
          β • (b : Fin (d + 1) → ℂ) := by
            rw [directSum_scale_sup_equiv_maps_left
                  (d := d) (A := A) (B := B)
                  hdisj α β hα hβ a,
                directSum_scale_sup_equiv_maps_right
                  (d := d) (A := A) (B := B)
                  hdisj α β hα hβ b]

/-- The span of a totally isotropic frame and an isotropic Kronecker-dual
frame is a nondegenerate hyperbolic block. -/
theorem complexMinkowski_hyperbolicFrameSpan_nondegenerate
    {d s : ℕ}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0) :
    ComplexMinkowskiNondegenerateSubspace d
      (Submodule.span ℂ (Set.range q) ⊔
        Submodule.span ℂ (Set.range qDual)) := by
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) := Submodule.span ℂ (Set.range q)
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  have hdual' :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (q c') =
        if c = c' then (1 : ℂ) else 0 := by
    intro c c'
    rw [sourceComplexMinkowskiInner_comm d (qDual c) (q c'), hdual c' c]
    by_cases h : c = c'
    · subst c'
      simp
    · simp [h, eq_comm]
  intro x horth
  rcases Submodule.mem_sup.mp x.2 with ⟨qx, hqx, qdx, hqdx, hxsum⟩
  rcases exists_coefficients_of_mem_span_finite_frame
      (d := d) (s := s) (q := q) (by simpa [Q] using hqx) with
    ⟨a, ha⟩
  rcases exists_coefficients_of_mem_span_finite_frame
      (d := d) (s := s) (q := qDual) (by simpa [Qd] using hqdx) with
    ⟨b, hb⟩
  have hzero_a : ∀ c, a c = 0 := by
    intro c
    have hx_pair : sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (qDual c) = 0 := by
      exact horth ⟨qDual c, by
        change qDual c ∈ Q ⊔ Qd
        exact Submodule.mem_sup_right (by
          exact Submodule.subset_span ⟨c, rfl⟩)⟩
    have hcalc : sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (qDual c) = a c := by
      rw [show (x : Fin (d + 1) → ℂ) = qx + qdx from hxsum.symm]
      rw [sourceComplexMinkowskiInner_add_left]
      have hqx_pair : sourceComplexMinkowskiInner d qx (qDual c) = a c := by
        rw [ha]
        exact sourceComplexMinkowskiInner_sum_smul_dual_left
          (d := d) (m := s) (u := q) (e := qDual) hdual a c
      have hqdx_pair : sourceComplexMinkowskiInner d qdx (qDual c) = 0 := by
        rw [hb]
        rw [sourceComplexMinkowskiInner_sum_smul_left]
        simp [hqDual_pair_zero]
      rw [hqx_pair, hqdx_pair, add_zero]
    rw [hx_pair] at hcalc
    exact hcalc.symm
  have hzero_b : ∀ c, b c = 0 := by
    intro c
    have hx_pair : sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (q c) = 0 := by
      exact horth ⟨q c, by
        change q c ∈ Q ⊔ Qd
        exact Submodule.mem_sup_left (by
          exact Submodule.subset_span ⟨c, rfl⟩)⟩
    have hcalc : sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (q c) = b c := by
      rw [show (x : Fin (d + 1) → ℂ) = qx + qdx from hxsum.symm]
      rw [sourceComplexMinkowskiInner_add_left]
      have hqx_pair : sourceComplexMinkowskiInner d qx (q c) = 0 := by
        rw [ha]
        rw [sourceComplexMinkowskiInner_sum_smul_left]
        simp [hq_pair_zero]
      have hqdx_pair : sourceComplexMinkowskiInner d qdx (q c) = b c := by
        rw [hb]
        exact sourceComplexMinkowskiInner_sum_smul_dual_left
          (d := d) (m := s) (u := qDual) (e := q) hdual' b c
      rw [hqx_pair, hqdx_pair, zero_add]
    rw [hx_pair] at hcalc
    exact hcalc.symm
  apply Subtype.ext
  calc
    (x : Fin (d + 1) → ℂ) = qx + qdx := hxsum.symm
    _ = (∑ c : Fin s, a c • q c) + qdx := by rw [ha]
    _ = (∑ c : Fin s, a c • q c) +
          (∑ c : Fin s, b c • qDual c) := by rw [hb]
    _ = 0 := by simp [hzero_a, hzero_b]

/-- Adding the hyperbolic residual block orthogonally to a nondegenerate
selected block remains nondegenerate. -/
theorem complexMinkowski_selected_sup_hyperbolicFrameSpan_nondegenerate
    {d s : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hq_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d (q c)
          (m : Fin (d + 1) → ℂ) = 0)
    (hqDual_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d (qDual c)
          (m : Fin (d + 1) → ℂ) = 0)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0) :
    ComplexMinkowskiNondegenerateSubspace d
      (M ⊔ (Submodule.span ℂ (Set.range q) ⊔
        Submodule.span ℂ (Set.range qDual))) := by
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) := Submodule.span ℂ (Set.range q)
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  let H : Submodule ℂ (Fin (d + 1) → ℂ) := Q ⊔ Qd
  have hH : ComplexMinkowskiNondegenerateSubspace d H := by
    simpa [H, Q, Qd] using
      complexMinkowski_hyperbolicFrameSpan_nondegenerate
        (d := d) (s := s) (q := q) (qDual := qDual)
        hq_pair_zero hqDual_pair_zero hdual
  have hH_orth_M :
      ∀ x : H, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ) (m : Fin (d + 1) → ℂ) = 0 := by
    intro x m
    rcases Submodule.mem_sup.mp x.2 with ⟨qx, hqx, qdx, hqdx, hxsum⟩
    have hqx_pair : sourceComplexMinkowskiInner d qx
        (m : Fin (d + 1) → ℂ) = 0 := by
      exact span_frame_orthogonal_to_subspace
        (d := d) (s := s) (M := M) (q := q)
        hq_orth_M (by simpa [Q] using hqx) m
    have hqdx_pair : sourceComplexMinkowskiInner d qdx
        (m : Fin (d + 1) → ℂ) = 0 := by
      exact span_frame_orthogonal_to_subspace
        (d := d) (s := s) (M := M) (q := qDual)
        hqDual_orth_M (by simpa [Qd] using hqdx) m
    rw [show (x : Fin (d + 1) → ℂ) = qx + qdx from hxsum.symm]
    rw [sourceComplexMinkowskiInner_add_left, hqx_pair, hqdx_pair, add_zero]
  intro x horth
  rcases Submodule.mem_sup.mp x.2 with ⟨m0, hm0, h0, hh0, hxsum⟩
  let m : M := ⟨m0, hm0⟩
  let h : H := ⟨h0, by simpa [H] using hh0⟩
  have hm_zero : m = 0 := by
    apply hM m
    intro y
    have hx_pair : sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) = 0 := by
      exact horth ⟨(y : Fin (d + 1) → ℂ), by
        exact Submodule.mem_sup_left y.2⟩
    have hcalc : sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (m : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) := by
      rw [show (x : Fin (d + 1) → ℂ) = m0 + h0 from hxsum.symm]
      rw [sourceComplexMinkowskiInner_add_left]
      have hh_pair : sourceComplexMinkowskiInner d h0
          (y : Fin (d + 1) → ℂ) = 0 := by
        exact hH_orth_M h y
      rw [hh_pair, add_zero]
    rw [hx_pair] at hcalc
    exact hcalc.symm
  have hh_zero : h = 0 := by
    apply hH h
    intro y
    have hx_pair : sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) = 0 := by
      exact horth ⟨(y : Fin (d + 1) → ℂ), by
        exact Submodule.mem_sup_right y.2⟩
    have hcalc : sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (h : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) := by
      rw [show (x : Fin (d + 1) → ℂ) = m0 + h0 from hxsum.symm]
      rw [sourceComplexMinkowskiInner_add_left]
      have hm_pair : sourceComplexMinkowskiInner d m0
          (y : Fin (d + 1) → ℂ) = 0 := by
        rw [sourceComplexMinkowskiInner_comm d m0 (y : Fin (d + 1) → ℂ)]
        exact hH_orth_M y m
      rw [hm_pair, zero_add]
    rw [hx_pair] at hcalc
    exact hcalc.symm
  apply Subtype.ext
  have hm0_zero : m0 = 0 := congrArg Subtype.val hm_zero
  have hh0_zero : h0 = 0 := congrArg Subtype.val hh_zero
  calc
    (x : Fin (d + 1) → ℂ) = m0 + h0 := hxsum.symm
    _ = 0 := by rw [hm0_zero, hh0_zero, zero_add]

/-- The hyperbolic-block contraction that scales `q` by `exp (-t)` and
`qDual` by `exp t`. -/
noncomputable def complexMinkowski_hyperbolicFrameSpanContraction
    {d s : ℕ}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (t : ℝ) :
    ↥(Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual)) ≃ₗ[ℂ]
    ↥(Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual)) := by
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) := Submodule.span ℂ (Set.range q)
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  have hdisj : Disjoint Q Qd := by
    simpa [Q, Qd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := q) (qDual := qDual)
        hqDual_pair_zero hdual
  exact directSum_scale_sup_equiv (d := d) (A := Q) (B := Qd)
    hdisj ((Real.exp (-t) : ℝ) : ℂ) ((Real.exp t : ℝ) : ℂ)
    (complex_exp_neg_ne_zero t) (complex_exp_pos_ne_zero t)

/-- The hyperbolic-block contraction scales the residual frame by
`exp (-t)`. -/
theorem complexMinkowski_hyperbolicFrameSpanContraction_maps_q
    {d s : ℕ}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (t : ℝ) (c : Fin s) :
    ((complexMinkowski_hyperbolicFrameSpanContraction
        (d := d) (s := s) (q := q) (qDual := qDual)
        hqDual_pair_zero hdual t
      ⟨q c, Submodule.mem_sup_left (Submodule.subset_span ⟨c, rfl⟩)⟩ :
        ↥(Submodule.span ℂ (Set.range q) ⊔
          Submodule.span ℂ (Set.range qDual))) : Fin (d + 1) → ℂ) =
      ((Real.exp (-t) : ℝ) : ℂ) • q c := by
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) := Submodule.span ℂ (Set.range q)
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  have hdisj : Disjoint Q Qd := by
    simpa [Q, Qd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := q) (qDual := qDual)
        hqDual_pair_zero hdual
  simpa [complexMinkowski_hyperbolicFrameSpanContraction, Q, Qd] using
    directSum_scale_sup_equiv_maps_left
      (d := d) (A := Q) (B := Qd) hdisj
      ((Real.exp (-t) : ℝ) : ℂ) ((Real.exp t : ℝ) : ℂ)
      (complex_exp_neg_ne_zero t) (complex_exp_pos_ne_zero t)
      (⟨q c, Submodule.subset_span ⟨c, rfl⟩⟩ : Q)

/-- The hyperbolic-block contraction scales the dual residual frame by
`exp t`. -/
theorem complexMinkowski_hyperbolicFrameSpanContraction_maps_qDual
    {d s : ℕ}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (t : ℝ) (c : Fin s) :
    ((complexMinkowski_hyperbolicFrameSpanContraction
        (d := d) (s := s) (q := q) (qDual := qDual)
        hqDual_pair_zero hdual t
      ⟨qDual c, Submodule.mem_sup_right (Submodule.subset_span ⟨c, rfl⟩)⟩ :
        ↥(Submodule.span ℂ (Set.range q) ⊔
          Submodule.span ℂ (Set.range qDual))) : Fin (d + 1) → ℂ) =
      ((Real.exp t : ℝ) : ℂ) • qDual c := by
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) := Submodule.span ℂ (Set.range q)
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  have hdisj : Disjoint Q Qd := by
    simpa [Q, Qd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := q) (qDual := qDual)
        hqDual_pair_zero hdual
  simpa [complexMinkowski_hyperbolicFrameSpanContraction, Q, Qd] using
    directSum_scale_sup_equiv_maps_right
      (d := d) (A := Q) (B := Qd) hdisj
      ((Real.exp (-t) : ℝ) : ℂ) ((Real.exp t : ℝ) : ℂ)
      (complex_exp_neg_ne_zero t) (complex_exp_pos_ne_zero t)
      (⟨qDual c, Submodule.subset_span ⟨c, rfl⟩⟩ : Qd)

/-- The hyperbolic-block contraction preserves the complex Minkowski pairing
on `span q ⊔ span qDual`. -/
theorem complexMinkowski_hyperbolicFrameSpanContraction_preserves
    {d s : ℕ}
    {q qDual : Fin s → Fin (d + 1) → ℂ}
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hdual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (t : ℝ) :
    let T := complexMinkowski_hyperbolicFrameSpanContraction
      (d := d) (s := s) (q := q) (qDual := qDual)
      hqDual_pair_zero hdual t
    ∀ x y : ↥(Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual)),
      sourceComplexMinkowskiInner d
        ((T x : ↥(Submodule.span ℂ (Set.range q) ⊔
          Submodule.span ℂ (Set.range qDual))) : Fin (d + 1) → ℂ)
        ((T y : ↥(Submodule.span ℂ (Set.range q) ⊔
          Submodule.span ℂ (Set.range qDual))) : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) := by
  intro T x y
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) := Submodule.span ℂ (Set.range q)
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  have hdisj : Disjoint Q Qd := by
    simpa [Q, Qd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := q) (qDual := qDual)
        hqDual_pair_zero hdual
  have hQiso : ComplexMinkowskiTotallyIsotropicSubspace d Q := by
    simpa [Q] using
      complexMinkowskiTotallyIsotropic_span_range d s q hq_pair_zero
  have hQdiso : ComplexMinkowskiTotallyIsotropicSubspace d Qd := by
    simpa [Qd] using
      complexMinkowskiTotallyIsotropic_span_range d s qDual hqDual_pair_zero
  rcases Submodule.mem_sup.mp x.2 with ⟨qx0, hqx0, qdx0, hqdx0, hxsum⟩
  rcases Submodule.mem_sup.mp y.2 with ⟨qy0, hqy0, qdy0, hqdy0, hysum⟩
  let qx : Q := ⟨qx0, by simpa [Q] using hqx0⟩
  let qdx : Qd := ⟨qdx0, by simpa [Qd] using hqdx0⟩
  let qy : Q := ⟨qy0, by simpa [Q] using hqy0⟩
  let qdy : Qd := ⟨qdy0, by simpa [Qd] using hqdy0⟩
  let α : ℂ := ((Real.exp (-t) : ℝ) : ℂ)
  let β : ℂ := ((Real.exp t : ℝ) : ℂ)
  have hTx : ((T x : ↥(Submodule.span ℂ (Set.range q) ⊔
        Submodule.span ℂ (Set.range qDual))) : Fin (d + 1) → ℂ) =
      α • qx0 + β • qdx0 := by
    simpa [T, complexMinkowski_hyperbolicFrameSpanContraction,
      Q, Qd, α, β, qx, qdx] using
      directSum_scale_sup_equiv_apply_of_eq_add
        (d := d) (A := Q) (B := Qd) hdisj α β
        (complex_exp_neg_ne_zero t) (complex_exp_pos_ne_zero t)
        (x := (x : ↥(Submodule.span ℂ (Set.range q) ⊔
          Submodule.span ℂ (Set.range qDual)))) (a := qx) (b := qdx)
        (by simpa [qx, qdx] using hxsum)
  have hTy : ((T y : ↥(Submodule.span ℂ (Set.range q) ⊔
        Submodule.span ℂ (Set.range qDual))) : Fin (d + 1) → ℂ) =
      α • qy0 + β • qdy0 := by
    simpa [T, complexMinkowski_hyperbolicFrameSpanContraction,
      Q, Qd, α, β, qy, qdy] using
      directSum_scale_sup_equiv_apply_of_eq_add
        (d := d) (A := Q) (B := Qd) hdisj α β
        (complex_exp_neg_ne_zero t) (complex_exp_pos_ne_zero t)
        (x := (y : ↥(Submodule.span ℂ (Set.range q) ⊔
          Submodule.span ℂ (Set.range qDual)))) (a := qy) (b := qdy)
        (by simpa [qy, qdy] using hysum)
  have hqx_qy : sourceComplexMinkowskiInner d qx0 qy0 = 0 := hQiso qx qy
  have hqdx_qdy : sourceComplexMinkowskiInner d qdx0 qdy0 = 0 :=
    hQdiso qdx qdy
  have hαβ : α * β = 1 := by simpa [α, β] using complex_exp_neg_mul_exp t
  have hβα : β * α = 1 := by rw [mul_comm, hαβ]
  rw [hTx, hTy,
    show (x : Fin (d + 1) → ℂ) = qx0 + qdx0 from hxsum.symm,
    show (y : Fin (d + 1) → ℂ) = qy0 + qdy0 from hysum.symm]
  simp [sourceComplexMinkowskiInner_add_left,
    sourceComplexMinkowskiInner_add_right,
    sourceComplexMinkowskiInner_smul_left,
    sourceComplexMinkowskiInner_smul_right,
    hqx_qy, hqdx_qdy, hβα, mul_assoc, mul_left_comm, mul_comm]

/-- A raw frame dual to a totally isotropic frame can be corrected, inside the
same subspace, to an isotropic dual frame.  The correction is the standard
Gram-matrix half-subtraction
`y c - (1 / 2) • ∑ k, ⟪y c, y k⟫ • q k`; the `q`-dual pairings are unchanged
because the `q`-frame is totally isotropic, and the self-pairings cancel by
symmetry of the complex Minkowski form. -/
theorem complexMinkowski_isotropicDualFrame_of_rawDualFrame
    {d s : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q y : Fin s → Fin (d + 1) → ℂ}
    (hq_mem : ∀ c, q c ∈ N)
    (hy_mem : ∀ c, y c ∈ N)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hy_dual :
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (y c') =
          if c = c' then (1 : ℂ) else 0) :
    ∃ qDual : Fin s → Fin (d + 1) → ℂ,
      (∀ c, qDual c ∈ N) ∧
      (∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0) ∧
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (qDual c') =
          if c = c' then (1 : ℂ) else 0 := by
  let corr : Fin s → Fin (d + 1) → ℂ :=
    fun c => (2 : ℂ)⁻¹ •
      (∑ k : Fin s, sourceComplexMinkowskiInner d (y c) (y k) • q k)
  let qDual : Fin s → Fin (d + 1) → ℂ := fun c => y c - corr c
  refine ⟨qDual, ?_, ?_, ?_⟩
  · intro c
    apply Submodule.sub_mem
    · exact hy_mem c
    · apply Submodule.smul_mem
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (hq_mem k)
  · intro i j
    have h_y_corr :
        sourceComplexMinkowskiInner d (y i) (corr j) =
          (2 : ℂ)⁻¹ * sourceComplexMinkowskiInner d (y i) (y j) := by
      change sourceComplexMinkowskiInner d (y i)
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y j) (y k) • q k)) = _
      rw [sourceComplexMinkowskiInner_smul_right,
        sourceComplexMinkowskiInner_sum_smul_right]
      have hsum :
          (∑ k : Fin s,
              sourceComplexMinkowskiInner d (y j) (y k) *
                sourceComplexMinkowskiInner d (y i) (q k)) =
            sourceComplexMinkowskiInner d (y j) (y i) := by
        calc
          (∑ k : Fin s,
              sourceComplexMinkowskiInner d (y j) (y k) *
                sourceComplexMinkowskiInner d (y i) (q k)) =
            ∑ k : Fin s,
              sourceComplexMinkowskiInner d (y j) (y k) *
                (if k = i then (1 : ℂ) else 0) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [sourceComplexMinkowskiInner_comm d (y i) (q k),
                  hy_dual]
          _ = sourceComplexMinkowskiInner d (y j) (y i) := by
                simp
      rw [hsum]
      rw [sourceComplexMinkowskiInner_comm d (y j) (y i)]
    have h_corr_y :
        sourceComplexMinkowskiInner d (corr i) (y j) =
          (2 : ℂ)⁻¹ * sourceComplexMinkowskiInner d (y i) (y j) := by
      change sourceComplexMinkowskiInner d
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y i) (y k) • q k))
          (y j) = _
      rw [sourceComplexMinkowskiInner_smul_left,
        sourceComplexMinkowskiInner_sum_smul_left]
      have hsum :
          (∑ k : Fin s,
              sourceComplexMinkowskiInner d (y i) (y k) *
                sourceComplexMinkowskiInner d (q k) (y j)) =
            sourceComplexMinkowskiInner d (y i) (y j) := by
        calc
          (∑ k : Fin s,
              sourceComplexMinkowskiInner d (y i) (y k) *
                sourceComplexMinkowskiInner d (q k) (y j)) =
            ∑ k : Fin s,
              sourceComplexMinkowskiInner d (y i) (y k) *
                (if k = j then (1 : ℂ) else 0) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [hy_dual]
          _ = sourceComplexMinkowskiInner d (y i) (y j) := by
                simp
      rw [hsum]
    have h_corr_corr :
        sourceComplexMinkowskiInner d (corr i) (corr j) = 0 := by
      change sourceComplexMinkowskiInner d
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y i) (y k) • q k))
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y j) (y k) • q k)) = 0
      rw [sourceComplexMinkowskiInner_smul_left,
        sourceComplexMinkowskiInner_smul_right,
        sourceComplexMinkowskiInner_sum_smul_left]
      simp [sourceComplexMinkowskiInner_sum_smul_right, hq_pair_zero]
    change sourceComplexMinkowskiInner d (y i - corr i) (y j - corr j) = 0
    rw [sourceComplexMinkowskiInner_sub_left,
      sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_sub_right]
    rw [h_y_corr, h_corr_y, h_corr_corr]
    ring
  · intro i j
    have hq_corr : sourceComplexMinkowskiInner d (q i) (corr j) = 0 := by
      change sourceComplexMinkowskiInner d (q i)
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y j) (y k) • q k)) = 0
      rw [sourceComplexMinkowskiInner_smul_right,
        sourceComplexMinkowskiInner_sum_smul_right]
      simp [hq_pair_zero]
    change sourceComplexMinkowskiInner d (q i) (y j - corr j) = _
    rw [sourceComplexMinkowskiInner_sub_right, hq_corr, sub_zero, hy_dual]

/-- In a nondegenerate subspace, an independent finite frame has raw dual
vectors for the restricted complex Minkowski pairing.  These raw duals are not
yet isotropic; `complexMinkowski_isotropicDualFrame_of_rawDualFrame` performs
the subsequent isotropization when the original frame is totally isotropic. -/
theorem complexMinkowski_rawDualFrameIn
    {d s : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (hN : ComplexMinkowskiNondegenerateSubspace d N)
    (hq_mem : ∀ c, q c ∈ N)
    (hq_independent : LinearIndependent ℂ q) :
    ∃ y : Fin s → Fin (d + 1) → ℂ,
      (∀ c, y c ∈ N) ∧
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (y c') =
          if c = c' then (1 : ℂ) else 0 := by
  let qN : Fin s → N := fun c => ⟨q c, hq_mem c⟩
  have hqN_independent : LinearIndependent ℂ qN := by
    rw [Fintype.linearIndependent_iff]
    intro a hsum i
    have hsum_val : (∑ j : Fin s, a j • q j) = 0 := by
      have h := congrArg (fun x : N => (x : Fin (d + 1) → ℂ)) hsum
      simpa [qN] using h
    exact (Fintype.linearIndependent_iff.mp hq_independent a hsum_val) i
  let Q : Submodule ℂ N := Submodule.span ℂ (Set.range qN)
  let bQ : Module.Basis (Fin s) ℂ Q := Module.Basis.span hqN_independent
  let B := (sourceComplexMinkowskiBilinForm d).restrict N
  have hBnd : B.Nondegenerate := by
    simpa [B] using complexMinkowskiNondegenerateSubspace_to_restrict d N hN
  let phi : Fin s → Module.Dual ℂ N := fun c =>
    Subspace.dualLift Q (bQ.coord c)
  let yN : Fin s → N := fun c => (B.toDual hBnd).symm (phi c)
  let y : Fin s → Fin (d + 1) → ℂ := fun c => yN c
  refine ⟨y, ?_, ?_⟩
  · intro c
    exact (yN c).2
  · intro i j
    have hraw : B (yN j) (qN i) = if i = j then (1 : ℂ) else 0 := by
      calc
        B (yN j) (qN i) = phi j (qN i) := by
          simp [yN]
        _ = bQ.coord j ⟨qN i, Submodule.subset_span ⟨i, rfl⟩⟩ := by
          change (Subspace.dualLift Q (bQ.coord j)) (qN i) =
            bQ.coord j ⟨qN i, Submodule.subset_span ⟨i, rfl⟩⟩
          exact Subspace.dualLift_of_mem (W := Q) (φ := bQ.coord j)
            (show qN i ∈ Q from Submodule.subset_span ⟨i, rfl⟩)
        _ = if i = j then (1 : ℂ) else 0 := by
          by_cases hij : i = j <;> simp [bQ, Q, hij]
    have hraw' :
        sourceComplexMinkowskiInner d (y j) (q i) =
          if i = j then (1 : ℂ) else 0 := by
      change B (yN j) (qN i) = if i = j then (1 : ℂ) else 0
      exact hraw
    rw [sourceComplexMinkowskiInner_comm d (q i) (y j)]
    exact hraw'

/-- An independent totally isotropic frame in a nondegenerate subspace admits an
isotropic dual frame inside the same subspace.  This is the finite-dimensional
dual-frame packet used by the low-rank null-boost construction. -/
theorem complexMinkowski_isotropicFrame_dualFrameIn
    {d s : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hN : ComplexMinkowskiNondegenerateSubspace d N)
    {q : Fin s → Fin (d + 1) → ℂ}
    (hq_mem : ∀ c, q c ∈ N)
    (hq_independent : LinearIndependent ℂ q)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0) :
    ∃ qDual : Fin s → Fin (d + 1) → ℂ,
      (∀ c, qDual c ∈ N) ∧
      (∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0) ∧
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (qDual c') =
          if c = c' then (1 : ℂ) else 0 := by
  rcases complexMinkowski_rawDualFrameIn
      (d := d) (s := s) (N := N) (q := q)
      hN hq_mem hq_independent with
    ⟨y, hy_mem, hy_dual⟩
  exact complexMinkowski_isotropicDualFrame_of_rawDualFrame
    (d := d) (s := s) (N := N) (q := q) (y := y)
    hq_mem hy_mem hq_pair_zero hy_dual

/-- A residual isotropic frame orthogonal to a nondegenerate selected span has
an isotropic dual frame in the same orthogonal complement.  The returned
orthogonality-to-`ξ` field is just orthogonality to `M`, since the base vectors
lie in `M`. -/
theorem complexMinkowski_isotropicDualFrame_of_residualFrame
    {d n s : ℕ}
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {q : Fin s → Fin (d + 1) → ℂ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hM_nondeg : ComplexMinkowskiNondegenerateSubspace d M)
    (hξ_mem : ∀ i, ξ i ∈ M)
    (hq_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d
          (q c) (m : Fin (d + 1) → ℂ) = 0)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hq_independent : LinearIndependent ℂ q) :
    ∃ qDual : Fin s → Fin (d + 1) → ℂ,
      (∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0) ∧
      (∀ c c',
        sourceComplexMinkowskiInner d (q c) (qDual c') =
          if c = c' then (1 : ℂ) else 0) ∧
      (∀ c (m : M),
        sourceComplexMinkowskiInner d
          (qDual c) (m : Fin (d + 1) → ℂ) = 0) ∧
      ∀ c i, sourceComplexMinkowskiInner d (qDual c) (ξ i) = 0 := by
  let N := complexMinkowskiOrthogonalSubmodule d M
  have hN : ComplexMinkowskiNondegenerateSubspace d N :=
    complexMinkowskiOrthogonalSubmodule_nondegenerate d hM_nondeg
  have hq_mem : ∀ c, q c ∈ N := by
    intro c
    change q c ∈ complexMinkowskiOrthogonalSubmodule d M
    rw [mem_complexMinkowskiOrthogonalSubmodule_iff]
    intro m
    exact hq_orth_M c m
  rcases complexMinkowski_isotropicFrame_dualFrameIn
      (d := d) (s := s) (N := N)
      hN hq_mem hq_independent hq_pair_zero with
    ⟨qDual, hqDual_mem, hqDual_pair_zero, hq_dual⟩
  have hqDual_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d
          (qDual c) (m : Fin (d + 1) → ℂ) = 0 := by
    intro c m
    exact
      (mem_complexMinkowskiOrthogonalSubmodule_iff d M (qDual c)).1
        (by simpa [N] using hqDual_mem c) m
  refine ⟨qDual, hqDual_pair_zero, hq_dual, hqDual_orth_M, ?_⟩
  intro c i
  exact hqDual_orth_M c ⟨ξ i, hξ_mem i⟩

/-- A finite residual expansion with all coefficients scaled by `exp (-t)`
converges to the base configuration.  This is the convergence calculation used
by the low-rank singular normal-form producer; it depends only on finite
products and `exp (-t) → 0`, not on any continuity of the chosen Lorentz
transform family. -/
theorem tendsto_isotropicResidual_exp_neg_base
    {d n s : ℕ}
    (ξ : Fin n → Fin (d + 1) → ℂ)
    (a : Fin n → Fin s → ℂ)
    (q : Fin s → Fin (d + 1) → ℂ) :
    Tendsto
      (fun t : ℝ =>
        fun i μ =>
          ξ i μ + ∑ c : Fin s, (Real.exp (-t) : ℂ) * a i c * q c μ)
      atTop (nhds ξ) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro μ
  have hsum :
      Tendsto
        (fun t : ℝ =>
          ∑ c : Fin s, (Real.exp (-t) : ℂ) * a i c * q c μ)
        atTop (nhds (0 : ℂ)) := by
    simpa using
      tendsto_finset_sum (s := Finset.univ)
        (fun c _ =>
          (tendsto_complex_exp_neg_atTop_nhds_zero.mul
            (tendsto_const_nhds (x := a i c))).mul
            (tendsto_const_nhds (x := q c μ)))
  have hconst : Tendsto (fun _ : ℝ => ξ i μ) atTop (nhds (ξ i μ)) :=
    tendsto_const_nhds
  simpa using hconst.add hsum

end BHW
