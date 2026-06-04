import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceFullComplexLorentzFrame

/-!
# Full-complex Witt extension support

This file contains the finite-dimensional bilinear algebra needed to extend
the high-rank Hall-Wightman source-span isometry to a determinant-unrestricted
complex Lorentz transformation.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Restricting a symmetric bilinear form to a submodule is symmetric. -/
theorem restrict_isSymm_of_isSymm
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    {B : LinearMap.BilinForm ℂ U}
    (hB : B.IsSymm)
    (W : Submodule ℂ U) :
    (B.restrict W).IsSymm :=
  hB.restrict W

/-- The complex Minkowski bilinear form is reflexive. -/
theorem sourceComplexMinkowskiBilinForm_isRefl
    (d : ℕ) :
    (sourceComplexMinkowskiBilinForm d).IsRefl :=
  (sourceComplexMinkowskiBilinForm_isSymm d).isRefl

/-- The ambient complex Minkowski bilinear form is nondegenerate. -/
theorem sourceComplexMinkowskiBilinForm_nondegenerate
    (d : ℕ) :
    (sourceComplexMinkowskiBilinForm d).Nondegenerate := by
  constructor
  · intro x hx
    exact sourceComplexMinkowskiInner_left_nonDegenerate d (w := x) (by
      intro y
      simpa [sourceComplexMinkowskiBilinForm] using hx y)
  · intro y hy
    exact sourceComplexMinkowskiInner_left_nonDegenerate d (w := y) (by
      intro x
      have h := hy x
      simpa [sourceComplexMinkowskiBilinForm,
        sourceComplexMinkowskiInner_comm d y x] using h)

/-- A nondegenerate source subspace gives a nondegenerate restricted
bilinear form. -/
theorem complexMinkowskiNondegenerateSubspace_to_restrict
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ))
    (hM : ComplexMinkowskiNondegenerateSubspace d M) :
    ((sourceComplexMinkowskiBilinForm d).restrict M).Nondegenerate := by
  constructor
  · intro x hx
    apply hM x
    intro y
    simpa [sourceComplexMinkowskiBilinForm,
      LinearMap.BilinForm.restrict] using hx y
  · intro y hy
    apply hM y
    intro x
    have h := hy x
    simpa [sourceComplexMinkowskiBilinForm,
      LinearMap.BilinForm.restrict,
      sourceComplexMinkowskiInner_comm d
        (y : Fin (d + 1) → ℂ) (x : Fin (d + 1) → ℂ)] using h

/-- Mathlib's right orthogonal complement of the source Minkowski bilinear form
agrees with the left-orthogonal complement used by the Hall-Wightman source
route, because the form is symmetric. -/
theorem sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) :
    (sourceComplexMinkowskiBilinForm d).orthogonal M =
      complexMinkowskiOrthogonalSubmodule d M := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff,
    mem_complexMinkowskiOrthogonalSubmodule_iff]
  constructor
  · intro hv x
    have h := hv (x : Fin (d + 1) → ℂ) x.property
    simpa [LinearMap.BilinForm.IsOrtho,
      sourceComplexMinkowskiBilinForm,
      sourceComplexMinkowskiInner_comm d
        (x : Fin (d + 1) → ℂ) v] using h
  · intro hv x hx
    have h := hv ⟨x, hx⟩
    simpa [LinearMap.BilinForm.IsOrtho,
      sourceComplexMinkowskiBilinForm,
      sourceComplexMinkowskiInner_comm d v x] using h

/-- Every nondegenerate symmetric complex bilinear form has a unit orthogonal
basis. -/
theorem exists_complex_unit_orthogonal_basis
    {U : Type*}
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (B : LinearMap.BilinForm ℂ U)
    (hB_symm : B.IsSymm)
    (hB_nd : B.Nondegenerate) :
    ∃ b : Module.Basis (Fin (Module.finrank ℂ U)) ℂ U,
      B.iIsOrtho b ∧ ∀ i, B (b i) (b i) = 1 := by
  have hsymm' : LinearMap.IsSymm B :=
    LinearMap.BilinForm.isSymm_iff.mp hB_symm
  rcases
    LinearMap.BilinForm.exists_orthogonal_basis
      (K := ℂ) (V := U) hsymm' with
  ⟨b0, hb0_orth⟩
  have hdiag_ne :
      ∀ i, B (b0 i) (b0 i) ≠ 0 := by
    intro i
    exact
      LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
        hb0_orth hB_nd i
  choose r hr using
    fun i =>
      IsAlgClosed.exists_pow_nat_eq
        (B (b0 i) (b0 i)) (by norm_num : 0 < 2)
  have hr_ne : ∀ i, r i ≠ 0 := by
    intro i hzero
    have : B (b0 i) (b0 i) = 0 := by
      simpa [hzero] using (hr i).symm
    exact hdiag_ne i this
  let c : Fin (Module.finrank ℂ U) → ℂ :=
    fun i => (r i)⁻¹
  have hc_unit : ∀ i, IsUnit (c i) := by
    intro i
    exact isUnit_iff_ne_zero.mpr (inv_ne_zero (hr_ne i))
  let b : Module.Basis (Fin (Module.finrank ℂ U)) ℂ U :=
    b0.isUnitSMul hc_unit
  refine ⟨b, ?_, ?_⟩
  · intro i j hij
    have hzero : B (b0 i) (b0 j) = 0 := hb0_orth hij
    change B (b i) (b j) = 0
    rw [Module.Basis.isUnitSMul_apply,
      Module.Basis.isUnitSMul_apply]
    simp [c, hzero]
  · intro i
    rw [Module.Basis.isUnitSMul_apply]
    simp [c]
    field_simp [hr_ne i]
    simpa [pow_two] using (hr i).symm

/-- In a unit orthogonal basis, a symmetric bilinear form is the coordinate
dot product. -/
theorem bilinForm_eq_sum_coords_of_unitOrthogonalBasis
    {ι U : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup U] [Module ℂ U]
    (B : LinearMap.BilinForm ℂ U)
    (b : Module.Basis ι ℂ U)
    (horth : B.iIsOrtho b)
    (hdiag : ∀ i, B (b i) (b i) = 1)
    (x y : U) :
    B x y = ∑ i, b.equivFun x i * b.equivFun y i := by
  have h1 :
      B x y =
        ∑ i, ∑ j,
          b.repr x i *
            (b.repr y j * B (b i) (b j)) := by
    have hsum :=
      (LinearMap.sum_repr_mul_repr_mul
        b b (B := B) x y).symm
    rw [hsum]
    rw [Finsupp.sum_fintype]
    · congr
      ext i
      rw [Finsupp.sum_fintype]
      · simp [smul_eq_mul]
      · intro j
        simp
    · intro i
      simp
  rw [h1]
  simp only [Module.Basis.equivFun_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    ∑ j,
        b.repr x i *
          (b.repr y j * B (b i) (b j))
        =
      b.repr x i *
        (b.repr y i * B (b i) (b i)) := by
          rw [← Finset.mul_sum]
          congr 1
          apply Finset.sum_eq_single i
          · intro j _ hji
            have hz : B (b i) (b j) = 0 :=
              horth hji.symm
            simp [hz]
          · intro hi_not
            simp at hi_not
    _ = b.repr x i * b.repr y i := by
          rw [hdiag i]
          ring

/-- Nondegenerate symmetric complex bilinear spaces of the same finite
dimension are linearly isometric. -/
theorem nondegenerate_complexSymmetricBilinForm_linearEquiv_of_finrank_eq
    {U V : Type*}
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (BU : LinearMap.BilinForm ℂ U)
    (BV : LinearMap.BilinForm ℂ V)
    (hBU_symm : BU.IsSymm)
    (hBV_symm : BV.IsSymm)
    (hBU_nd : BU.Nondegenerate)
    (hBV_nd : BV.Nondegenerate)
    (hfin : Module.finrank ℂ U = Module.finrank ℂ V) :
    ∃ E : U ≃ₗ[ℂ] V,
      ∀ x y, BV (E x) (E y) = BU x y := by
  rcases
    exists_complex_unit_orthogonal_basis
      BU hBU_symm hBU_nd with
  ⟨bU, hUorth, hUdiag⟩
  rcases
    exists_complex_unit_orthogonal_basis
      BV hBV_symm hBV_nd with
  ⟨bV0, hV0orth, hV0diag⟩
  let eι :
      Fin (Module.finrank ℂ U) ≃
        Fin (Module.finrank ℂ V) :=
    finCongr hfin
  let bV : Module.Basis (Fin (Module.finrank ℂ U)) ℂ V :=
    bV0.reindex eι.symm
  have hVorth : BV.iIsOrtho bV := by
    intro i j hij
    change BV (bV i) (bV j) = 0
    have hij' : eι i ≠ eι j :=
      fun h => hij (eι.injective h)
    simpa [bV, Module.Basis.reindex_apply] using hV0orth hij'
  have hVdiag : ∀ i, BV (bV i) (bV i) = 1 := by
    intro i
    simp [bV, Module.Basis.reindex_apply, hV0diag]
  let E : U ≃ₗ[ℂ] V := bU.equiv bV (Equiv.refl _)
  refine ⟨E, ?_⟩
  intro x y
  have hcoordx : bV.equivFun (E x) = bU.equivFun x := by
    have hmap : bU.map E = bV := by
      simp [E]
    rw [← hmap, Module.Basis.map_equivFun]
    exact congrArg bU.equivFun (E.symm_apply_apply x)
  have hcoordy : bV.equivFun (E y) = bU.equivFun y := by
    have hmap : bU.map E = bV := by
      simp [E]
    rw [← hmap, Module.Basis.map_equivFun]
    exact congrArg bU.equivFun (E.symm_apply_apply y)
  rw [
    bilinForm_eq_sum_coords_of_unitOrthogonalBasis
      BV bV hVorth hVdiag (E x) (E y)]
  rw [
    bilinForm_eq_sum_coords_of_unitOrthogonalBasis
      BU bU hUorth hUdiag x y]
  rw [hcoordx, hcoordy]

/-- The two nondegenerate orthogonal complements attached to high-rank
same-Gram source-span data are linearly isometric. -/
theorem exists_complexMinkowskiOrthogonalComplementIsometry
    {d n : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w) :
    ∃ C :
        complexMinkowskiOrthogonalSubmodule d S.M ≃ₗ[ℂ]
          complexMinkowskiOrthogonalSubmodule d S.N,
      ∀ x y,
        sourceComplexMinkowskiInner d
          ((C x : complexMinkowskiOrthogonalSubmodule d S.N) :
            Fin (d + 1) → ℂ)
          ((C y : complexMinkowskiOrthogonalSubmodule d S.N) :
            Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) := by
  let B := sourceComplexMinkowskiBilinForm d
  have hB_nd : B.Nondegenerate :=
    sourceComplexMinkowskiBilinForm_nondegenerate d
  have hB_symm : B.IsSymm :=
    sourceComplexMinkowskiBilinForm_isSymm d
  have hOM_nd :
      (B.restrict
        (complexMinkowskiOrthogonalSubmodule d S.M)).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict
      d _
      (complexMinkowskiOrthogonalSubmodule_nondegenerate
        d S.M_nondegenerate)
  have hON_nd :
      (B.restrict
        (complexMinkowskiOrthogonalSubmodule d S.N)).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict
      d _
      (complexMinkowskiOrthogonalSubmodule_nondegenerate
        d S.N_nondegenerate)
  have hfin_MN : Module.finrank ℂ S.M = Module.finrank ℂ S.N :=
    S.T.finrank_eq
  have hfin_comp :
      Module.finrank ℂ
          (complexMinkowskiOrthogonalSubmodule d S.M) =
        Module.finrank ℂ
          (complexMinkowskiOrthogonalSubmodule d S.N) := by
    have hM :=
      LinearMap.BilinForm.finrank_orthogonal
        (B := B) hB_nd S.M
    have hN :=
      LinearMap.BilinForm.finrank_orthogonal
        (B := B) hB_nd S.N
    rw [
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d S.M] at hM
    rw [
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d S.N] at hN
    omega
  rcases
    nondegenerate_complexSymmetricBilinForm_linearEquiv_of_finrank_eq
      (B.restrict
        (complexMinkowskiOrthogonalSubmodule d S.M))
      (B.restrict
        (complexMinkowskiOrthogonalSubmodule d S.N))
      (restrict_isSymm_of_isSymm hB_symm _)
      (restrict_isSymm_of_isSymm hB_symm _)
      hOM_nd hON_nd hfin_comp with
  ⟨C, hC⟩
  exact ⟨C, by
    intro x y
    simpa [LinearMap.BilinForm.restrict, B,
      sourceComplexMinkowskiBilinForm] using hC x y⟩

/-- The product decomposition by a nondegenerate source span and its complex
Minkowski orthogonal complement splits the source pairing into the two diagonal
summands. -/
theorem sourceInner_prodEquivOfIsCompl
    {d : ℕ}
    (M : Submodule ℂ (Fin (d + 1) → ℂ))
    (hcompl : IsCompl M (complexMinkowskiOrthogonalSubmodule d M))
    (x y : M × complexMinkowskiOrthogonalSubmodule d M) :
    sourceComplexMinkowskiInner d
        (Submodule.prodEquivOfIsCompl M
          (complexMinkowskiOrthogonalSubmodule d M) hcompl x)
        (Submodule.prodEquivOfIsCompl M
          (complexMinkowskiOrthogonalSubmodule d M) hcompl y) =
      sourceComplexMinkowskiInner d
        (x.1 : Fin (d + 1) → ℂ)
        (y.1 : Fin (d + 1) → ℂ) +
      sourceComplexMinkowskiInner d
        (x.2 : Fin (d + 1) → ℂ)
        (y.2 : Fin (d + 1) → ℂ) := by
  rw [Submodule.coe_prodEquivOfIsCompl',
    Submodule.coe_prodEquivOfIsCompl']
  rw [sourceComplexMinkowskiInner_add_left,
    sourceComplexMinkowskiInner_add_right,
    sourceComplexMinkowskiInner_add_right]
  have hx2_y1 :
      sourceComplexMinkowskiInner d
        (x.2 : Fin (d + 1) → ℂ)
        (y.1 : Fin (d + 1) → ℂ) = 0 :=
    (mem_complexMinkowskiOrthogonalSubmodule_iff d M
      (x.2 : Fin (d + 1) → ℂ)).1 x.2.property y.1
  have hy2_x1 :
      sourceComplexMinkowskiInner d
        (y.2 : Fin (d + 1) → ℂ)
        (x.1 : Fin (d + 1) → ℂ) = 0 :=
    (mem_complexMinkowskiOrthogonalSubmodule_iff d M
      (y.2 : Fin (d + 1) → ℂ)).1 y.2.property x.1
  have hx1_y2 :
      sourceComplexMinkowskiInner d
        (x.1 : Fin (d + 1) → ℂ)
        (y.2 : Fin (d + 1) → ℂ) = 0 := by
    simpa [sourceComplexMinkowskiInner_comm d
      (x.1 : Fin (d + 1) → ℂ)
      (y.2 : Fin (d + 1) → ℂ)] using hy2_x1
  rw [hx1_y2, hx2_y1]
  ring

/-- Extend the high-rank source-span isometry to a full complex Lorentz
transformation.  This is the determinant-unrestricted Witt extension consumed
by the determinant-repair branch. -/
theorem complexMinkowski_wittExtension_full_of_sourceSpan
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w) :
    ∃ A : HallWightmanFullComplexLorentzGroup d,
      ∀ i,
        hallWightmanFullComplexLorentzVectorAction A (z i) = w i := by
  rcases exists_complexMinkowskiOrthogonalComplementIsometry S with
  ⟨C, hC⟩
  let B := sourceComplexMinkowskiBilinForm d
  have hSM_rest : (B.restrict S.M).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict
      d S.M S.M_nondegenerate
  have hSN_rest : (B.restrict S.N).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict
      d S.N S.N_nondegenerate
  have hSM_compl0 : IsCompl S.M (B.orthogonal S.M) :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := B) (W := S.M)
      (sourceComplexMinkowskiBilinForm_isRefl d)).mp hSM_rest
  have hSN_compl0 : IsCompl S.N (B.orthogonal S.N) :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := B) (W := S.N)
      (sourceComplexMinkowskiBilinForm_isRefl d)).mp hSN_rest
  have hSM_compl :
      IsCompl S.M (complexMinkowskiOrthogonalSubmodule d S.M) := by
    simpa [B,
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d S.M] using hSM_compl0
  have hSN_compl :
      IsCompl S.N (complexMinkowskiOrthogonalSubmodule d S.N) := by
    simpa [B,
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d S.N] using hSN_compl0
  let OM := complexMinkowskiOrthogonalSubmodule d S.M
  let ON := complexMinkowskiOrthogonalSubmodule d S.N
  let eM : (S.M × OM) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    Submodule.prodEquivOfIsCompl S.M OM hSM_compl
  let eN : (S.N × ON) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    Submodule.prodEquivOfIsCompl S.N ON hSN_compl
  let P : (S.M × OM) ≃ₗ[ℂ] (S.N × ON) :=
    S.T.prodCongr C
  let L : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    eM.symm.trans (P.trans eN)
  have hL :
      ∀ u v,
        sourceComplexMinkowskiInner d (L u) (L v) =
          sourceComplexMinkowskiInner d u v := by
    intro u v
    let xu : S.M × OM := eM.symm u
    let yv : S.M × OM := eM.symm v
    calc
      sourceComplexMinkowskiInner d (L u) (L v) =
          sourceComplexMinkowskiInner d (eN (P xu)) (eN (P yv)) := by
            simp [L, xu, yv]
      _ =
          sourceComplexMinkowskiInner d
            ((P xu).1 : Fin (d + 1) → ℂ)
            ((P yv).1 : Fin (d + 1) → ℂ) +
          sourceComplexMinkowskiInner d
            ((P xu).2 : Fin (d + 1) → ℂ)
            ((P yv).2 : Fin (d + 1) → ℂ) := by
            exact sourceInner_prodEquivOfIsCompl
              S.N hSN_compl (P xu) (P yv)
      _ =
          sourceComplexMinkowskiInner d
            (xu.1 : Fin (d + 1) → ℂ)
            (yv.1 : Fin (d + 1) → ℂ) +
          sourceComplexMinkowskiInner d
            (xu.2 : Fin (d + 1) → ℂ)
            (yv.2 : Fin (d + 1) → ℂ) := by
            simp [P, S.T_preserves, hC]
      _ = sourceComplexMinkowskiInner d (eM xu) (eM yv) := by
            rw [sourceInner_prodEquivOfIsCompl
              S.M hSM_compl xu yv]
      _ = sourceComplexMinkowskiInner d u v := by
            simp [xu, yv]
  let A : HallWightmanFullComplexLorentzGroup d :=
    HallWightmanFullComplexLorentzGroup.ofLinearMap L.toLinearMap hL
  refine ⟨A, ?_⟩
  intro i
  calc
    hallWightmanFullComplexLorentzVectorAction A (z i) =
        L (z i) := by
          exact
            HallWightmanFullComplexLorentzGroup.ofLinearMap_vectorAction
              L.toLinearMap hL (z i)
    _ = w i := by
          have hz :
              eM.symm (z i) =
                ((⟨z i, S.z_mem i⟩ : S.M), 0) := by
            exact
              Submodule.prodEquivOfIsCompl_symm_apply_left
                S.M OM hSM_compl (⟨z i, S.z_mem i⟩ : S.M)
          calc
            L (z i) = eN (P (eM.symm (z i))) := by
              rfl
            _ = eN (P ((⟨z i, S.z_mem i⟩ : S.M), 0)) := by
              rw [hz]
            _ = eN (⟨w i, S.w_mem i⟩, 0) := by
              simp [P, S.T_z i]
            _ = w i := by
              simp [eN]

/-- Determinant-`1` Witt extension from high-rank source-span data.  In a
proper source span, a checked reflection on the orthogonal complement flips the
determinant if needed; in full ambient rank the selected full-frame determinant
compatibility supplies the determinant. -/
theorem complexMinkowski_wittExtension_detOne_of_sourceSpan
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w)
    (hSO : HWSameSourceGramSOOrientationCompatible d n z w) :
    ∃ Λ : ComplexLorentzGroup d,
      ∀ i, complexLorentzVectorAction Λ (z i) = w i := by
  rcases complexMinkowski_wittExtension_full_of_sourceSpan d n S with
  ⟨A, hA⟩
  by_cases hproper :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1
  · by_cases hdetA : hallWightmanFullComplexLorentzDet A = 1
    · rcases
        fullComplexLorentz_to_complexLorentzGroup_of_det_one A hdetA with
      ⟨Λ, hΛA⟩
      exact ⟨Λ, fun i => by rw [hΛA, hA i]⟩
    · rcases
        fullComplexLorentz_det_neg_reflection_fixing_sourceSpan
          d n S hproper with
      ⟨R, hRdet, hRfix⟩
      let AR := hallWightmanFullComplexLorentzMul A R
      have hARdet : hallWightmanFullComplexLorentzDet AR = 1 := by
        have hA_sq := hallWightmanFullComplexLorentz_det_sq_eq_one A
        have hA_neg : hallWightmanFullComplexLorentzDet A = -1 :=
          det_eq_neg_one_of_sq_one_of_ne_one hA_sq hdetA
        simp [AR, fullComplexLorentz_mul_det, hA_neg, hRdet]
      rcases
        fullComplexLorentz_to_complexLorentzGroup_of_det_one AR hARdet with
      ⟨Λ, hΛAR⟩
      refine ⟨Λ, ?_⟩
      intro i
      calc
        complexLorentzVectorAction Λ (z i) =
            hallWightmanFullComplexLorentzVectorAction AR (z i) := by
              rw [hΛAR]
        _ =
            hallWightmanFullComplexLorentzVectorAction A
              (hallWightmanFullComplexLorentzVectorAction R (z i)) := by
              simpa [AR] using
                fullComplexLorentz_mul_vectorAction A R (z i)
        _ = hallWightmanFullComplexLorentzVectorAction A (z i) := by
              rw [hRfix (⟨z i, S.z_mem i⟩ : S.M)]
        _ = w i := hA i
  · have hle :
        sourceGramMatrixRank n (sourceMinkowskiGram d n z) ≤ d + 1 :=
      le_trans (sourceGramMatrixRank_le_spacetime_source_min d n z)
        (min_le_left (d + 1) n)
    have hfull :
        sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1 :=
      le_antisymm hle (Nat.le_of_not_lt hproper)
    have hdetA : hallWightmanFullComplexLorentzDet A = 1 := by
      have hdet_frame :=
        fullComplexLorentz_det_eq_frameMapDet_of_fullRank
          d n hfull (HWHighRankSpanIsometryData_sourceGram_eq d n S) A hA
      rcases hSO with hlt | hone
      · have :
            ¬ sourceGramMatrixRank n (sourceMinkowskiGram d n z) <
              d + 1 := by
          rw [hfull]
          exact Nat.lt_irrefl _
        exact False.elim (this hlt)
      · exact hdet_frame.trans hone
    rcases
      fullComplexLorentz_to_complexLorentzGroup_of_det_one A hdetA with
    ⟨Λ, hΛA⟩
    exact ⟨Λ, fun i => by rw [hΛA, hA i]⟩

/-- High scalar-rank same-Gram data with determinant compatibility gives a
proper complex Lorentz orbit. -/
theorem hw_sameSourceGram_regular_orbit
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hzOrbit : HWSourceGramOrbitRankAt d n z)
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (hSO : HWSameSourceGramSOOrientationCompatible d n z w) :
    ∃ Λ : ComplexLorentzGroup d, w = complexLorentzAction Λ z := by
  let S : HWHighRankSpanIsometryData d n z w :=
    hw_highRank_spanIsometryData_of_sameSourceGram d n hzOrbit hgram
  rcases complexMinkowski_wittExtension_detOne_of_sourceSpan d n S hSO with
  ⟨Λ, hΛ⟩
  refine ⟨Λ, ?_⟩
  funext i
  exact (hΛ i).symm

/-- Oriented max-rank configurations with the same oriented invariant are in
the same proper complex Lorentz orbit. -/
theorem hw_sameSourceOrientedInvariant_maxRank_properOrbit
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hzmax :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z))
    (hinv :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    ∃ Λ : ComplexLorentzGroup d, w = complexLorentzAction Λ z := by
  have hgram :
      sourceMinkowskiGram d n z = sourceMinkowskiGram d n w :=
    same_sourceOrientedInvariant_sourceGram hinv
  have hHWmax : HWSourceGramMaxRankAt d n z :=
    (sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt
      d n z).1 hzmax
  have hzOrbit : HWSourceGramOrbitRankAt d n z := by
    have hle_min : min d n ≤ min (d + 1) n :=
      min_le_min_right n (Nat.le_succ d)
    exact le_trans hle_min hHWmax
  have hSO : HWSameSourceGramSOOrientationCompatible d n z w :=
    sourceOriented_soCompatible_of_sameInvariant d n hgram hinv
  exact hw_sameSourceGram_regular_orbit d n hzOrbit hgram hSO

end BHW
