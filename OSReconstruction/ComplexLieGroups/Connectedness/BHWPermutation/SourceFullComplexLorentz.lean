import Mathlib.LinearAlgebra.Reflection
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceRank

/-!
# Full complex Lorentz support for the Hall-Wightman source route

This file contains the determinant-unrestricted complex Lorentz group used in
the high-rank Hall-Wightman same-source-Gram branch.  It is purely
finite-dimensional matrix algebra: no OS, Wightman, PET, or locality input is
used here.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Full complex Lorentz group `O(1,d;ℂ)`: complex matrices preserving the
Minkowski metric, without imposing determinant `1`. -/
structure HallWightmanFullComplexLorentzGroup (d : ℕ) where
  val : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  metric_preserving :
    ∀ μ ν : Fin (d + 1),
      ∑ α : Fin (d + 1),
        (minkowskiSignature d α : ℂ) * val α μ * val α ν =
      if μ = ν then (minkowskiSignature d μ : ℂ) else 0

/-- Action of a full complex Lorentz matrix on one source vector. -/
def hallWightmanFullComplexLorentzVectorAction
    {d : ℕ}
    (A : HallWightmanFullComplexLorentzGroup d)
    (v : Fin (d + 1) → ℂ) :
    Fin (d + 1) → ℂ :=
  fun μ => ∑ ν : Fin (d + 1), A.val μ ν * v ν

/-- Action of a full complex Lorentz matrix on a source tuple. -/
def hallWightmanFullComplexLorentzAction
    {d n : ℕ}
    (A : HallWightmanFullComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i => hallWightmanFullComplexLorentzVectorAction A (z i)

/-- Determinant of a full complex Lorentz matrix. -/
def hallWightmanFullComplexLorentzDet
    {d : ℕ}
    (A : HallWightmanFullComplexLorentzGroup d) : ℂ :=
  A.val.det

/-- Componentwise metric preservation as the matrix equation `Aᵀ η A = η`. -/
theorem hallWightmanFullComplexLorentz_metric_preserving_matrix
    {d : ℕ}
    (A : HallWightmanFullComplexLorentzGroup d) :
    A.val.transpose * ComplexLorentzGroup.ηℂ (d := d) * A.val =
      ComplexLorentzGroup.ηℂ (d := d) := by
  ext μ ν
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    ComplexLorentzGroup.ηℂ, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  convert A.metric_preserving μ ν using 1
  apply Finset.sum_congr rfl
  intro α _
  ring

/-- The complex Minkowski metric matrix has nonzero determinant. -/
theorem complexLorentzEta_det_ne_zero (d : ℕ) :
    (ComplexLorentzGroup.ηℂ (d := d)).det ≠ 0 := by
  rw [ComplexLorentzGroup.ηℂ, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  by_cases hi : i = 0
  · simp [minkowskiSignature, hi]
  · simp [minkowskiSignature, hi]

/-- Full complex Lorentz determinants square to `1`. -/
theorem hallWightmanFullComplexLorentz_det_sq_eq_one
    {d : ℕ}
    (A : HallWightmanFullComplexLorentzGroup d) :
    hallWightmanFullComplexLorentzDet A ^ 2 = 1 := by
  have hmat := hallWightmanFullComplexLorentz_metric_preserving_matrix A
  have hdet := congrArg Matrix.det hmat
  have hη : (ComplexLorentzGroup.ηℂ (d := d)).det ≠ 0 :=
    complexLorentzEta_det_ne_zero d
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hdet' :
      A.val.det * A.val.det *
          (ComplexLorentzGroup.ηℂ (d := d)).det =
        1 * (ComplexLorentzGroup.ηℂ (d := d)).det := by
    calc
      A.val.det * A.val.det *
          (ComplexLorentzGroup.ηℂ (d := d)).det =
        A.val.det * (ComplexLorentzGroup.ηℂ (d := d)).det *
          A.val.det := by
            ring
      _ = (ComplexLorentzGroup.ηℂ (d := d)).det := hdet
      _ = 1 * (ComplexLorentzGroup.ηℂ (d := d)).det := by ring
  have hcancel := mul_right_cancel₀ hη hdet'
  simpa [hallWightmanFullComplexLorentzDet, pow_two] using hcancel

/-- A scalar whose square is one and which is not one is minus one. -/
theorem det_eq_neg_one_of_sq_one_of_ne_one
    {a : ℂ}
    (hsq : a ^ 2 = 1)
    (hne : a ≠ 1) :
    a = -1 := by
  have hfactor : (a - 1) * (a + 1) = 0 := by
    calc
      (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
      _ = 0 := by
        rw [hsq]
        ring
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · exact False.elim (hne (sub_eq_zero.mp hminus))
  · exact eq_neg_of_add_eq_zero_left hplus

/-- Forget a determinant-one complex Lorentz element into the full complex
Lorentz group. -/
def complexLorentzGroup_to_fullComplexLorentz
    {d : ℕ}
    (Λ : ComplexLorentzGroup d) :
    HallWightmanFullComplexLorentzGroup d where
  val := Λ.val
  metric_preserving := Λ.metric_preserving

/-- Product in the full complex Lorentz group. -/
def hallWightmanFullComplexLorentzMul
    {d : ℕ}
    (A B : HallWightmanFullComplexLorentzGroup d) :
    HallWightmanFullComplexLorentzGroup d where
  val := A.val * B.val
  metric_preserving := by
    apply ComplexLorentzGroup.of_metric_preserving_matrix
    rw [Matrix.transpose_mul]
    calc
      B.val.transpose * A.val.transpose *
          ComplexLorentzGroup.ηℂ * (A.val * B.val) =
        B.val.transpose *
            (A.val.transpose * ComplexLorentzGroup.ηℂ * A.val) *
          B.val := by
            simp only [Matrix.mul_assoc]
      _ = B.val.transpose * ComplexLorentzGroup.ηℂ * B.val := by
            rw [hallWightmanFullComplexLorentz_metric_preserving_matrix A]
      _ = ComplexLorentzGroup.ηℂ :=
            hallWightmanFullComplexLorentz_metric_preserving_matrix B

/-- Determinant of a product in the full complex Lorentz group. -/
theorem fullComplexLorentz_mul_det
    {d : ℕ}
    (A B : HallWightmanFullComplexLorentzGroup d) :
    hallWightmanFullComplexLorentzDet
        (hallWightmanFullComplexLorentzMul A B) =
      hallWightmanFullComplexLorentzDet A *
        hallWightmanFullComplexLorentzDet B := by
  simp [hallWightmanFullComplexLorentzDet,
    hallWightmanFullComplexLorentzMul, Matrix.det_mul]

/-- Vector action of a product in the full complex Lorentz group. -/
theorem fullComplexLorentz_mul_vectorAction
    {d : ℕ}
    (A B : HallWightmanFullComplexLorentzGroup d)
    (v : Fin (d + 1) → ℂ) :
    hallWightmanFullComplexLorentzVectorAction
        (hallWightmanFullComplexLorentzMul A B) v =
      hallWightmanFullComplexLorentzVectorAction A
        (hallWightmanFullComplexLorentzVectorAction B v) := by
  ext μ
  simp only [hallWightmanFullComplexLorentzVectorAction,
    hallWightmanFullComplexLorentzMul, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext ν
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

/-- Tuple action of a product in the full complex Lorentz group. -/
theorem fullComplexLorentz_mul_configAction
    {d n : ℕ}
    (A B : HallWightmanFullComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    hallWightmanFullComplexLorentzAction
        (hallWightmanFullComplexLorentzMul A B) z =
      hallWightmanFullComplexLorentzAction A
        (hallWightmanFullComplexLorentzAction B z) := by
  ext i μ
  simpa [hallWightmanFullComplexLorentzAction] using
    congrFun (fullComplexLorentz_mul_vectorAction A B (z i)) μ

/-- A determinant-one full complex Lorentz element is a proper complex Lorentz
element with the same vector action. -/
theorem fullComplexLorentz_to_complexLorentzGroup_of_det_one
    {d : ℕ}
    (A : HallWightmanFullComplexLorentzGroup d)
    (hdet : hallWightmanFullComplexLorentzDet A = 1) :
    ∃ Λ : ComplexLorentzGroup d,
      ∀ v,
        complexLorentzVectorAction Λ v =
          hallWightmanFullComplexLorentzVectorAction A v := by
  let Λ : ComplexLorentzGroup d :=
    { val := A.val
      metric_preserving := A.metric_preserving
      proper := hdet }
  exact ⟨Λ, fun _ => rfl⟩

namespace HallWightmanFullComplexLorentzGroup

/-- Build a full complex Lorentz element from a linear map preserving the
complex Minkowski pairing. -/
noncomputable def ofLinearMap
    {d : ℕ}
    (L : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hpres :
      ∀ x y,
        sourceComplexMinkowskiInner d (L x) (L y) =
          sourceComplexMinkowskiInner d x y) :
    HallWightmanFullComplexLorentzGroup d where
  val := LinearMap.toMatrix' L
  metric_preserving := by
    intro μ ν
    have h := hpres (Pi.single μ (1 : ℂ)) (Pi.single ν (1 : ℂ))
    by_cases hμν : μ = ν
    · subst ν
      simpa [sourceComplexMinkowskiInner, LinearMap.toMatrix'_apply,
        Pi.single_apply, MinkowskiSpace.metricSignature, minkowskiSignature,
        mul_comm, mul_left_comm, mul_assoc] using h
    · have hνμ : ν ≠ μ := fun h => hμν h.symm
      simpa [sourceComplexMinkowskiInner, LinearMap.toMatrix'_apply,
        Pi.single_apply, MinkowskiSpace.metricSignature, minkowskiSignature,
        hμν, hνμ, mul_comm, mul_left_comm, mul_assoc] using h

/-- The vector action of `ofLinearMap` is the original linear map. -/
theorem ofLinearMap_vectorAction
    {d : ℕ}
    (L : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hpres :
      ∀ x y,
        sourceComplexMinkowskiInner d (L x) (L y) =
          sourceComplexMinkowskiInner d x y)
    (v : Fin (d + 1) → ℂ) :
    hallWightmanFullComplexLorentzVectorAction
        (ofLinearMap L hpres) v =
      L v := by
  ext μ
  have h := congrFun (LinearMap.toMatrix'_mulVec L v) μ
  simpa [hallWightmanFullComplexLorentzVectorAction, ofLinearMap,
    Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, mul_assoc] using h

end HallWightmanFullComplexLorentzGroup

/-- The Householder reflection across a nonisotropic vector in the source-span
orthogonal complement, as a linear map. -/
noncomputable def fullComplexLorentzReflectionLinear
    {d : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (u : complexMinkowskiOrthogonalSubmodule d M)
    (_hu :
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ) where
  toFun v :=
    v -
      ((2 * sourceComplexMinkowskiInner d v
          (u : Fin (d + 1) → ℂ)) /
        sourceComplexMinkowskiInner d
          (u : Fin (d + 1) → ℂ)
          (u : Fin (d + 1) → ℂ)) •
      (u : Fin (d + 1) → ℂ)
  map_add' := by
    intro v w
    ext μ
    simp [sourceComplexMinkowskiInner_add_left, sub_eq_add_neg]
    ring
  map_smul' := by
    intro c v
    ext μ
    simp [sourceComplexMinkowskiInner_smul_left]
    ring

/-- Formula for the Householder reflection linear map. -/
theorem fullComplexLorentzReflectionLinear_apply
    {d : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (u : complexMinkowskiOrthogonalSubmodule d M)
    (hu :
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0)
    (v : Fin (d + 1) → ℂ) :
    fullComplexLorentzReflectionLinear u hu v =
      v -
        ((2 * sourceComplexMinkowskiInner d v
            (u : Fin (d + 1) → ℂ)) /
          sourceComplexMinkowskiInner d
            (u : Fin (d + 1) → ℂ)
            (u : Fin (d + 1) → ℂ)) •
        (u : Fin (d + 1) → ℂ) :=
  rfl

/-- The Householder reflection preserves the complex Minkowski pairing. -/
theorem fullComplexLorentzReflectionLinear_preserves_inner
    {d : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (u : complexMinkowskiOrthogonalSubmodule d M)
    (hu :
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0)
    (v w : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d
        (fullComplexLorentzReflectionLinear u hu v)
        (fullComplexLorentzReflectionLinear u hu w) =
      sourceComplexMinkowskiInner d v w := by
  rw [fullComplexLorentzReflectionLinear_apply u hu v,
    fullComplexLorentzReflectionLinear_apply u hu w]
  rw [sourceComplexMinkowskiInner_sub_left,
    sourceComplexMinkowskiInner_sub_right,
    sourceComplexMinkowskiInner_sub_right]
  simp [sourceComplexMinkowskiInner_smul_left,
    sourceComplexMinkowskiInner_smul_right]
  have hwu_sym :
      sourceComplexMinkowskiInner d
          (u : Fin (d + 1) → ℂ) w =
        sourceComplexMinkowskiInner d w
          (u : Fin (d + 1) → ℂ) :=
    sourceComplexMinkowskiInner_comm d
      (u : Fin (d + 1) → ℂ) w
  rw [hwu_sym]
  field_simp [hu]
  ring

/-- The Householder reflection fixes the source span pointwise. -/
theorem fullComplexLorentzReflectionLinear_fix_subspace
    {d : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (u : complexMinkowskiOrthogonalSubmodule d M)
    (hu :
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0)
    (x : M) :
    fullComplexLorentzReflectionLinear u hu
        (x : Fin (d + 1) → ℂ) =
      x := by
  rw [fullComplexLorentzReflectionLinear_apply]
  have hux :
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (x : Fin (d + 1) → ℂ) = 0 :=
    (mem_complexMinkowskiOrthogonalSubmodule_iff d M
      (u : Fin (d + 1) → ℂ)).1 u.property x
  have hxu :
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) = 0 := by
    simpa [sourceComplexMinkowskiInner_comm] using hux
  simp [hxu]

/-- Determinants are invariant under conjugation by a linear equivalence. -/
theorem det_eq_of_conj_by_linearEquiv
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (L : V ≃ₗ[ℂ] W)
    (T : W →ₗ[ℂ] W)
    (S : V →ₗ[ℂ] V)
    (h : L.symm.toLinearMap.comp (T.comp L.toLinearMap) = S) :
    LinearMap.det T = LinearMap.det S := by
  have hdet := LinearMap.det_conj (A := ℂ) T L.symm
  simpa [LinearMap.comp_assoc, h] using hdet.symm

/-- The restriction of a module reflection to its reflection line has
determinant `-1`. -/
theorem det_restrict_reflection_span
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (x : V) (hx : x ≠ 0)
    (f : Module.Dual ℂ V)
    (hf : f x = 2) :
    let e := ((Module.reflection (x := x) (f := f) hf : V ≃ₗ[ℂ] V) :
      V →ₗ[ℂ] V)
    let W : Submodule ℂ V := ℂ ∙ x
    ∀ hW : W ≤ W.comap e,
      LinearMap.det (e.restrict hW) = -1 := by
  intro e W hW
  let L : ℂ ≃ₗ[ℂ] W := by
    subst W
    exact LinearEquiv.toSpanNonzeroSingleton ℂ V x hx
  have hconj :
      L.symm.toLinearMap.comp ((e.restrict hW).comp L.toLinearMap) =
        (-1 : ℂ) • LinearMap.id := by
    apply LinearMap.ext
    intro a
    subst W
    change L.symm ((e.restrict hW) (L a)) =
      ((-1 : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) a
    have hLa :
        L a =
          (⟨a • x, Submodule.smul_mem _ a
            (Submodule.mem_span_singleton_self x)⟩ : ℂ ∙ x) := by
      simp [L]
    have harg :
        (e.restrict hW
          ⟨a • x, Submodule.smul_mem _ a
            (Submodule.mem_span_singleton_self x)⟩) =
        (⟨(-a) • x, Submodule.smul_mem _ (-a)
            (Submodule.mem_span_singleton_self x)⟩ : ℂ ∙ x) := by
      ext
      simp only [LinearMap.restrict_apply, Subtype.coe_mk]
      rw [map_smul]
      change a • ((Module.reflection (x := x) (f := f) hf : V ≃ₗ[ℂ] V) x) =
        (-a) • x
      simp [Module.reflection_apply_self hf]
    rw [hLa, harg]
    apply_fun (fun c : ℂ => c • x)
    · simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        smul_eq_mul]
      dsimp [L]
      simp
    · exact smul_left_injective ℂ hx
  calc
    LinearMap.det (e.restrict hW) =
        LinearMap.det ((-1 : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) := by
          exact det_eq_of_conj_by_linearEquiv L _ _ hconj
    _ = -1 := by
          simp

/-- The quotient map induced by a module reflection modulo its reflection line
has determinant `1`. -/
theorem det_quotient_reflection_span
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (x : V) (_hx : x ≠ 0)
    (f : Module.Dual ℂ V)
    (hf : f x = 2) :
    let e := ((Module.reflection (x := x) (f := f) hf : V ≃ₗ[ℂ] V) :
      V →ₗ[ℂ] V)
    let W : Submodule ℂ V := ℂ ∙ x
    ∀ hW : W ≤ W.comap e,
      LinearMap.det (W.mapQ W e hW) = 1 := by
  intro e W hW
  have hmap : W.mapQ W e hW = LinearMap.id := by
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on W q ?_
    intro y
    rw [Submodule.mapQ_apply]
    apply (Submodule.Quotient.eq W).mpr
    change ((Module.reflection (x := x) (f := f) hf : V ≃ₗ[ℂ] V) y - y) ∈ W
    rw [Module.reflection_apply]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      Submodule.smul_mem W (-(f y))
        (Submodule.mem_span_singleton_self x)
  rw [hmap, LinearMap.det_id]

/-- A module reflection across a nonzero line has determinant `-1`. -/
theorem det_moduleReflection_of_nonzero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (x : V) (hx : x ≠ 0)
    (f : Module.Dual ℂ V)
    (hf : f x = 2) :
    LinearMap.det
        ((Module.reflection (x := x) (f := f) hf : V ≃ₗ[ℂ] V) :
          V →ₗ[ℂ] V) = -1 := by
  let e := ((Module.reflection (x := x) (f := f) hf : V ≃ₗ[ℂ] V) :
    V →ₗ[ℂ] V)
  let W : Submodule ℂ V := ℂ ∙ x
  have hW : W ≤ W.comap e := by
    intro y hy
    rw [Submodule.mem_comap]
    rcases Submodule.mem_span_singleton.mp hy with ⟨a, rfl⟩
    rw [map_smul]
    have hex : e x ∈ W := by
      change ((Module.reflection (x := x) (f := f) hf : V ≃ₗ[ℂ] V) :
          V →ₗ[ℂ] V) x ∈ W
      simpa [LinearEquiv.coe_coe, Module.reflection_apply_self hf] using
        W.neg_mem (Submodule.mem_span_singleton_self x)
    exact W.smul_mem a hex
  have hdet := LinearMap.det_eq_det_mul_det W e hW
  have hres : LinearMap.det (e.restrict hW) = -1 := by
    exact det_restrict_reflection_span (x := x) hx f hf hW
  have hquot : LinearMap.det (W.mapQ W e hW) = 1 := by
    exact det_quotient_reflection_span (x := x) hx f hf hW
  rw [hdet, hres, hquot, mul_one]

/-- The Householder reflection linear map has determinant `-1`. -/
theorem fullComplexLorentzReflectionLinear_det
    {d : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (u : complexMinkowskiOrthogonalSubmodule d M)
    (hu :
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0) :
    LinearMap.det (fullComplexLorentzReflectionLinear u hu) = -1 := by
  let V := Fin (d + 1) → ℂ
  let q := sourceComplexMinkowskiInner d (u : V) (u : V)
  have hu0 : (u : V) ≠ 0 := by
    intro h0
    exact hu (by
      unfold sourceComplexMinkowskiInner
      simp [h0])
  let f : Module.Dual ℂ V :=
    { toFun := fun v => (2 / q) * sourceComplexMinkowskiInner d v (u : V)
      map_add' := by
        intro v w
        rw [sourceComplexMinkowskiInner_add_left]
        ring
      map_smul' := by
        intro c v
        rw [sourceComplexMinkowskiInner_smul_left]
        simp only [RingHom.id_apply, smul_eq_mul]
        ring_nf }
  have hf : f (u : V) = 2 := by
    simp [f, q]
    field_simp [hu]
  have hR_eq :
      fullComplexLorentzReflectionLinear u hu =
        ((Module.reflection (x := (u : V)) (f := f) hf : V ≃ₗ[ℂ] V) :
          V →ₗ[ℂ] V) := by
    apply LinearMap.ext
    intro v
    funext μ
    rw [fullComplexLorentzReflectionLinear_apply]
    simp [Module.reflection_apply, f, q, div_eq_mul_inv, mul_comm,
      mul_left_comm, mul_assoc]
  rw [hR_eq]
  exact det_moduleReflection_of_nonzero (x := (u : V)) hu0 f hf

/-- The Householder reflection packaged as a full complex Lorentz element. -/
noncomputable def fullComplexLorentzReflection
    {d : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (u : complexMinkowskiOrthogonalSubmodule d M)
    (hu :
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0) :
    HallWightmanFullComplexLorentzGroup d :=
  HallWightmanFullComplexLorentzGroup.ofLinearMap
    (fullComplexLorentzReflectionLinear u hu)
    (fullComplexLorentzReflectionLinear_preserves_inner u hu)

/-- The packaged Householder reflection has determinant `-1`. -/
theorem fullComplexLorentzReflection_det
    {d : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (u : complexMinkowskiOrthogonalSubmodule d M)
    (hu :
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0) :
    hallWightmanFullComplexLorentzDet
        (fullComplexLorentzReflection u hu) = -1 := by
  rw [fullComplexLorentzReflection, hallWightmanFullComplexLorentzDet,
    HallWightmanFullComplexLorentzGroup.ofLinearMap, LinearMap.det_toMatrix']
  exact fullComplexLorentzReflectionLinear_det u hu

/-- The packaged Householder reflection fixes the source span pointwise. -/
theorem fullComplexLorentzReflection_fix_subspace
    {d : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (u : complexMinkowskiOrthogonalSubmodule d M)
    (hu :
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0)
    (x : M) :
    hallWightmanFullComplexLorentzVectorAction
        (fullComplexLorentzReflection u hu)
        (x : Fin (d + 1) → ℂ) =
      x := by
  rw [fullComplexLorentzReflection]
  rw [HallWightmanFullComplexLorentzGroup.ofLinearMap_vectorAction]
  exact fullComplexLorentzReflectionLinear_fix_subspace u hu x

/-- In the proper-span high-rank branch, a determinant-`-1` full complex
Lorentz reflection fixes the source span pointwise. -/
theorem fullComplexLorentz_det_neg_reflection_fixing_sourceSpan
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w)
    (hproper :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1) :
    ∃ R : HallWightmanFullComplexLorentzGroup d,
      hallWightmanFullComplexLorentzDet R = -1 ∧
      ∀ x : S.M,
        hallWightmanFullComplexLorentzVectorAction R
            (x : Fin (d + 1) → ℂ) =
          x := by
  rcases
    exists_nonisotropic_mem_sourceSpan_orthogonalComplement_of_proper
      d n S hproper with
  ⟨u, hu⟩
  refine
    ⟨fullComplexLorentzReflection u hu,
      fullComplexLorentzReflection_det u hu,
      ?_⟩
  intro x
  exact fullComplexLorentzReflection_fix_subspace u hu x

end BHW
