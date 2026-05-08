import Mathlib.Analysis.InnerProductSpace.PiL2
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTakagiFixed

/-!
# Positive-eigenspace phase support for Autonne-Takagi

This file packages the normalized conjugate-linear Takagi map on a positive
eigenspace of `S * Sᴴ` as a conjugate-linear isometric involution.  The
ambient space is `EuclideanSpace ℂ (Fin m)`, matching the Hilbert norm used by
the Hermitian spectral theorem; we coerce to functions only when applying
matrix `mulVec`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator ComplexOrder ComplexConjugate

namespace BHW

/-- The conjugate-linear map `v ↦ S *ᵥ star v` as a map of finite-dimensional
Euclidean Hilbert spaces. -/
def takagiConjugateLinearEuclideanMap
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (v : EuclideanSpace ℂ (Fin m)) :
    EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 (takagiConjugateLinearMap m S (v : Fin m → ℂ))

theorem takagiConjugateLinearEuclideanMap_add
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (v w : EuclideanSpace ℂ (Fin m)) :
    takagiConjugateLinearEuclideanMap m S (v + w) =
      takagiConjugateLinearEuclideanMap m S v +
        takagiConjugateLinearEuclideanMap m S w := by
  ext i
  simp [takagiConjugateLinearEuclideanMap, takagiConjugateLinearMap_add]

theorem takagiConjugateLinearEuclideanMap_smul
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (c : ℂ) (v : EuclideanSpace ℂ (Fin m)) :
    takagiConjugateLinearEuclideanMap m S (c • v) =
      star c • takagiConjugateLinearEuclideanMap m S v := by
  ext i
  simp [takagiConjugateLinearEuclideanMap, takagiConjugateLinearMap_smul]

/-- The eigenspace of the Hermitian square `S * Sᴴ` for the real eigenvalue
`lambda`, as a complex subspace of Euclidean space. -/
def takagiHermitianEigenspace
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) (lambda : ℝ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin m)) where
  carrier := {v | (S * Sᴴ) *ᵥ (v : Fin m → ℂ) = (lambda : ℂ) • (v : Fin m → ℂ)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (S * Sᴴ) *ᵥ ((x + y : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) =
      (lambda : ℂ) • (((x + y : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ))
    ext i
    have hxi := congrFun hx i
    have hyi := congrFun hy i
    simp [Matrix.mulVec_add, hxi, hyi, mul_add]
  smul_mem' := by
    intro c x hx
    change (S * Sᴴ) *ᵥ ((c • x : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) =
      (lambda : ℂ) • (((c • x : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ))
    ext i
    have hxi := congrFun hx i
    by_cases hc : c = 0
    · simp [hc]
    · simp [Matrix.mulVec_smul, hxi, mul_left_comm]

/-- On a Hermitian-square eigenspace, the Takagi conjugate-linear map has norm
`sqrt(lambda)` times the original norm.  This is the matrix identity
`‖Sᴴv‖² = ⟪v, S Sᴴ v⟫`. -/
theorem takagiConjugateLinearEuclideanMap_norm_sq_of_eigen
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    {lambda : ℝ} {v : EuclideanSpace ℂ (Fin m)}
    (hv : (S * Sᴴ) *ᵥ (v : Fin m → ℂ) = (lambda : ℂ) • (v : Fin m → ℂ)) :
    ‖takagiConjugateLinearEuclideanMap m S v‖ ^ 2 = lambda * ‖v‖ ^ 2 := by
  have hnorm : ‖takagiConjugateLinearEuclideanMap m S v‖ ^ 2 =
      Complex.re (star (v : Fin m → ℂ) ⬝ᵥ ((S * Sᴴ) *ᵥ (v : Fin m → ℂ))) := by
    have hstar := takagiConjugateLinearMap_conjTranspose_mulVec_eq_star
      (m := m) (S := S) hSym (v : Fin m → ℂ)
    calc
      ‖takagiConjugateLinearEuclideanMap m S v‖ ^ 2 =
          ‖WithLp.toLp 2 (star (takagiConjugateLinearMap m S (v : Fin m → ℂ)))‖ ^ 2 := by
        simp [takagiConjugateLinearEuclideanMap, EuclideanSpace.norm_sq_eq]
      _ = ‖WithLp.toLp 2 (Sᴴ *ᵥ (v : Fin m → ℂ))‖ ^ 2 := by rw [← hstar]
      _ = Complex.re (star (v : Fin m → ℂ) ⬝ᵥ
          ((S * Sᴴ) *ᵥ (v : Fin m → ℂ))) := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
        rw [EuclideanSpace.inner_toLp_toLp]
        rw [Matrix.star_mulVec]
        rw [dotProduct_comm]
        rw [Matrix.dotProduct_mulVec]
        rw [Matrix.vecMul_vecMul]
        rw [conjTranspose_conjTranspose]
        rw [Matrix.dotProduct_mulVec]
        rfl
  have hdot :
      star (v : Fin m → ℂ) ⬝ᵥ (v : Fin m → ℂ) = (‖v‖ : ℂ) ^ 2 := by
    rw [dotProduct_comm]
    rw [← EuclideanSpace.inner_eq_star_dotProduct]
    rw [inner_self_eq_norm_sq_to_K]
    rfl
  rw [hnorm, hv]
  calc
    Complex.re (star (v : Fin m → ℂ) ⬝ᵥ ((lambda : ℂ) • (v : Fin m → ℂ))) =
        Complex.re ((lambda : ℂ) * (star (v : Fin m → ℂ) ⬝ᵥ (v : Fin m → ℂ))) := by
      rw [dotProduct_smul]
      change Complex.re ((lambda : ℂ) * (star (v : Fin m → ℂ) ⬝ᵥ (v : Fin m → ℂ))) =
        Complex.re ((lambda : ℂ) * (star (v : Fin m → ℂ) ⬝ᵥ (v : Fin m → ℂ)))
      rfl
    _ = Complex.re ((lambda : ℂ) * ((‖v‖ : ℂ) ^ 2)) := by
      exact congrArg (fun z : ℂ => Complex.re ((lambda : ℂ) * z)) hdot
    _ = lambda * ‖v‖ ^ 2 := by
      have hcast : ((lambda * ‖v‖ ^ 2 : ℝ) : ℂ) =
          (lambda : ℂ) * ((‖v‖ : ℂ) ^ 2) := by
        norm_num
      rw [← hcast]
      exact Complex.ofReal_re _

theorem takagiConjugateLinearEuclideanMap_norm_of_eigen
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) {v : EuclideanSpace ℂ (Fin m)}
    (hv : (S * Sᴴ) *ᵥ (v : Fin m → ℂ) = (lambda : ℂ) • (v : Fin m → ℂ)) :
    ‖takagiConjugateLinearEuclideanMap m S v‖ = Real.sqrt lambda * ‖v‖ := by
  have hsq := takagiConjugateLinearEuclideanMap_norm_sq_of_eigen
    (m := m) (S := S) hSym hv
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg lambda) (norm_nonneg _))).mp
  rw [hsq]
  rw [mul_pow]
  rw [Real.sq_sqrt hlambda]

theorem takagiConjugateLinearEuclideanMap_normalized_norm_of_eigen
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    {lambda : ℝ} (hlambda : 0 < lambda) {v : EuclideanSpace ℂ (Fin m)}
    (hv : (S * Sᴴ) *ᵥ (v : Fin m → ℂ) = (lambda : ℂ) • (v : Fin m → ℂ)) :
    ‖(((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
        takagiConjugateLinearEuclideanMap m S v‖ = ‖v‖ := by
  have hnorm := takagiConjugateLinearEuclideanMap_norm_of_eigen
    (m := m) (S := S) hSym hlambda.le hv
  have hsqrt_pos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  have hsqrt_ne : Real.sqrt lambda ≠ 0 := ne_of_gt hsqrt_pos
  rw [norm_smul]
  have hnorm_scalar : ‖(((Real.sqrt lambda)⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt lambda)⁻¹ := by
    exact RCLike.norm_of_nonneg (K := ℂ) (inv_nonneg.mpr hsqrt_pos.le)
  rw [hnorm_scalar, hnorm]
  field_simp [hsqrt_ne]

/-- The normalized map `lambda^{-1/2} C` on the positive eigenspace is a
conjugate-linear isometric involution. -/
noncomputable def takagiPositiveEigenspaceConjugation
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ}
    (hSym : S.transpose = S)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    takagiHermitianEigenspace m S lambda ≃ₗᵢ⋆[ℂ]
      takagiHermitianEigenspace m S lambda where
  toFun x := by
    refine ⟨(((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
      takagiConjugateLinearEuclideanMap m S (x : EuclideanSpace ℂ (Fin m)), ?_⟩
    exact (takagiHermitianEigenspace m S lambda).smul_mem _
      (takagiConjugateLinearMap_mem_eigenspace (m := m) (S := S) hSym x.2)
  invFun x := by
    refine ⟨(((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
      takagiConjugateLinearEuclideanMap m S (x : EuclideanSpace ℂ (Fin m)), ?_⟩
    exact (takagiHermitianEigenspace m S lambda).smul_mem _
      (takagiConjugateLinearMap_mem_eigenspace (m := m) (S := S) hSym x.2)
  left_inv := by
    intro x
    ext i
    change (((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
        takagiConjugateLinearMap m S
          (((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
            takagiConjugateLinearMap m S
              ((x : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ)))) i =
      ((x : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) i)
    rw [takagiConjugateLinearMap_smul]
    have hscale_star : star ((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) : ℂ) =
        ((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) : ℂ) := by
      exact Complex.conj_ofReal ((Real.sqrt lambda)⁻¹)
    rw [hscale_star]
    rw [← smul_assoc]
    have hsq := congrFun (takagiConjugateLinearMap_sq (m := m) (S := S) hSym)
      (x : Fin m → ℂ)
    rw [hsq, x.2]
    simp only [Pi.smul_apply]
    have hsqrt_pos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
    simp only [smul_eq_mul]
    have hscalar : (((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ)) * (lambda : ℂ)) = 1 := by
      have hsqrt_ne : Real.sqrt lambda ≠ 0 := ne_of_gt hsqrt_pos
      have hsqrt_sq : (Real.sqrt lambda) ^ 2 = lambda := by
        rw [Real.sq_sqrt hlambda.le]
      have hreal : ((Real.sqrt lambda)⁻¹ * (Real.sqrt lambda)⁻¹) * lambda =
          (1 : ℝ) := by
        field_simp [hsqrt_ne]
        nlinarith
      exact_mod_cast hreal
    rw [← mul_assoc, hscalar]
    simp
  right_inv := by
    intro x
    ext i
    change (((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
        takagiConjugateLinearMap m S
          (((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
            takagiConjugateLinearMap m S
              ((x : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ)))) i =
      ((x : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) i)
    rw [takagiConjugateLinearMap_smul]
    have hscale_star : star ((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) : ℂ) =
        ((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) : ℂ) := by
      exact Complex.conj_ofReal ((Real.sqrt lambda)⁻¹)
    rw [hscale_star]
    rw [← smul_assoc]
    have hsq := congrFun (takagiConjugateLinearMap_sq (m := m) (S := S) hSym)
      (x : Fin m → ℂ)
    rw [hsq, x.2]
    simp only [Pi.smul_apply]
    have hsqrt_pos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
    simp only [smul_eq_mul]
    have hscalar : (((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ)) * (lambda : ℂ)) = 1 := by
      have hsqrt_ne : Real.sqrt lambda ≠ 0 := ne_of_gt hsqrt_pos
      have hsqrt_sq : (Real.sqrt lambda) ^ 2 = lambda := by
        rw [Real.sq_sqrt hlambda.le]
      have hreal : ((Real.sqrt lambda)⁻¹ * (Real.sqrt lambda)⁻¹) * lambda =
          (1 : ℝ) := by
        field_simp [hsqrt_ne]
        nlinarith
      exact_mod_cast hreal
    rw [← mul_assoc, hscalar]
    simp
  map_add' := by
    intro x y
    ext i
    simp [takagiConjugateLinearEuclideanMap_add, smul_add]
  map_smul' := by
    intro c x
    ext i
    simp [takagiConjugateLinearEuclideanMap_smul, mul_comm, mul_assoc]
  norm_map' := by
    intro x
    change ‖(((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
        takagiConjugateLinearEuclideanMap m S (x : EuclideanSpace ℂ (Fin m))‖ =
      ‖(x : EuclideanSpace ℂ (Fin m))‖
    exact takagiConjugateLinearEuclideanMap_normalized_norm_of_eigen
      (m := m) (S := S) hSym hlambda x.2

/-- A fixed vector of the normalized positive-eigenspace conjugation satisfies
the unnormalized Takagi column equation. -/
theorem takagiConjugateLinearEuclideanMap_eq_sqrt_smul_of_positive_fixed
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (x : takagiHermitianEigenspace m S lambda)
    (hx : takagiPositiveEigenspaceConjugation (m := m) (S := S) hSym hlambda x = x) :
    takagiConjugateLinearEuclideanMap m S (x : EuclideanSpace ℂ (Fin m)) =
      (Real.sqrt lambda : ℂ) • (x : EuclideanSpace ℂ (Fin m)) := by
  have hval := congrArg (fun y : takagiHermitianEigenspace m S lambda =>
    (y : EuclideanSpace ℂ (Fin m))) hx
  change (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
      takagiConjugateLinearEuclideanMap m S (x : EuclideanSpace ℂ (Fin m)) =
    (x : EuclideanSpace ℂ (Fin m)) at hval
  have hsqrt_pos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  have hsqrt_ne : Real.sqrt lambda ≠ 0 := ne_of_gt hsqrt_pos
  have hscalar : ((Real.sqrt lambda : ℂ) * (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ)) = 1 := by
    have hreal : Real.sqrt lambda * (Real.sqrt lambda)⁻¹ = (1 : ℝ) := by
      field_simp [hsqrt_ne]
    exact_mod_cast hreal
  calc
    takagiConjugateLinearEuclideanMap m S (x : EuclideanSpace ℂ (Fin m)) =
        (1 : ℂ) • takagiConjugateLinearEuclideanMap m S
          (x : EuclideanSpace ℂ (Fin m)) := by
      simp
    _ = ((Real.sqrt lambda : ℂ) * (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ)) •
        takagiConjugateLinearEuclideanMap m S (x : EuclideanSpace ℂ (Fin m)) := by
      rw [hscalar]
    _ = (Real.sqrt lambda : ℂ) •
        ((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
          takagiConjugateLinearEuclideanMap m S (x : EuclideanSpace ℂ (Fin m))) := by
      rw [smul_smul]
    _ = (Real.sqrt lambda : ℂ) • (x : EuclideanSpace ℂ (Fin m)) := by
      rw [hval]

/-- The fixed orthonormal basis chosen inside a positive Hermitian-square
eigenspace, using the normalized Takagi conjugation. -/
noncomputable def takagiPositiveEigenspaceFixedBasis
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ (takagiHermitianEigenspace m S lambda))) ℂ
      (takagiHermitianEigenspace m S lambda) :=
  conjugationFixedComplexOrthonormalBasis
    (takagiPositiveEigenspaceConjugation (m := m) (S := S) hSym hlambda)
    (fun x =>
      (takagiPositiveEigenspaceConjugation
        (m := m) (S := S) hSym hlambda).left_inv x)

/-- The positive-eigenspace fixed basis is fixed by the normalized Takagi
conjugation. -/
theorem takagiPositiveEigenspaceFixedBasis_fixed
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (i :
      Fin (Module.finrank ℂ (takagiHermitianEigenspace m S lambda))) :
    takagiPositiveEigenspaceConjugation (m := m) (S := S) hSym hlambda
        (takagiPositiveEigenspaceFixedBasis (m := m) (S := S) hSym hlambda i) =
      takagiPositiveEigenspaceFixedBasis (m := m) (S := S) hSym hlambda i := by
  unfold takagiPositiveEigenspaceFixedBasis
  exact conjugationFixedComplexOrthonormalBasis_fixed
    (E := takagiHermitianEigenspace m S lambda)
    (takagiPositiveEigenspaceConjugation (m := m) (S := S) hSym hlambda)
    (fun x =>
      (takagiPositiveEigenspaceConjugation
        (m := m) (S := S) hSym hlambda).left_inv x)
    i

/-- The fixed orthonormal basis chosen in a positive Hermitian-square
eigenspace consists of Takagi columns with singular value `sqrt lambda`. -/
theorem takagiPositiveEigenspace_fixedBasis_col_eigen
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (i :
      Fin (Module.finrank ℂ (takagiHermitianEigenspace m S lambda))) :
    takagiConjugateLinearEuclideanMap m S
        ((takagiPositiveEigenspaceFixedBasis (m := m) (S := S) hSym hlambda i :
          takagiHermitianEigenspace m S lambda) :
          EuclideanSpace ℂ (Fin m)) =
      (Real.sqrt lambda : ℂ) •
        ((takagiPositiveEigenspaceFixedBasis (m := m) (S := S) hSym hlambda i :
          takagiHermitianEigenspace m S lambda) :
          EuclideanSpace ℂ (Fin m)) := by
  exact
    takagiConjugateLinearEuclideanMap_eq_sqrt_smul_of_positive_fixed
      (m := m) (S := S) (lambda := lambda) hSym hlambda
      (x := takagiPositiveEigenspaceFixedBasis (m := m) (S := S) hSym hlambda i)
      (takagiPositiveEigenspaceFixedBasis_fixed
        (m := m) (S := S) hSym hlambda i)

/-- Vectors in the zero eigenspace of `S * Sᴴ` are killed by the Takagi
conjugate-linear map. -/
theorem takagiConjugateLinearEuclideanMap_zero_eigenspace_eq_zero
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    {v : EuclideanSpace ℂ (Fin m)}
    (hv : (S * Sᴴ) *ᵥ (v : Fin m → ℂ) = 0) :
    takagiConjugateLinearEuclideanMap m S v = 0 := by
  ext i
  have hraw := takagiConjugateLinearMap_zero_eigenspace_eq_zero (m := m) (S := S) hSym hv
  have hi := congrFun hraw i
  simpa [takagiConjugateLinearEuclideanMap] using hi

/-- Vectors in the zero Hermitian-square eigenspace are Takagi columns with
singular value zero. -/
theorem takagiZeroEigenspace_col_eigen
    (m : ℕ) {S : Matrix (Fin m) (Fin m) ℂ} (hSym : S.transpose = S)
    (v : takagiHermitianEigenspace m S 0) :
    takagiConjugateLinearEuclideanMap m S (v : EuclideanSpace ℂ (Fin m)) =
      (0 : ℂ) • (v : EuclideanSpace ℂ (Fin m)) := by
  have hv0 : (S * Sᴴ) *ᵥ ((v : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) = 0 := by
    have hv := v.2
    change (S * Sᴴ) *ᵥ ((v : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) =
      (0 : ℂ) • (((v : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ)) at hv
    simpa using hv
  simpa using
    takagiConjugateLinearEuclideanMap_zero_eigenspace_eq_zero
      (m := m) (S := S) hSym (v := (v : EuclideanSpace ℂ (Fin m))) hv0

end BHW
