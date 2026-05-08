import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedCauchyBinet

/-!
# Concrete source/dot tuple transport for oriented coordinates

This file records the finite determinant-scale facts behind the source-to-dot
invariant-coordinate transport.  The linear equivalence
`complexMinkowskiToDotLinearEquiv` sends the complex Minkowski bilinear form to
the ordinary dot form.  On full-frame determinants it multiplies selected
volumes by the determinant of the diagonal coordinate scale; the contravariant
coordinate-ring map therefore uses the inverse determinant scale.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Determinant scale of `complexMinkowskiToDotLinearEquiv d`, written as the
finite product of its diagonal coordinate scales. -/
def sourceMinkowskiToDotDetScale (d : ℕ) : ℂ :=
  ∏ μ : Fin (d + 1), complexMinkowskiDotScale d μ

/-- Determinant scale of the inverse of `complexMinkowskiToDotLinearEquiv d`. -/
def sourceMinkowskiToDotInvDetScale (d : ℕ) : ℂ :=
  ∏ μ : Fin (d + 1), complexMinkowskiDotInvScale d μ

/-- The inverse determinant scale times the forward determinant scale is one. -/
theorem sourceMinkowskiToDotInvDetScale_mul_detScale
    (d : ℕ) :
    sourceMinkowskiToDotInvDetScale d *
      sourceMinkowskiToDotDetScale d = 1 := by
  simp [sourceMinkowskiToDotInvDetScale, sourceMinkowskiToDotDetScale,
    ← Finset.prod_mul_distrib, complexMinkowskiDotInvScale_mul_scale]

/-- The forward determinant scale times the inverse determinant scale is one. -/
theorem sourceMinkowskiToDotDetScale_mul_invDetScale
    (d : ℕ) :
    sourceMinkowskiToDotDetScale d *
      sourceMinkowskiToDotInvDetScale d = 1 := by
  rw [mul_comm]
  exact sourceMinkowskiToDotInvDetScale_mul_detScale d

/-- The two Minkowski-signature conventions agree after coercion to `ℂ`. -/
theorem metricSignature_eq_minkowskiSignature_complex
    (d : ℕ) (μ : Fin (d + 1)) :
    (MinkowskiSpace.metricSignature d μ : ℂ) =
      (minkowskiSignature d μ : ℂ) := by
  by_cases hμ : μ = 0 <;>
    simp [MinkowskiSpace.metricSignature, minkowskiSignature, hμ]

/-- The square of the forward determinant scale is the Minkowski metric
determinant. -/
theorem sourceMinkowskiToDotDetScale_mul_self
    (d : ℕ) :
    sourceMinkowskiToDotDetScale d *
      sourceMinkowskiToDotDetScale d = minkowskiMetricDet d := by
  simp [sourceMinkowskiToDotDetScale, minkowskiMetricDet,
    ComplexLorentzGroup.ηℂ, Matrix.det_diagonal, ← Finset.prod_mul_distrib,
    complexMinkowskiDotScale_sq, metricSignature_eq_minkowskiSignature_complex]

/-- The square of the inverse determinant scale is also the Minkowski metric
determinant. -/
theorem sourceMinkowskiToDotInvDetScale_mul_self
    (d : ℕ) :
    sourceMinkowskiToDotInvDetScale d *
      sourceMinkowskiToDotInvDetScale d = minkowskiMetricDet d := by
  simp [sourceMinkowskiToDotInvDetScale, minkowskiMetricDet,
    ComplexLorentzGroup.ηℂ, Matrix.det_diagonal, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro μ _hμ
  by_cases hμ0 : μ = 0 <;>
    simp [complexMinkowskiDotInvScale, minkowskiSignature, hμ0]

/-- The source Cauchy-Binet metric factor cancels the two inverse determinant
scales in the standard-dot coordinate direction. -/
theorem minkowskiMetricDet_mul_invDetScale_mul_invDetScale
    (d : ℕ) :
    minkowskiMetricDet d * sourceMinkowskiToDotInvDetScale d *
      sourceMinkowskiToDotInvDetScale d = 1 := by
  calc
    minkowskiMetricDet d * sourceMinkowskiToDotInvDetScale d *
        sourceMinkowskiToDotInvDetScale d
        =
          minkowskiMetricDet d *
            (sourceMinkowskiToDotInvDetScale d *
              sourceMinkowskiToDotInvDetScale d) := by
          ring
    _ = minkowskiMetricDet d * minkowskiMetricDet d := by
          rw [sourceMinkowskiToDotInvDetScale_mul_self]
    _ = 1 := minkowskiMetricDet_mul_self d

/-- The determinant scale of `complexMinkowskiToDotLinearEquiv d` is nonzero. -/
theorem sourceMinkowskiToDotDetScale_ne_zero
    (d : ℕ) :
    sourceMinkowskiToDotDetScale d ≠ 0 := by
  rw [sourceMinkowskiToDotDetScale, Finset.prod_ne_zero_iff]
  intro μ _hμ
  by_cases hμ0 : μ = 0 <;>
    simp [complexMinkowskiDotScale, hμ0]

/-- The determinant scale of `(complexMinkowskiToDotLinearEquiv d).symm` is
nonzero. -/
theorem sourceMinkowskiToDotInvDetScale_ne_zero
    (d : ℕ) :
    sourceMinkowskiToDotInvDetScale d ≠ 0 := by
  rw [sourceMinkowskiToDotInvDetScale, Finset.prod_ne_zero_iff]
  intro μ _hμ
  by_cases hμ0 : μ = 0 <;>
    simp [complexMinkowskiDotInvScale, hμ0]

/-- Pulling a standard-dot tuple back by
`(complexMinkowskiToDotLinearEquiv d).symm` turns the source Minkowski Gram
matrix into the ordinary dot Gram matrix. -/
theorem sourceMinkowskiGram_after_complexMinkowskiToDotLinearEquiv_symm
    (d n : ℕ)
    (y : Fin n → Fin (d + 1) → ℂ) :
    sourceMinkowskiGram d n
        (fun i => (complexMinkowskiToDotLinearEquiv d).symm (y i)) =
      sourceComplexDotGram (d + 1) n y := by
  rw [sourceMinkowskiGram_eq_dotGram_after_equiv]
  congr
  ext i μ
  simp [complexMinkowskiToDotLinearEquiv]
  calc
    complexMinkowskiDotScale d μ *
        (complexMinkowskiDotInvScale d μ * y i μ)
        =
          (complexMinkowskiDotInvScale d μ *
            complexMinkowskiDotScale d μ) * y i μ := by
            ring
    _ = y i μ := by
          rw [complexMinkowskiDotInvScale_mul_scale]
          ring

/-- Applying `complexMinkowskiToDotLinearEquiv d` to a source tuple multiplies
each selected full-frame determinant by the forward determinant scale. -/
theorem standardFullFrameDet_after_complexMinkowskiToDotLinearEquiv
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Matrix.det
        (fun a μ : Fin (d + 1) =>
          complexMinkowskiToDotLinearEquiv d (z (ι a)) μ) =
      sourceMinkowskiToDotDetScale d * sourceFullFrameDet d n ι z := by
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι z
  let S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    Matrix.diagonal (complexMinkowskiDotScale d)
  have hmat :
      (fun a μ : Fin (d + 1) =>
          complexMinkowskiToDotLinearEquiv d (z (ι a)) μ) =
        M * S := by
    ext a μ
    simp [M, S, sourceFullFrameMatrix, Matrix.mul_apply,
      Matrix.diagonal, mul_comm]
  rw [hmat]
  simp [M, S, sourceMinkowskiToDotDetScale, sourceFullFrameDet,
    Matrix.det_mul, mul_comm]

/-- Pulling a standard-dot tuple back by
`(complexMinkowskiToDotLinearEquiv d).symm` multiplies each selected
full-frame determinant by the inverse determinant scale. -/
theorem sourceFullFrameDet_after_complexMinkowskiToDotLinearEquiv_symm
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (y : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameDet d n ι
        (fun i => (complexMinkowskiToDotLinearEquiv d).symm (y i)) =
      sourceMinkowskiToDotInvDetScale d *
        Matrix.det (fun a μ : Fin (d + 1) => y (ι a) μ) := by
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    fun a μ => y (ι a) μ
  let S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    Matrix.diagonal (complexMinkowskiDotInvScale d)
  have hmat :
      (fun a μ : Fin (d + 1) =>
          (complexMinkowskiToDotLinearEquiv d).symm (y (ι a)) μ) =
        M * S := by
    ext a μ
    simp [M, S, complexMinkowskiToDotLinearEquiv, Matrix.mul_apply,
      Matrix.diagonal, mul_comm]
  unfold sourceFullFrameDet sourceFullFrameMatrix
  rw [hmat]
  simp [M, S, sourceMinkowskiToDotInvDetScale, Matrix.det_mul, mul_comm]

end BHW
