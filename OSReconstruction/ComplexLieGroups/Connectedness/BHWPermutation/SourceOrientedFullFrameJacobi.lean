import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameOrbit

/-!
# Jacobi derivative helpers for full-frame oriented coordinates

This file proves the actual Frechet-derivative packet for the full-frame
oriented map.  The Gram component is checked from the product rule for matrix
multiplication, and the determinant component is checked by reducing Jacobi's
formula to the derivative of `det(1 + tX)` at `t = 0`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- The matrix-entry projection as a continuous linear map. -/
noncomputable def matrixEntryCLM
    {D : Type} (i j : D) :
    Matrix D D ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℂ) i : Matrix D D ℂ →L[ℂ] D → ℂ)

/-- The determinant derivative obtained by differentiating the Leibniz
expansion term-by-term. -/
noncomputable def matrixDetExpansionFDerivCLM
    {D : Type} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) : Matrix D D ℂ →L[ℂ] ℂ :=
  ∑ σ : Equiv.Perm D,
    (σ.sign : ℂ) •
      ∑ k : D,
        (∏ i ∈ (Finset.univ : Finset D).erase k, A (σ i) i) •
          matrixEntryCLM (σ k) k

/-- Matrix trace as a continuous linear map. -/
noncomputable def matrixTraceCLM
    {D : Type} [Fintype D] :
    Matrix D D ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Matrix.trace X
      map_add' := by
        intro X Y
        simp [Matrix.trace_add]
      map_smul' := by
        intro c X
        simp [Matrix.trace_smul] }

/-- Left multiplication by a fixed matrix as a continuous linear map. -/
noncomputable def matrixMulLeftCLM
    {D : Type} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) :
    Matrix D D ℂ →L[ℂ] Matrix D D ℂ :=
  (ContinuousLinearMap.mul ℂ (Matrix D D ℂ)) A

/-- Jacobi's determinant differential in trace form. -/
noncomputable def matrixDetTraceFDerivCLM
    {D : Type} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) :
    Matrix D D ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => A.det * Matrix.trace (A⁻¹ * X)
      map_add' := by
        intro X Y
        simp [mul_add, Matrix.trace_add]
      map_smul' := by
        intro c X
        simp [Matrix.trace_smul, smul_eq_mul, mul_left_comm] }

/-- Frechet derivative of determinant in the raw Leibniz-expansion form. -/
theorem matrix_det_hasFDerivAt_expansion
    {D : Type} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) :
    HasFDerivAt
      (fun B : Matrix D D ℂ => B.det)
      (matrixDetExpansionFDerivCLM A) A := by
  have hsummand :
      ∀ σ : Equiv.Perm D, σ ∈ (Finset.univ : Finset (Equiv.Perm D)) →
        HasFDerivAt
          (fun B : Matrix D D ℂ =>
            (σ.sign : ℂ) * ∏ i : D, B (σ i) i)
          ((σ.sign : ℂ) •
            ∑ k : D,
              (∏ i ∈ (Finset.univ : Finset D).erase k, A (σ i) i) •
                matrixEntryCLM (σ k) k) A := by
    intro σ _hσ
    have hprod :
        HasFDerivAt
          (fun B : Matrix D D ℂ => ∏ i : D, B (σ i) i)
          (∑ k : D,
            (∏ j ∈ (Finset.univ : Finset D).erase k, A (σ j) j) •
              matrixEntryCLM (σ k) k) A := by
      simpa using
        (HasFDerivAt.finset_prod
          (u := (Finset.univ : Finset D))
          (g := fun i B => B (σ i) i)
          (g' := fun i => matrixEntryCLM (σ i) i)
          (x := A)
          (by
            intro i _hi
            simpa [matrixEntryCLM] using
              (matrixEntryCLM (σ i) i).hasFDerivAt (x := A)))
    simpa [smul_eq_mul] using hprod.const_mul (σ.sign : ℂ)
  have hsum :=
    HasFDerivAt.sum (u := (Finset.univ : Finset (Equiv.Perm D))) hsummand
  have hsum_fun :
      HasFDerivAt
        (fun B : Matrix D D ℂ =>
          ∑ σ : Equiv.Perm D, (σ.sign : ℂ) * ∏ i : D, B (σ i) i)
        (matrixDetExpansionFDerivCLM A) A := by
    refine (hsum.congr_of_eventuallyEq ?_).congr_fderiv ?_
    · filter_upwards with B
      simp
    · simp [matrixDetExpansionFDerivCLM]
  simpa [Matrix.det_apply'] using hsum_fun

/-- One-variable derivative of `t ↦ det(1 + tX)` at zero. -/
theorem matrix_det_one_add_hasDerivAt_trace
    {D : Type} [Fintype D] [DecidableEq D]
    (X : Matrix D D ℂ) :
    HasDerivAt (fun t : ℂ => (1 + t • X).det) (Matrix.trace X) 0 := by
  let XP : Matrix D D (Polynomial ℂ) :=
    X.map (Polynomial.C : ℂ → Polynomial ℂ)
  let p : Polynomial ℂ :=
    ((1 : Matrix D D (Polynomial ℂ)) + (Polynomial.X : Polynomial ℂ) • XP).det
  have hp : HasDerivAt (fun t : ℂ => Polynomial.eval t p)
      (Polynomial.eval 0 (Polynomial.derivative p)) 0 :=
    Polynomial.hasDerivAt p 0
  have hder :
      Polynomial.eval 0 (Polynomial.derivative p) = Matrix.trace X := by
    simpa [p, XP] using Matrix.derivative_det_one_add_X_smul (R := ℂ) X
  have hfun :
      (fun t : ℂ => Polynomial.eval t p) =
        fun t : ℂ => (1 + t • X).det := by
    ext t
    change (Polynomial.evalRingHom t)
        (((1 : Matrix D D (Polynomial ℂ)) +
          (Polynomial.X : Polynomial ℂ) • XP).det) =
      (1 + t • X).det
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [XP, RingHom.mapMatrix_apply]
      ring
    · simp [XP, RingHom.mapMatrix_apply, hij]
      ring
  simpa [hfun, hder] using hp

/-- Frechet derivative of determinant at the identity is trace. -/
theorem matrix_det_one_hasFDerivAt_trace
    {D : Type} [Fintype D] [DecidableEq D] :
    HasFDerivAt
      (fun B : Matrix D D ℂ => B.det)
      matrixTraceCLM (1 : Matrix D D ℂ) := by
  have hdet :=
    matrix_det_hasFDerivAt_expansion (1 : Matrix D D ℂ)
  have hclm :
      matrixDetExpansionFDerivCLM (1 : Matrix D D ℂ) =
        (matrixTraceCLM : Matrix D D ℂ →L[ℂ] ℂ) := by
    ext X
    have hline :
        HasDerivAt (fun t : ℂ => (1 : Matrix D D ℂ) + t • X) X 0 := by
      simpa using
        ((hasDerivAt_id (0 : ℂ)).smul_const X).const_add
          (1 : Matrix D D ℂ)
    have hcomp :=
      HasFDerivAt.comp_hasDerivAt_of_eq 0 hdet hline (by simp)
    have hpoly := matrix_det_one_add_hasDerivAt_trace X
    have hval :
        matrixDetExpansionFDerivCLM (1 : Matrix D D ℂ) X =
          Matrix.trace X :=
      hcomp.unique hpoly
    simpa [matrixTraceCLM] using hval
  exact hdet.congr_fderiv hclm

/-- Jacobi's formula for the Frechet derivative of determinant at an
invertible matrix. -/
theorem matrix_det_hasFDerivAt_trace
    {D : Type} [Fintype D] [DecidableEq D]
    {A : Matrix D D ℂ}
    (hA : IsUnit A.det) :
    HasFDerivAt
      (fun B : Matrix D D ℂ => B.det)
      (matrixDetTraceFDerivCLM A) A := by
  let Mat := Matrix D D ℂ
  let Ainv : Mat := A⁻¹
  have hleft :
      HasFDerivAt (fun B : Mat => Ainv * B)
        (matrixMulLeftCLM Ainv) A := by
    simpa [matrixMulLeftCLM, Mat, Ainv] using
      ((matrixMulLeftCLM Ainv).hasFDerivAt (x := A))
  have hone_at :
      HasFDerivAt (fun C : Mat => C.det) matrixTraceCLM (Ainv * A) := by
    simpa [Ainv, Matrix.nonsing_inv_mul A hA] using
      (matrix_det_one_hasFDerivAt_trace (D := D))
  have hcomp := hone_at.comp A hleft
  have hscaled :
      HasFDerivAt
        (fun B : Mat => A.det * (Ainv * B).det)
        (A.det • (matrixTraceCLM.comp (matrixMulLeftCLM Ainv))) A := by
    simpa [Function.comp_def, Ainv] using hcomp.const_mul A.det
  have hfun :
      (fun B : Mat => A.det * (Ainv * B).det) =
        fun B : Mat => B.det := by
    ext B
    have hdet_inv : A.det * (A⁻¹).det = 1 := by
      have h := congrArg Matrix.det (Matrix.mul_nonsing_inv A hA)
      simpa [Matrix.det_mul] using h
    calc
      A.det * (Ainv * B).det = A.det * ((A⁻¹).det * B.det) := by
        change A.det * (A⁻¹ * B).det = A.det * ((A⁻¹).det * B.det)
        rw [Matrix.det_mul]
      _ = B.det := by
        rw [← mul_assoc, hdet_inv, one_mul]
  have hclm :
      A.det • (matrixTraceCLM.comp (matrixMulLeftCLM Ainv)) =
        matrixDetTraceFDerivCLM A := by
    ext X
    simp [matrixTraceCLM, matrixMulLeftCLM, matrixDetTraceFDerivCLM, Ainv]
  exact
    (hscaled.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun B => by rw [hfun]))).congr_fderiv hclm

/-- Matrix transpose as a continuous linear map on square full-frame matrices. -/
noncomputable def sourceFullFrameTransposeCLM
    (d : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    (Matrix.transposeLinearEquiv (Fin (d + 1)) (Fin (d + 1)) ℂ ℂ).toLinearMap

/-- Linearized Gram component of `M ↦ M η Mᵀ`. -/
noncomputable def sourceFullFrameGramDifferentialCLM
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X =>
        X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
          M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose
      map_add' := by
        intro X Y
        ext a b
        simp [add_mul, mul_add, Matrix.transpose_add]
        abel
      map_smul' := by
        intro c X
        ext a b
        simp [smul_eq_mul]
        ring }

/-- The transpose map has derivative equal to itself. -/
theorem sourceFullFrameTranspose_hasFDerivAt
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    HasFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M.transpose)
      (sourceFullFrameTransposeCLM d) M0 := by
  simpa [sourceFullFrameTransposeCLM, Matrix.transposeLinearEquiv_apply] using
    (sourceFullFrameTransposeCLM d).hasFDerivAt (x := M0)

/-- Frechet derivative of the matrix-valued full-frame Gram map
`M ↦ M η Mᵀ`. -/
theorem sourceFullFrameGramMatrix_hasFDerivAt
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    HasFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        M * ComplexLorentzGroup.ηℂ (d := d) * M.transpose)
      (sourceFullFrameGramDifferentialCLM d M0) M0 := by
  let Mat := Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  let eta : Mat := ComplexLorentzGroup.ηℂ (d := d)
  have hf : HasFDerivAt (fun M : Mat => M * eta)
      (((ContinuousLinearMap.mul ℂ Mat).flip eta)) M0 := by
    simpa [Mat, eta] using
      ((1 : Mat →L[ℂ] Mat).hasFDerivAt (x := M0)).mul_const' eta
  have hg : HasFDerivAt (fun M : Mat => M.transpose)
      (sourceFullFrameTransposeCLM d) M0 := by
    simpa [sourceFullFrameTransposeCLM, Matrix.transposeLinearEquiv_apply, Mat] using
      (sourceFullFrameTransposeCLM d).hasFDerivAt (x := M0)
  have hmul := hf.mul' hg
  refine hmul.congr_fderiv ?_
  ext X a b
  simp [sourceFullFrameGramDifferentialCLM, sourceFullFrameTransposeCLM,
    Matrix.transposeLinearEquiv_apply, smul_eq_mul, Mat, eta]
  ring

/-- Frechet derivative of `sourceFullFrameGram`. -/
theorem sourceFullFrameGram_hasFDerivAt
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    HasFDerivAt
      (sourceFullFrameGram d)
      (sourceFullFrameGramDifferentialCLM d M0) M0 := by
  apply
    (sourceFullFrameGramMatrix_hasFDerivAt d M0).congr_of_eventuallyEq
  filter_upwards with M
  ext a b
  change (sourceFullFrameGram d M) a b =
    (M * ComplexLorentzGroup.ηℂ (d := d) * M.transpose) a b
  rw [← sourceFullFrameGram_eq_mul_eta_transpose d M]
  rfl

/-- Frechet derivative of the determinant coordinate of a full frame. -/
theorem sourceFullFrameDet_hasFDerivAt
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    HasFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M.det)
      (matrixDetTraceFDerivCLM M0) M0 :=
  matrix_det_hasFDerivAt_trace hM0

/-- Frechet derivative of the full oriented full-frame coordinate map. -/
theorem sourceFullFrameOrientedGram_hasFDerivAt
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    HasFDerivAt
      (sourceFullFrameOrientedGramCoord d)
      (sourceFullFrameOrientedDifferentialCLM d M0) M0 := by
  have hGram := sourceFullFrameGram_hasFDerivAt d M0
  have hDet := sourceFullFrameDet_hasFDerivAt (d := d) hM0
  have hprod := hGram.prodMk hDet
  have hprod' :
      HasFDerivAt
        (sourceFullFrameOrientedGramCoord d)
        ((sourceFullFrameGramDifferentialCLM d M0).prod
          (matrixDetTraceFDerivCLM M0)) M0 := by
    simpa [sourceFullFrameOrientedGramCoord,
      SourceFullFrameOrientedGramData.toCoord, sourceFullFrameOrientedGram]
      using hprod
  refine hprod'.congr_fderiv ?_
  ext X a b
  · change
      (X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
          M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose) a b =
        (sourceFullFrameOrientedDifferential d M0 X).1 a b
    rfl
  · change
      M0.det * Matrix.trace (M0⁻¹ * X) =
        (sourceFullFrameOrientedDifferential d M0 X).2
    rfl

/-- Strict Frechet derivative of the full oriented full-frame coordinate map.
This is the strict-derivative form needed by the selected-frame product-chart
construction. -/
theorem sourceFullFrameOrientedGram_hasStrictFDerivAt
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    HasStrictFDerivAt
      (sourceFullFrameOrientedGramCoord d)
      (sourceFullFrameOrientedDifferentialCLM d M0) M0 := by
  have hcd : ContDiffAt ℂ ⊤ (sourceFullFrameOrientedGramCoord d) M0 :=
    (contDiff_sourceFullFrameOrientedGramCoord d).contDiffAt
  have hstrict := hcd.hasStrictFDerivAt (by simp)
  have hfderiv := (sourceFullFrameOrientedGram_hasFDerivAt (d := d) hM0).fderiv
  exact hstrict.congr_fderiv hfderiv

/-- Trace-form Frechet derivative of the oriented hypersurface equation. -/
theorem sourceFullFrameOrientedEquation_hasFDerivAt_trace
    (d : ℕ)
    {H0 : SourceFullFrameOrientedGramData d}
    (hGram : IsUnit (Matrix.of H0.gram).det) :
    HasFDerivAt
      (sourceFullFrameOrientedEquation d)
      (sourceFullFrameOrientedEquationDerivCLM d H0) H0.toCoord := by
  let G0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.of H0.gram
  let Fst : SourceFullFrameOrientedCoord d →L[ℂ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    ContinuousLinearMap.fst ℂ (Fin (d + 1) → Fin (d + 1) → ℂ) ℂ
  let Snd : SourceFullFrameOrientedCoord d →L[ℂ] ℂ :=
    ContinuousLinearMap.snd ℂ (Fin (d + 1) → Fin (d + 1) → ℂ) ℂ
  have hgramMap : HasFDerivAt
      (fun H : SourceFullFrameOrientedCoord d => Matrix.of H.1)
      Fst H0.toCoord := by
    simpa [Fst] using Fst.hasFDerivAt (x := H0.toCoord)
  have hdetBase : HasFDerivAt
      (fun G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => G.det)
      (matrixDetTraceFDerivCLM G0) G0 := by
    exact matrix_det_hasFDerivAt_trace (A := G0) hGram
  have hdet : HasFDerivAt
      (fun H : SourceFullFrameOrientedCoord d => (Matrix.of H.1).det)
      ((matrixDetTraceFDerivCLM G0).comp Fst) H0.toCoord := by
    simpa [G0] using hdetBase.comp (x := H0.toCoord) hgramMap
  have hsnd : HasFDerivAt (fun H : SourceFullFrameOrientedCoord d => H.2)
      Snd H0.toCoord := by
    simpa [Snd] using Snd.hasFDerivAt (x := H0.toCoord)
  have hsq0 : HasFDerivAt
      (fun H : SourceFullFrameOrientedCoord d => H.2 ^ 2)
      (H0.det • Snd + H0.det • Snd) H0.toCoord := by
    simpa [pow_two, SourceFullFrameOrientedGramData.toCoord] using hsnd.mul hsnd
  have hsq : HasFDerivAt (fun H : SourceFullFrameOrientedCoord d => H.2 ^ 2)
      (((2 : ℂ) * H0.det) • Snd) H0.toCoord :=
    hsq0.congr_fderiv (by
      apply ContinuousLinearMap.ext
      intro Y
      simp [two_mul]
      ring)
  have hterm : HasFDerivAt
      (fun H : SourceFullFrameOrientedCoord d => minkowskiMetricDet d * H.2 ^ 2)
      (minkowskiMetricDet d • (((2 : ℂ) * H0.det) • Snd)) H0.toCoord := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hsq.const_mul (minkowskiMetricDet d)
  have hsub : HasFDerivAt
      (fun H : SourceFullFrameOrientedCoord d =>
        (Matrix.of H.1).det - minkowskiMetricDet d * H.2 ^ 2)
      (((matrixDetTraceFDerivCLM G0).comp Fst) -
        (minkowskiMetricDet d • (((2 : ℂ) * H0.det) • Snd))) H0.toCoord :=
    hdet.sub hterm
  have hsub' : HasFDerivAt
      (sourceFullFrameOrientedEquation d)
      (((matrixDetTraceFDerivCLM G0).comp Fst) -
        (minkowskiMetricDet d • (((2 : ℂ) * H0.det) • Snd))) H0.toCoord := by
    refine hsub.congr_of_eventuallyEq ?_
    filter_upwards with H
    rfl
  have hclm :
      ((matrixDetTraceFDerivCLM G0).comp Fst) -
        (minkowskiMetricDet d • (((2 : ℂ) * H0.det) • Snd)) =
      sourceFullFrameOrientedEquationDerivCLM d H0 := by
    apply ContinuousLinearMap.ext
    intro Y
    change
      (Matrix.of H0.gram).det *
            Matrix.trace ((Matrix.of H0.gram)⁻¹ * Matrix.of Y.1) -
          minkowskiMetricDet d * ((2 : ℂ) * H0.det * Y.2) =
        (Matrix.of H0.gram).det *
            Matrix.trace ((Matrix.of H0.gram)⁻¹ * Matrix.of Y.1) -
          (2 : ℂ) * minkowskiMetricDet d * H0.det * Y.2
    ring
  exact hsub'.congr_fderiv hclm

/-- The full-frame oriented tangent space is the kernel of the actual Frechet
derivative of the oriented hypersurface equation inside symmetric coordinates. -/
theorem mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_fderiv_eq_zero
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {Y : SourceFullFrameOrientedCoord d} :
    Y ∈ sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) ↔
      Y ∈ sourceFullFrameSymmetricCoordSubmodule d ∧
        (fderiv ℂ (sourceFullFrameOrientedEquation d)
          (sourceFullFrameOrientedGramCoord d M0)) Y = 0 := by
  have hGramUnit :
      IsUnit (Matrix.of (sourceFullFrameOrientedGram d M0).gram).det := by
    simpa [sourceFullFrameOrientedGram] using
      sourceFullFrameGram_det_isUnit_of_frame_det_isUnit (d := d) hM0
  have hf :=
    (sourceFullFrameOrientedEquation_hasFDerivAt_trace (d := d)
      (H0 := sourceFullFrameOrientedGram d M0) hGramUnit).fderiv
  change
    Y ∈ sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) ↔
      Y ∈ sourceFullFrameSymmetricCoordSubmodule d ∧
        (fderiv ℂ (sourceFullFrameOrientedEquation d)
          (sourceFullFrameOrientedGram d M0).toCoord) Y = 0
  rw [hf]
  exact mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_deriv_eq_zero

@[simp]
theorem sourceFullFrameGaugeSliceMap_zero
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    sourceFullFrameGaugeSliceMap d M0 S 0 =
      sourceFullFrameOrientedGramCoord d M0 := by
  simp [sourceFullFrameGaugeSliceMap]

/-- Every point of the full-frame gauge-slice map is by definition in the
full-frame oriented image variety. -/
theorem sourceFullFrameGaugeSliceMap_mem_varietyCoord
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (X : S.slice) :
    sourceFullFrameGaugeSliceMap d M0 S X ∈
      sourceFullFrameOrientedGramVarietyCoord d := by
  exact ⟨M0 + (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), rfl⟩

/-- Every point of the full-frame gauge-slice map satisfies the oriented
hypersurface equation. -/
theorem sourceFullFrameGaugeSliceMap_mem_hypersurface
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (X : S.slice) :
    sourceFullFrameGaugeSliceMap d M0 S X ∈
      sourceFullFrameOrientedHypersurfaceCoord d :=
  sourceFullFrameOrientedGramVarietyCoord_subset_hypersurface d
    (sourceFullFrameGaugeSliceMap_mem_varietyCoord d M0 S X)

/-- Frechet derivative of the full-frame gauge-slice map at the slice origin. -/
theorem sourceFullFrameGaugeSliceMap_hasFDerivAt
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    HasFDerivAt
      (sourceFullFrameGaugeSliceMap d M0 S)
      ((sourceFullFrameOrientedDifferentialCLM d M0).comp S.slice.subtypeL) 0 := by
  let trans : S.slice → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    fun X => M0 + (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
  have htranslate : HasFDerivAt trans S.slice.subtypeL 0 := by
    dsimp [trans]
    have h0 :=
      (hasFDerivAt_const (x := (0 : S.slice)) (c := M0)).add
        S.slice.subtypeL.hasFDerivAt
    have h1 : HasFDerivAt
        (fun X : S.slice =>
          M0 + (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ))
        (0 + S.slice.subtypeL) 0 := by
      convert h0 using 1
    refine h1.congr_fderiv ?_
    ext X a b
    simp
  have hmain0 : HasFDerivAt (sourceFullFrameOrientedGramCoord d)
      (sourceFullFrameOrientedDifferentialCLM d M0) (trans 0) := by
    dsimp [trans]
    simpa using sourceFullFrameOrientedGram_hasFDerivAt (d := d) hM0
  have hcomp : HasFDerivAt ((sourceFullFrameOrientedGramCoord d) ∘ trans)
      ((sourceFullFrameOrientedDifferentialCLM d M0).comp S.slice.subtypeL) 0 :=
    hmain0.comp (x := 0) htranslate
  simpa [sourceFullFrameGaugeSliceMap, trans, Function.comp_def] using hcomp

/-- Strict derivative form of the full-frame gauge-slice map, suitable for
Mathlib's finite-dimensional inverse/implicit-function APIs. -/
theorem sourceFullFrameGaugeSliceMap_hasStrictFDerivAt
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    HasStrictFDerivAt
      (sourceFullFrameGaugeSliceMap d M0 S)
      ((sourceFullFrameOrientedDifferentialCLM d M0).comp S.slice.subtypeL) 0 := by
  have hcd : ContDiffAt ℂ ⊤ (sourceFullFrameGaugeSliceMap d M0 S) 0 :=
    (contDiff_sourceFullFrameGaugeSliceMap d M0 S).contDiffAt
  have hstrict := hcd.hasStrictFDerivAt (by simp)
  have hfderiv := (sourceFullFrameGaugeSliceMap_hasFDerivAt (d := d) hM0 S).fderiv
  exact hstrict.congr_fderiv hfderiv

/-- The computed Frechet derivative of the gauge-slice map. -/
theorem sourceFullFrameGaugeSliceMap_fderiv_eq
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    fderiv ℂ (sourceFullFrameGaugeSliceMap d M0 S) 0 =
      (sourceFullFrameOrientedDifferentialCLM d M0).comp S.slice.subtypeL :=
  (sourceFullFrameGaugeSliceMap_hasFDerivAt (d := d) hM0 S).fderiv

/-- The Frechet derivative of the gauge-slice map has exactly the oriented
hypersurface tangent space as its range. -/
theorem sourceFullFrameGaugeSliceMap_fderiv_range_eq_tangent
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    LinearMap.range
        (fderiv ℂ (sourceFullFrameGaugeSliceMap d M0 S) 0).toLinearMap =
      sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) := by
  rw [sourceFullFrameGaugeSliceMap_fderiv_eq (d := d) hM0 S]
  simpa using sourceFullFrameSlice_restricted_range_eq_tangent (d := d) S

/-- The Frechet derivative of the gauge-slice map is injective. -/
theorem sourceFullFrameGaugeSliceMap_fderiv_kernel_eq_bot
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    LinearMap.ker
        (fderiv ℂ (sourceFullFrameGaugeSliceMap d M0 S) 0).toLinearMap =
      ⊥ := by
  rw [sourceFullFrameGaugeSliceMap_fderiv_eq (d := d) hM0 S]
  ext X
  constructor
  · intro hX
    rw [LinearMap.mem_ker] at hX
    have hiso :
        S.differential_iso X =
          (0 : sourceFullFrameOrientedTangentSpace d
            (sourceFullFrameOrientedGram d M0)) := by
      apply Subtype.ext
      have h := S.differential_iso_eq X
      simpa [h] using hX
    have hiso' : S.differential_iso X = S.differential_iso 0 := by
      simpa using hiso
    have hX0 : X = 0 := S.differential_iso.injective hiso'
    simp [hX0]
  · intro hX
    rw [Submodule.mem_bot] at hX
    subst X
    simp

end BHW
