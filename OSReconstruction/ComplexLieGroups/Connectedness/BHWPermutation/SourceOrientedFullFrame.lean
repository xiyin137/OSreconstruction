import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented
import OSReconstruction.ComplexLieGroups.MatrixLieGroup

/-!
# Full-frame oriented source coordinates

This file starts the finite-dimensional full-frame coordinate layer used by the
source-oriented BHW local-chart route.  The objects here are deliberately
low-level: the full-frame Gram/determinant coordinates, their symmetric
coordinate subspace, the determinant-nonzero sheet, and the bridge from a
selected source frame to the ambient `SourceOrientedGramData`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

variable {d n : ℕ}

/-- The Minkowski Gram matrix of an ordered full frame. -/
def sourceFullFrameGram (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Fin (d + 1) → Fin (d + 1) → ℂ :=
  fun a b =>
    ∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ : ℂ) * M a μ * M b μ

@[simp]
theorem sourceFullFrameGram_apply
    (d : ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (a b : Fin (d + 1)) :
    sourceFullFrameGram d M a b =
      ∑ μ : Fin (d + 1),
        (MinkowskiSpace.metricSignature d μ : ℂ) * M a μ * M b μ :=
  rfl

/-- Full-frame Gram coordinates are symmetric. -/
theorem sourceFullFrameGram_symm
    (d : ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (a b : Fin (d + 1)) :
    sourceFullFrameGram d M a b =
      sourceFullFrameGram d M b a := by
  simp [sourceFullFrameGram, mul_comm, mul_left_comm]

/-- Matrix form of the full-frame Gram map:
`sourceFullFrameGram M = M * η * Mᵀ`. -/
theorem sourceFullFrameGram_eq_mul_eta_transpose
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix.of (sourceFullFrameGram d M) =
      M * ComplexLorentzGroup.ηℂ (d := d) * M.transpose := by
  ext a b
  simp [sourceFullFrameGram, Matrix.mul_apply, ComplexLorentzGroup.ηℂ,
    Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro μ _
  rw [show LorentzLieGroup.minkowskiSignature d μ =
      MinkowskiSpace.metricSignature d μ from rfl]
  ring_nf

/-- The selected source full-frame matrix has the selected Gram block as its
full-frame Gram matrix. -/
theorem sourceFullFrameGram_sourceFullFrameMatrix
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameGram d (sourceFullFrameMatrix d n ι z) =
      fun a b => sourceMinkowskiGram d n z (ι a) (ι b) := by
  ext a b
  simp [sourceFullFrameGram, sourceFullFrameMatrix, sourceMinkowskiGram]

/-- Continuity of the full-frame Gram map. -/
theorem continuous_sourceFullFrameGram (d : ℕ) :
    Continuous (sourceFullFrameGram d) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  exact continuous_finset_sum _ fun μ _ => by
    have haμ :
        Continuous
          (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
            M a μ) :=
      continuous_apply_apply a μ
    have hbμ :
        Continuous
          (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
            M b μ) :=
      continuous_apply_apply b μ
    simpa [mul_assoc] using (continuous_const.mul haμ).mul hbμ

/-- Matrix entry projections are smooth for the matrix norm used in this
project. -/
theorem contDiff_matrix_apply_apply
    (d : ℕ) (a b : Fin (d + 1)) :
    ContDiff ℂ ⊤
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M a b) := by
  apply IsBoundedLinearMap.contDiff
  refine ⟨⟨?_, ?_⟩, 1, one_pos, fun M => ?_⟩
  · intro M N
    rfl
  · intro c M
    rfl
  · rw [one_mul]
    have h1 : ‖M a b‖₊ ≤ ∑ j : Fin (d + 1), ‖M a j‖₊ :=
      Finset.single_le_sum (f := fun j => ‖M a j‖₊)
        (fun _ _ => zero_le') (Finset.mem_univ b)
    have h2 : (∑ j : Fin (d + 1), ‖M a j‖₊) ≤ ‖M‖₊ := by
      rw [Matrix.linfty_opNNNorm_def]
      exact
        Finset.le_sup
          (f := fun i : Fin (d + 1) =>
            ∑ j : Fin (d + 1), ‖M i j‖₊)
          (Finset.mem_univ a)
    exact_mod_cast h1.trans h2

/-- The full-frame Gram map is smooth. -/
theorem contDiff_sourceFullFrameGram (d : ℕ) :
    ContDiff ℂ ⊤ (sourceFullFrameGram d) := by
  rw [contDiff_pi]
  intro a
  rw [contDiff_pi]
  intro b
  unfold sourceFullFrameGram
  apply ContDiff.sum
  intro μ _
  exact
    ((contDiff_const.mul (contDiff_matrix_apply_apply d a μ)).mul
      (contDiff_matrix_apply_apply d b μ))

/-- The full-frame Gram map is complex differentiable. -/
theorem differentiable_sourceFullFrameGram (d : ℕ) :
    Differentiable ℂ (sourceFullFrameGram d) :=
  (contDiff_sourceFullFrameGram d).differentiable (by simp)

/-- Full-frame oriented Gram data: Gram matrix plus the oriented determinant. -/
structure SourceFullFrameOrientedGramData (d : ℕ) where
  gram : Fin (d + 1) → Fin (d + 1) → ℂ
  det : ℂ

namespace SourceFullFrameOrientedGramData

/-- Product-coordinate model for full-frame oriented Gram data. -/
abbrev Coord (d : ℕ) :=
  (Fin (d + 1) → Fin (d + 1) → ℂ) × ℂ

/-- Convert structured full-frame data to its product coordinates. -/
def toCoord (H : SourceFullFrameOrientedGramData d) : Coord d :=
  (H.gram, H.det)

/-- Convert product coordinates to structured full-frame data. -/
def ofCoord (H : Coord d) : SourceFullFrameOrientedGramData d where
  gram := H.1
  det := H.2

@[simp]
theorem toCoord_fst (H : SourceFullFrameOrientedGramData d) :
    H.toCoord.1 = H.gram :=
  rfl

@[simp]
theorem toCoord_snd (H : SourceFullFrameOrientedGramData d) :
    H.toCoord.2 = H.det :=
  rfl

@[simp]
theorem ofCoord_toCoord (H : SourceFullFrameOrientedGramData d) :
    ofCoord H.toCoord = H := by
  cases H
  rfl

@[simp]
theorem toCoord_ofCoord (H : Coord d) :
    (ofCoord H).toCoord = H := by
  cases H
  rfl

end SourceFullFrameOrientedGramData

/-- The concrete product-coordinate model used for full-frame calculations. -/
abbrev SourceFullFrameOrientedCoord (d : ℕ) :=
  SourceFullFrameOrientedGramData.Coord d

/-- Full-frame oriented data and its product coordinate model are equivalent. -/
def sourceFullFrameOrientedCoordEquiv
    (d : ℕ) :
    SourceFullFrameOrientedGramData d ≃
      SourceFullFrameOrientedCoord d where
  toFun := SourceFullFrameOrientedGramData.toCoord
  invFun := SourceFullFrameOrientedGramData.ofCoord
  left_inv := SourceFullFrameOrientedGramData.ofCoord_toCoord
  right_inv := SourceFullFrameOrientedGramData.toCoord_ofCoord

/-- The full-frame oriented invariant. -/
def sourceFullFrameOrientedGram
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    SourceFullFrameOrientedGramData d where
  gram := sourceFullFrameGram d M
  det := M.det

/-- The image variety of full-frame oriented invariants. -/
def sourceFullFrameOrientedGramVariety
    (d : ℕ) : Set (SourceFullFrameOrientedGramData d) :=
  Set.range (sourceFullFrameOrientedGram d)

/-- The full-frame oriented invariant in product coordinates. -/
def sourceFullFrameOrientedGramCoord
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    SourceFullFrameOrientedCoord d :=
  (sourceFullFrameOrientedGram d M).toCoord

@[simp]
theorem sourceFullFrameOrientedGramCoord_fst
    (d : ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    (sourceFullFrameOrientedGramCoord d M).1 =
      sourceFullFrameGram d M :=
  rfl

@[simp]
theorem sourceFullFrameOrientedGramCoord_snd
    (d : ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    (sourceFullFrameOrientedGramCoord d M).2 = M.det :=
  rfl

/-- The full-frame oriented image variety in product coordinates. -/
def sourceFullFrameOrientedGramVarietyCoord
    (d : ℕ) : Set (SourceFullFrameOrientedCoord d) :=
  Set.range (sourceFullFrameOrientedGramCoord d)

/-- The coordinate full-frame variety is the product-coordinate image of the
structured full-frame variety. -/
theorem sourceFullFrameOrientedGramVarietyCoord_eq_image
    (d : ℕ) :
    sourceFullFrameOrientedGramVarietyCoord d =
      ((fun H : SourceFullFrameOrientedGramData d => H.toCoord) ''
        sourceFullFrameOrientedGramVariety d) := by
  ext H
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨sourceFullFrameOrientedGram d M, ⟨M, rfl⟩, rfl⟩
  · rintro ⟨Hdata, ⟨M, rfl⟩, rfl⟩
    exact ⟨M, rfl⟩

/-- Continuity of the full-frame oriented invariant in product coordinates. -/
theorem continuous_sourceFullFrameOrientedGramCoord
    (d : ℕ) :
    Continuous (sourceFullFrameOrientedGramCoord d) := by
  change
    Continuous
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        (sourceFullFrameGram d M, M.det))
  exact
    (continuous_sourceFullFrameGram d).prodMk
      (continuous_id.matrix_det :
        Continuous
          (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M.det))

/-- Smoothness of the full-frame oriented invariant in product coordinates. -/
theorem contDiff_sourceFullFrameOrientedGramCoord
    (d : ℕ) :
    ContDiff ℂ ⊤ (sourceFullFrameOrientedGramCoord d) := by
  change
    ContDiff ℂ ⊤
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        (sourceFullFrameGram d M, M.det))
  exact
    ContDiff.prodMk
      (contDiff_sourceFullFrameGram d)
      (by
        simpa using MatrixLieGroup.contDiff_det (d + 1))

/-- The full-frame oriented invariant in product coordinates is complex
differentiable. -/
theorem differentiable_sourceFullFrameOrientedGramCoord
    (d : ℕ) :
    Differentiable ℂ (sourceFullFrameOrientedGramCoord d) :=
  (contDiff_sourceFullFrameOrientedGramCoord d).differentiable (by simp)

/-- The open full-frame sheet where the oriented determinant is nonzero. -/
def sourceFullFrameOrientedCoord_detNonzero
    (d : ℕ) : Set (SourceFullFrameOrientedCoord d) :=
  {H | H.2 ≠ 0}

/-- The nonzero-determinant full-frame sheet is open. -/
theorem sourceFullFrameOrientedCoord_detNonzero_open
    (d : ℕ) :
    IsOpen (sourceFullFrameOrientedCoord_detNonzero d) := by
  exact isOpen_ne_fun continuous_snd continuous_const

@[simp]
theorem sourceFullFrameOrientedGramCoord_mem_detNonzero_iff
    (d : ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    sourceFullFrameOrientedGramCoord d M ∈
        sourceFullFrameOrientedCoord_detNonzero d ↔
      M.det ≠ 0 :=
  Iff.rfl

/-- The symmetric coordinate submodule for full-frame oriented coordinates. -/
def sourceFullFrameSymmetricCoordSubmodule
    (d : ℕ) : Submodule ℂ (SourceFullFrameOrientedCoord d) where
  carrier := {H | ∀ a b : Fin (d + 1), H.1 a b = H.1 b a}
  zero_mem' := by
    intro a b
    rfl
  add_mem' := by
    intro H K hH hK a b
    change H.1 a b + K.1 a b = H.1 b a + K.1 b a
    rw [hH a b, hK a b]
  smul_mem' := by
    intro c H hH a b
    change c • H.1 a b = c • H.1 b a
    rw [hH a b]

theorem mem_sourceFullFrameSymmetricCoordSubmodule
    {d : ℕ} {H : SourceFullFrameOrientedCoord d} :
    H ∈ sourceFullFrameSymmetricCoordSubmodule d ↔
      ∀ a b : Fin (d + 1), H.1 a b = H.1 b a :=
  Iff.rfl

/-- Full-frame oriented invariants land in the symmetric coordinate submodule. -/
theorem sourceFullFrameOrientedGramCoord_mem_symmetric
    (d : ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    sourceFullFrameOrientedGramCoord d M ∈
      sourceFullFrameSymmetricCoordSubmodule d := by
  intro a b
  exact sourceFullFrameGram_symm d M a b

/-- The full-frame coordinate variety is contained in the symmetric coordinate
submodule. -/
theorem sourceFullFrameOrientedGramVarietyCoord_subset_symmetric
    (d : ℕ) :
    sourceFullFrameOrientedGramVarietyCoord d ⊆
      sourceFullFrameSymmetricCoordSubmodule d := by
  rintro H ⟨M, rfl⟩
  exact sourceFullFrameOrientedGramCoord_mem_symmetric d M

/-- Determinant of the Minkowski metric matrix.  This scalar appears in the
oriented full-frame hypersurface equation. -/
def minkowskiMetricDet (d : ℕ) : ℂ :=
  (ComplexLorentzGroup.ηℂ (d := d)).det

/-- The determinant of the complex Minkowski metric squares to one because
`η² = 1`. -/
theorem minkowskiMetricDet_mul_self (d : ℕ) :
    minkowskiMetricDet d * minkowskiMetricDet d = 1 := by
  have h := congr_arg Matrix.det (ComplexLorentzGroup.ηℂ_sq (d := d))
  simpa [minkowskiMetricDet, Matrix.det_mul] using h

/-- The determinant of the complex Minkowski metric is a unit. -/
theorem isUnit_minkowskiMetricDet (d : ℕ) :
    IsUnit (minkowskiMetricDet d) :=
  IsUnit.of_mul_eq_one _ (minkowskiMetricDet_mul_self d)

/-- The determinant of the complex Minkowski metric is nonzero. -/
theorem minkowskiMetricDet_ne_zero (d : ℕ) :
    minkowskiMetricDet d ≠ 0 :=
  (isUnit_minkowskiMetricDet d).ne_zero

/-- Determinant relation for a full-frame Gram matrix:
`det(M η Mᵀ) = det(η) * det(M)^2`. -/
theorem sourceFullFrameGram_det_eq
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    (Matrix.of (sourceFullFrameGram d M)).det =
      minkowskiMetricDet d * M.det ^ 2 := by
  rw [sourceFullFrameGram_eq_mul_eta_transpose]
  simp [minkowskiMetricDet, Matrix.det_mul, Matrix.det_transpose, pow_two,
    mul_comm, mul_assoc]

/-- If the full-frame matrix is invertible, then its full-frame Gram determinant
is a unit. -/
theorem sourceFullFrameGram_det_isUnit_of_frame_det_isUnit
    (d : ℕ)
    {M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM : IsUnit M.det) :
    IsUnit (Matrix.of (sourceFullFrameGram d M)).det := by
  rw [sourceFullFrameGram_det_eq]
  exact (isUnit_minkowskiMetricDet d).mul (hM.pow 2)

/-- The full-frame oriented hypersurface equation in product coordinates. -/
def sourceFullFrameOrientedEquation
    (d : ℕ) (H : SourceFullFrameOrientedCoord d) : ℂ :=
  (Matrix.of H.1).det - minkowskiMetricDet d * H.2 ^ 2

/-- The full-frame oriented hypersurface in symmetric product coordinates. -/
def sourceFullFrameOrientedHypersurfaceCoord
    (d : ℕ) : Set (SourceFullFrameOrientedCoord d) :=
  (sourceFullFrameSymmetricCoordSubmodule d : Set
    (SourceFullFrameOrientedCoord d)) ∩
    {H | sourceFullFrameOrientedEquation d H = 0}

theorem sourceFullFrameOrientedHypersurfaceCoord_eq
    (d : ℕ) :
    sourceFullFrameOrientedHypersurfaceCoord d =
      (sourceFullFrameSymmetricCoordSubmodule d : Set
        (SourceFullFrameOrientedCoord d)) ∩
        {H | sourceFullFrameOrientedEquation d H = 0} :=
  rfl

/-- Full-frame oriented invariants satisfy the oriented hypersurface equation. -/
theorem sourceFullFrameOrientedGramCoord_mem_hypersurface
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    sourceFullFrameOrientedGramCoord d M ∈
      sourceFullFrameOrientedHypersurfaceCoord d := by
  constructor
  · exact sourceFullFrameOrientedGramCoord_mem_symmetric d M
  · simp [sourceFullFrameOrientedEquation, sourceFullFrameOrientedGramCoord,
      sourceFullFrameOrientedGram, SourceFullFrameOrientedGramData.toCoord,
      sourceFullFrameGram_det_eq]

/-- The full-frame oriented coordinate variety is contained in the oriented
hypersurface. -/
theorem sourceFullFrameOrientedGramVarietyCoord_subset_hypersurface
    (d : ℕ) :
    sourceFullFrameOrientedGramVarietyCoord d ⊆
      sourceFullFrameOrientedHypersurfaceCoord d := by
  rintro H ⟨M, rfl⟩
  exact sourceFullFrameOrientedGramCoord_mem_hypersurface d M

/-- Continuity of the full-frame oriented hypersurface equation. -/
theorem continuous_sourceFullFrameOrientedEquation
    (d : ℕ) :
    Continuous (sourceFullFrameOrientedEquation d) := by
  unfold sourceFullFrameOrientedEquation
  have hdet :
      Continuous
        (fun H : SourceFullFrameOrientedCoord d =>
          (Matrix.of H.1).det) :=
    continuous_fst.matrix_det
  exact hdet.sub (continuous_const.mul (continuous_snd.pow 2))

/-- Linearization of the full-frame oriented hypersurface equation at `H0`.
The remaining Jacobi theorem proves that this is the Frechet derivative of
`sourceFullFrameOrientedEquation`. -/
def sourceFullFrameOrientedEquationDerivLinear
    (d : ℕ)
    (H0 : SourceFullFrameOrientedGramData d) :
    SourceFullFrameOrientedCoord d →ₗ[ℂ] ℂ where
  toFun := fun Y =>
    (Matrix.of H0.gram).det *
        Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1) -
      (2 : ℂ) * minkowskiMetricDet d * H0.det * Y.2
  map_add' := by
    intro Y Z
    calc
      (Matrix.of H0.gram).det *
          Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of (Y + Z).1) -
        (2 : ℂ) * minkowskiMetricDet d * H0.det * (Y + Z).2
          = (Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) *
                (Matrix.of Y.1 + Matrix.of Z.1)) -
            (2 : ℂ) * minkowskiMetricDet d * H0.det * (Y.2 + Z.2) := by
              simp [← Matrix.of_add_of]
      _ = (Matrix.of H0.gram).det *
              Matrix.trace ((((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1) +
                (((Matrix.of H0.gram)⁻¹) * Matrix.of Z.1)) -
            (2 : ℂ) * minkowskiMetricDet d * H0.det * (Y.2 + Z.2) := by
              rw [mul_add]
      _ = ((Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1) -
            (2 : ℂ) * minkowskiMetricDet d * H0.det * Y.2) +
          ((Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of Z.1) -
            (2 : ℂ) * minkowskiMetricDet d * H0.det * Z.2) := by
              rw [Matrix.trace_add]
              ring
  map_smul' := by
    intro c Y
    calc
      (Matrix.of H0.gram).det *
          Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of (c • Y).1) -
        (2 : ℂ) * minkowskiMetricDet d * H0.det * (c • Y).2
          = (Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) * (c • Matrix.of Y.1)) -
            (2 : ℂ) * minkowskiMetricDet d * H0.det * (c • Y.2) := by
              simp [← Matrix.smul_of]
      _ = (Matrix.of H0.gram).det *
              Matrix.trace (c • (((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1)) -
            (2 : ℂ) * minkowskiMetricDet d * H0.det * (c • Y.2) := by
              rw [Matrix.mul_smul]
      _ = c * ((Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1) -
            (2 : ℂ) * minkowskiMetricDet d * H0.det * Y.2) := by
              rw [Matrix.trace_smul]
              simp [smul_eq_mul]
              ring

/-- Continuous linear version of the linearized full-frame oriented equation. -/
noncomputable def sourceFullFrameOrientedEquationDerivCLM
    (d : ℕ)
    (H0 : SourceFullFrameOrientedGramData d) :
    SourceFullFrameOrientedCoord d →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    (sourceFullFrameOrientedEquationDerivLinear d H0)

/-- The pure determinant-coordinate direction. -/
def sourceFullFrameDetDirection (d : ℕ) :
    SourceFullFrameOrientedCoord d :=
  (0, 1)

/-- The determinant-coordinate direction lies in the symmetric coordinate
submodule. -/
theorem sourceFullFrameDetDirection_mem_symmetric (d : ℕ) :
    sourceFullFrameDetDirection d ∈
      sourceFullFrameSymmetricCoordSubmodule d := by
  intro a b
  rfl

/-- The determinant-coordinate direction as an element of the symmetric
coordinate submodule. -/
def sourceFullFrameSymmetricDetDirection (d : ℕ) :
    sourceFullFrameSymmetricCoordSubmodule d :=
  ⟨sourceFullFrameDetDirection d,
    sourceFullFrameDetDirection_mem_symmetric d⟩

/-- The linearized oriented equation evaluated on the determinant-coordinate
direction. -/
theorem sourceFullFrameOrientedEquationDeriv_detDirection
    (d : ℕ) (H0 : SourceFullFrameOrientedGramData d) :
    sourceFullFrameOrientedEquationDerivLinear d H0
        (sourceFullFrameDetDirection d) =
      -((2 : ℂ) * minkowskiMetricDet d * H0.det) := by
  simp [sourceFullFrameOrientedEquationDerivLinear,
    sourceFullFrameDetDirection]

/-- If the oriented determinant coordinate is nonzero, the linearized equation
is nonzero in the determinant-coordinate direction. -/
theorem sourceFullFrameOrientedEquationDeriv_detDirection_ne_zero
    (d : ℕ) {H0 : SourceFullFrameOrientedGramData d}
    (hH0 : H0.det ≠ 0) :
    sourceFullFrameOrientedEquationDerivLinear d H0
        (sourceFullFrameDetDirection d) ≠ 0 := by
  rw [sourceFullFrameOrientedEquationDeriv_detDirection]
  exact
    neg_ne_zero.mpr
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (minkowskiMetricDet_ne_zero d)) hH0)

/-- Nonzero determinant coordinate makes the linearized equation map
surjective on the ambient product-coordinate space. -/
theorem sourceFullFrameOrientedEquationDeriv_surjective_of_det_ne_zero
    (d : ℕ) {H0 : SourceFullFrameOrientedGramData d}
    (hH0 : H0.det ≠ 0) :
    Function.Surjective
      (sourceFullFrameOrientedEquationDerivLinear d H0) := by
  intro c
  let a : ℂ := (2 : ℂ) * minkowskiMetricDet d * H0.det
  have ha : a ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (minkowskiMetricDet_ne_zero d)) hH0
  refine ⟨((-c / a) • sourceFullFrameDetDirection d), ?_⟩
  calc
    sourceFullFrameOrientedEquationDerivLinear d H0
        ((-c / a) • sourceFullFrameDetDirection d)
        = (-c / a) *
          sourceFullFrameOrientedEquationDerivLinear d H0
            (sourceFullFrameDetDirection d) := by
          simp
    _ = (-c / a) * (-a) := by
          rw [sourceFullFrameOrientedEquationDeriv_detDirection]
    _ = c := by
          field_simp [ha]

/-- The linearized oriented equation restricted to the symmetric coordinate
submodule. -/
def sourceFullFrameOrientedEquationDerivOnSymmetric
    (d : ℕ) (H0 : SourceFullFrameOrientedGramData d) :
    sourceFullFrameSymmetricCoordSubmodule d →ₗ[ℂ] ℂ :=
  (sourceFullFrameOrientedEquationDerivLinear d H0).comp
    (sourceFullFrameSymmetricCoordSubmodule d).subtype

/-- Evaluation of the symmetric-restricted linearized equation on the
determinant-coordinate direction. -/
theorem sourceFullFrameOrientedEquationDerivOnSymmetric_detDirection
    (d : ℕ) (H0 : SourceFullFrameOrientedGramData d) :
    sourceFullFrameOrientedEquationDerivOnSymmetric d H0
        (sourceFullFrameSymmetricDetDirection d) =
      -((2 : ℂ) * minkowskiMetricDet d * H0.det) :=
  sourceFullFrameOrientedEquationDeriv_detDirection d H0

/-- Nonzero determinant coordinate makes the linearized equation map
surjective even after restricting to symmetric coordinates. -/
theorem sourceFullFrameOrientedEquationDerivOnSymmetric_surjective_of_det_ne_zero
    (d : ℕ) {H0 : SourceFullFrameOrientedGramData d}
    (hH0 : H0.det ≠ 0) :
    Function.Surjective
      (sourceFullFrameOrientedEquationDerivOnSymmetric d H0) := by
  intro c
  let a : ℂ := (2 : ℂ) * minkowskiMetricDet d * H0.det
  have ha : a ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (minkowskiMetricDet_ne_zero d)) hH0
  refine ⟨((-c / a) • sourceFullFrameSymmetricDetDirection d), ?_⟩
  calc
    sourceFullFrameOrientedEquationDerivOnSymmetric d H0
        ((-c / a) • sourceFullFrameSymmetricDetDirection d)
        = (-c / a) *
          sourceFullFrameOrientedEquationDerivOnSymmetric d H0
            (sourceFullFrameSymmetricDetDirection d) := by
          simp
    _ = (-c / a) * (-a) := by
          rw [sourceFullFrameOrientedEquationDerivOnSymmetric_detDirection]
    _ = c := by
          field_simp [ha]

/-- The special complex Lorentz Lie algebra in full-frame matrix coordinates. -/
def specialComplexLorentzLieAlgebra
    (d : ℕ) :
    Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) where
  carrier :=
    {A | A.transpose * ComplexLorentzGroup.ηℂ (d := d) +
        ComplexLorentzGroup.ηℂ (d := d) * A = 0 ∧
      Matrix.trace A = 0}
  zero_mem' := by
    constructor <;> simp
  add_mem' := by
    intro A B hA hB
    constructor
    · calc
        (A + B).transpose * ComplexLorentzGroup.ηℂ (d := d) +
            ComplexLorentzGroup.ηℂ (d := d) * (A + B)
            =
          (A.transpose * ComplexLorentzGroup.ηℂ (d := d) +
            ComplexLorentzGroup.ηℂ (d := d) * A) +
          (B.transpose * ComplexLorentzGroup.ηℂ (d := d) +
            ComplexLorentzGroup.ηℂ (d := d) * B) := by
            ext i j
            simp [add_mul, mul_add, add_comm, add_left_comm, add_assoc]
        _ = 0 := by simp [hA.1, hB.1]
    · simp [Matrix.trace_add, hA.2, hB.2]
  smul_mem' := by
    intro c A hA
    constructor
    · calc
        (c • A).transpose * ComplexLorentzGroup.ηℂ (d := d) +
            ComplexLorentzGroup.ηℂ (d := d) * (c • A)
            =
          c • (A.transpose * ComplexLorentzGroup.ηℂ (d := d) +
            ComplexLorentzGroup.ηℂ (d := d) * A) := by
            ext i j
            simp [smul_eq_mul]
            ring
        _ = 0 := by simp [hA.1]
    · simp [Matrix.trace_smul, hA.2]

/-- Infinitesimal right action of the special complex Lorentz Lie algebra on a
full-frame matrix. -/
def infinitesimalRightSpecialLorentzAction
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    specialComplexLorentzLieAlgebra d →ₗ[ℂ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ where
  toFun := fun A => M0 * (A : Matrix _ _ ℂ).transpose
  map_add' := by
    intro A B
    ext i j
    simp [mul_add]
  map_smul' := by
    intro c A
    ext i j
    simp

/-- Tangent space to the full-frame special Lorentz orbit through `M0`. -/
def sourceFullFrameOrbitTangent
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  LinearMap.range (infinitesimalRightSpecialLorentzAction d M0)

/-- Linearized full-frame oriented invariant at `M0`.  The determinant
component is written in Jacobi form, valid on the invertible full-frame sheet
used downstream. -/
def sourceFullFrameOrientedDifferential
    (d : ℕ)
    (M0 X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    SourceFullFrameOrientedCoord d :=
  (fun a b =>
      ((X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose) +
        (M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose)) a b,
    M0.det * Matrix.trace (M0⁻¹ * X))

/-- The full-frame oriented differential as a linear map in the tangent
variable. -/
def sourceFullFrameOrientedDifferentialLinear
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →ₗ[ℂ]
      SourceFullFrameOrientedCoord d where
  toFun := sourceFullFrameOrientedDifferential d M0
  map_add' := by
    intro X Y
    apply Prod.ext
    · ext a b
      simp [sourceFullFrameOrientedDifferential, add_mul, mul_add,
        add_left_comm, add_assoc]
    · calc
        M0.det * Matrix.trace (M0⁻¹ * (X + Y))
            = M0.det * Matrix.trace (M0⁻¹ * X + M0⁻¹ * Y) := by
              rw [mul_add]
        _ = M0.det * Matrix.trace (M0⁻¹ * X) +
              M0.det * Matrix.trace (M0⁻¹ * Y) := by
              rw [Matrix.trace_add, mul_add]
  map_smul' := by
    intro c X
    apply Prod.ext
    · ext a b
      simp [sourceFullFrameOrientedDifferential, smul_eq_mul,
        mul_left_comm, mul_assoc]
      ring
    · simp [sourceFullFrameOrientedDifferential, smul_eq_mul,
        Matrix.trace_smul, mul_left_comm, mul_assoc]

/-- The full-frame oriented differential as a continuous linear map. -/
noncomputable def sourceFullFrameOrientedDifferentialCLM
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ]
      SourceFullFrameOrientedCoord d :=
  LinearMap.toContinuousLinearMap
    (sourceFullFrameOrientedDifferentialLinear d M0)

/-- The linearized tangent submodule to the full-frame oriented hypersurface at
`H0`.  The equality is the derivative of
`det(gram) - minkowskiMetricDet d * det^2 = 0`. -/
def sourceFullFrameOrientedTangentSpace
    (d : ℕ)
    (H0 : SourceFullFrameOrientedGramData d) :
    Submodule ℂ (SourceFullFrameOrientedCoord d) where
  carrier :=
    {Y |
      (∀ a b : Fin (d + 1), Y.1 a b = Y.1 b a) ∧
      (Matrix.of H0.gram).det *
          Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1) =
        (2 : ℂ) * minkowskiMetricDet d * H0.det * Y.2}
  zero_mem' := by
    constructor
    · intro a b
      rfl
    · simp
  add_mem' := by
    intro Y Z hY hZ
    constructor
    · intro a b
      change Y.1 a b + Z.1 a b = Y.1 b a + Z.1 b a
      rw [hY.1 a b, hZ.1 a b]
    · calc
        (Matrix.of H0.gram).det *
            Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of (Y.1 + Z.1))
            = (Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) *
                (Matrix.of Y.1 + Matrix.of Z.1)) := by
                rw [← Matrix.of_add_of]
        _ = (Matrix.of H0.gram).det *
              Matrix.trace ((((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1) +
                (((Matrix.of H0.gram)⁻¹) * Matrix.of Z.1)) := by
                rw [mul_add]
        _ = (Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1) +
            (Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of Z.1) := by
                rw [Matrix.trace_add, mul_add]
        _ = (2 : ℂ) * minkowskiMetricDet d * H0.det * Y.2 +
            (2 : ℂ) * minkowskiMetricDet d * H0.det * Z.2 := by
                rw [hY.2, hZ.2]
        _ = (2 : ℂ) * minkowskiMetricDet d * H0.det * (Y + Z).2 := by
                simp [mul_add]
  smul_mem' := by
    intro c Y hY
    constructor
    · intro a b
      change c • Y.1 a b = c • Y.1 b a
      rw [hY.1 a b]
    · calc
        (Matrix.of H0.gram).det *
            Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of (c • Y.1))
            = (Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) * (c • Matrix.of Y.1)) := by
                rw [← Matrix.smul_of]
        _ = (Matrix.of H0.gram).det *
              Matrix.trace (c • (((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1)) := by
                rw [Matrix.mul_smul]
        _ = c * ((Matrix.of H0.gram).det *
              Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1)) := by
                rw [Matrix.trace_smul]
                simp [smul_eq_mul]
                ring
        _ = c * ((2 : ℂ) * minkowskiMetricDet d * H0.det * Y.2) := by
                rw [hY.2]
        _ = (2 : ℂ) * minkowskiMetricDet d * H0.det * (c • Y.2) := by
                simp [smul_eq_mul]
                ring

theorem mem_sourceFullFrameOrientedTangentSpace
    {d : ℕ} {H0 : SourceFullFrameOrientedGramData d}
    {Y : SourceFullFrameOrientedCoord d} :
    Y ∈ sourceFullFrameOrientedTangentSpace d H0 ↔
      (∀ a b : Fin (d + 1), Y.1 a b = Y.1 b a) ∧
      (Matrix.of H0.gram).det *
          Matrix.trace (((Matrix.of H0.gram)⁻¹) * Matrix.of Y.1) =
        (2 : ℂ) * minkowskiMetricDet d * H0.det * Y.2 :=
  Iff.rfl

/-- The tangent submodule is the symmetric-coordinate kernel of the linearized
oriented equation. -/
theorem mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_deriv_eq_zero
    {d : ℕ} {H0 : SourceFullFrameOrientedGramData d}
    {Y : SourceFullFrameOrientedCoord d} :
    Y ∈ sourceFullFrameOrientedTangentSpace d H0 ↔
      Y ∈ sourceFullFrameSymmetricCoordSubmodule d ∧
        sourceFullFrameOrientedEquationDerivLinear d H0 Y = 0 := by
  constructor
  · intro hY
    exact ⟨hY.1, by simp [sourceFullFrameOrientedEquationDerivLinear, hY.2]⟩
  · rintro ⟨hYsym, hYder⟩
    constructor
    · exact hYsym
    · exact
        sub_eq_zero.mp
          (by
            simpa [sourceFullFrameOrientedEquationDerivLinear] using hYder)

/-- A finite-dimensional gauge-slice packet for the full-frame local-image
theorem.  The hard producers prove that such a slice exists and that the
linearized oriented differential identifies it with the hypersurface tangent. -/
structure SourceFullFrameGaugeSliceData
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) where
  slice :
    Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
  isCompl :
    IsCompl slice (sourceFullFrameOrbitTangent d M0)
  differential_iso :
    slice ≃ₗ[ℂ]
      (sourceFullFrameOrientedTangentSpace d
        (sourceFullFrameOrientedGram d M0))
  differential_iso_eq :
    ∀ X : slice,
      (differential_iso X :
        SourceFullFrameOrientedCoord d) =
        sourceFullFrameOrientedDifferential d M0 X

/-- The local full-frame slice map associated to a gauge slice. -/
def sourceFullFrameGaugeSliceMap
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    S.slice → SourceFullFrameOrientedCoord d :=
  fun X =>
    sourceFullFrameOrientedGramCoord d
      (M0 + (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ))

/-- The translated full-frame oriented invariant is differentiable at the slice
origin. -/
theorem sourceFullFrameOrientedGramCoord_differentiableAt_translate
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    DifferentiableAt ℂ
      (sourceFullFrameGaugeSliceMap d M0 S) 0 := by
  have htranslate :
      Differentiable ℂ
        (fun X : S.slice =>
          M0 + (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) := by
    exact
      (differentiable_const (c := M0)).add S.slice.subtypeL.differentiable
  exact
    (differentiable_sourceFullFrameOrientedGramCoord d).differentiableAt.comp
      0 htranslate.differentiableAt

/-- If a vector lies in both complementary submodules, it is zero. -/
theorem submodule_mem_isCompl_inter_eq_zero
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {S K : Submodule ℂ E}
    (hSK : IsCompl S K)
    {x : E} (hxS : x ∈ S) (hxK : x ∈ K) :
    x = 0 := by
  have hxinf : x ∈ S ⊓ K := ⟨hxS, hxK⟩
  have hinf : S ⊓ K = ⊥ := hSK.inf_eq_bot
  rw [hinf, Submodule.mem_bot] at hxinf
  exact hxinf

/-- Decompose a vector using complementary submodules. -/
theorem submodule_decompose_of_isCompl
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {S K : Submodule ℂ E}
    (hSK : IsCompl S K)
    (x : E) :
    ∃ s : S, ∃ k : K, (s : E) + (k : E) = x := by
  have hx_top : x ∈ (⊤ : Submodule ℂ E) := trivial
  have hx_sup : x ∈ S ⊔ K := by
    rw [hSK.sup_eq_top]
    exact hx_top
  rcases Submodule.mem_sup.mp hx_sup with ⟨s, hs, k, hk, hsk⟩
  exact ⟨⟨s, hs⟩, ⟨k, hk⟩, hsk⟩

/-- Select the full-frame oriented coordinate block indexed by `ι` from the
ambient oriented source invariant. -/
def sourceFullFrameOrientedCoordOfSource
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n) :
    SourceFullFrameOrientedCoord d :=
  (fun a b => G.gram (ι a) (ι b), G.det ι)

/-- The selected full-frame coordinate projection is continuous. -/
theorem continuous_sourceFullFrameOrientedCoordOfSource
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n) :
    Continuous (sourceFullFrameOrientedCoordOfSource d n ι) := by
  unfold sourceFullFrameOrientedCoordOfSource
  have hgram :
      Continuous
        (fun G : SourceOrientedGramData d n =>
          fun a b : Fin (d + 1) => G.gram (ι a) (ι b)) := by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    exact
      (continuous_apply (ι b)).comp
        ((continuous_apply (ι a)).comp
          (continuous_sourceOrientedGramData_gram (d := d) (n := n)))
  have hdet :
      Continuous
        (fun G : SourceOrientedGramData d n => G.det ι) :=
    (continuous_apply ι).comp
      (continuous_sourceOrientedGramData_det (d := d) (n := n))
  exact hgram.prodMk hdet

@[simp]
theorem sourceFullFrameOrientedCoordOfSource_fst
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n) :
    (sourceFullFrameOrientedCoordOfSource d n ι G).1 =
      fun a b => G.gram (ι a) (ι b) :=
  rfl

@[simp]
theorem sourceFullFrameOrientedCoordOfSource_snd
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n) :
    (sourceFullFrameOrientedCoordOfSource d n ι G).2 = G.det ι :=
  rfl

/-- Selecting full-frame coordinates from the ambient source invariant agrees
with applying the full-frame oriented invariant to the selected source matrix. -/
theorem sourceFullFrameOrientedCoordOfSource_sourceOrientedMinkowskiInvariant
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameOrientedCoordOfSource d n ι
        (sourceOrientedMinkowskiInvariant d n z) =
      sourceFullFrameOrientedGramCoord d
        (sourceFullFrameMatrix d n ι z) := by
  ext <;> simp [sourceFullFrameOrientedCoordOfSource,
    sourceFullFrameOrientedGramCoord, sourceFullFrameOrientedGram,
    SourceFullFrameOrientedGramData.toCoord,
    sourceOrientedMinkowskiInvariant,
    sourceFullFrameGram_sourceFullFrameMatrix,
    SourceOrientedGramData.gram, SourceOrientedGramData.det,
    sourceFullFrameDet]

/-- A selected full-frame coordinate block of an ambient oriented source-variety
point lies in the full-frame coordinate variety. -/
theorem sourceFullFrameOrientedCoordOfSource_mem_varietyCoord_of_mem_variety
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    sourceFullFrameOrientedCoordOfSource d n ι G ∈
      sourceFullFrameOrientedGramVarietyCoord d := by
  rcases hG with ⟨z, rfl⟩
  rw [sourceFullFrameOrientedCoordOfSource_sourceOrientedMinkowskiInvariant]
  exact ⟨sourceFullFrameMatrix d n ι z, rfl⟩

@[simp]
theorem sourceFullFrameOrientedCoordOfSource_mem_detNonzero_iff
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n) :
    sourceFullFrameOrientedCoordOfSource d n ι G ∈
        sourceFullFrameOrientedCoord_detNonzero d ↔
      G.det ι ≠ 0 :=
  Iff.rfl

end BHW
