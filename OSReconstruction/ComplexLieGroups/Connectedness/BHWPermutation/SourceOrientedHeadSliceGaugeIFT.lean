import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Submodule
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGauge
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTailWindow

/-!
# Source-oriented head-slice gauge by inverse-function coordinates

This file starts the finite-dimensional inverse-function construction of the
corrected head-slice gauge.  The key coordinate is
`K = H * η - η`, where `η = sourceHeadMetric d r hrD`.  In this coordinate
the sliced Gram map is the polynomial

`K ↦ η + 2K + K * η * K`,

so its derivative at the origin is scalar multiplication by `2`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped RightActions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace BHW

/-- The symmetric complex square matrices as a complex submodule. -/
def sourceSymmetricMatrixSubmodule (r : ℕ) :
    Submodule ℂ (Matrix (Fin r) (Fin r) ℂ) where
  carrier := {A | Aᵀ = A}
  zero_mem' := by
    simp
  add_mem' := by
    intro A B hA hB
    change (A + B)ᵀ = A + B
    rw [Matrix.transpose_add, hA, hB]
  smul_mem' := by
    intro c A hA
    change (c • A)ᵀ = c • A
    rw [Matrix.transpose_smul, hA]

local instance sourceSymmetricMatrixSubmodule_isUniformAddGroup
    (r : ℕ) :
    IsUniformAddGroup (sourceSymmetricMatrixSubmodule r) :=
  (sourceSymmetricMatrixSubmodule r).toAddSubgroup.isUniformAddGroup

instance sourceSymmetricMatrixSubmodule_completeSpace
    (r : ℕ) :
    CompleteSpace (sourceSymmetricMatrixSubmodule r) :=
  FiniteDimensional.complete ℂ (sourceSymmetricMatrixSubmodule r)

@[simp]
theorem mem_sourceSymmetricMatrixSubmodule
    {r : ℕ}
    {A : Matrix (Fin r) (Fin r) ℂ} :
    A ∈ sourceSymmetricMatrixSubmodule r ↔ Aᵀ = A :=
  Iff.rfl

/-- The canonical source head metric, viewed in the symmetric submodule. -/
def sourceHeadMetricSymmSubmodule
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceSymmetricMatrixSubmodule r :=
  ⟨sourceHeadMetric d r hrD, sourceHeadMetric_transpose d r hrD⟩

/-- Convert the existing symmetric-coordinate subtype to the symmetric
submodule coordinate. -/
def sourceSymmetricMatrixCoordToSubmodule
    (r : ℕ) :
    SourceSymmetricMatrixCoord r ≃ₜ sourceSymmetricMatrixSubmodule r where
  toFun A := ⟨A.1, A.2⟩
  invFun A := ⟨A.1, A.2⟩
  left_inv A := by
    rfl
  right_inv A := by
    rfl
  continuous_toFun := by
    exact continuous_subtype_val.subtype_mk (fun A => A.2)
  continuous_invFun := by
    exact continuous_subtype_val.subtype_mk (fun A => A.2)

@[simp]
theorem sourceSymmetricMatrixCoordToSubmodule_apply
    (r : ℕ)
    (A : SourceSymmetricMatrixCoord r) :
    (sourceSymmetricMatrixCoordToSubmodule r A :
      Matrix (Fin r) (Fin r) ℂ) = A.1 :=
  rfl

@[simp]
theorem sourceSymmetricMatrixCoordToSubmodule_symm_apply
    (r : ℕ)
    (A : sourceSymmetricMatrixSubmodule r) :
    ((sourceSymmetricMatrixCoordToSubmodule r).symm A :
      Matrix (Fin r) (Fin r) ℂ) = A.1 :=
  rfl

/-- The head metric is an involution. -/
theorem sourceHeadMetric_mul_self
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadMetric d r hrD * sourceHeadMetric d r hrD =
      (1 : Matrix (Fin r) (Fin r) ℂ) := by
  rw [sourceHeadMetric, Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases hzero : finSourceHead (Nat.le_of_lt hrD) a = (0 : Fin (d + 1))
    · simp [Matrix.diagonal, MinkowskiSpace.metricSignature, hzero]
    · simp [Matrix.diagonal, MinkowskiSpace.metricSignature, hzero]
  · simp [Matrix.diagonal, hab]

/-- The coordinate `K = H * η - η` on the head-gauge slice. -/
def sourceHeadGaugeSliceSymmCoord
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : SourceHeadGaugeSlice d r hrD) :
    sourceSymmetricMatrixSubmodule r :=
  ⟨H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD, by
    change
      (H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD)ᵀ =
        H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD
    rw [Matrix.transpose_sub, ← H.2, sourceHeadMetric_transpose d r hrD]⟩

/-- Rebuild a head-slice point from the symmetric coordinate `K`. -/
def sourceHeadGaugeSliceOfSymmCoord
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    SourceHeadGaugeSlice d r hrD :=
  ⟨(sourceHeadMetric d r hrD + K.1) * sourceHeadMetric d r hrD, by
    rw [Matrix.mul_assoc, sourceHeadMetric_mul_self d r hrD, Matrix.mul_one]
    rw [Matrix.transpose_add, sourceHeadMetric_transpose d r hrD, K.2]⟩

@[simp]
theorem sourceHeadGaugeSliceOfSymmCoord_val
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1 =
      (sourceHeadMetric d r hrD + K.1) * sourceHeadMetric d r hrD :=
  rfl

/-- Coordinate homeomorphism from the head slice to symmetric matrices. -/
def sourceHeadGaugeSliceSymmCoordHomeomorph
    (d r : ℕ)
    (hrD : r < d + 1) :
    SourceHeadGaugeSlice d r hrD ≃ₜ sourceSymmetricMatrixSubmodule r where
  toFun := sourceHeadGaugeSliceSymmCoord d r hrD
  invFun := sourceHeadGaugeSliceOfSymmCoord d r hrD
  left_inv H := by
    let η := sourceHeadMetric d r hrD
    have hcancel :
        η + (H.1 * η - η) = H.1 * η := by
      abel
    apply Subtype.ext
    calc
      ((sourceHeadGaugeSliceOfSymmCoord d r hrD
          (sourceHeadGaugeSliceSymmCoord d r hrD H)).1) =
          ((sourceHeadMetric d r hrD +
              (H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD)) *
            sourceHeadMetric d r hrD) := rfl
      _ = (H.1 * sourceHeadMetric d r hrD) *
            sourceHeadMetric d r hrD := by
            change (η + (H.1 * η - η)) * η = (H.1 * η) * η
            exact congrArg (fun M => M * η) hcancel
      _ = H.1 * (sourceHeadMetric d r hrD * sourceHeadMetric d r hrD) := by
            rw [Matrix.mul_assoc]
      _ = H.1 := by
            rw [sourceHeadMetric_mul_self d r hrD, Matrix.mul_one]
  right_inv K := by
    let η := sourceHeadMetric d r hrD
    apply Subtype.ext
    calc
      ((sourceHeadGaugeSliceSymmCoord d r hrD
          (sourceHeadGaugeSliceOfSymmCoord d r hrD K)).1) =
          ((sourceHeadMetric d r hrD + K.1) * sourceHeadMetric d r hrD) *
              sourceHeadMetric d r hrD -
            sourceHeadMetric d r hrD := rfl
      _ = (sourceHeadMetric d r hrD + K.1) *
              (sourceHeadMetric d r hrD * sourceHeadMetric d r hrD) -
            sourceHeadMetric d r hrD := by
            rw [Matrix.mul_assoc]
      _ = K.1 := by
            rw [sourceHeadMetric_mul_self d r hrD, Matrix.mul_one]
            simp
  continuous_toFun := by
    have hcont :
        Continuous fun H : SourceHeadGaugeSlice d r hrD =>
          H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD := by
      fun_prop
    exact hcont.subtype_mk (fun H => (sourceHeadGaugeSliceSymmCoord d r hrD H).2)
  continuous_invFun := by
    have hcont :
        Continuous fun K : sourceSymmetricMatrixSubmodule r =>
          (sourceHeadMetric d r hrD + K.1) * sourceHeadMetric d r hrD := by
      fun_prop
    exact hcont.subtype_mk
      (fun K => (sourceHeadGaugeSliceOfSymmCoord d r hrD K).2)

@[simp]
theorem sourceHeadGaugeSliceSymmCoordHomeomorph_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : SourceHeadGaugeSlice d r hrD) :
    sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD H =
      sourceHeadGaugeSliceSymmCoord d r hrD H :=
  rfl

@[simp]
theorem sourceHeadGaugeSliceSymmCoordHomeomorph_symm_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    (sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD).symm K =
      sourceHeadGaugeSliceOfSymmCoord d r hrD K :=
  rfl

@[simp]
theorem sourceHeadGaugeSliceOfSymmCoord_symmCoord
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : SourceHeadGaugeSlice d r hrD) :
    sourceHeadGaugeSliceOfSymmCoord d r hrD
        (sourceHeadGaugeSliceSymmCoord d r hrD H) = H := by
  simpa [sourceHeadGaugeSliceSymmCoordHomeomorph] using
    (sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD).left_inv H

@[simp]
theorem sourceHeadGaugeSliceSymmCoord_ofSymmCoord
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    sourceHeadGaugeSliceSymmCoord d r hrD
        (sourceHeadGaugeSliceOfSymmCoord d r hrD K) = K := by
  simpa [sourceHeadGaugeSliceSymmCoordHomeomorph] using
    (sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD).right_inv K

@[simp]
theorem sourceHeadGaugeSliceSymmCoord_center
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadGaugeSliceSymmCoord d r hrD
        (sourceHeadGaugeSliceCenter d r hrD) =
      (0 : sourceSymmetricMatrixSubmodule r) := by
  apply Subtype.ext
  simp [sourceHeadGaugeSliceSymmCoord, sourceHeadGaugeSliceCenter]

@[simp]
theorem sourceHeadGaugeSliceOfSymmCoord_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadGaugeSliceOfSymmCoord d r hrD
        (0 : sourceSymmetricMatrixSubmodule r) =
      sourceHeadGaugeSliceCenter d r hrD := by
  apply Subtype.ext
  simp [sourceHeadGaugeSliceOfSymmCoord, sourceHeadGaugeSliceCenter,
    sourceHeadMetric_mul_self]

@[simp]
theorem sourceHeadGaugeSliceSymmCoordHomeomorph_symm_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    (sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD).symm
        (0 : sourceSymmetricMatrixSubmodule r) =
      sourceHeadGaugeSliceCenter d r hrD := by
  simp [sourceHeadGaugeSliceSymmCoordHomeomorph]

/-- Entrywise coordinate window around zero in the symmetric `K` coordinate. -/
def sourceSymmetricMatrixCoordinateWindow
    (r : ℕ)
    (ρ : ℝ) :
    Set (sourceSymmetricMatrixSubmodule r) :=
  {K | ∀ a b, ‖(K : Matrix (Fin r) (Fin r) ℂ) a b‖ < ρ}

theorem isOpen_sourceSymmetricMatrixCoordinateWindow
    (r : ℕ)
    (ρ : ℝ) :
    IsOpen (sourceSymmetricMatrixCoordinateWindow r ρ) := by
  have hfull :
      IsOpen
        (sourceMatrixCoordinateWindow
          (0 : Matrix (Fin r) (Fin r) ℂ) ρ) :=
    isOpen_sourceMatrixCoordinateWindow
      (0 : Matrix (Fin r) (Fin r) ℂ) ρ
  simpa [sourceSymmetricMatrixCoordinateWindow, sourceMatrixCoordinateWindow]
    using hfull.preimage continuous_subtype_val

theorem zero_mem_sourceSymmetricMatrixCoordinateWindow
    (r : ℕ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    (0 : sourceSymmetricMatrixSubmodule r) ∈
      sourceSymmetricMatrixCoordinateWindow r ρ := by
  intro a b
  simpa using hρ

theorem sourceSymmetricMatrixCoordinateWindow_mem_nhds_zero
    (r : ℕ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    sourceSymmetricMatrixCoordinateWindow r ρ ∈
      𝓝 (0 : sourceSymmetricMatrixSubmodule r) :=
  (isOpen_sourceSymmetricMatrixCoordinateWindow r ρ).mem_nhds
    (zero_mem_sourceSymmetricMatrixCoordinateWindow r hρ)

/-- The diagonal entries of the head metric have norm one. -/
theorem norm_sourceHeadMetric_diag
    (d r : ℕ)
    (hrD : r < d + 1)
    (b : Fin r) :
    ‖(MinkowskiSpace.metricSignature d
        (finSourceHead (Nat.le_of_lt hrD) b) : ℂ)‖ = 1 := by
  by_cases hzero : finSourceHead (Nat.le_of_lt hrD) b = (0 : Fin (d + 1))
  · simp [MinkowskiSpace.metricSignature, hzero]
  · simp [MinkowskiSpace.metricSignature, hzero]

/-- Multiplication by the diagonal head metric scales the `b`-th column. -/
theorem sourceHeadMetric_mul_entry
    (d r : ℕ)
    (hrD : r < d + 1)
    (M : Matrix (Fin r) (Fin r) ℂ)
    (a b : Fin r) :
    (M * sourceHeadMetric d r hrD) a b =
      M a b *
        (MinkowskiSpace.metricSignature d
          (finSourceHead (Nat.le_of_lt hrD) b) : ℂ) := by
  rw [sourceHeadMetric, Matrix.mul_apply]
  rw [Finset.sum_eq_single b]
  · simp [Matrix.diagonal]
  · intro j _hj hjb
    simp [Matrix.diagonal, hjb]
  · intro hb
    exact False.elim (hb (Finset.mem_univ b))

/-- Entry formula for the symmetric coordinate `K = H * η - η`. -/
theorem sourceHeadGaugeSliceSymmCoord_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : SourceHeadGaugeSlice d r hrD)
    (a b : Fin r) :
    (sourceHeadGaugeSliceSymmCoord d r hrD H :
        Matrix (Fin r) (Fin r) ℂ) a b =
      (H.1 a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b) *
        (MinkowskiSpace.metricSignature d
          (finSourceHead (Nat.le_of_lt hrD) b) : ℂ) := by
  change
    (H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD) a b =
      (H.1 a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b) *
        (MinkowskiSpace.metricSignature d
          (finSourceHead (Nat.le_of_lt hrD) b) : ℂ)
  rw [Matrix.sub_apply, sourceHeadMetric_mul_entry]
  by_cases hab : a = b
  · subst b
    simp [sourceHeadMetric, sub_mul]
  · simp [sourceHeadMetric, hab]

/-- The slice coordinate window is exactly the zero-centered symmetric
coordinate window under `K = H * η - η`. -/
theorem sourceHeadGaugeSliceSymmCoord_mem_coordinateWindow_iff
    (d r : ℕ)
    (hrD : r < d + 1)
    (ρ : ℝ)
    (H : SourceHeadGaugeSlice d r hrD) :
    sourceHeadGaugeSliceSymmCoord d r hrD H ∈
        sourceSymmetricMatrixCoordinateWindow r ρ ↔
      H ∈ sourceHeadGaugeSliceCoordinateWindow d r hrD ρ := by
  constructor
  · intro hK a b
    have hKab := hK a b
    rw [sourceHeadGaugeSliceSymmCoord_apply d r hrD H a b,
      norm_mul, norm_sourceHeadMetric_diag d r hrD b, mul_one] at hKab
    simpa [sourceHeadGaugeSliceCoordinateWindow,
      sourceHeadFactorCoordinateWindow] using hKab
  · intro hH a b
    have hHab : ‖H.1 a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ρ := by
      simpa [sourceHeadGaugeSliceCoordinateWindow,
        sourceHeadFactorCoordinateWindow] using hH a b
    rw [sourceHeadGaugeSliceSymmCoord_apply d r hrD H a b,
      norm_mul, norm_sourceHeadMetric_diag d r hrD b, mul_one]
    exact hHab

/-- Zero-centered symmetric coordinate windows form a neighborhood basis at
zero for the finite-dimensional symmetric submodule. -/
theorem exists_sourceSymmetricMatrixCoordinateWindow_subset_of_mem_nhds_zero
    (r : ℕ)
    {V : Set (sourceSymmetricMatrixSubmodule r)}
    (hV : V ∈ 𝓝 (0 : sourceSymmetricMatrixSubmodule r)) :
    ∃ ρ : ℝ, 0 < ρ ∧ sourceSymmetricMatrixCoordinateWindow r ρ ⊆ V := by
  rcases Metric.mem_nhds_iff.mp hV with ⟨ε, hε, hεsub⟩
  refine ⟨ε, hε, ?_⟩
  intro K hK
  apply hεsub
  have hnorm :
      ‖(K : Matrix (Fin r) (Fin r) ℂ)‖ < ε :=
    (Matrix.norm_lt_iff hε).2 hK
  have hdist : dist K 0 = ‖(K : Matrix (Fin r) (Fin r) ℂ)‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
    simp
  simpa [Metric.mem_ball, hdist] using hnorm

/-- Slice-coordinate windows form a neighborhood basis at the slice center. -/
theorem exists_sourceHeadGaugeSliceCoordinateWindow_subset_of_mem_nhds_center
    (d r : ℕ)
    (hrD : r < d + 1)
    {V : Set (SourceHeadGaugeSlice d r hrD)}
    (hV : V ∈ 𝓝 (sourceHeadGaugeSliceCenter d r hrD)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      sourceHeadGaugeSliceCoordinateWindow d r hrD ρ ⊆ V := by
  let e := sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD
  let W : Set (sourceSymmetricMatrixSubmodule r) := e.symm ⁻¹' V
  have hV' : V ∈ 𝓝 (e.symm (0 : sourceSymmetricMatrixSubmodule r)) := by
    simpa [e] using hV
  have hW : W ∈ 𝓝 (0 : sourceSymmetricMatrixSubmodule r) :=
    e.symm.continuous.continuousAt hV'
  rcases exists_sourceSymmetricMatrixCoordinateWindow_subset_of_mem_nhds_zero
      r hW with ⟨ρ, hρ, hρsub⟩
  refine ⟨ρ, hρ, ?_⟩
  intro H hH
  have hK :
      e H ∈ sourceSymmetricMatrixCoordinateWindow r ρ := by
    simpa [e] using
      (sourceHeadGaugeSliceSymmCoord_mem_coordinateWindow_iff
        d r hrD ρ H).2 hH
  have hWin : e H ∈ W := hρsub hK
  simpa [W] using hWin

/-- The sliced Gram map in symmetric `K = H * η - η` coordinates. -/
def sourceHeadSliceGramPolynomial
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    sourceSymmetricMatrixSubmodule r :=
  ⟨sourceHeadMetric d r hrD + (2 : ℂ) • K.1 +
      K.1 * sourceHeadMetric d r hrD * K.1, by
    change
      (sourceHeadMetric d r hrD + (2 : ℂ) • K.1 +
          K.1 * sourceHeadMetric d r hrD * K.1)ᵀ =
        sourceHeadMetric d r hrD + (2 : ℂ) • K.1 +
          K.1 * sourceHeadMetric d r hrD * K.1
    rw [Matrix.transpose_add, Matrix.transpose_add,
      sourceHeadMetric_transpose d r hrD, Matrix.transpose_smul, K.2]
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      sourceHeadMetric_transpose d r hrD, K.2]
    simp [Matrix.mul_assoc]⟩

@[simp]
theorem sourceHeadSliceGramPolynomial_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadSliceGramPolynomial d r hrD 0 =
      sourceHeadMetricSymmSubmodule d r hrD := by
  apply Subtype.ext
  simp [sourceHeadSliceGramPolynomial, sourceHeadMetricSymmSubmodule]

/-- In slice coordinates, the polynomial equals `H * η * Hᵀ`. -/
theorem sourceHeadSliceGramPolynomial_eq_factorGram
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    (sourceHeadSliceGramPolynomial d r hrD K :
        Matrix (Fin r) (Fin r) ℂ) =
      (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1 *
        sourceHeadMetric d r hrD *
        (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1ᵀ := by
  let η := sourceHeadMetric d r hrD
  have hηη : η * η = (1 : Matrix (Fin r) (Fin r) ℂ) := by
    simpa [η] using sourceHeadMetric_mul_self d r hrD
  have hηT : ηᵀ = η := by
    simpa [η] using sourceHeadMetric_transpose d r hrD
  have hKT : K.1ᵀ = K.1 := K.2
  have hquad :
      (η + K.1) * η * (η + K.1) =
        η + (2 : ℂ) • K.1 + K.1 * η * K.1 := by
    calc
      (η + K.1) * η * (η + K.1) =
          (η * η + K.1 * η) * (η + K.1) := by
            rw [add_mul]
      _ = (η * η) * (η + K.1) + (K.1 * η) * (η + K.1) := by
            rw [add_mul]
      _ = η * η * η + η * η * K.1 +
            (K.1 * η * η + K.1 * η * K.1) := by
            rw [mul_add, mul_add]
      _ = η + K.1 + (K.1 + K.1 * η * K.1) := by
            rw [hηη]
            rw [Matrix.mul_assoc K.1 η η, hηη, Matrix.mul_one]
            simp [Matrix.mul_assoc]
      _ = η + (2 : ℂ) • K.1 + K.1 * η * K.1 := by
            simp [two_smul, add_assoc]
  calc
    (sourceHeadSliceGramPolynomial d r hrD K :
        Matrix (Fin r) (Fin r) ℂ) =
        η + (2 : ℂ) • K.1 + K.1 * η * K.1 := by
          rfl
    _ = (η + K.1) * η * (η + K.1) := by
          exact hquad.symm
    _ =
      (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1 *
        sourceHeadMetric d r hrD *
        (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1ᵀ := by
          simp [sourceHeadGaugeSliceOfSymmCoord, Matrix.transpose_mul,
            hηT, hKT, hηη, Matrix.mul_assoc, η]

/-- The derivative of the sliced Gram polynomial at the origin is
scalar multiplication by `2`. -/
def sourceHeadSliceGramPolynomialDerivEquiv
    (r : ℕ) :
    sourceSymmetricMatrixSubmodule r ≃L[ℂ]
      sourceSymmetricMatrixSubmodule r :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℂ) (by norm_num))

end BHW
