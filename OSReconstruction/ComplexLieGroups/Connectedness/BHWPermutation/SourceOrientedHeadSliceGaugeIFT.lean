import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
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

/-- A sufficiently small identity-centered slice coordinate window consists of
invertible head factors. -/
theorem sourceHeadGaugeSliceCoordinateWindow_det_isUnit
    (d r : ℕ)
    (hrD : r < d + 1)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρ_half : ρ < (1 : ℝ) / 2)
    (hcardρ : (Fintype.card (Fin r) : ℝ) * ρ < (1 : ℝ) / 2)
    {H : SourceHeadGaugeSlice d r hrD}
    (hH : H ∈ sourceHeadGaugeSliceCoordinateWindow d r hrD ρ) :
    IsUnit H.1.det := by
  have hdet_ne :
      H.1.det ≠ 0 :=
    det_ne_zero_of_sum_row_lt_diag (A := H.1) (fun k => by
      have hsum_le :
          (∑ j ∈ Finset.univ.erase k, ‖H.1 k j‖) ≤
            (Fintype.card (Fin r) : ℝ) * ρ := by
        calc
          (∑ j ∈ Finset.univ.erase k, ‖H.1 k j‖) ≤
              ∑ _j ∈ Finset.univ.erase k, ρ := by
                refine Finset.sum_le_sum ?_
                intro j hj
                have hjne : j ≠ k := (Finset.mem_erase.mp hj).1
                have hentry : ‖H.1 k j‖ < ρ := by
                  have hkj := hH k j
                  simpa [sourceHeadGaugeSliceCoordinateWindow,
                    sourceHeadFactorCoordinateWindow, Matrix.one_apply, hjne.symm]
                    using hkj
                exact le_of_lt hentry
          _ = ((Finset.univ.erase k).card : ℝ) * ρ := by
                simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Fintype.card (Fin r) : ℝ) * ρ := by
                gcongr
                exact_mod_cast (Finset.univ.erase k).card_le_univ
      have hsum_half :
          (∑ j ∈ Finset.univ.erase k, ‖H.1 k j‖) < (1 : ℝ) / 2 :=
        lt_of_le_of_lt hsum_le hcardρ
      have hdiagdiff : ‖H.1 k k - (1 : ℂ)‖ < ρ := by
        have hkk := hH k k
        simpa [sourceHeadGaugeSliceCoordinateWindow,
          sourceHeadFactorCoordinateWindow, Matrix.one_apply] using hkk
      have hdiag_gt_half : (1 : ℝ) / 2 < ‖H.1 k k‖ := by
        have hnorm_one :
            (1 : ℝ) ≤ ‖H.1 k k‖ + ‖H.1 k k - (1 : ℂ)‖ := by
          calc
            (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
            _ = ‖H.1 k k - (H.1 k k - (1 : ℂ))‖ := by
                  congr 1
                  ring
            _ ≤ ‖H.1 k k‖ + ‖H.1 k k - (1 : ℂ)‖ :=
                  norm_sub_le _ _
        nlinarith
      exact lt_trans hsum_half hdiag_gt_half)
  exact isUnit_iff_ne_zero.mpr hdet_ne

/-- A fixed small radius for the final determinant-unit shrink of the
head-slice IFT chart. -/
noncomputable def sourceHeadSliceGaugeIFTWindowRadius
    (r : ℕ) : ℝ :=
  (1 : ℝ) / (4 * ((Fintype.card (Fin r) : ℝ) + 1))

theorem sourceHeadSliceGaugeIFTWindowRadius_pos
    (r : ℕ) :
    0 < sourceHeadSliceGaugeIFTWindowRadius r := by
  unfold sourceHeadSliceGaugeIFTWindowRadius
  positivity

theorem sourceHeadSliceGaugeIFTWindowRadius_lt_half
    (r : ℕ) :
    sourceHeadSliceGaugeIFTWindowRadius r < (1 : ℝ) / 2 := by
  let c : ℝ := Fintype.card (Fin r)
  have hc : 0 ≤ c := by positivity
  have hden : 2 < 4 * (c + 1) := by nlinarith
  have hpos : (0 : ℝ) < 2 := by norm_num
  simpa [sourceHeadSliceGaugeIFTWindowRadius, c] using
    one_div_lt_one_div_of_lt hpos hden

theorem sourceHeadSliceGaugeIFTWindowRadius_card_mul_lt_half
    (r : ℕ) :
    (Fintype.card (Fin r) : ℝ) *
        sourceHeadSliceGaugeIFTWindowRadius r < (1 : ℝ) / 2 := by
  let c : ℝ := Fintype.card (Fin r)
  have hc : 0 ≤ c := by positivity
  have hden_pos : 0 < 4 * (c + 1) := by positivity
  have hle : c / (4 * (c + 1)) ≤ (1 : ℝ) / 4 := by
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hquarter : (1 : ℝ) / 4 < (1 : ℝ) / 2 := by norm_num
  calc
    c * sourceHeadSliceGaugeIFTWindowRadius r =
        c / (4 * (c + 1)) := by
          rw [sourceHeadSliceGaugeIFTWindowRadius]
          change c * (1 / (4 * (c + 1))) = c / (4 * (c + 1))
          ring
    _ < (1 : ℝ) / 2 := lt_of_le_of_lt hle hquarter

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

/-- Local codomain restriction for strict derivatives into a submodule. -/
theorem hasStrictFDerivAt_submodule_codRestrict_local
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (S : Submodule 𝕜 F)
    {f : E → F} {f' : E →L[𝕜] F} {x : E}
    (hf : HasStrictFDerivAt f f' x)
    (hmem : ∀ y, f y ∈ S)
    (hderiv : ∀ y, f' y ∈ S) :
    HasStrictFDerivAt (fun y => ⟨f y, hmem y⟩ : E → S)
      (f'.codRestrict S hderiv) x := by
  refine HasStrictFDerivAt.of_isLittleO ?_
  have hfo := hf.isLittleO
  rw [Asymptotics.isLittleO_iff] at hfo ⊢
  intro c hc
  filter_upwards [hfo hc] with p hp
  simpa using hp

/-- The ambient continuous bilinear map `(K,L) ↦ K * η * L` used for the
quadratic Gram correction.  The finite-dimensional constructor keeps the
existing elementwise matrix norm in force. -/
noncomputable def sourceHeadMetricQuadraticBilinear
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceSymmetricMatrixSubmodule r →L[ℂ]
      sourceSymmetricMatrixSubmodule r →L[ℂ]
        Matrix (Fin r) (Fin r) ℂ :=
  (show IsBilinearMap ℂ
      (fun K L : sourceSymmetricMatrixSubmodule r =>
        K.1 * sourceHeadMetric d r hrD * L.1) from by
    refine
      { add_left := ?_
        smul_left := ?_
        add_right := ?_
        smul_right := ?_ }
    · intro K₁ K₂ L
      simp [Matrix.add_mul, Matrix.mul_assoc]
    · intro c K L
      simp [Matrix.mul_assoc]
    · intro K L₁ L₂
      simp [Matrix.mul_add, Matrix.mul_assoc]
    · intro c K L
      simp [Matrix.mul_assoc])
    |>.toContinuousBilinearMap

@[simp]
theorem sourceHeadMetricQuadraticBilinear_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (K L : sourceSymmetricMatrixSubmodule r) :
    sourceHeadMetricQuadraticBilinear d r hrD K L =
      K.1 * sourceHeadMetric d r hrD * L.1 :=
  rfl

/-- The symmetric quadratic part `K ↦ K * η * K` of the slice Gram polynomial. -/
def sourceHeadMetricQuadraticSymm
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    sourceSymmetricMatrixSubmodule r :=
  ⟨K.1 * sourceHeadMetric d r hrD * K.1, by
    change
      (K.1 * sourceHeadMetric d r hrD * K.1)ᵀ =
        K.1 * sourceHeadMetric d r hrD * K.1
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      sourceHeadMetric_transpose d r hrD, K.2]
    simp [Matrix.mul_assoc]⟩

@[simp]
theorem sourceHeadMetricQuadraticSymm_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    (sourceHeadMetricQuadraticSymm d r hrD K :
        Matrix (Fin r) (Fin r) ℂ) =
      K.1 * sourceHeadMetric d r hrD * K.1 :=
  rfl

/-- The quadratic correction has zero strict derivative at the origin, in the
ambient matrix codomain. -/
theorem sourceHeadMetricQuadratic_ambient_hasStrictFDerivAt_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    HasStrictFDerivAt
      (fun K : sourceSymmetricMatrixSubmodule r =>
        K.1 * sourceHeadMetric d r hrD * K.1)
      (0 : sourceSymmetricMatrixSubmodule r →L[ℂ]
        Matrix (Fin r) (Fin r) ℂ) 0 := by
  let S := sourceSymmetricMatrixSubmodule r
  let B := sourceHeadMetricQuadraticBilinear d r hrD
  have hid : HasStrictFDerivAt (fun K : S => K) (1 : S →L[ℂ] S) 0 :=
    (1 : S →L[ℂ] S).hasStrictFDerivAt
  have hB : HasStrictFDerivAt (fun K : S => B K K)
      (B.precompR S (0 : S) (1 : S →L[ℂ] S) +
        B.precompL S (1 : S →L[ℂ] S) (0 : S)) 0 :=
    B.hasStrictFDerivAt_of_bilinear hid hid
  have hderiv :
      B.precompR S (0 : S) (1 : S →L[ℂ] S) +
          B.precompL S (1 : S →L[ℂ] S) (0 : S) =
        (0 : S →L[ℂ] Matrix (Fin r) (Fin r) ℂ) := by
    ext K a b
    change (B (0 : S) K + B K (0 : S)) a b = 0
    simp [B, sourceHeadMetricQuadraticBilinear]
  simpa [S, B, sourceHeadMetricQuadraticBilinear] using hB.congr_fderiv hderiv

/-- The symmetric quadratic correction has zero strict derivative at the origin. -/
theorem sourceHeadMetricQuadraticSymm_hasStrictFDerivAt_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    HasStrictFDerivAt
      (sourceHeadMetricQuadraticSymm d r hrD)
      (0 : sourceSymmetricMatrixSubmodule r →L[ℂ]
        sourceSymmetricMatrixSubmodule r) 0 := by
  let S := sourceSymmetricMatrixSubmodule r
  let zeroCLM : S →L[ℂ] Matrix (Fin r) (Fin r) ℂ := 0
  have hamb :
      HasStrictFDerivAt
        (fun K : S => K.1 * sourceHeadMetric d r hrD * K.1)
        zeroCLM 0 := by
    simpa [S, zeroCLM] using
      sourceHeadMetricQuadratic_ambient_hasStrictFDerivAt_zero d r hrD
  have hzeroMem : ∀ K : S, zeroCLM K ∈ S := by
    intro K
    change (0 : Matrix (Fin r) (Fin r) ℂ) ∈ sourceSymmetricMatrixSubmodule r
    simp [sourceSymmetricMatrixSubmodule]
  have hcod :
      HasStrictFDerivAt
        (fun K : S =>
          ⟨K.1 * sourceHeadMetric d r hrD * K.1,
            (sourceHeadMetricQuadraticSymm d r hrD K).2⟩ :
            S → S)
        (zeroCLM.codRestrict S hzeroMem) 0 :=
    hasStrictFDerivAt_submodule_codRestrict_local S hamb
      (fun K => (sourceHeadMetricQuadraticSymm d r hrD K).2)
      hzeroMem
  have hzero :
      zeroCLM.codRestrict S hzeroMem =
        (0 : S →L[ℂ] S) := by
    ext K
    rfl
  simpa [S, sourceHeadMetricQuadraticSymm] using hcod.congr_fderiv hzero

/-- The sliced Gram polynomial has strict derivative `K ↦ 2K` at the origin. -/
theorem sourceHeadSliceGramPolynomial_hasStrictFDerivAt
    (d r : ℕ)
    (hrD : r < d + 1) :
    HasStrictFDerivAt
      (sourceHeadSliceGramPolynomial d r hrD)
      (sourceHeadSliceGramPolynomialDerivEquiv r :
        sourceSymmetricMatrixSubmodule r →L[ℂ]
          sourceSymmetricMatrixSubmodule r) 0 := by
  let S := sourceSymmetricMatrixSubmodule r
  let ηS := sourceHeadMetricSymmSubmodule d r hrD
  let D : S →L[ℂ] S :=
    (sourceHeadSliceGramPolynomialDerivEquiv r :
      S →L[ℂ] S)
  let Q := sourceHeadMetricQuadraticSymm d r hrD
  have hlin : HasStrictFDerivAt (fun K : S => D K) D 0 :=
    D.hasStrictFDerivAt
  have hquad : HasStrictFDerivAt Q (0 : S →L[ℂ] S) 0 := by
    simpa [S, Q] using
      sourceHeadMetricQuadraticSymm_hasStrictFDerivAt_zero d r hrD
  have hsum : HasStrictFDerivAt (fun K : S => D K + Q K) D 0 := by
    have hsum0 := hlin.add hquad
    have hD : D + (0 : S →L[ℂ] S) = D := by
      ext K
      simp
    simpa [Pi.add_apply] using hsum0.congr_fderiv hD
  have hconst : HasStrictFDerivAt (fun K : S => ηS + (D K + Q K)) D 0 :=
    hsum.const_add ηS
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards with K
  apply Subtype.ext
  simp [sourceHeadSliceGramPolynomial, sourceHeadMetricQuadraticSymm,
    sourceHeadMetricSymmSubmodule, D, sourceHeadSliceGramPolynomialDerivEquiv,
    ηS, Q, add_assoc]

/-- The inverse-function-theorem local chart for the sliced head Gram
polynomial. -/
noncomputable def sourceHeadSliceGramPolynomialOpenPartialHomeomorph
    (d r : ℕ)
    (hrD : r < d + 1) :
    OpenPartialHomeomorph
      (sourceSymmetricMatrixSubmodule r)
      (sourceSymmetricMatrixSubmodule r) := by
  have hderiv :
      HasStrictFDerivAt
        (sourceHeadSliceGramPolynomial d r hrD)
        (sourceHeadSliceGramPolynomialDerivEquiv r :
          sourceSymmetricMatrixSubmodule r →L[ℂ]
            sourceSymmetricMatrixSubmodule r) 0 :=
    sourceHeadSliceGramPolynomial_hasStrictFDerivAt d r hrD
  exact
    @HasStrictFDerivAt.toOpenPartialHomeomorph ℂ _
      (sourceSymmetricMatrixSubmodule r) _ _
      (sourceSymmetricMatrixSubmodule r) _ _
      (sourceHeadSliceGramPolynomial d r hrD)
      (sourceHeadSliceGramPolynomialDerivEquiv r) 0
      (sourceSymmetricMatrixSubmodule_completeSpace r)
      hderiv

@[simp]
theorem sourceHeadSliceGramPolynomialOpenPartialHomeomorph_coe
    (d r : ℕ)
    (hrD : r < d + 1) :
    (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD :
      sourceSymmetricMatrixSubmodule r → sourceSymmetricMatrixSubmodule r) =
      sourceHeadSliceGramPolynomial d r hrD :=
  rfl

theorem sourceHeadSliceGramPolynomial_zero_mem_chartSource
    (d r : ℕ)
    (hrD : r < d + 1) :
    (0 : sourceSymmetricMatrixSubmodule r) ∈
      (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).source := by
  have hderiv :
      HasStrictFDerivAt
        (sourceHeadSliceGramPolynomial d r hrD)
        (sourceHeadSliceGramPolynomialDerivEquiv r :
          sourceSymmetricMatrixSubmodule r →L[ℂ]
            sourceSymmetricMatrixSubmodule r) 0 :=
    sourceHeadSliceGramPolynomial_hasStrictFDerivAt d r hrD
  unfold sourceHeadSliceGramPolynomialOpenPartialHomeomorph
  simp only [HasStrictFDerivAt.toOpenPartialHomeomorph,
    ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  exact (Classical.choose_spec hderiv.approximates_deriv_on_open_nhds).1

theorem sourceHeadSliceGramPolynomial_center_mem_chartTarget
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadMetricSymmSubmodule d r hrD ∈
      (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).target := by
  have hsource :=
    sourceHeadSliceGramPolynomial_zero_mem_chartSource d r hrD
  have htarget :=
    (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).map_source
      hsource
  simpa using htarget

theorem sourceHeadSliceGramPolynomial_chartSource_mem_nhds_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).source ∈
      𝓝 (0 : sourceSymmetricMatrixSubmodule r) :=
  (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).open_source.mem_nhds
    (sourceHeadSliceGramPolynomial_zero_mem_chartSource d r hrD)

theorem sourceHeadSliceGramPolynomial_chartTarget_mem_nhds_center
    (d r : ℕ)
    (hrD : r < d + 1) :
    (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).target ∈
      𝓝 (sourceHeadMetricSymmSubmodule d r hrD) :=
  (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).open_target.mem_nhds
    (sourceHeadSliceGramPolynomial_center_mem_chartTarget d r hrD)

theorem sourceHeadSliceGramPolynomial_right_inv_on_chartTarget
    (d r : ℕ)
    (hrD : r < d + 1)
    {A : sourceSymmetricMatrixSubmodule r}
    (hA : A ∈
      (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).target) :
    sourceHeadSliceGramPolynomial d r hrD
        ((sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).symm A) =
      A := by
  simpa [sourceHeadSliceGramPolynomialOpenPartialHomeomorph_coe] using
    (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).right_inv hA

theorem sourceHeadSliceGramPolynomial_left_inv_on_chartSource
    (d r : ℕ)
    (hrD : r < d + 1)
    {K : sourceSymmetricMatrixSubmodule r}
    (hK : K ∈
      (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).source) :
    (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).symm
        (sourceHeadSliceGramPolynomial d r hrD K) =
      K := by
  simpa [sourceHeadSliceGramPolynomialOpenPartialHomeomorph_coe] using
    (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).left_inv hK

/-- The local IFT chart restricted to a fixed small coordinate window where
the recovered head factor is invertible. -/
noncomputable def sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph
    (d r : ℕ)
    (hrD : r < d + 1) :
    OpenPartialHomeomorph
      (sourceSymmetricMatrixSubmodule r)
      (sourceSymmetricMatrixSubmodule r) :=
  (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).restrOpen
    (sourceSymmetricMatrixCoordinateWindow r
      (sourceHeadSliceGaugeIFTWindowRadius r))
    (isOpen_sourceSymmetricMatrixCoordinateWindow r
      (sourceHeadSliceGaugeIFTWindowRadius r))

@[simp]
theorem sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph_coe
    (d r : ℕ)
    (hrD : r < d + 1) :
    (sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD :
      sourceSymmetricMatrixSubmodule r → sourceSymmetricMatrixSubmodule r) =
      sourceHeadSliceGramPolynomial d r hrD :=
  rfl

@[simp]
theorem sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph_source
    (d r : ℕ)
    (hrD : r < d + 1) :
    (sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD).source =
      (sourceHeadSliceGramPolynomialOpenPartialHomeomorph d r hrD).source ∩
        sourceSymmetricMatrixCoordinateWindow r
          (sourceHeadSliceGaugeIFTWindowRadius r) :=
  rfl

theorem sourceHeadSliceGramPolynomialRestricted_zero_mem_chartSource
    (d r : ℕ)
    (hrD : r < d + 1) :
    (0 : sourceSymmetricMatrixSubmodule r) ∈
      (sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD).source := by
  simp [sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph,
    sourceHeadSliceGramPolynomial_zero_mem_chartSource,
    zero_mem_sourceSymmetricMatrixCoordinateWindow,
    sourceHeadSliceGaugeIFTWindowRadius_pos]

theorem sourceHeadSliceGramPolynomialRestricted_center_mem_chartTarget
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadMetricSymmSubmodule d r hrD ∈
      (sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD).target := by
  have hsource :=
    sourceHeadSliceGramPolynomialRestricted_zero_mem_chartSource d r hrD
  have htarget :=
    (sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD).map_source
      hsource
  simpa using htarget

/-- Slice-domain set for the final head-slice gauge data. -/
def sourceHeadSliceIFTFactorDomain
    (d r : ℕ)
    (hrD : r < d + 1) :
    Set (SourceHeadGaugeSlice d r hrD) :=
  {H | sourceHeadGaugeSliceSymmCoord d r hrD H ∈
    (sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD).source}

/-- Target symmetric-head neighborhood for the final head-slice gauge data,
expressed in the legacy `SourceSymmetricMatrixCoord` subtype. -/
def sourceHeadSliceIFTTargetU
    (d r : ℕ)
    (hrD : r < d + 1) :
    Set (SourceSymmetricMatrixCoord r) :=
  {A | sourceSymmetricMatrixCoordToSubmodule r A ∈
    (sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD).target}

/-- The local inverse head factor produced by the restricted head-slice chart. -/
noncomputable def sourceHeadSliceIFTFactor
    (d r : ℕ)
    (hrD : r < d + 1)
    (A : SourceSymmetricMatrixCoord r) :
    SourceHeadGaugeSlice d r hrD :=
  sourceHeadGaugeSliceOfSymmCoord d r hrD
    ((sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD).symm
      (sourceSymmetricMatrixCoordToSubmodule r A))

theorem isOpen_sourceHeadSliceIFTFactorDomain
    (d r : ℕ)
    (hrD : r < d + 1) :
    IsOpen (sourceHeadSliceIFTFactorDomain d r hrD) := by
  have hcont :
      Continuous (sourceHeadGaugeSliceSymmCoord d r hrD) :=
    (sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD).continuous
  exact
    (sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD).open_source.preimage
      hcont

theorem sourceHeadSliceIFTFactorDomain_center_mem
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadGaugeSliceCenter d r hrD ∈
      sourceHeadSliceIFTFactorDomain d r hrD := by
  simpa [sourceHeadSliceIFTFactorDomain] using
    sourceHeadSliceGramPolynomialRestricted_zero_mem_chartSource d r hrD

theorem sourceHeadSliceIFTFactorDomain_coordinate
    (d r : ℕ)
    (hrD : r < d + 1) :
    ∃ ρ : ℝ, 0 < ρ ∧
      sourceHeadGaugeSliceCoordinateWindow d r hrD ρ ⊆
        sourceHeadSliceIFTFactorDomain d r hrD := by
  exact
    exists_sourceHeadGaugeSliceCoordinateWindow_subset_of_mem_nhds_center
      d r hrD
      ((isOpen_sourceHeadSliceIFTFactorDomain d r hrD).mem_nhds
        (sourceHeadSliceIFTFactorDomain_center_mem d r hrD))

theorem isOpen_sourceHeadSliceIFTTargetU
    (d r : ℕ)
    (hrD : r < d + 1) :
    IsOpen (sourceHeadSliceIFTTargetU d r hrD) :=
  (sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD).open_target.preimage
    (sourceSymmetricMatrixCoordToSubmodule r).continuous

theorem sourceHeadSliceIFTTargetU_center_mem
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadMetricSymmCoord d r hrD ∈
      sourceHeadSliceIFTTargetU d r hrD := by
  simpa [sourceHeadSliceIFTTargetU, sourceHeadMetricSymmCoord,
    sourceHeadMetricSymmSubmodule] using
    sourceHeadSliceGramPolynomialRestricted_center_mem_chartTarget d r hrD

theorem sourceHeadSliceIFTFactor_mem_domain
    (d r : ℕ)
    (hrD : r < d + 1)
    (A : SourceSymmetricMatrixCoord r)
    (hA : A ∈ sourceHeadSliceIFTTargetU d r hrD) :
    sourceHeadSliceIFTFactor d r hrD A ∈
      sourceHeadSliceIFTFactorDomain d r hrD := by
  let e := sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD
  have htarget :
      sourceSymmetricMatrixCoordToSubmodule r A ∈ e.target := by
    simpa [sourceHeadSliceIFTTargetU, e] using hA
  have hsource : e.symm (sourceSymmetricMatrixCoordToSubmodule r A) ∈ e.source :=
    e.symm.map_source htarget
  simpa [sourceHeadSliceIFTFactorDomain, sourceHeadSliceIFTFactor, e] using hsource

theorem sourceHeadSliceIFTFactor_continuousOn
    (d r : ℕ)
    (hrD : r < d + 1) :
    ContinuousOn (sourceHeadSliceIFTFactor d r hrD)
      (sourceHeadSliceIFTTargetU d r hrD) := by
  let e := sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD
  have hcoord :
      ContinuousOn (fun A : SourceSymmetricMatrixCoord r =>
        sourceSymmetricMatrixCoordToSubmodule r A)
        (sourceHeadSliceIFTTargetU d r hrD) :=
    (sourceSymmetricMatrixCoordToSubmodule r).continuous.continuousOn
  have hmaps :
      ∀ A ∈ sourceHeadSliceIFTTargetU d r hrD,
        sourceSymmetricMatrixCoordToSubmodule r A ∈ e.target := by
    intro A hA
    simpa [sourceHeadSliceIFTTargetU, e] using hA
  have hsymm :
      ContinuousOn
        (fun A : SourceSymmetricMatrixCoord r =>
          e.symm (sourceSymmetricMatrixCoordToSubmodule r A))
        (sourceHeadSliceIFTTargetU d r hrD) :=
    ContinuousOn.comp e.symm.continuousOn hcoord hmaps
  exact
    (sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD).symm.continuous.comp_continuousOn
      hsymm

theorem sourceHeadSliceIFTFactor_center
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadSliceIFTFactor d r hrD
        (sourceHeadMetricSymmCoord d r hrD) =
      sourceHeadGaugeSliceCenter d r hrD := by
  let e := sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD
  have hsource :
      (0 : sourceSymmetricMatrixSubmodule r) ∈ e.source := by
    simpa [e] using
      sourceHeadSliceGramPolynomialRestricted_zero_mem_chartSource d r hrD
  have hsymm :
      e.symm (sourceHeadMetricSymmSubmodule d r hrD) =
        (0 : sourceSymmetricMatrixSubmodule r) := by
    have hleft := e.left_inv hsource
    simpa [e, sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph_coe,
      sourceHeadSliceGramPolynomial_zero] using hleft
  change sourceHeadGaugeSliceOfSymmCoord d r hrD
      (e.symm
        (sourceSymmetricMatrixCoordToSubmodule r
          (sourceHeadMetricSymmCoord d r hrD))) =
    sourceHeadGaugeSliceCenter d r hrD
  rw [show sourceSymmetricMatrixCoordToSubmodule r
      (sourceHeadMetricSymmCoord d r hrD) =
        sourceHeadMetricSymmSubmodule d r hrD by rfl, hsymm]
  simp

theorem sourceHeadSliceIFTFactor_gram
    (d r : ℕ)
    (hrD : r < d + 1)
    (A : SourceSymmetricMatrixCoord r)
    (hA : A ∈ sourceHeadSliceIFTTargetU d r hrD) :
    (sourceHeadSliceIFTFactor d r hrD A).1 *
        sourceHeadMetric d r hrD *
        (sourceHeadSliceIFTFactor d r hrD A).1ᵀ =
      (A : Matrix (Fin r) (Fin r) ℂ) := by
  let e := sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD
  let K := e.symm (sourceSymmetricMatrixCoordToSubmodule r A)
  have htarget :
      sourceSymmetricMatrixCoordToSubmodule r A ∈ e.target := by
    simpa [sourceHeadSliceIFTTargetU, e] using hA
  have hpoly :
      sourceHeadSliceGramPolynomial d r hrD K =
        sourceSymmetricMatrixCoordToSubmodule r A := by
    have hright := e.right_inv htarget
    simpa [K, e, sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph_coe]
      using hright
  have hgram := sourceHeadSliceGramPolynomial_eq_factorGram d r hrD K
  calc
    (sourceHeadSliceIFTFactor d r hrD A).1 *
        sourceHeadMetric d r hrD *
        (sourceHeadSliceIFTFactor d r hrD A).1ᵀ =
        (sourceHeadSliceGramPolynomial d r hrD K :
          Matrix (Fin r) (Fin r) ℂ) := by
          simpa [sourceHeadSliceIFTFactor, K] using hgram.symm
    _ = (A : Matrix (Fin r) (Fin r) ℂ) := by
          exact congrArg Subtype.val hpoly

/-- The ordinary Gram coordinate of a slice factor is the sliced Gram
polynomial of its symmetric `K = Hη - η` coordinate. -/
theorem sourceHeadFactorGramSymmCoord_eq_sourceHeadSliceGramPolynomial
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : SourceHeadGaugeSlice d r hrD) :
    sourceSymmetricMatrixCoordToSubmodule r
        (sourceHeadFactorGramSymmCoord d r hrD H.1) =
      sourceHeadSliceGramPolynomial d r hrD
        (sourceHeadGaugeSliceSymmCoord d r hrD H) := by
  let K := sourceHeadGaugeSliceSymmCoord d r hrD H
  apply Subtype.ext
  have hH_eq :
      sourceHeadGaugeSliceOfSymmCoord d r hrD K = H := by
    change sourceHeadGaugeSliceOfSymmCoord d r hrD
        (sourceHeadGaugeSliceSymmCoord d r hrD H) = H
    exact sourceHeadGaugeSliceOfSymmCoord_symmCoord d r hrD H
  calc
    (sourceSymmetricMatrixCoordToSubmodule r
        (sourceHeadFactorGramSymmCoord d r hrD H.1) :
        Matrix (Fin r) (Fin r) ℂ) =
        H.1 * sourceHeadMetric d r hrD * H.1ᵀ := rfl
    _ =
        (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1 *
          sourceHeadMetric d r hrD *
          (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1ᵀ := by
          rw [hH_eq]
    _ =
        (sourceHeadSliceGramPolynomial d r hrD K :
          Matrix (Fin r) (Fin r) ℂ) := by
          exact (sourceHeadSliceGramPolynomial_eq_factorGram d r hrD K).symm

theorem sourceHeadSliceIFTFactorDomain_mem
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : SourceHeadGaugeSlice d r hrD)
    (hH : H ∈ sourceHeadSliceIFTFactorDomain d r hrD) :
    sourceHeadFactorGramSymmCoord d r hrD H.1 ∈
      sourceHeadSliceIFTTargetU d r hrD := by
  let e := sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD
  let K := sourceHeadGaugeSliceSymmCoord d r hrD H
  have hK : K ∈ e.source := by
    simpa [sourceHeadSliceIFTFactorDomain, K, e] using hH
  have htarget : e K ∈ e.target := e.map_source hK
  have hpoly_target :
      sourceHeadSliceGramPolynomial d r hrD K ∈ e.target := by
    simpa [e, sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph_coe]
      using htarget
  have hAeq :
      sourceSymmetricMatrixCoordToSubmodule r
          (sourceHeadFactorGramSymmCoord d r hrD H.1) =
        sourceHeadSliceGramPolynomial d r hrD K := by
    simpa [K] using
      sourceHeadFactorGramSymmCoord_eq_sourceHeadSliceGramPolynomial d r hrD H
  simpa [sourceHeadSliceIFTTargetU, hAeq, e] using hpoly_target

theorem sourceHeadSliceIFTFactor_left_inverse
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : SourceHeadGaugeSlice d r hrD)
    (hH : H ∈ sourceHeadSliceIFTFactorDomain d r hrD) :
    sourceHeadSliceIFTFactor d r hrD
        (sourceHeadFactorGramSymmCoord d r hrD H.1) = H := by
  let e := sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD
  let K := sourceHeadGaugeSliceSymmCoord d r hrD H
  have hK : K ∈ e.source := by
    simpa [sourceHeadSliceIFTFactorDomain, K, e] using hH
  have hleft :
      e.symm (sourceHeadSliceGramPolynomial d r hrD K) = K := by
    have h := e.left_inv hK
    simpa [e, sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph_coe]
      using h
  have hAeq :
      sourceSymmetricMatrixCoordToSubmodule r
          (sourceHeadFactorGramSymmCoord d r hrD H.1) =
        sourceHeadSliceGramPolynomial d r hrD K := by
    simpa [K] using
      sourceHeadFactorGramSymmCoord_eq_sourceHeadSliceGramPolynomial d r hrD H
  change sourceHeadGaugeSliceOfSymmCoord d r hrD
      (e.symm
        (sourceSymmetricMatrixCoordToSubmodule r
          (sourceHeadFactorGramSymmCoord d r hrD H.1))) = H
  rw [hAeq, hleft]
  exact sourceHeadGaugeSliceOfSymmCoord_symmCoord d r hrD H

theorem sourceHeadSliceIFTFactor_det_unit
    (d r : ℕ)
    (hrD : r < d + 1)
    (A : SourceSymmetricMatrixCoord r)
    (hA : A ∈ sourceHeadSliceIFTTargetU d r hrD) :
    IsUnit ((sourceHeadSliceIFTFactor d r hrD A).1).det := by
  let H := sourceHeadSliceIFTFactor d r hrD A
  have hdomain :
      H ∈ sourceHeadSliceIFTFactorDomain d r hrD := by
    simpa [H] using sourceHeadSliceIFTFactor_mem_domain d r hrD A hA
  let e := sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph d r hrD
  have hKsource :
      sourceHeadGaugeSliceSymmCoord d r hrD H ∈ e.source := by
    simpa [sourceHeadSliceIFTFactorDomain, e] using hdomain
  have hKwindow :
      sourceHeadGaugeSliceSymmCoord d r hrD H ∈
        sourceSymmetricMatrixCoordinateWindow r
          (sourceHeadSliceGaugeIFTWindowRadius r) := by
    simpa [e, sourceHeadSliceGramPolynomialRestrictedOpenPartialHomeomorph_source]
      using hKsource.2
  have hHwindow :
      H ∈ sourceHeadGaugeSliceCoordinateWindow d r hrD
        (sourceHeadSliceGaugeIFTWindowRadius r) :=
    (sourceHeadGaugeSliceSymmCoord_mem_coordinateWindow_iff d r hrD
      (sourceHeadSliceGaugeIFTWindowRadius r) H).1 hKwindow
  exact
    sourceHeadGaugeSliceCoordinateWindow_det_isUnit d r hrD
      (sourceHeadSliceGaugeIFTWindowRadius_pos r)
      (sourceHeadSliceGaugeIFTWindowRadius_lt_half r)
      (sourceHeadSliceGaugeIFTWindowRadius_card_mul_lt_half r)
      hHwindow

/-- Checked finite-dimensional local producer for the corrected rank-deficient
head-slice gauge data. -/
noncomputable def sourceRankDeficientHeadSliceGaugeData
    (d r : ℕ)
    (hrD : r < d + 1) :
    SourceRankDeficientHeadSliceGaugeData d r hrD where
  factorDomain := sourceHeadSliceIFTFactorDomain d r hrD
  factorDomain_open := isOpen_sourceHeadSliceIFTFactorDomain d r hrD
  factorDomain_center_mem := sourceHeadSliceIFTFactorDomain_center_mem d r hrD
  factorDomain_coordinate := sourceHeadSliceIFTFactorDomain_coordinate d r hrD
  U := sourceHeadSliceIFTTargetU d r hrD
  U_open := isOpen_sourceHeadSliceIFTTargetU d r hrD
  center_mem := sourceHeadSliceIFTTargetU_center_mem d r hrD
  factor := sourceHeadSliceIFTFactor d r hrD
  factor_mem_domain := sourceHeadSliceIFTFactor_mem_domain d r hrD
  factor_continuousOn := sourceHeadSliceIFTFactor_continuousOn d r hrD
  factor_center := sourceHeadSliceIFTFactor_center d r hrD
  factor_gram := sourceHeadSliceIFTFactor_gram d r hrD
  factorDomain_mem := sourceHeadSliceIFTFactorDomain_mem d r hrD
  factor_left_inverse := sourceHeadSliceIFTFactor_left_inverse d r hrD
  factor_det_unit := sourceHeadSliceIFTFactor_det_unit d r hrD

end BHW
