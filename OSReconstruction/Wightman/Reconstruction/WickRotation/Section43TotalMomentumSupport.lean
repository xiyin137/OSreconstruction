import OSReconstruction.Wightman.Reconstruction.HeadBlockDecomposition
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

/-!
# Section 4.3 Total-Momentum Support Infrastructure

This file contains the finite-dimensional coordinate change that exposes the
total-momentum hyperplane as a zero head block.  It is the bridge between the
generic compact head-block division theorem and the Section 4.3
total-momentum support theorem.
-/

noncomputable def section43TotalMomentumHeadTailForward
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) :
    Fin ((d + 1) + (N' * (d + 1))) → ℝ :=
  fun i =>
    Fin.addCases
      (fun μ : Fin (d + 1) => section43TotalMomentumFlat d (N' + 1) ξ μ)
      (fun j : Fin (N' * (d + 1)) =>
        let p := finProdFinEquiv.symm j
        ξ (finProdFinEquiv (p.1.succ, p.2)))
      i

noncomputable def section43TotalMomentumHeadTailInverse
    (d N' : ℕ) [NeZero d]
    (η : Fin ((d + 1) + (N' * (d + 1))) → ℝ) :
    Fin ((N' + 1) * (d + 1)) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i
    Fin.cases
      (η (Fin.castAdd (N' * (d + 1)) p.2) -
        ∑ j : Fin N', η (Fin.natAdd (d + 1) (finProdFinEquiv (j, p.2))))
      (fun j : Fin N' => η (Fin.natAdd (d + 1) (finProdFinEquiv (j, p.2))))
      p.1

@[simp] theorem section43TotalMomentumHeadTailForward_head
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) (μ : Fin (d + 1)) :
    section43TotalMomentumHeadTailForward d N' ξ (Fin.castAdd (N' * (d + 1)) μ) =
      section43TotalMomentumFlat d (N' + 1) ξ μ := by
  simp [section43TotalMomentumHeadTailForward]

@[simp] theorem section43TotalMomentumHeadTailForward_tail
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) (j : Fin (N' * (d + 1))) :
    section43TotalMomentumHeadTailForward d N' ξ (Fin.natAdd (d + 1) j) =
      ξ (finProdFinEquiv ((finProdFinEquiv.symm j).1.succ, (finProdFinEquiv.symm j).2)) := by
  simp [section43TotalMomentumHeadTailForward]

@[simp] theorem section43TotalMomentumHeadTailInverse_zero
    (d N' : ℕ) [NeZero d]
    (η : Fin ((d + 1) + (N' * (d + 1))) → ℝ) (μ : Fin (d + 1)) :
    section43TotalMomentumHeadTailInverse d N' η
        (finProdFinEquiv ((0 : Fin (N' + 1)), μ)) =
      η (Fin.castAdd (N' * (d + 1)) μ) -
        ∑ j : Fin N', η (Fin.natAdd (d + 1) (finProdFinEquiv (j, μ))) := by
  simp [section43TotalMomentumHeadTailInverse]

@[simp] theorem section43TotalMomentumHeadTailInverse_succ
    (d N' : ℕ) [NeZero d]
    (η : Fin ((d + 1) + (N' * (d + 1))) → ℝ)
    (j : Fin N') (μ : Fin (d + 1)) :
    section43TotalMomentumHeadTailInverse d N' η (finProdFinEquiv (j.succ, μ)) =
      η (Fin.natAdd (d + 1) (finProdFinEquiv (j, μ))) := by
  simp [section43TotalMomentumHeadTailInverse]

theorem section43TotalMomentumHeadTail_left_inv
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) :
    section43TotalMomentumHeadTailInverse d N'
        (section43TotalMomentumHeadTailForward d N' ξ) = ξ := by
  ext i
  let p : Fin (N' + 1) × Fin (d + 1) := finProdFinEquiv.symm i
  have hi : finProdFinEquiv p = i := by
    exact Equiv.apply_symm_apply finProdFinEquiv i
  rcases p with ⟨k, μ⟩
  cases k using Fin.cases with
  | zero =>
      rw [← hi]
      simp [section43TotalMomentumFlat]
      rw [Fin.sum_univ_succ]
      ring_nf
  | succ j =>
      rw [← hi]
      simp

theorem section43TotalMomentumHeadTail_right_inv
    (d N' : ℕ) [NeZero d]
    (η : Fin ((d + 1) + (N' * (d + 1))) → ℝ) :
    section43TotalMomentumHeadTailForward d N'
        (section43TotalMomentumHeadTailInverse d N' η) = η := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro μ
    simp [section43TotalMomentumHeadTailForward, section43TotalMomentumFlat]
    rw [Fin.sum_univ_succ]
    simp [section43TotalMomentumHeadTailInverse_zero,
      section43TotalMomentumHeadTailInverse_succ]
  · intro j
    rw [section43TotalMomentumHeadTailForward_tail]
    let p : Fin N' × Fin (d + 1) := finProdFinEquiv.symm j
    have hj : finProdFinEquiv p = j := by
      exact Equiv.apply_symm_apply finProdFinEquiv j
    change section43TotalMomentumHeadTailInverse d N' η
        (finProdFinEquiv (p.1.succ, p.2)) =
      η (Fin.natAdd (d + 1) j)
    rcases p with ⟨k, μ⟩
    rw [section43TotalMomentumHeadTailInverse_succ]
    change η (Fin.natAdd (d + 1) (finProdFinEquiv (k, μ))) =
      η (Fin.natAdd (d + 1) j)
    rw [hj]

noncomputable def section43TotalMomentumHeadTailLinearEquiv
    (d N' : ℕ) [NeZero d] :
    (Fin ((N' + 1) * (d + 1)) → ℝ) ≃ₗ[ℝ]
      (Fin ((d + 1) + (N' * (d + 1))) → ℝ) :=
  { toFun := section43TotalMomentumHeadTailForward d N'
    invFun := section43TotalMomentumHeadTailInverse d N'
    map_add' := by
      intro ξ ζ
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro μ
        simp [section43TotalMomentumHeadTailForward, section43TotalMomentumFlat,
          Finset.sum_add_distrib]
      · intro j
        simp [section43TotalMomentumHeadTailForward]
    map_smul' := by
      intro a ξ
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro μ
        simp [section43TotalMomentumHeadTailForward, section43TotalMomentumFlat,
          Finset.mul_sum]
      · intro j
        simp [section43TotalMomentumHeadTailForward]
    left_inv := section43TotalMomentumHeadTail_left_inv d N'
    right_inv := section43TotalMomentumHeadTail_right_inv d N' }

noncomputable def section43TotalMomentumHeadTailCLE
    (d N' : ℕ) [NeZero d] :
    (Fin ((N' + 1) * (d + 1)) → ℝ) ≃L[ℝ]
      (Fin ((d + 1) + (N' * (d + 1))) → ℝ) :=
  (section43TotalMomentumHeadTailLinearEquiv d N').toContinuousLinearEquiv

@[simp] theorem section43TotalMomentumHeadTailCLE_head
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) (μ : Fin (d + 1)) :
    section43TotalMomentumHeadTailCLE d N' ξ (Fin.castAdd (N' * (d + 1)) μ) =
      section43TotalMomentumFlat d (N' + 1) ξ μ := by
  change section43TotalMomentumHeadTailForward d N' ξ
      (Fin.castAdd (N' * (d + 1)) μ) = _
  simp

@[simp] theorem section43TotalMomentumHeadTailCLE_tail
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) (j : Fin (N' * (d + 1))) :
    section43TotalMomentumHeadTailCLE d N' ξ (Fin.natAdd (d + 1) j) =
      ξ (finProdFinEquiv ((finProdFinEquiv.symm j).1.succ, (finProdFinEquiv.symm j).2)) := by
  change section43TotalMomentumHeadTailForward d N' ξ (Fin.natAdd (d + 1) j) = _
  simp

@[simp] theorem section43TotalMomentumHeadTailCLE_symm_zero
    (d N' : ℕ) [NeZero d]
    (η : Fin ((d + 1) + (N' * (d + 1))) → ℝ) (μ : Fin (d + 1)) :
    (section43TotalMomentumHeadTailCLE d N').symm η
        (finProdFinEquiv ((0 : Fin (N' + 1)), μ)) =
      η (Fin.castAdd (N' * (d + 1)) μ) -
        ∑ j : Fin N', η (Fin.natAdd (d + 1) (finProdFinEquiv (j, μ))) := by
  change section43TotalMomentumHeadTailInverse d N' η
      (finProdFinEquiv ((0 : Fin (N' + 1)), μ)) = _
  simp

@[simp] theorem section43TotalMomentumHeadTailCLE_symm_succ
    (d N' : ℕ) [NeZero d]
    (η : Fin ((d + 1) + (N' * (d + 1))) → ℝ)
    (j : Fin N') (μ : Fin (d + 1)) :
    (section43TotalMomentumHeadTailCLE d N').symm η (finProdFinEquiv (j.succ, μ)) =
      η (Fin.natAdd (d + 1) (finProdFinEquiv (j, μ))) := by
  change section43TotalMomentumHeadTailInverse d N' η (finProdFinEquiv (j.succ, μ)) = _
  simp

@[simp] theorem splitFirst_section43TotalMomentumHeadTailCLE
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) :
    splitFirst (d + 1) (N' * (d + 1)) (section43TotalMomentumHeadTailCLE d N' ξ) =
      section43TotalMomentumFlat d (N' + 1) ξ := by
  ext μ
  simp [splitFirst]

@[simp] theorem splitLast_section43TotalMomentumHeadTailCLE
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) :
    splitLast (d + 1) (N' * (d + 1)) (section43TotalMomentumHeadTailCLE d N' ξ) =
      fun j : Fin (N' * (d + 1)) =>
        ξ (finProdFinEquiv ((finProdFinEquiv.symm j).1.succ, (finProdFinEquiv.symm j).2)) := by
  ext j
  simp [splitLast]

end OSReconstruction
