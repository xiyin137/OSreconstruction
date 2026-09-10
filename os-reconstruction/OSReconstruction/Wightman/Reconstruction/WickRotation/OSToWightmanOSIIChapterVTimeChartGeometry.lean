import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTimeChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceGeometry

/-!
# OS-II Chapter V Reflected Time-Chart Geometry

This file identifies the doubled Chapter V scalar chart with the existing
two-block axis-pair coordinate change.  Each block starts with a fixed zeroth
absolute-time coordinate and has independently translated chronological gaps.
After reflecting and reversing the left block, the global difference chart has
one extra zeroth coordinate recording a common translation.  Removing that
coordinate leaves exactly the reduced Chapter V displacement.
-/

noncomputable section

open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The two separate `(k + 1)`-point chronological source displacements before
the reflected-left blocks are assembled into one global difference chart. -/
def reflectedBlockTimeDisplacement
    {𝕜 : Type*} [Neg 𝕜] [Zero 𝕜]
    {k : ℕ}
    (u : Fin (k + k) → 𝕜) :
    Fin ((k + 1) + (k + 1)) → 𝕜 :=
  Fin.append
    (Fin.cons 0 fun i => -u (Fin.castAdd k i))
    (Fin.cons 0 fun i => -u (Fin.natAdd k i))

@[simp] theorem reflectedBlockTimeDisplacement_left_zero
    {𝕜 : Type*} [Neg 𝕜] [Zero 𝕜]
    {k : ℕ}
    (u : Fin (k + k) → 𝕜) :
    reflectedBlockTimeDisplacement u
        (Fin.castAdd (k + 1) (0 : Fin (k + 1))) = 0 := by
  simp [reflectedBlockTimeDisplacement]

@[simp] theorem reflectedBlockTimeDisplacement_left_succ
    {𝕜 : Type*} [Neg 𝕜] [Zero 𝕜]
    {k : ℕ}
    (u : Fin (k + k) → 𝕜)
    (i : Fin k) :
    reflectedBlockTimeDisplacement u
        (Fin.castAdd (k + 1) i.succ) =
      -u (Fin.castAdd k i) := by
  simp [reflectedBlockTimeDisplacement]

@[simp] theorem reflectedBlockTimeDisplacement_right_zero
    {𝕜 : Type*} [Neg 𝕜] [Zero 𝕜]
    {k : ℕ}
    (u : Fin (k + k) → 𝕜) :
    reflectedBlockTimeDisplacement u
        (Fin.natAdd (k + 1) (0 : Fin (k + 1))) = 0 := by
  rw [reflectedBlockTimeDisplacement, Fin.append_right]
  simp

@[simp] theorem reflectedBlockTimeDisplacement_right_succ
    {𝕜 : Type*} [Neg 𝕜] [Zero 𝕜]
    {k : ℕ}
    (u : Fin (k + k) → 𝕜)
    (i : Fin k) :
    reflectedBlockTimeDisplacement u
        (Fin.natAdd (k + 1) i.succ) =
      -u (Fin.natAdd k i) := by
  rw [reflectedBlockTimeDisplacement, Fin.append_right]
  simp

@[simp] theorem splitFirst_reflectedBlockTimeDisplacement
    {k : ℕ}
    (u : Fin (k + k) → ℝ) :
    splitFirst (k + 1) (k + 1)
        (reflectedBlockTimeDisplacement u) =
      Fin.cons 0 (fun i => -u (Fin.castAdd k i)) := by
  exact splitFirst_fin_append _ _

@[simp] theorem splitLast_reflectedBlockTimeDisplacement
    {k : ℕ}
    (u : Fin (k + k) → ℝ) :
    splitLast (k + 1) (k + 1)
        (reflectedBlockTimeDisplacement u) =
      Fin.cons 0 (fun i => -u (Fin.natAdd k i)) := by
  exact splitLast_fin_append _ _

/-- Successive cumulative coordinates recover the corresponding nonzeroth
difference coordinate. -/
private theorem section43ScalarDiffCLE_symm_succ_sub_castSucc
    {k : ℕ}
    (δ : Fin (k + 1) → ℝ)
    (i : Fin k) :
    (section43ScalarDiffCLE (k + 1)).symm δ i.succ -
        (section43ScalarDiffCLE (k + 1)).symm δ i.castSucc =
      δ i.succ := by
  have h := congrFun
    ((section43ScalarDiffCLE (k + 1)).apply_symm_apply δ) i.succ
  simpa [section43ScalarDiffCLE_apply] using h

/-- The reflected two-block global chart, with its common-translation
coordinate removed, is exactly the doubled Chapter V reduced displacement. -/
theorem osiiAxisPairBlockGlobalTimeCLE_reflectedBlockTimeDisplacement_tail
    {k : ℕ}
    (u : Fin (k + k) → ℝ)
    (j : Fin (k + (k + 1))) :
    osiiAxisPairBlockGlobalTimeCLE (k + 1) (k + 1)
        (reflectedBlockTimeDisplacement u)
        ⟨j.val + 1, by omega⟩ =
      reflectedReducedTimeDisplacement u j := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedReducedTimeDisplacement_left]
    change
      section43ScalarDiffCLE ((k + 1) + (k + 1))
          (osiiAxisPairReflectReverseLeftTimeCLE (k + 1) (k + 1)
            ((osiiAxisPairBlockwiseTimeDiffCLE (k + 1) (k + 1)).symm
              (reflectedBlockTimeDisplacement u)))
          ⟨i.val + 1, by omega⟩ =
        -u (Fin.castAdd k (Fin.rev i))
    rw [section43ScalarDiffCLE_apply]
    rw [dif_neg (by
      simpa only [Nat.succ_eq_add_one] using Nat.succ_ne_zero i.val)]
    have hcurrent :
        (⟨i.val + 1, by omega⟩ :
            Fin ((k + 1) + (k + 1))) =
          Fin.castAdd (k + 1) i.succ := by
      ext
      rfl
    have hprevious :
        (⟨i.val + 1 - 1, by omega⟩ :
            Fin ((k + 1) + (k + 1))) =
          Fin.castAdd (k + 1) i.castSucc := by
      ext
      simp
    simp only [hcurrent, hprevious,
      osiiAxisPairReflectReverseLeftTimeCLE_apply_left,
      osiiAxisPairReflectReverseLeftTimeCLE_apply_left,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left]
    rw [Fin.rev_succ, Fin.rev_castSucc]
    have hdiff :=
      section43ScalarDiffCLE_symm_succ_sub_castSucc
        (splitFirst (k + 1) (k + 1)
          (reflectedBlockTimeDisplacement u))
        (Fin.rev i)
    have hvalue :
        splitFirst (k + 1) (k + 1)
            (reflectedBlockTimeDisplacement u) (Fin.rev i).succ =
          -u (Fin.castAdd k (Fin.rev i)) := by
      rw [splitFirst_reflectedBlockTimeDisplacement]
      simp
    rw [hvalue] at hdiff
    linarith
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · rw [reflectedReducedTimeDisplacement_bridge]
      change
        section43ScalarDiffCLE ((k + 1) + (k + 1))
            (osiiAxisPairReflectReverseLeftTimeCLE (k + 1) (k + 1)
              ((osiiAxisPairBlockwiseTimeDiffCLE (k + 1) (k + 1)).symm
                (reflectedBlockTimeDisplacement u)))
            ⟨k + 1, by omega⟩ = 0
      rw [section43ScalarDiffCLE_apply]
      rw [dif_neg (by
        simpa only [Nat.succ_eq_add_one] using Nat.succ_ne_zero k)]
      have hcurrent :
          (⟨k + 1, by omega⟩ :
              Fin ((k + 1) + (k + 1))) =
            Fin.natAdd (k + 1) (0 : Fin (k + 1)) := by
        ext
        simp
      have hprevious :
          (⟨k + 1 - 1, by omega⟩ :
              Fin ((k + 1) + (k + 1))) =
            Fin.castAdd (k + 1) (Fin.last k) := by
        ext
        simp
      simp only [hcurrent, hprevious,
        osiiAxisPairReflectReverseLeftTimeCLE_apply_right,
        osiiAxisPairReflectReverseLeftTimeCLE_apply_left,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left]
      have hright0 :
          (section43ScalarDiffCLE (k + 1)).symm
              (splitLast (k + 1) (k + 1)
                (reflectedBlockTimeDisplacement u)) 0 = 0 := by
        rw [section43ScalarDiffCLE_symm_apply]
        simp
      have hleft0 :
          (section43ScalarDiffCLE (k + 1)).symm
              (splitFirst (k + 1) (k + 1)
                (reflectedBlockTimeDisplacement u))
              (Fin.rev (Fin.last k)) = 0 := by
        rw [Fin.rev_last, section43ScalarDiffCLE_symm_apply]
        simp
      simpa only [hright0, hleft0, neg_zero, sub_zero]
    · rw [reflectedReducedTimeDisplacement_right]
      change
        section43ScalarDiffCLE ((k + 1) + (k + 1))
            (osiiAxisPairReflectReverseLeftTimeCLE (k + 1) (k + 1)
              ((osiiAxisPairBlockwiseTimeDiffCLE (k + 1) (k + 1)).symm
                (reflectedBlockTimeDisplacement u)))
            ⟨k + i.val + 2, by omega⟩ =
          -u (Fin.natAdd k i)
      rw [section43ScalarDiffCLE_apply]
      rw [dif_neg (by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
          Nat.succ_ne_zero (k + i.val + 1))]
      have hcurrent :
          (⟨k + i.val + 2, by omega⟩ :
              Fin ((k + 1) + (k + 1))) =
            Fin.natAdd (k + 1) i.succ := by
        ext
        simp
        omega
      have hprevious :
          (⟨k + i.val + 2 - 1, by omega⟩ :
              Fin ((k + 1) + (k + 1))) =
            Fin.natAdd (k + 1) i.castSucc := by
        ext
        simp
        omega
      simp only [hcurrent, hprevious,
        osiiAxisPairReflectReverseLeftTimeCLE_apply_right,
        osiiAxisPairReflectReverseLeftTimeCLE_apply_right,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right]
      have hdiff :=
        section43ScalarDiffCLE_symm_succ_sub_castSucc
          (splitLast (k + 1) (k + 1)
            (reflectedBlockTimeDisplacement u))
          i
      have hvalue :
          splitLast (k + 1) (k + 1)
              (reflectedBlockTimeDisplacement u) i.succ =
            -u (Fin.natAdd k i) := by
        rw [splitLast_reflectedBlockTimeDisplacement]
        simp
      rw [hvalue] at hdiff
      exact hdiff

end OSIIChapterV
end OSReconstruction
