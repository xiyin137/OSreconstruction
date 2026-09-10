/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVProductBasepointMixedDelta












noncomputable section

open Complex MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

/-- Evaluation of an equality-transported finite tuple at a target index. -/
theorem section43TimeTupleTransport_apply_cast
    {n m : Nat} (h : n = m) (x : Fin n -> Real) (j : Fin m) :
    section43TimeTupleTransport h x j = x ((finCongr h).symm j) := by
  subst m
  rfl

/-- The block-global reduced coordinate is exactly the reflected
chronological gap coordinate.  This foundational support identity is shared
by the reflected A0 and equation-`(6.21)` routes. -/
theorem osiiMixedBlockGlobalReducedTime_append_eq_reflectedChronologicalGapMap
    (k : Nat)
    (tauLeft tauRight : Fin (k + 1) -> Real) :
    osiiMixedBlockGlobalReducedTime k (Fin.append tauLeft tauRight) =
      reflectedChronologicalGapMap k (tauLeft, tauRight) := by
  let h :
      (k + 1) + (k + 1) = (k + (k + 1)) + 1 := by omega
  ext i
  change
    section43TimeTupleTransport h
        (osiiAxisPairBlockGlobalTimeAffine
          (k + 1) (k + 1) 0 0 (Fin.append tauLeft tauRight))
        i.succ =
      reflectedChronologicalGapMap k (tauLeft, tauRight) i
  rw [section43TimeTupleTransport_apply_cast]
  let j : Fin ((k + 1) + (k + 1)) := (finCongr h).symm i.succ
  change
    osiiAxisPairBlockGlobalTimeAffine
        (k + 1) (k + 1) 0 0 (Fin.append tauLeft tauRight) j =
      reflectedChronologicalGapMap k (tauLeft, tauRight) i
  rw [← congrFun
    (section43ScalarDiffCLE_blockGlobalAbsoluteTimeConfig
      (k + 1) (k + 1) (by omega) (by omega)
      0 0 (Fin.append tauLeft tauRight)) j]
  rw [section43ScalarDiffCLE_apply, dif_neg (by simp [j])]
  by_cases hleft : i.val < k
  · have hjlt : j.val < k + 1 := by simp [j]; omega
    let a : Fin (k + 1) := ⟨j.val, hjlt⟩
    let a' : Fin (k + 1) := ⟨j.val - 1, by omega⟩
    have hj : j = Fin.castAdd (k + 1) a := by
      apply Fin.ext
      rfl
    have hj' :
        (⟨j.val - 1, by omega⟩ : Fin ((k + 1) + (k + 1))) =
          Fin.castAdd (k + 1) a' := by
      apply Fin.ext
      rfl
    rw [hj', hj,
      osiiAxisPairBlockGlobalAbsoluteTimeConfig_left,
      osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
    let r : Fin (k + 1) := ⟨k - i.val, by omega⟩
    have hr0 : r.val ≠ 0 := by simp [r]; omega
    have hcancel := congrFun
      ((section43ScalarDiffCLE (k + 1)).apply_symm_apply tauLeft) r
    rw [section43ScalarDiffCLE_apply, dif_neg hr0] at hcancel
    have hreva' : Fin.rev a' = r := by
      apply Fin.ext
      simp [a', r, j]
    have hpred :
        (⟨r.val - 1, by omega⟩ : Fin (k + 1)) = Fin.rev a := by
      apply Fin.ext
      simp [a, r, j]
      omega
    simp only [splitFirst_fin_append] at *
    rw [hreva', ← hpred]
    simp [section43ScalarDiffCLE_symm_apply] at hcancel
    simp [reflectedChronologicalGapMap, hleft, r]
    nlinarith [hcancel]
  · by_cases hbridge : i.val = k
    · let a : Fin (k + 1) := ⟨k, by omega⟩
      let b : Fin (k + 1) := 0
      have hj : j = Fin.natAdd (k + 1) b := by
        apply Fin.ext
        simp [j, b, hbridge]
      have hj' :
          (⟨j.val - 1, by omega⟩ : Fin ((k + 1) + (k + 1))) =
            Fin.castAdd (k + 1) a := by
        apply Fin.ext
        simp [j, a, hbridge]
      rw [hj', hj,
        osiiAxisPairBlockGlobalAbsoluteTimeConfig_right,
        osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
      have hleft0 :
          (section43ScalarDiffCLE (k + 1)).symm tauLeft 0 = tauLeft 0 := by
        have hzero := congrFun
          ((section43ScalarDiffCLE (k + 1)).apply_symm_apply tauLeft)
            (0 : Fin (k + 1))
        simpa [section43ScalarDiffCLE_apply] using hzero
      have hright0 :
          (section43ScalarDiffCLE (k + 1)).symm tauRight 0 = tauRight 0 := by
        have hzero := congrFun
          ((section43ScalarDiffCLE (k + 1)).apply_symm_apply tauRight)
            (0 : Fin (k + 1))
        simpa [section43ScalarDiffCLE_apply] using hzero
      have hreva : Fin.rev a = (0 : Fin (k + 1)) := by
        apply Fin.ext
        simp [a]
      rw [hreva]
      simp only [splitFirst_fin_append, splitLast_fin_append] at *
      simp only [b, add_zero]
      rw [hleft0, hright0]
      simp [reflectedChronologicalGapMap, hbridge]
      ring
    · have hright : k < i.val := by omega
      have hjright : k + 1 < j.val := by simp [j]; omega
      let b : Fin (k + 1) := ⟨j.val - (k + 1), by omega⟩
      let b' : Fin (k + 1) := ⟨j.val - (k + 1) - 1, by omega⟩
      have hj : j = Fin.natAdd (k + 1) b := by
        apply Fin.ext
        simp [b]
        omega
      have hj' :
          (⟨j.val - 1, by omega⟩ : Fin ((k + 1) + (k + 1))) =
            Fin.natAdd (k + 1) b' := by
        apply Fin.ext
        simp [b']
        omega
      rw [hj', hj,
        osiiAxisPairBlockGlobalAbsoluteTimeConfig_right,
        osiiAxisPairBlockGlobalAbsoluteTimeConfig_right]
      have hb0 : b.val ≠ 0 := by simp [b]; omega
      have hcancel := congrFun
        ((section43ScalarDiffCLE (k + 1)).apply_symm_apply tauRight) b
      rw [section43ScalarDiffCLE_apply, dif_neg hb0] at hcancel
      have hpred :
          (⟨b.val - 1, by omega⟩ : Fin (k + 1)) = b' := by
        apply Fin.ext
        simp [b, b']
      have hbtarget :
          b = (⟨i.val - k, by omega⟩ : Fin (k + 1)) := by
        apply Fin.ext
        simp [b, j]
      simp only [splitLast_fin_append] at *
      rw [hpred] at hcancel
      simpa [reflectedChronologicalGapMap, hleft, hbridge, hbtarget]
        using hcancel

end OSIIChapterV
end OSReconstruction
