/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup

/-!
# OS II Real-Edge Semigroup Agreement

OS II V.1 directional branches must agree on the real log edge.  The OS-I
semigroup algebra behind that agreement is that, after splitting the real
positive time differences around a chosen coordinate, the OS pairing only sees
the total time shift.
-/

noncomputable section

open scoped Classical BigOperators
open BigOperators Finset

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Sum of time differences strictly before the selected coordinate. -/
def osiiLeftTimeSum {m : ℕ} (τ : Fin m → ℝ) (q : Fin m) : ℝ :=
  ∑ p : Fin m, if p.val < q.val then τ p else 0

/-- Sum of time differences strictly after the selected coordinate. -/
def osiiRightTimeSum {m : ℕ} (τ : Fin m → ℝ) (q : Fin m) : ℝ :=
  ∑ p : Fin m, if q.val < p.val then τ p else 0

/-- Splitting a finite ordered list into the part before `q`, the `q` entry,
and the part after `q` recovers the total sum. -/
theorem osii_left_add_self_add_right_eq_sum
    {m : ℕ} (τ : Fin m → ℝ) (q : Fin m) :
    osiiLeftTimeSum τ q + τ q + osiiRightTimeSum τ q =
      ∑ p : Fin m, τ p := by
  have hmiddle :
      τ q = ∑ p : Fin m, if p = q then τ p else (0 : ℝ) := by
    symm
    simpa using
      (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin m)))
        (a := q) (f := fun p : Fin m => if p = q then τ p else (0 : ℝ))
        (by
          intro p _ hp
          simp [hp])
        (by
          intro hq
          exact (hq (Finset.mem_univ q)).elim))
  calc
    osiiLeftTimeSum τ q + τ q + osiiRightTimeSum τ q
        =
          (∑ p : Fin m, if p.val < q.val then τ p else 0) +
            (∑ p : Fin m, if p = q then τ p else (0 : ℝ)) +
              (∑ p : Fin m, if q.val < p.val then τ p else 0) := by
          rw [hmiddle]
          rfl
    _ =
          ∑ p : Fin m,
            ((if p.val < q.val then τ p else 0) +
              (if p = q then τ p else (0 : ℝ)) +
                (if q.val < p.val then τ p else 0)) := by
          simp [Finset.sum_add_distrib]
    _ = ∑ p : Fin m, τ p := by
          apply Finset.sum_congr rfl
          intro p _
          rcases lt_trichotomy p.val q.val with hpq | hpq | hpq
          · simp [hpq, not_lt_of_gt hpq, Fin.ne_of_val_ne hpq.ne]
          · have hp : p = q := Fin.ext hpq
            simp [hp]
          · have hp_ne : p ≠ q := fun hp => by
              have hval : p.val = q.val := congrArg Fin.val hp
              omega
            simp [hpq, not_lt_of_gt hpq, hp_ne]

theorem osiiLeftTimeSum_nonneg
    {m : ℕ} {τ : Fin m → ℝ} (hτ : ∀ p, 0 ≤ τ p) (q : Fin m) :
    0 ≤ osiiLeftTimeSum τ q := by
  unfold osiiLeftTimeSum
  exact Finset.sum_nonneg fun p _ => by
    by_cases hp : p.val < q.val
    · simpa [hp] using hτ p
    · simp [hp]

theorem osiiRightTimeSum_nonneg
    {m : ℕ} {τ : Fin m → ℝ} (hτ : ∀ p, 0 ≤ τ p) (q : Fin m) :
    0 ≤ osiiRightTimeSum τ q := by
  unfold osiiRightTimeSum
  exact Finset.sum_nonneg fun p _ => by
    by_cases hp : q.val < p.val
    · simpa [hp] using hτ p
    · simp [hp]

/-- Positive-time left branch obtained by freezing the time differences before
the selected coordinate. -/
def osiiLeftSplitPositiveBranch
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ p, 0 ≤ τ p)
    (F : PositiveTimeBorchersSequence d) (q : Fin m) :
    PositiveTimeBorchersSequence d :=
  timeShiftNonnegPositiveTimeBorchers (d := d)
    (osiiLeftTimeSum τ q) (osiiLeftTimeSum_nonneg hτ q) F

/-- Positive-time right branch obtained by freezing the time differences after
the selected coordinate. -/
def osiiRightSplitPositiveBranch
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ p, 0 ≤ τ p)
    (G : PositiveTimeBorchersSequence d) (q : Fin m) :
    PositiveTimeBorchersSequence d :=
  timeShiftNonnegPositiveTimeBorchers (d := d)
    (osiiRightTimeSum τ q) (osiiRightTimeSum_nonneg hτ q) G

omit [NeZero d] in
theorem osiiLeftSplitPositiveBranch_hasCompactSupport
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ p, 0 ≤ τ p)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport (((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) :
    ∀ q n,
      HasCompactSupport
        ((((osiiLeftSplitPositiveBranch (d := d) τ hτ F q :
            PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
  intro q
  exact timeShiftNonnegPositiveTimeBorchers_hasCompactSupport
    (d := d) (osiiLeftTimeSum τ q) (osiiLeftTimeSum_nonneg hτ q) F hF_compact

omit [NeZero d] in
theorem osiiRightSplitPositiveBranch_hasCompactSupport
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ p, 0 ≤ τ p)
    (G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) :
    ∀ q n,
      HasCompactSupport
        ((((osiiRightSplitPositiveBranch (d := d) τ hτ G q :
            PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
  intro q
  exact timeShiftNonnegPositiveTimeBorchers_hasCompactSupport
    (d := d) (osiiRightTimeSum τ q) (osiiRightTimeSum_nonneg hτ q) G hG_compact

/-- Real-edge OS semigroup agreement for a directional split of the time
differences.

This is the scalar-product algebra needed before proving that the OS-II
directional log branches have a common Schwinger real edge. -/
theorem osii_real_edge_directional_timeShift_agrees_total
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} (F G : BorchersSequence d) (τ : Fin m → ℝ) (q : Fin m)
    (hbranch :
      OSTensorAdmissible d
        (timeShiftBorchers (d := d) (osiiLeftTimeSum τ q) F)
        (timeShiftBorchers (d := d) (τ q + osiiRightTimeSum τ q) G))
    (htotal :
      OSTensorAdmissible d F
        (timeShiftBorchers (d := d) (∑ p : Fin m, τ p) G)) :
    OSInnerProduct d OS.S
        (timeShiftBorchers (d := d) (osiiLeftTimeSum τ q) F)
        (timeShiftBorchers (d := d) (τ q + osiiRightTimeSum τ q) G) =
      OSInnerProduct d OS.S F
        (timeShiftBorchers (d := d) (∑ p : Fin m, τ p) G) := by
  have hsum := osii_left_add_self_add_right_eq_sum τ q
  have hsum' :
      osiiLeftTimeSum τ q + (τ q + osiiRightTimeSum τ q) =
        ∑ p : Fin m, τ p := by
    linarith
  have htotal' :
      OSTensorAdmissible d F
        (timeShiftBorchers (d := d)
          (osiiLeftTimeSum τ q + (τ q + osiiRightTimeSum τ q)) G) := by
    simpa [hsum'] using htotal
  have hshift :=
    OSInnerProduct_timeShift_eq (d := d) OS F G
      (τ q + osiiRightTimeSum τ q) (osiiLeftTimeSum τ q)
      hbranch htotal'
  simpa [hsum'] using hshift

/-- Variable selected-time form of the OS-II split.  The times strictly before
and after `q` are frozen into the left and right Borchers vectors; the selected
time is the free one-variable semigroup parameter. -/
theorem osii_real_edge_split_branch_agrees_combined
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} (F G : BorchersSequence d) (τ : Fin m → ℝ) (q : Fin m) (s : ℝ)
    (hbranch :
      OSTensorAdmissible d
        (timeShiftBorchers (d := d) (osiiLeftTimeSum τ q) F)
        (timeShiftBorchers (d := d) (s + osiiRightTimeSum τ q) G))
    (hcombined :
      OSTensorAdmissible d F
        (timeShiftBorchers (d := d)
          (osiiLeftTimeSum τ q + (s + osiiRightTimeSum τ q)) G)) :
    OSInnerProduct d OS.S
        (timeShiftBorchers (d := d) (osiiLeftTimeSum τ q) F)
        (timeShiftBorchers (d := d) s
          (timeShiftBorchers (d := d) (osiiRightTimeSum τ q) G)) =
      OSInnerProduct d OS.S F
        (timeShiftBorchers (d := d)
          (osiiLeftTimeSum τ q + (s + osiiRightTimeSum τ q)) G) := by
  have hcompose :
      OSInnerProduct d OS.S
          (timeShiftBorchers (d := d) (osiiLeftTimeSum τ q) F)
          (timeShiftBorchers (d := d) s
            (timeShiftBorchers (d := d) (osiiRightTimeSum τ q) G)) =
        OSInnerProduct d OS.S
          (timeShiftBorchers (d := d) (osiiLeftTimeSum τ q) F)
          (timeShiftBorchers (d := d) (s + osiiRightTimeSum τ q) G) := by
    refine OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ ?_
    intro n
    ext y
    change
      (G.funcs n)
          (fun i => y i - timeShiftVec d s - timeShiftVec d (osiiRightTimeSum τ q)) =
        (G.funcs n)
          (fun i => y i - timeShiftVec d (s + osiiRightTimeSum τ q))
    congr 1
    funext i
    ext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
      ring
    · simp [timeShiftVec, hμ]
  rw [hcompose]
  exact OSInnerProduct_timeShift_eq (d := d) OS F G
    (s + osiiRightTimeSum τ q) (osiiLeftTimeSum τ q) hbranch hcombined

/-- Positive-time-branch form of the variable selected-time split.  This is the
shape consumed by the q-indexed MZ branch family. -/
theorem osii_real_edge_positiveBranch_agrees_combined
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (τ : Fin m → ℝ) (hτ : ∀ p, 0 ≤ τ p) (q : Fin m) (s : ℝ)
    (hbranch :
      OSTensorAdmissible d
        (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
        (timeShiftBorchers (d := d) (s + osiiRightTimeSum τ q)
          (G : BorchersSequence d)))
    (hcombined :
      OSTensorAdmissible d (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (osiiLeftTimeSum τ q + (s + osiiRightTimeSum τ q))
          (G : BorchersSequence d))) :
    OSInnerProduct d OS.S
        (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
        (timeShiftBorchers (d := d) s
          (osiiRightSplitPositiveBranch (d := d) τ hτ G q : BorchersSequence d)) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (osiiLeftTimeSum τ q + (s + osiiRightTimeSum τ q))
          (G : BorchersSequence d)) := by
  simpa [osiiLeftSplitPositiveBranch, osiiRightSplitPositiveBranch] using
    osii_real_edge_split_branch_agrees_combined
      (d := d) OS (F : BorchersSequence d) (G : BorchersSequence d)
      τ q s hbranch hcombined

/-- The positive-time branch split has automatic admissibility when the free
selected time is nonnegative. -/
theorem osii_real_edge_positiveBranch_agrees_combined_of_nonneg
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (τ : Fin m → ℝ) (hτ : ∀ p, 0 ≤ τ p) (q : Fin m) (s : ℝ) (hs : 0 ≤ s) :
    OSInnerProduct d OS.S
        (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
        (timeShiftBorchers (d := d) s
          (osiiRightSplitPositiveBranch (d := d) τ hτ G q : BorchersSequence d)) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (osiiLeftTimeSum τ q + (s + osiiRightTimeSum τ q))
          (G : BorchersSequence d)) := by
  have hright_nonneg : 0 ≤ s + osiiRightTimeSum τ q :=
    add_nonneg hs (osiiRightTimeSum_nonneg hτ q)
  have hcombined_nonneg :
      0 ≤ osiiLeftTimeSum τ q + (s + osiiRightTimeSum τ q) :=
    add_nonneg (osiiLeftTimeSum_nonneg hτ q) hright_nonneg
  have hbranch :
      OSTensorAdmissible d
        (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
        (timeShiftBorchers (d := d) (s + osiiRightTimeSum τ q)
          (G : BorchersSequence d)) := by
    simpa [timeShiftNonnegPositiveTimeBorchers_toBorchersSequence] using
      PositiveTimeBorchersSequence.ostensorAdmissible (d := d)
        (osiiLeftSplitPositiveBranch (d := d) τ hτ F q)
        (timeShiftNonnegPositiveTimeBorchers
          (d := d) (s + osiiRightTimeSum τ q) hright_nonneg G)
  have hcombined :
      OSTensorAdmissible d (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (osiiLeftTimeSum τ q + (s + osiiRightTimeSum τ q))
          (G : BorchersSequence d)) := by
    simpa [timeShiftNonnegPositiveTimeBorchers_toBorchersSequence] using
      PositiveTimeBorchersSequence.ostensorAdmissible (d := d)
        F
        (timeShiftNonnegPositiveTimeBorchers
          (d := d)
          (osiiLeftTimeSum τ q + (s + osiiRightTimeSum τ q))
          hcombined_nonneg G)
  exact osii_real_edge_positiveBranch_agrees_combined
    (d := d) OS F G τ hτ q s hbranch hcombined

/-- Real-log-edge form of the directional split: the q-branch right vector is
first shifted by the sum of the later positive time differences and then by
`exp x_q`.  This composed right shift is the same scalar product as the total
positive-time shift. -/
theorem osii_real_edge_log_split_branch_agrees_total
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} (F G : BorchersSequence d) (x : Fin m → ℝ) (q : Fin m)
    (hbranch :
      OSTensorAdmissible d
        (timeShiftBorchers (d := d) (osiiLeftTimeSum (fun p => Real.exp (x p)) q) F)
        (timeShiftBorchers (d := d)
          (Real.exp (x q) + osiiRightTimeSum (fun p => Real.exp (x p)) q) G))
    (htotal :
      OSTensorAdmissible d F
        (timeShiftBorchers (d := d) (∑ p : Fin m, Real.exp (x p)) G)) :
    OSInnerProduct d OS.S
        (timeShiftBorchers (d := d) (osiiLeftTimeSum (fun p => Real.exp (x p)) q) F)
        (timeShiftBorchers (d := d) (Real.exp (x q))
          (timeShiftBorchers (d := d)
            (osiiRightTimeSum (fun p => Real.exp (x p)) q) G)) =
      OSInnerProduct d OS.S F
        (timeShiftBorchers (d := d) (∑ p : Fin m, Real.exp (x p)) G) := by
  have hcompose :
      OSInnerProduct d OS.S
          (timeShiftBorchers (d := d) (osiiLeftTimeSum (fun p => Real.exp (x p)) q) F)
          (timeShiftBorchers (d := d) (Real.exp (x q))
            (timeShiftBorchers (d := d)
              (osiiRightTimeSum (fun p => Real.exp (x p)) q) G)) =
        OSInnerProduct d OS.S
          (timeShiftBorchers (d := d) (osiiLeftTimeSum (fun p => Real.exp (x p)) q) F)
          (timeShiftBorchers (d := d)
            (Real.exp (x q) + osiiRightTimeSum (fun p => Real.exp (x p)) q) G) := by
    refine OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ ?_
    intro n
    ext y
    change
      (G.funcs n)
          (fun i =>
            y i - timeShiftVec d (Real.exp (x q)) -
              timeShiftVec d (osiiRightTimeSum (fun p => Real.exp (x p)) q)) =
        (G.funcs n)
          (fun i =>
            y i -
              timeShiftVec d (Real.exp (x q) + osiiRightTimeSum (fun p => Real.exp (x p)) q))
    congr 1
    funext i
    ext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
      ring
    · simp [timeShiftVec, hμ]
  rw [hcompose]
  exact osii_real_edge_directional_timeShift_agrees_total
    (d := d) OS F G (fun p => Real.exp (x p)) q hbranch htotal

end OSReconstruction
