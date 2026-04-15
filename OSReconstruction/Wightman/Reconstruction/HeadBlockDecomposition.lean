import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz

noncomputable section

open scoped Classical LineDeriv Topology ContDiff

open SchwartzMap

namespace OSReconstruction

/-!
# Compact Head-Block Division

This file contains the block-coordinate version of the compact-support
division theorem from `TranslationInvariantSchwartz`.  It is intentionally
kept separate from that large stable file: the theorem here is generic support
infrastructure used by the Section 4.3 total-momentum support route.
-/

theorem hasCompactSupport_reindexSchwartzFin {a b : ℕ} (h : a = b)
    (F : SchwartzMap (Fin a → ℝ) ℂ)
    (hF : HasCompactSupport (F : (Fin a → ℝ) → ℂ)) :
    HasCompactSupport ((reindexSchwartzFin h F : SchwartzMap (Fin b → ℝ) ℂ) :
      (Fin b → ℝ) → ℂ) := by
  subst h
  simpa [reindexSchwartzFin] using hF

theorem exists_eq_sum_headBlock_coord_smul_of_zeroHeadSection_of_hasCompactSupport :
    ∀ {p q : ℕ}
      (F : SchwartzMap (Fin (p + q) → ℝ) ℂ),
      HasCompactSupport (F : (Fin (p + q) → ℝ) → ℂ) →
      (∀ y : Fin q → ℝ,
        F (zeroHeadBlockShift (m := p) (n := q) y) = 0) →
      ∃ G : Fin p → SchwartzMap (Fin (p + q) → ℝ) ℂ,
        F =
          ∑ μ : Fin p,
            SchwartzMap.smulLeftCLM ℂ
              (fun x : Fin (p + q) → ℝ => x (Fin.castAdd q μ))
              (G μ) := by
  intro p
  induction p with
  | zero =>
      intro q F _hFcs hFzero
      refine ⟨Fin.elim0, ?_⟩
      ext x
      have hx : x = zeroHeadBlockShift (m := 0) (n := q) (splitLast 0 q x) := by
        ext i
        simp [zeroHeadBlockShift, splitLast, castFinCLE]
      calc
        F x = F (zeroHeadBlockShift (m := 0) (n := q) (splitLast 0 q x)) := by
          exact congrArg F hx
        _ = 0 := hFzero (splitLast 0 q x)
        _ = (∑ μ : Fin 0,
              SchwartzMap.smulLeftCLM ℂ
                (fun x : Fin (0 + q) → ℝ => x (Fin.castAdd q μ))
                (Fin.elim0 μ)) x := by
          simp
  | succ p ih =>
      intro q F hFcs hFzero
      let F' : SchwartzMap (Fin ((p + q) + 1) → ℝ) ℂ :=
        reindexSchwartzFin (Nat.succ_add p q) F
      have hF'cs : HasCompactSupport (F' : (Fin ((p + q) + 1) → ℝ) → ℂ) := by
        simpa [F'] using hasCompactSupport_reindexSchwartzFin (Nat.succ_add p q) F hFcs
      let h : SchwartzMap (Fin (p + q) → ℝ) ℂ := headSectionCLM (p + q) F'
      have hhcs : HasCompactSupport (h : (Fin (p + q) → ℝ) → ℂ) := by
        exact hasCompactSupport_headSection F' hF'cs
      have hhzero : ∀ y : Fin q → ℝ,
          h (zeroHeadBlockShift (m := p) (n := q) y) = 0 := by
        intro y
        have hy : F' (Fin.cons 0 (zeroHeadBlockShift (m := p) (n := q) y)) = 0 := by
          simpa [F', reindexSchwartzFin_apply, zeroHeadBlockShift] using hFzero y
        simpa [h, headSectionCLM_apply] using hy
      obtain ⟨gTail, hgTail⟩ := ih (q := q) h hhcs hhzero
      let r : SchwartzMap (Fin ((p + q) + 1) → ℝ) ℂ :=
        F' - unitBumpSchwartz.prependField h
      have hprependcs : HasCompactSupport (unitBumpSchwartz.prependField h :
          (Fin ((p + q) + 1) → ℝ) → ℂ) := by
        exact hasCompactSupport_prependField unitBumpSchwartz h
          (by
            let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
            exact b.hasCompactSupport.comp_left Complex.ofReal_zero)
          hhcs
      have hrcs : HasCompactSupport (r : (Fin ((p + q) + 1) → ℝ) → ℂ) := by
        simpa [r, sub_eq_add_neg] using HasCompactSupport.add hF'cs hprependcs.neg
      have hr0 : headSectionCLM (p + q) r = 0 := by
        simpa [r] using headSection_remainder_eq_zero unitBumpSchwartz unitBumpSchwartz_zero F'
      obtain ⟨g0, hg0⟩ :=
        exists_eq_coord_smul_of_headSection_zero_of_hasCompactSupport r hr0 hrcs
      let hcast : (p + 1) + q = (p + q) + 1 := Nat.succ_add p q
      let G0 : SchwartzMap (Fin ((p + 1) + q) → ℝ) ℂ :=
        reindexSchwartzFin hcast.symm g0
      let GTail : Fin p → SchwartzMap (Fin ((p + 1) + q) → ℝ) ℂ :=
        fun μ => reindexSchwartzFin hcast.symm (unitBumpSchwartz.prependField (gTail μ))
      refine ⟨Fin.cases G0 GTail, ?_⟩
      ext x
      let x' : Fin ((p + q) + 1) → ℝ := (castFinCLE hcast) x
      have hFx' : F x = F' x' := by
        simp [F', x', reindexSchwartzFin_apply, castFinCLE]
      have hx0 : x' 0 = x (Fin.castAdd q (0 : Fin (p + 1))) := by
        change ((castFinCLE (Nat.succ_add p q)) x) 0 =
          x (Fin.castAdd q (0 : Fin (p + 1)))
        change x ((finCongr (Nat.succ_add p q).symm) 0) =
          x (Fin.castAdd q (0 : Fin (p + 1)))
        congr 1
      have hxSucc : ∀ μ : Fin p,
          x' (Fin.succ (Fin.castAdd q μ)) = x (Fin.castAdd q μ.succ) := by
        intro μ
        change ((castFinCLE (Nat.succ_add p q)) x) (Fin.succ (Fin.castAdd q μ)) =
          x (Fin.castAdd q μ.succ)
        change x ((finCongr (Nat.succ_add p q).symm) (Fin.succ (Fin.castAdd q μ))) =
          x (Fin.castAdd q μ.succ)
        congr 1
      have hcoord0 : (fun y : Fin ((p + q) + 1) → ℝ => y 0).HasTemperateGrowth :=
        (headCoordProjCLM (p + q)).hasTemperateGrowth
      have hcoordTail : ∀ μ : Fin p,
          (fun y : Fin (p + q) → ℝ => y (Fin.castAdd q μ)).HasTemperateGrowth := by
        intro μ
        exact (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (p + q))
          (φ := fun _ => ℝ) (Fin.castAdd q μ)).hasTemperateGrowth
      have hcoordOrig : ∀ μ : Fin (p + 1),
          (fun y : Fin ((p + 1) + q) → ℝ => y (Fin.castAdd q μ)).HasTemperateGrowth := by
        intro μ
        exact (ContinuousLinearMap.proj (R := ℝ) (ι := Fin ((p + 1) + q))
          (φ := fun _ => ℝ) (Fin.castAdd q μ)).hasTemperateGrowth
      have hrx : r x' = (x' 0) • g0 x' := by
        have hg0x :=
          congrArg (fun G : SchwartzMap (Fin ((p + q) + 1) → ℝ) ℂ => G x') hg0
        simpa [SchwartzMap.smulLeftCLM_apply_apply hcoord0] using hg0x
      have htailx :
          h (fun i : Fin (p + q) => x' i.succ) =
            ∑ μ : Fin p,
              (x' (Fin.succ (Fin.castAdd q μ))) •
                gTail μ (fun i : Fin (p + q) => x' i.succ) := by
        let y : Fin (p + q) → ℝ := fun i => x' i.succ
        have hEval := congrArg (fun G : SchwartzMap (Fin (p + q) → ℝ) ℂ => G y) hgTail
        calc
          h y = ((∑ μ : Fin p,
              SchwartzMap.smulLeftCLM ℂ
                (fun y : Fin (p + q) → ℝ => y (Fin.castAdd q μ))
                (gTail μ)) : SchwartzMap (Fin (p + q) → ℝ) ℂ) y := hEval
          _ = ∑ μ : Fin p,
              ((SchwartzMap.smulLeftCLM ℂ
                (fun y : Fin (p + q) → ℝ => y (Fin.castAdd q μ))
                (gTail μ)) y) := by
            simp
          _ = ∑ μ : Fin p,
              (x' (Fin.succ (Fin.castAdd q μ))) •
                gTail μ (fun i : Fin (p + q) => x' i.succ) := by
            refine Finset.sum_congr rfl ?_
            intro μ _hμ
            rw [SchwartzMap.smulLeftCLM_apply_apply (hcoordTail μ)]
            rfl
      have hprependx :
          (unitBumpSchwartz.prependField h) x' =
            ∑ μ : Fin p,
              (x' (Fin.succ (Fin.castAdd q μ))) •
                (unitBumpSchwartz.prependField (gTail μ)) x' := by
        calc
          (unitBumpSchwartz.prependField h) x' =
              unitBumpSchwartz (x' 0) * h (fun i : Fin (p + q) => x' i.succ) := by
            simp [SchwartzMap.prependField_apply]
          _ = unitBumpSchwartz (x' 0) *
              (∑ μ : Fin p,
                (x' (Fin.succ (Fin.castAdd q μ))) •
                  gTail μ (fun i : Fin (p + q) => x' i.succ)) := by
            rw [htailx]
          _ = ∑ μ : Fin p,
                unitBumpSchwartz (x' 0) *
                  ((x' (Fin.succ (Fin.castAdd q μ))) •
                    gTail μ (fun i : Fin (p + q) => x' i.succ)) := by
            rw [Finset.mul_sum]
          _ = ∑ μ : Fin p,
                (x' (Fin.succ (Fin.castAdd q μ))) •
                  (unitBumpSchwartz.prependField (gTail μ)) x' := by
            refine Finset.sum_congr rfl ?_
            intro μ _hμ
            rw [SchwartzMap.prependField_apply]
            change unitBumpSchwartz (x' 0) *
                ((x' (Fin.succ (Fin.castAdd q μ)) : ℂ) *
                  gTail μ (fun i : Fin (p + q) => x' i.succ)) =
              (x' (Fin.succ (Fin.castAdd q μ)) : ℂ) *
                (unitBumpSchwartz (x' 0) *
                  gTail μ (fun i : Fin (p + q) => x' i.succ))
            ring
      have hfirst :
          ((SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin ((p + 1) + q) → ℝ => x (Fin.castAdd q (0 : Fin (p + 1))))
            G0) x) =
          (x' 0) • g0 x' := by
        rw [SchwartzMap.smulLeftCLM_apply_apply (hcoordOrig 0)]
        congr 1
      have htailSum :
          (∑ μ : Fin p,
            ((SchwartzMap.smulLeftCLM ℂ
              (fun x : Fin ((p + 1) + q) → ℝ => x (Fin.castAdd q μ.succ))
              (GTail μ)) x)) =
          ∑ μ : Fin p,
            (x' (Fin.succ (Fin.castAdd q μ))) •
              (unitBumpSchwartz.prependField (gTail μ)) x' := by
        refine Finset.sum_congr rfl ?_
        intro μ _hμ
        rw [SchwartzMap.smulLeftCLM_apply_apply (hcoordOrig μ.succ)]
        congr 1
      have hsum_decomp :
          (∑ μ : Fin (p + 1),
            (SchwartzMap.smulLeftCLM ℂ
              (fun x : Fin ((p + 1) + q) → ℝ => x (Fin.castAdd q μ))
              (Fin.cases G0 GTail μ))) x
            =
          (x' 0) • g0 x' +
            ∑ μ : Fin p,
              (x' (Fin.succ (Fin.castAdd q μ))) •
                (unitBumpSchwartz.prependField (gTail μ)) x' := by
        let A0 : SchwartzMap (Fin ((p + 1) + q) → ℝ) ℂ :=
          SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin ((p + 1) + q) → ℝ => x (Fin.castAdd q (0 : Fin (p + 1)))) G0
        let Bsum : SchwartzMap (Fin ((p + 1) + q) → ℝ) ℂ :=
          ∑ i : Fin p,
            SchwartzMap.smulLeftCLM ℂ
              (fun x : Fin ((p + 1) + q) → ℝ => x (Fin.castAdd q i.succ)) (GTail i)
        have hBsum : Bsum x = ∑ i : Fin p,
            ((SchwartzMap.smulLeftCLM ℂ
              (fun x : Fin ((p + 1) + q) → ℝ => x (Fin.castAdd q i.succ))
              (GTail i)) x) := by
          simp [Bsum]
        rw [Fin.sum_univ_succ]
        change (A0 + Bsum) x =
          (x' 0) • g0 x' +
            ∑ μ : Fin p,
              (x' (Fin.succ (Fin.castAdd q μ))) •
                (unitBumpSchwartz.prependField (gTail μ)) x'
        rw [show (A0 + Bsum) x = A0 x + Bsum x by simp]
        rw [show A0 x = (x' 0) • g0 x' by simpa [A0] using hfirst]
        rw [hBsum, htailSum]
      calc
        F x = F' x' := hFx'
        _ = r x' + (unitBumpSchwartz.prependField h) x' := by
          simp [r]
        _ = (x' 0) • g0 x' +
            ∑ μ : Fin p,
              (x' (Fin.succ (Fin.castAdd q μ))) •
                (unitBumpSchwartz.prependField (gTail μ)) x' := by
          rw [hrx, hprependx]
        _ = (∑ μ : Fin (p + 1),
              SchwartzMap.smulLeftCLM ℂ
                (fun x : Fin ((p + 1) + q) → ℝ => x (Fin.castAdd q μ))
                (Fin.cases G0 GTail μ)) x := by
          exact hsum_decomp.symm

end OSReconstruction
