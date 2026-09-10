/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralSupport
import OSReconstruction.SCV.PaleyWienerSchwartz
import Init
import OSReconstruction.SCV.ConeDefs
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.Wightman.SchwartzTensorProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv













open scoped Classical NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Reindex a flattened sum that only samples the time-coordinate slots. -/
private theorem sum_over_flat_timeSlots
    {n : ℕ}
    (a : Fin n → ℝ)
    (ξ : Fin (n * (d + 1)) → ℝ) :
    (∑ i, (if (finProdFinEquiv.symm i).2 = 0 then a ((finProdFinEquiv.symm i).1) else 0) * ξ i) =
      ∑ k : Fin n, a k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
  classical
  symm
  simpa [Fintype.sum_prod_type] using
    (Fintype.sum_bijective
      (fun p : Fin n × Fin (d + 1) => finProdFinEquiv p)
      finProdFinEquiv.bijective
      (fun p : Fin n × Fin (d + 1) => (if p.2 = 0 then a p.1 else 0) * ξ (finProdFinEquiv p))
      (fun i : Fin (n * (d + 1)) =>
        (if (finProdFinEquiv.symm i).2 = 0 then a ((finProdFinEquiv.symm i).1) else 0) * ξ i)
      (by
        intro p
        simp))

 /-
/-- Tail-block version of `flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone`:
after inserting the right-block time-shift vector into the full flattened
`(n+m)`-point space, every dual-cone frequency still pairs nonpositively with
that inserted translation direction. This is the exact geometry needed by the
final full-flat spectral assembly. -/
private theorem zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    {n m : ℕ}
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    ∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i ≤ 0 := by
  classical
  let S : ℝ :=
    ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1))))
  have hS_nonneg : 0 ≤ S := by
    by_contra hS
    have hSneg : S < 0 := lt_of_not_ge hS
    let W : ℝ :=
      ∑ k : Fin (n + m),
        (if (k : ℕ) < n then ((k : ℝ) + 1) else (k : ℝ)) *
          ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
    let ε : ℝ := (-S) / (2 * (|W| + 1))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      apply div_pos
      · linarith
      · positivity
    let yε : Fin (n + m) → Fin (d + 1) → ℝ :=
      fun k μ =>
        if μ = 0 then
          if (k : ℕ) < n then (((k : ℝ) + 1) * ε : ℝ)
          else (1 + (k : ℝ) * ε : ℝ)
        else 0
    let e0 : Fin (d + 1) → ℝ := fun μ => if μ = 0 then 1 else 0
    have he0 : InOpenForwardCone d e0 := by
      constructor
      · simp [e0]
      · simp [e0, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
    have hεe0 : InOpenForwardCone d (ε • e0) :=
      inOpenForwardCone_smul d ε hε_pos e0 he0
    have hyε_mem : yε ∈ ForwardConeAbs d (n + m) := by
      intro k
      by_cases hk0 : (k : ℕ) = 0
      · have hk_nat : (k : ℕ) = 0 := hk0
        have hk_zero : (k : ℝ) = 0 := by exact_mod_cast hk_nat
        convert inOpenForwardCone_smul d
          (if (0 : ℕ) < n then (1 : ℝ) * ε else (1 : ℝ))
          (by
            by_cases hn : 0 < n
            · simp [hn, hε_pos]
            · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
              simp [hn0])
          e0 he0 using 1
        ext μ
        by_cases hμ : μ = 0
        · subst hμ
          by_cases hn : 0 < n
          · have hk_lt : (k : ℕ) < n := by simpa [hk0] using hn
            simp [yε, e0, hk0, hk_zero, hk_lt, hn, Pi.smul_apply, smul_eq_mul]
          · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
            simp [yε, e0, hk0, hk_zero, hn0, Pi.smul_apply, smul_eq_mul]
        · simp [yε, e0, hk0, hμ, Pi.smul_apply, smul_eq_mul]
      · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk0
        by_cases hk_lt : (k : ℕ) < n
        · have hkcast :
            ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
              have hnat : (k : ℕ) - 1 + 1 = (k : ℕ) :=
                Nat.sub_add_cancel (show 1 ≤ (k : ℕ) from hkpos)
              exact_mod_cast hnat
          convert hεe0 using 1
          ext μ
          by_cases hμ : μ = 0
          · subst hμ
            have hkprev_lt : ((k : ℕ) - 1) < n := by omega
            have hmain :
                (((k : ℝ) + 1) * ε) -
                    (((((k : ℕ) - 1 : ℕ) : ℝ) + 1) * ε) = ε := by
              nlinarith [hkcast]
            simp [yε, e0, hk_lt, hk0, Pi.smul_apply, smul_eq_mul, hmain, hkprev_lt]
          · simp [yε, e0, hk_lt, hk0, hμ, Pi.smul_apply, smul_eq_mul]
        · by_cases hk_eq : (k : ℕ) = n
          · convert he0 using 1
            ext μ
            by_cases hμ : μ = 0
            · subst hμ
              have hn_pos : 0 < n := by omega
              have hn0_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
              have hkprev_lt : ((k : ℕ) - 1) < n := by omega
              have hkcast : (k : ℝ) = (n : ℝ) := by exact_mod_cast hk_eq
              have hprev_cast :
                  ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
                have hnat : (k : ℕ) - 1 + 1 = n := by
                  rw [hk_eq]
                  exact Nat.sub_add_cancel (show 1 ≤ n from hn_pos)
                exact_mod_cast hnat
              have hmain :
                  (1 + (k : ℝ) * ε) -
                    (((((k : ℕ) - 1 : ℕ) : ℝ) + 1) * ε) = 1 := by
                nlinarith [hkcast, hprev_cast]
              simpa [yε, e0, hk_lt, hk_eq, hk0, hn0_ne,
                hkprev_lt, hn_pos, Pi.smul_apply, smul_eq_mul] using hmain
            · have hn_pos : 0 < n := by omega
              have hn0_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
              have hkprev_lt : ((k : ℕ) - 1) < n := by omega
              simp [yε, e0, hk_lt, hk_eq, hk0, hn0_ne, hkprev_lt,
                hn_pos, hμ, Pi.smul_apply, smul_eq_mul]
          · have hk_gt : n < (k : ℕ) := by omega
            have hkprev_ge : n ≤ (k : ℕ) - 1 := by omega
            have hkprev_not_lt : ¬ ((k : ℕ) - 1 < n) := by omega
            have hkcast :
                (((k : ℕ) - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
              have hnat : (k : ℕ) - 1 + 1 = (k : ℕ) :=
                Nat.sub_add_cancel (show 1 ≤ (k : ℕ) from hkpos)
              have hreal : ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
                exact_mod_cast hnat
              linarith
            convert hεe0 using 1
            ext μ
            by_cases hμ : μ = 0
            · subst hμ
              have hmain :
                  (1 + (k : ℝ) * ε) -
                    (1 + ((((k : ℕ) - 1 : ℕ) : ℝ)) * ε) = ε := by
                nlinarith [hkcast]
              simp [yε, e0, hk_lt, hk_eq, hk_gt, hkprev_ge, hkprev_not_lt, hk0,
                Pi.smul_apply, smul_eq_mul, hmain]
            · simpa [yε, e0, hk_lt, hk_eq, hk_gt, hkprev_ge, hkprev_not_lt, hk0, hμ,
                Pi.smul_apply, smul_eq_mul]
    have hpair_nonneg :
        0 ≤ ∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i := by
      exact (mem_dualConeFlat.mp hξ)
        ((flattenCLEquivReal (n + m) (d + 1)) yε) ⟨yε, hyε_mem, rfl⟩
    have hsum_rewrite :
        (∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i) = S + ε * W := by
      let a : Fin (n + m) → ℝ :=
        fun k =>
          if (k : ℕ) < n then (((k : ℝ) + 1) * ε : ℝ)
          else (1 + (k : ℝ) * ε : ℝ)
      let b : Fin (n + m) → ℝ := fun k => if (k : ℕ) < n then 0 else 1
      let c : Fin (n + m) → ℝ :=
        fun k => if (k : ℕ) < n then ((k : ℝ) + 1) else (k : ℝ)
      calc
        (∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i)
            = ∑ k : Fin (n + m), a k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
                simpa [yε, a, flattenCLEquivReal_apply] using
                  (sum_over_flat_timeSlots (d := d) (a := a) ξ)
        _ = ∑ k : Fin (n + m),
              (b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) +
                ε * (c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hk_lt : (k : ℕ) < n
              · simp [a, b, c, hk_lt]
                ring
              · simp [a, b, c, hk_lt]
                ring
        _ = (∑ k : Fin (n + m), b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) +
              ε * (∑ k : Fin (n + m), c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = S + ε * W := by
              have hb :
                  ∑ k : Fin (n + m), b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) = S := by
                rw [Fin.sum_univ_add]
                simp [b, S]
              have hc :
                  ∑ k : Fin (n + m), c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) = W := by
                simp [c, W]
              rw [hb, hc]
    have hW_bound : ε * W ≤ (-S) / 2 := by
      have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
      have hstep1 : ε * W ≤ ε * |W| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self W) hε_nonneg
      have hstep2 : ε * |W| ≤ (-S) / 2 := by
        have hratio : |W| / (|W| + 1) ≤ (1 : ℝ) := by
          have hne : (|W| + 1 : ℝ) ≠ 0 := by positivity
          field_simp [hne]
          nlinarith [abs_nonneg W]
        have hrepr : ε * |W| = ((-S) / 2) * (|W| / (|W| + 1)) := by
          have hne : 2 * (|W| + 1) ≠ 0 := by positivity
          dsimp [ε]
          field_simp [hne]
        rw [hrepr]
        have hcoeff_nonneg : 0 ≤ (-S) / 2 := by linarith
        simpa using mul_le_mul_of_nonneg_left hratio hcoeff_nonneg
      exact le_trans hstep1 hstep2
    rw [hsum_rewrite] at hpair_nonneg
    linarith [hpair_nonneg, hW_bound, hSneg]
  let vEff : Fin ((n + m) * (d + 1)) → ℝ :=
    ((OSReconstruction.castFinCLE
      (Nat.add_mul n m (d + 1)).symm)
      (OSReconstruction.zeroHeadBlockShift
        (m := n * (d + 1)) (n := m * (d + 1))
        (flatTimeShiftDirection d m)))
  let y : Fin (n + m) → Fin (d + 1) → ℝ :=
    (flattenCLEquivReal (n + m) (d + 1)).symm vEff
  have hsplitFirst :
      splitFirst n m y = 0 := by
    dsimp [y, vEff]
    rw [splitFirst_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := OSReconstruction.zeroHeadBlockShift
        (m := n * (d + 1)) (n := m * (d + 1))
        (flatTimeShiftDirection d m))]
    simp
  have hsplitLast :
      splitLast n m y =
        (flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m) := by
    dsimp [y, vEff]
    rw [splitLast_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := OSReconstruction.zeroHeadBlockShift
        (m := n * (d + 1)) (n := m * (d + 1))
        (flatTimeShiftDirection d m))]
    simp
  have hy_formula :
      ∀ k : Fin (n + m), ∀ μ : Fin (d + 1),
        y k μ = if μ = 0 then if (k : ℕ) < n then 0 else -1 else 0 := by
    intro k μ
    by_cases hk : (k : ℕ) < n
    · let k' : Fin n := ⟨k, hk⟩
      have hk_cast : Fin.castAdd m k' = k := by
        apply Fin.ext
        simp [k']
      have hval :
          y k μ = 0 := by
        have h := congrArg (fun z : Fin n → Fin (d + 1) → ℝ => z k') hsplitFirst
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [k', hk_cast] using h'
      simp [hk, hval]
    · let j : Fin m := ⟨(k : ℕ) - n, by omega⟩
      have hk_tail : Fin.natAdd n j = k := by
        apply Fin.ext
        simp [j]
        omega
      have h := congrArg (fun z : Fin m → Fin (d + 1) → ℝ => z j) hsplitLast
      have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
      have htail :
          y k μ = ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ := by
        simpa [j, hk_tail] using h'
      have htail_formula :
          ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ =
            if μ = 0 then -1 else 0 := by
        simp [flatTimeShiftDirection]
      simp [hk, htail, htail_formula]
  have hsum_eq :
      ∑ i, vEff i * ξ i = -S := by
    let a : Fin (n + m) → ℝ := fun k => if (k : ℕ) < n then 0 else -1
    calc
      ∑ i, vEff i * ξ i
          = ∑ i, (flattenCLEquivReal (n + m) (d + 1) y) i * ξ i := by
              simp [y, vEff]
      _ = ∑ k : Fin (n + m), a k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
            simpa [a, hy_formula, flattenCLEquivReal_apply] using
              (sum_over_flat_timeSlots (d := d) (a := a) ξ)
      _ = -S := by
            rw [Fin.sum_univ_eq_sum_range]
            rw [Finset.sum_range_add]
            have hhead_zero :
                ∑ k in Finset.range n,
                  a ⟨k, by omega⟩ *
                    ξ (finProdFinEquiv (⟨k, by omega⟩, (0 : Fin (d + 1)))) = 0 := by
              refine Finset.sum_eq_zero ?_
              intro k hk
              have hk_lt' : ((⟨k, by omega⟩ : Fin (n + m)) : ℕ) < n := by simpa
              simp [a, hk_lt']
            have htail :
                ∑ k in Finset.range m,
                  a ⟨n + k, by omega⟩ *
                    ξ (finProdFinEquiv (⟨n + k, by omega⟩, (0 : Fin (d + 1)))) = -S := by
              rw [S, Fin.sum_univ_eq_sum_range]
              refine congrArg Neg.neg ?_
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hk_not_lt : ¬ ((⟨n + k, by omega⟩ : Fin (n + m)) : ℕ) < n := by omega
              simp [a, hk_not_lt]
            rw [hhead_zero, zero_add, htail]
  dsimp [vEff]
  rw [hsum_eq]
  linarith

-/

/-- Reindexing the flattened `(n+m)`-point real block into
`n*(d+1) + m*(d+1)` identifies the first block with the first `n` spacetime
variables. -/
private theorem splitFirst_reindex_flatten_symm_eq
    {n m : ℕ}
    (x : Fin (n * (d + 1) + m * (d + 1)) → ℝ) :
    splitFirst n m
        ((flattenCLEquivReal (n + m) (d + 1)).symm
          ((OSReconstruction.castFinCLE (by ring : (n + m) * (d + 1) =
            n * (d + 1) + m * (d + 1))).symm x)) =
      (flattenCLEquivReal n (d + 1)).symm
        (splitFirst (n * (d + 1)) (m * (d + 1)) x) := by
  ext i μ
  change
    x ((finCongr (by ring : (n + m) * (d + 1) =
      n * (d + 1) + m * (d + 1)))
      (finProdFinEquiv (Fin.castAdd m i, μ))) =
    x (Fin.castAdd (m * (d + 1)) (finProdFinEquiv (i, μ)))
  refine congrArg x ?_
  apply Fin.ext
  simp [finProdFinEquiv]

/-- Reindexing the flattened `(n+m)`-point real block into
`n*(d+1) + m*(d+1)` identifies the last block with the final `m` spacetime
variables. -/
private theorem splitLast_reindex_flatten_symm_eq
    {n m : ℕ}
    (x : Fin (n * (d + 1) + m * (d + 1)) → ℝ) :
    splitLast n m
        ((flattenCLEquivReal (n + m) (d + 1)).symm
          ((OSReconstruction.castFinCLE (by ring : (n + m) * (d + 1) =
            n * (d + 1) + m * (d + 1))).symm x)) =
      (flattenCLEquivReal m (d + 1)).symm
        (splitLast (n * (d + 1)) (m * (d + 1)) x) := by
  ext j μ
  change
    x ((finCongr (by ring : (n + m) * (d + 1) =
      n * (d + 1) + m * (d + 1)))
      (finProdFinEquiv (Fin.natAdd n j, μ))) =
    x (Fin.natAdd (n * (d + 1)) (finProdFinEquiv (j, μ)))
  refine congrArg x ?_
  apply Fin.ext
  simp [finProdFinEquiv]
  ring

/-- The inserted full-flat tail time-shift vector pairs with any frequency
vector as the negative sum of the tail-block time-frequency coordinates.

This is just the algebraic content of the inserted-tail geometry. It does not
yet use the dual-cone hypothesis; that analytic sign step remains the live
blocker. -/
theorem zeroHeadBlockShift_flatTimeShiftDirection_pairing_eq_neg_tailTimeSum
    {n m : ℕ}
    (ξ : Fin ((n + m) * (d + 1)) → ℝ) :
    ∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i =
      - ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1)))) := by
  let S : ℝ :=
    ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1))))
  let xSplit : Fin (n * (d + 1) + m * (d + 1)) → ℝ :=
    OSReconstruction.zeroHeadBlockShift
      (m := n * (d + 1)) (n := m * (d + 1))
      (flatTimeShiftDirection d m)
  let vEff : Fin ((n + m) * (d + 1)) → ℝ :=
    ((OSReconstruction.castFinCLE
      (by ring : (n + m) * (d + 1) = n * (d + 1) + m * (d + 1))).symm xSplit)
  have hvEff_targetVec :
      vEff =
        ((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm) xSplit) := by
    ext i
    rfl
  let y : Fin (n + m) → Fin (d + 1) → ℝ :=
    (flattenCLEquivReal (n + m) (d + 1)).symm vEff
  have hsplitFirst :
      splitFirst n m y = 0 := by
    dsimp [y, vEff, xSplit]
    rw [splitFirst_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := xSplit)]
    simpa [xSplit] using
      (splitFirst_zeroHeadBlockShift_eq_zero
        (m := n * (d + 1)) (n := m * (d + 1))
        (a := flatTimeShiftDirection d m))
  have hsplitLast :
      splitLast n m y =
        (flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m) := by
    dsimp [y, vEff, xSplit]
    rw [splitLast_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := xSplit)]
    simpa [xSplit] using
      (splitLast_zeroHeadBlockShift_eq
        (m := n * (d + 1)) (n := m * (d + 1))
        (a := flatTimeShiftDirection d m))
  have hy_formula :
      ∀ k : Fin (n + m), ∀ μ : Fin (d + 1),
        y k μ = if μ = 0 then if (k : ℕ) < n then 0 else -1 else 0 := by
    intro k μ
    by_cases hk : (k : ℕ) < n
    · let k' : Fin n := ⟨k, hk⟩
      have hk_cast : Fin.castAdd m k' = k := by
        apply Fin.ext
        simp [k']
      have hval :
          y k μ = 0 := by
        have h := congrArg (fun z : Fin n → Fin (d + 1) → ℝ => z k') hsplitFirst
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [k', hk_cast] using h'
      simp [hk, hval]
    · let j : Fin m := ⟨(k : ℕ) - n, by omega⟩
      have hk_tail : Fin.natAdd n j = k := by
        apply Fin.ext
        simp [j, Fin.natAdd]
        omega
      have hval :
          y k μ =
            ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ := by
        have h := congrArg (fun z : Fin m → Fin (d + 1) → ℝ => z j) hsplitLast
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [splitLast, j, hk_tail] using h'
      have hflat :
          ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ =
            if μ = 0 then -1 else 0 := by
        change flatTimeShiftDirection d m (finProdFinEquiv (j, μ)) = _
        simp [flatTimeShiftDirection]
      simp [hk, hval, hflat]
  have hvEff_formula :
      ∀ i,
        vEff i =
          (if (finProdFinEquiv.symm i).2 = 0 then
            if (((finProdFinEquiv.symm i).1 : Fin (n + m)) : ℕ) < n then 0 else (-1 : ℝ)
           else 0) := by
    intro i
    have hv :
        (flattenCLEquivReal (n + m) (d + 1) y) i = vEff i := by
      simpa [y] using
        congrArg (fun z : Fin ((n + m) * (d + 1)) → ℝ => z i)
          ((flattenCLEquivReal (n + m) (d + 1)).apply_symm_apply vEff)
    rw [← hv]
    simpa [flattenCLEquivReal_apply] using
      hy_formula (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have hsum_eq :
      ∑ i, vEff i * ξ i = -S := by
    calc
      ∑ i, vEff i * ξ i
          = ∑ i,
              (if (finProdFinEquiv.symm i).2 = 0 then
                  if (((finProdFinEquiv.symm i).1 : Fin (n + m)) : ℕ) < n then 0 else (-1 : ℝ)
                else 0) * ξ i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hvEff_formula i]
      _ = -S := by
        rw [sum_over_flat_timeSlots
          (d := d)
          (a := fun k : Fin (n + m) => if (k : ℕ) < n then (0 : ℝ) else -1) ξ]
        rw [Fin.sum_univ_add]
        have hhead_zero :
            (∑ k : Fin n,
              (if ((Fin.castAdd m k : Fin (n + m)) : ℕ) < n then (0 : ℝ) else -1) *
                ξ (finProdFinEquiv (Fin.castAdd m k, (0 : Fin (d + 1))))) = 0 := by
          simp
        have htail_eq :
            (∑ k : Fin m,
              (if ((Fin.natAdd n k : Fin (n + m)) : ℕ) < n then (0 : ℝ) else -1) *
                ξ (finProdFinEquiv (Fin.natAdd n k, (0 : Fin (d + 1))))) = -S := by
          simp [S]
        rw [hhead_zero, zero_add, htail_eq]
  simpa [S, xSplit, hvEff_targetVec] using hsum_eq

/-- Tail-block version of `flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone`:
after inserting the right-block time-shift vector into the full flattened
`(n+m)`-point space, every dual-cone frequency still pairs nonpositively with
that inserted translation direction. This is the exact geometry needed by the
final full-flat spectral assembly. -/
theorem zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    {n m : ℕ}
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    ∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i ≤ 0 := by
  classical
  let S : ℝ :=
    ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1))))
  have hS_nonneg : 0 ≤ S := by
    by_contra hS
    have hSneg : S < 0 := lt_of_not_ge hS
    let W : ℝ :=
      ∑ k : Fin (n + m),
        (if (k : ℕ) < n then ((k : ℝ) + 1) else (k : ℝ)) *
          ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
    let ε : ℝ := (-S) / (2 * (|W| + 1))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      apply div_pos
      · linarith
      · positivity
    let yε : Fin (n + m) → Fin (d + 1) → ℝ :=
      fun k μ =>
        if μ = 0 then
          if (k : ℕ) < n then (((k : ℝ) + 1) * ε : ℝ)
          else (1 + (k : ℝ) * ε : ℝ)
        else 0
    let e0 : Fin (d + 1) → ℝ := fun μ => if μ = 0 then 1 else 0
    have he0 : InOpenForwardCone d e0 := by
      constructor
      · simp [e0]
      · simp [e0, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
    have hεe0 : InOpenForwardCone d (ε • e0) :=
      inOpenForwardCone_smul d ε hε_pos e0 he0
    have hyε_mem : yε ∈ ForwardConeAbs d (n + m) := by
      intro k
      by_cases hk0 : (k : ℕ) = 0
      · have hk_nat : (k : ℕ) = 0 := hk0
        have hk_zero : (k : ℝ) = 0 := by exact_mod_cast hk_nat
        convert inOpenForwardCone_smul d
          (if (0 : ℕ) < n then (1 : ℝ) * ε else (1 : ℝ))
          (by
            by_cases hn : 0 < n
            · simp [hn, hε_pos]
            · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
              simp [hn0])
          e0 he0 using 1
        ext μ
        by_cases hμ : μ = 0
        · subst hμ
          by_cases hn : 0 < n
          · have hk_lt : (k : ℕ) < n := by simpa [hk0] using hn
            simp [yε, e0, hk0, hk_zero, hk_lt, hn, Pi.smul_apply, smul_eq_mul]
          · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
            simp [yε, e0, hk0, hk_zero, hn0, Pi.smul_apply, smul_eq_mul]
        · simp [yε, e0, hk0, hμ, Pi.smul_apply, smul_eq_mul]
      · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk0
        by_cases hk_lt : (k : ℕ) < n
        · have hkcast :
            ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
            have hnat : (k : ℕ) - 1 + 1 = (k : ℕ) :=
              Nat.sub_add_cancel (show 1 ≤ (k : ℕ) from hkpos)
            exact_mod_cast hnat
          convert hεe0 using 1
          ext μ
          by_cases hμ : μ = 0
          · subst hμ
            have hkprev_lt : ((k : ℕ) - 1) < n := by omega
            have hmain :
                (((k : ℝ) + 1) * ε) -
                    (((((k : ℕ) - 1 : ℕ) : ℝ) + 1) * ε) = ε := by
              nlinarith [hkcast]
            simp [yε, e0, hk_lt, hk0, Pi.smul_apply, smul_eq_mul, hmain, hkprev_lt]
          · simp [yε, e0, hk_lt, hk0, hμ, Pi.smul_apply, smul_eq_mul]
        · by_cases hk_eq : (k : ℕ) = n
          · convert he0 using 1
            ext μ
            by_cases hμ : μ = 0
            · subst hμ
              have hn_pos : 0 < n := by omega
              have hn0_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
              have hkprev_lt : ((k : ℕ) - 1) < n := by omega
              have hkcast : (k : ℝ) = (n : ℝ) := by exact_mod_cast hk_eq
              have hprev_cast :
                  ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
                have hnat : (k : ℕ) - 1 + 1 = n := by
                  rw [hk_eq]
                  exact Nat.sub_add_cancel (show 1 ≤ n from hn_pos)
                exact_mod_cast hnat
              have hmain :
                  (1 + (k : ℝ) * ε) -
                    (((((k : ℕ) - 1 : ℕ) : ℝ) + 1) * ε) = 1 := by
                nlinarith [hkcast, hprev_cast]
              simpa [yε, e0, hk_lt, hk_eq, hk0, hn0_ne,
                hkprev_lt, hn_pos, Pi.smul_apply, smul_eq_mul] using hmain
            · have hn_pos : 0 < n := by omega
              have hn0_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
              have hkprev_lt : ((k : ℕ) - 1) < n := by omega
              simp [yε, e0, hk_lt, hk_eq, hk0, hn0_ne, hkprev_lt,
                hn_pos, hμ, Pi.smul_apply, smul_eq_mul]
          · have hk_gt : n < (k : ℕ) := by omega
            have hkprev_ge : n ≤ (k : ℕ) - 1 := by omega
            have hkprev_not_lt : ¬ ((k : ℕ) - 1 < n) := by omega
            have hkcast :
                (((k : ℕ) - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
              have hnat : (k : ℕ) - 1 + 1 = (k : ℕ) :=
                Nat.sub_add_cancel (show 1 ≤ (k : ℕ) from hkpos)
              have hreal : ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
                exact_mod_cast hnat
              linarith
            convert hεe0 using 1
            ext μ
            by_cases hμ : μ = 0
            · subst hμ
              have hmain :
                  (1 + (k : ℝ) * ε) -
                    (1 + ((((k : ℕ) - 1 : ℕ) : ℝ)) * ε) = ε := by
                nlinarith [hkcast]
              simp [yε, e0, hk_lt, hk_eq, hk_gt, hkprev_ge, hkprev_not_lt, hk0,
                Pi.smul_apply, smul_eq_mul, hmain]
            · simpa [yε, e0, hk_lt, hk_eq, hk_gt, hkprev_ge, hkprev_not_lt, hk0, hμ,
                Pi.smul_apply, smul_eq_mul]
    have hpair_nonneg :
        0 ≤ ∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i := by
      exact (mem_dualConeFlat.mp hξ)
        ((flattenCLEquivReal (n + m) (d + 1)) yε) ⟨yε, hyε_mem, rfl⟩
    have hsum_rewrite :
        (∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i) = S + ε * W := by
      let a : Fin (n + m) → ℝ :=
        fun k =>
          if (k : ℕ) < n then (((k : ℝ) + 1) * ε : ℝ)
          else (1 + (k : ℝ) * ε : ℝ)
      let b : Fin (n + m) → ℝ := fun k => if (k : ℕ) < n then 0 else 1
      let c : Fin (n + m) → ℝ :=
        fun k => if (k : ℕ) < n then ((k : ℝ) + 1) else (k : ℝ)
      calc
        (∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i)
            = ∑ k : Fin (n + m), a k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
                simpa [yε, a, flattenCLEquivReal_apply] using
                  (sum_over_flat_timeSlots (d := d) (a := a) ξ)
        _ = ∑ k : Fin (n + m),
              (b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) +
                ε * (c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hk_lt : (k : ℕ) < n
              · simp [a, b, c, hk_lt]
                ring
              · simp [a, b, c, hk_lt]
                ring
        _ = (∑ k : Fin (n + m), b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) +
              ε * (∑ k : Fin (n + m), c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = S + ε * W := by
              have hb :
                  ∑ k : Fin (n + m), b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) = S := by
                rw [Fin.sum_univ_add]
                simp [b, S]
              have hc :
                  ∑ k : Fin (n + m), c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) = W := by
                simp [c, W]
              rw [hb, hc]
    have hW_bound : ε * W ≤ (-S) / 2 := by
      have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
      have hstep1 : ε * W ≤ ε * |W| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self W) hε_nonneg
      have hstep2 : ε * |W| ≤ (-S) / 2 := by
        have hratio : |W| / (|W| + 1) ≤ (1 : ℝ) := by
          have hne : (|W| + 1 : ℝ) ≠ 0 := by positivity
          field_simp [hne]
          nlinarith [abs_nonneg W]
        have hrepr : ε * |W| = ((-S) / 2) * (|W| / (|W| + 1)) := by
          have hne : 2 * (|W| + 1) ≠ 0 := by positivity
          dsimp [ε]
          field_simp [hne]
        rw [hrepr]
        have hcoeff_nonneg : 0 ≤ (-S) / 2 := by linarith
        simpa using mul_le_mul_of_nonneg_left hratio hcoeff_nonneg
      exact le_trans hstep1 hstep2
    rw [hsum_rewrite] at hpair_nonneg
    linarith [hpair_nonneg, hW_bound, hSneg]
  rw [zeroHeadBlockShift_flatTimeShiftDirection_pairing_eq_neg_tailTimeSum
    (d := d) (n := n) (m := m) ξ]
  linarith

/-- After flattening and reindexing the real block into head/tail form, the
ambient conjugated tensor product is exactly the ordinary flat tensor product of
the left Borchers conjugate with the right factor. This is the precise
factorization seam needed to turn the live Stage-5 right-block CLM into a
consumer of the full flattened `(n+m)`-point spectral package. -/
theorem reindex_flattenSchwartzNPoint_conjTensorProduct_eq_tensorProduct
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    OSReconstruction.reindexSchwartzFin (by ring : (n + m) * (d + 1) =
        n * (d + 1) + m * (d + 1))
      (flattenSchwartzNPoint (d := d) (f.conjTensorProduct g)) =
      (flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct
        (flattenSchwartzNPoint (d := d) g) := by
  ext x
  rw [OSReconstruction.reindexSchwartzFin_apply, flattenSchwartzNPoint_apply,
    SchwartzMap.tensorProduct_apply, flattenSchwartzNPoint_apply,
    flattenSchwartzNPoint_apply, SchwartzMap.borchersConj_apply,
    SchwartzMap.conjTensorProduct_apply]
  simp only [splitFirst_reindex_flatten_symm_eq, splitLast_reindex_flatten_symm_eq]

/- Exact continuity of the full flattened Fourier-shift orbit used in the
final Stage-5 support theorem. -/

/- Polynomial seminorm growth of the full flattened Fourier-shift orbit. This
is the exact Schwartz-family bound needed by `schwartz_clm_fubini_exchange` in
the final flattened spectral step. -/

