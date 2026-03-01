import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-! ### d=1 `n≥4` arithmetic infrastructure

This file isolates the rank/arithmetic lemmas used by the `d=1, n≥4`
linear witness construction strategy.
-/

def d1Nge4_sigmaRankN (σ : Equiv.Perm (Fin n)) (k : Fin n) : ℕ :=
  (σ⁻¹ k).val

def d1Nge4_sigmaRankR (σ : Equiv.Perm (Fin n)) (k : Fin n) : ℝ :=
  (d1Nge4_sigmaRankN σ k : ℝ)

def d1Nge4_Bseq (σ : Equiv.Perm (Fin n)) (k : Fin n) : ℝ :=
  (2 : ℝ) * (d1Nge4_sigmaRankR σ k + 1)

def d1Nge4_Mseq (n : ℕ) : ℝ := (2 : ℝ) * (n : ℝ)

def d1Nge4_Aseq (n : ℕ) (i : Fin n) (k : Fin n) : ℝ :=
  (2 : ℝ) * (n : ℝ) + d1Nge4_Mseq n * (k.val : ℝ) -
    (if i.val + 1 ≤ k.val then (d1Nge4_Mseq n + 1) else 0)

lemma d1Nge4_Astep_nat
    (n : ℕ) (i : Fin n) (k : Fin n) (hk : k.val ≠ 0) :
    d1Nge4_Aseq n i k - d1Nge4_Aseq n i ⟨k.val - 1, by omega⟩ =
      (if k.val = i.val + 1 then (-1 : ℝ) else d1Nge4_Mseq n) := by
  have hcast : (k.val : ℝ) = ((k.val - 1 : ℕ) : ℝ) + 1 := by
    have hnat : k.val - 1 + 1 = k.val := Nat.sub_add_cancel (Nat.pos_iff_ne_zero.mpr hk)
    exact_mod_cast hnat.symm
  by_cases hki : k.val = i.val + 1
  · simp [d1Nge4_Aseq, d1Nge4_Mseq, hki]
    nlinarith
  · have hiff : (i.val + 1 ≤ k.val) ↔ (i.val + 1 ≤ k.val - 1) := by omega
    by_cases hcur : i.val + 1 ≤ k.val
    · have hprev : i.val + 1 ≤ k.val - 1 := (hiff.mp hcur)
      simp [d1Nge4_Aseq, d1Nge4_Mseq, hcur, hprev, hki]
      nlinarith
    · have hprev : ¬ i.val + 1 ≤ k.val - 1 := by
        intro h
        exact hcur ((hiff).mpr h)
      simp [d1Nge4_Aseq, d1Nge4_Mseq, hcur, hprev, hki]
      nlinarith

lemma d1Nge4_Astep_special
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    d1Nge4_Aseq n i ⟨i.val + 1, hi⟩ - d1Nge4_Aseq n i i = (-1 : ℝ) := by
  have hip1_ne0 : (⟨i.val + 1, hi⟩ : Fin n).val ≠ 0 := by
    exact Nat.succ_ne_zero i.val
  simpa using d1Nge4_Astep_nat n i ⟨i.val + 1, hi⟩ hip1_ne0

lemma d1Nge4_Astep_regular
    (n : ℕ) (i : Fin n) (k : Fin n)
    (hk0 : k.val ≠ 0)
    (hkSpecial : k.val ≠ i.val + 1) :
    d1Nge4_Aseq n i k - d1Nge4_Aseq n i ⟨k.val - 1, by omega⟩ = d1Nge4_Mseq n := by
  rw [d1Nge4_Astep_nat n i k hk0]
  simp [hkSpecial]

lemma d1Nge4_Bdiff_rewrite
    (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩ =
      (2 : ℝ) * (d1Nge4_sigmaRankR σ k - d1Nge4_sigmaRankR σ ⟨k.val - 1, by omega⟩) := by
  unfold d1Nge4_Bseq d1Nge4_sigmaRankR
  ring

lemma d1Nge4_Bdiff_bounds
    (σ : Equiv.Perm (Fin n)) (k : Fin n) (hk : k.val ≠ 0) :
    -((2 : ℝ) * (((n - 1 : ℕ) : ℝ)))
      ≤ d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩ ∧
    d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩
      ≤ (2 : ℝ) * (((n - 1 : ℕ) : ℝ)) := by
  have hklt : d1Nge4_sigmaRankN σ k < n := by
    simpa [d1Nge4_sigmaRankN] using (σ⁻¹ k).is_lt
  have hprevlt : d1Nge4_sigmaRankN σ ⟨k.val - 1, by omega⟩ < n := by
    simpa [d1Nge4_sigmaRankN] using (σ⁻¹ ⟨k.val - 1, by omega⟩).is_lt
  have hkubN : d1Nge4_sigmaRankN σ k ≤ n - 1 := Nat.le_pred_of_lt hklt
  have hprevubN : d1Nge4_sigmaRankN σ ⟨k.val - 1, by omega⟩ ≤ n - 1 :=
    Nat.le_pred_of_lt hprevlt
  have hkub : d1Nge4_sigmaRankR σ k ≤ (((n - 1 : ℕ) : ℝ)) := by
    unfold d1Nge4_sigmaRankR
    exact_mod_cast hkubN
  have hprevub : d1Nge4_sigmaRankR σ ⟨k.val - 1, by omega⟩ ≤ (((n - 1 : ℕ) : ℝ)) := by
    unfold d1Nge4_sigmaRankR
    exact_mod_cast hprevubN
  have hkge : (0 : ℝ) ≤ d1Nge4_sigmaRankR σ k := by
    unfold d1Nge4_sigmaRankR
    positivity
  have hprevge : (0 : ℝ) ≤ d1Nge4_sigmaRankR σ ⟨k.val - 1, by omega⟩ := by
    unfold d1Nge4_sigmaRankR
    positivity
  rw [d1Nge4_Bdiff_rewrite (n := n) σ k]
  constructor <;> nlinarith

lemma d1Nge4_Bdiff_special_sign_pos
    (σ : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (hord : (σ⁻¹ i).val < (σ⁻¹ ⟨i.val + 1, hi⟩).val) :
    (2 : ℝ) ≤ d1Nge4_Bseq σ ⟨i.val + 1, hi⟩ - d1Nge4_Bseq σ i := by
  have hnat : (d1Nge4_sigmaRankN σ i).succ ≤ d1Nge4_sigmaRankN σ ⟨i.val + 1, hi⟩ := by
    simpa [d1Nge4_sigmaRankN] using Nat.succ_le_of_lt hord
  have hreal : d1Nge4_sigmaRankR σ i + 1 ≤ d1Nge4_sigmaRankR σ ⟨i.val + 1, hi⟩ := by
    unfold d1Nge4_sigmaRankR d1Nge4_sigmaRankN at *
    exact_mod_cast hnat
  dsimp [d1Nge4_Bseq]
  nlinarith

lemma d1Nge4_Bdiff_special_sign_neg
    (σ : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (hord : (σ⁻¹ ⟨i.val + 1, hi⟩).val < (σ⁻¹ i).val) :
    d1Nge4_Bseq σ ⟨i.val + 1, hi⟩ - d1Nge4_Bseq σ i ≤ (-2 : ℝ) := by
  have hnat : (d1Nge4_sigmaRankN σ ⟨i.val + 1, hi⟩).succ ≤ d1Nge4_sigmaRankN σ i := by
    simpa [d1Nge4_sigmaRankN] using Nat.succ_le_of_lt hord
  have hreal : d1Nge4_sigmaRankR σ ⟨i.val + 1, hi⟩ + 1 ≤ d1Nge4_sigmaRankR σ i := by
    unfold d1Nge4_sigmaRankR d1Nge4_sigmaRankN at *
    exact_mod_cast hnat
  dsimp [d1Nge4_Bseq]
  nlinarith

lemma d1Nge4_B_at_sigma
    (σ : Equiv.Perm (Fin n))
    (k : Fin n) :
    d1Nge4_Bseq σ (σ k) = (2 : ℝ) * ((k : ℝ) + 1) := by
  simp [d1Nge4_Bseq, d1Nge4_sigmaRankR, d1Nge4_sigmaRankN]

lemma d1Nge4_B_sigma_step_pos
    (σ : Equiv.Perm (Fin n))
    (k : Fin n) (hk : k.val ≠ 0) :
    0 < d1Nge4_Bseq σ (σ k) - d1Nge4_Bseq σ (σ ⟨k.val - 1, by omega⟩) := by
  rw [d1Nge4_B_at_sigma (n := n) σ k,
    d1Nge4_B_at_sigma (n := n) σ ⟨k.val - 1, by omega⟩]
  have hcast : (k.val : ℝ) = ((k.val - 1 : ℕ) : ℝ) + 1 := by
    have hnat : k.val - 1 + 1 = k.val := Nat.sub_add_cancel (Nat.pos_iff_ne_zero.mpr hk)
    exact_mod_cast hnat.symm
  nlinarith [hcast]

lemma d1Nge4_B_sigma_zero_pos
    (σ : Equiv.Perm (Fin n))
    (hn : 1 ≤ n) :
    0 < d1Nge4_Bseq σ (σ ⟨0, hn⟩) := by
  rw [d1Nge4_B_at_sigma (n := n) σ ⟨0, hn⟩]
  norm_num

lemma d1Nge4_B_bounds
    (σ : Equiv.Perm (Fin n))
    (hn : 1 ≤ n)
    (k : Fin n) :
    (2 : ℝ) ≤ d1Nge4_Bseq σ k ∧ d1Nge4_Bseq σ k ≤ (2 : ℝ) * (n : ℝ) := by
  have hklt : d1Nge4_sigmaRankN σ k < n := by
    simpa [d1Nge4_sigmaRankN] using (σ⁻¹ k).is_lt
  have hkubN : d1Nge4_sigmaRankN σ k ≤ n - 1 := Nat.le_pred_of_lt hklt
  have hkub : d1Nge4_sigmaRankR σ k ≤ ((n - 1 : ℕ) : ℝ) := by
    unfold d1Nge4_sigmaRankR
    exact_mod_cast hkubN
  have hkge : (0 : ℝ) ≤ d1Nge4_sigmaRankR σ k := by
    unfold d1Nge4_sigmaRankR
    positivity
  constructor
  · dsimp [d1Nge4_Bseq]
    nlinarith
  · dsimp [d1Nge4_Bseq]
    have hpred_add : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel hn)
    nlinarith [hkub, hpred_add]

lemma d1Nge4_A_zero
    (n : ℕ) (i : Fin n) (hn : 1 ≤ n) :
    d1Nge4_Aseq n i ⟨0, hn⟩ = (2 : ℝ) * (n : ℝ) := by
  simp [d1Nge4_Aseq, d1Nge4_Mseq]

def d1Nge4_Tplus
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n)) :
    Fin n → ℝ :=
  fun k => (4 * d1Nge4_Aseq n i k - 3 * d1Nge4_Bseq σ k) / 7

def d1Nge4_Rplus
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n)) :
    Fin n → ℝ :=
  fun k => (4 * d1Nge4_Bseq σ k - 3 * d1Nge4_Aseq n i k) / 7

def d1Nge4_Tminus
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n)) :
    Fin n → ℝ :=
  fun k => (4 * d1Nge4_Aseq n i k + 3 * d1Nge4_Bseq σ k) / 25

def d1Nge4_Rminus
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n)) :
    Fin n → ℝ :=
  fun k => (3 * d1Nge4_Aseq n i k - 4 * d1Nge4_Bseq σ k) / 25

lemma d1Nge4_rel_plus_A
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n))
    (k : Fin n) :
    (4 : ℝ) * d1Nge4_Tplus n i σ k + 3 * d1Nge4_Rplus n i σ k =
      d1Nge4_Aseq n i k := by
  dsimp [d1Nge4_Tplus, d1Nge4_Rplus]
  ring

lemma d1Nge4_rel_plus_B
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n))
    (k : Fin n) :
    (3 : ℝ) * d1Nge4_Tplus n i σ k + 4 * d1Nge4_Rplus n i σ k =
      d1Nge4_Bseq σ k := by
  dsimp [d1Nge4_Tplus, d1Nge4_Rplus]
  ring

lemma d1Nge4_rel_minus_A
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n))
    (k : Fin n) :
    (4 : ℝ) * d1Nge4_Tminus n i σ k + 3 * d1Nge4_Rminus n i σ k =
      d1Nge4_Aseq n i k := by
  dsimp [d1Nge4_Tminus, d1Nge4_Rminus]
  ring

lemma d1Nge4_rel_minus_B
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n))
    (k : Fin n) :
    (3 : ℝ) * d1Nge4_Tminus n i σ k - 4 * d1Nge4_Rminus n i σ k =
      d1Nge4_Bseq σ k := by
  dsimp [d1Nge4_Tminus, d1Nge4_Rminus]
  ring

lemma d1Nge4_Tplus_zero_pos
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n))
    (hn4 : 4 ≤ n) :
    0 < d1Nge4_Tplus n i σ ⟨0, by omega⟩ := by
  have hBn : d1Nge4_Bseq σ ⟨0, by omega⟩ ≤ (2 : ℝ) * (n : ℝ) :=
    (d1Nge4_B_bounds (n := n) σ (by omega) ⟨0, by omega⟩).2
  have hA0 : d1Nge4_Aseq n i ⟨0, by omega⟩ = (2 : ℝ) * (n : ℝ) :=
    d1Nge4_A_zero n i (by omega)
  have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  dsimp [d1Nge4_Tplus]
  rw [hA0]
  nlinarith

lemma d1Nge4_Tminus_zero_pos
    (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n))
    (hn4 : 4 ≤ n) :
    0 < d1Nge4_Tminus n i σ ⟨0, by omega⟩ := by
  have hB2 : (2 : ℝ) ≤ d1Nge4_Bseq σ ⟨0, by omega⟩ :=
    (d1Nge4_B_bounds (n := n) σ (by omega) ⟨0, by omega⟩).1
  have hA0 : d1Nge4_Aseq n i ⟨0, by omega⟩ = (2 : ℝ) * (n : ℝ) :=
    d1Nge4_A_zero n i (by omega)
  have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  dsimp [d1Nge4_Tminus]
  rw [hA0]
  nlinarith

lemma d1Nge4_Tplus_step_pos
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
    (hord : (σ⁻¹ ⟨i.val + 1, hi⟩).val < (σ⁻¹ i).val)
    (hn4 : 4 ≤ n)
    (k : Fin n) (hk0 : k.val ≠ 0) :
    0 <
      d1Nge4_Tplus n i σ k -
      d1Nge4_Tplus n i σ ⟨k.val - 1, by omega⟩ := by
  by_cases hki : k.val = i.val + 1
  · have hA : d1Nge4_Aseq n i k - d1Nge4_Aseq n i ⟨k.val - 1, by omega⟩ = (-1 : ℝ) := by
      have hk_eq : k = ⟨i.val + 1, hi⟩ := by
        apply Fin.ext
        simpa using hki
      subst hk_eq
      simpa using d1Nge4_Astep_special n i hi
    have hB :
        d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩ ≤ (-2 : ℝ) := by
      have hk_eq : k = ⟨i.val + 1, hi⟩ := by
        apply Fin.ext
        simpa using hki
      subst hk_eq
      simpa using d1Nge4_Bdiff_special_sign_neg (n := n) σ i hi hord
    dsimp [d1Nge4_Tplus]
    nlinarith [hA, hB]
  · have hA : d1Nge4_Aseq n i k - d1Nge4_Aseq n i ⟨k.val - 1, by omega⟩ = d1Nge4_Mseq n :=
      d1Nge4_Astep_regular n i k hk0 hki
    have hBbounds :
        d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩
          ≤ (2 : ℝ) * (((n - 1 : ℕ) : ℝ)) :=
      (d1Nge4_Bdiff_bounds (n := n) σ k hk0).2
    have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hdiff :
        d1Nge4_Tplus n i σ k - d1Nge4_Tplus n i σ ⟨k.val - 1, by omega⟩ =
          (4 * (d1Nge4_Aseq n i k - d1Nge4_Aseq n i ⟨k.val - 1, by omega⟩) -
            3 * (d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩)) / 7 := by
      dsimp [d1Nge4_Tplus]
      ring
    have hnum_low :
        4 * d1Nge4_Mseq n - 3 * ((2 : ℝ) * (((n - 1 : ℕ) : ℝ))) ≤
          4 * d1Nge4_Mseq n -
            3 * (d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩) := by
      nlinarith [hBbounds]
    have hnum_pos :
        0 < 4 * d1Nge4_Mseq n - 3 * ((2 : ℝ) * (((n - 1 : ℕ) : ℝ))) := by
      have hn1 : 1 ≤ n := by omega
      have hpred_add : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel hn1)
      unfold d1Nge4_Mseq
      nlinarith [hn4r, hpred_add]
    have hnum_pos' :
        0 < 4 * d1Nge4_Mseq n -
          3 * (d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩) :=
      lt_of_lt_of_le hnum_pos hnum_low
    rw [hdiff, hA]
    have h7 : (0 : ℝ) < 7 := by norm_num
    nlinarith [hnum_pos', h7]

lemma d1Nge4_Tminus_step_pos
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
    (hord : (σ⁻¹ i).val < (σ⁻¹ ⟨i.val + 1, hi⟩).val)
    (hn4 : 4 ≤ n)
    (k : Fin n) (hk0 : k.val ≠ 0) :
    0 <
      d1Nge4_Tminus n i σ k -
      d1Nge4_Tminus n i σ ⟨k.val - 1, by omega⟩ := by
  by_cases hki : k.val = i.val + 1
  · have hA : d1Nge4_Aseq n i k - d1Nge4_Aseq n i ⟨k.val - 1, by omega⟩ = (-1 : ℝ) := by
      have hk_eq : k = ⟨i.val + 1, hi⟩ := by
        apply Fin.ext
        simpa using hki
      subst hk_eq
      simpa using d1Nge4_Astep_special n i hi
    have hB :
        (2 : ℝ) ≤ d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩ := by
      have hk_eq : k = ⟨i.val + 1, hi⟩ := by
        apply Fin.ext
        simpa using hki
      subst hk_eq
      simpa using d1Nge4_Bdiff_special_sign_pos (n := n) σ i hi hord
    dsimp [d1Nge4_Tminus]
    nlinarith [hA, hB]
  · have hA : d1Nge4_Aseq n i k - d1Nge4_Aseq n i ⟨k.val - 1, by omega⟩ = d1Nge4_Mseq n :=
      d1Nge4_Astep_regular n i k hk0 hki
    have hBbounds :
        -((2 : ℝ) * (((n - 1 : ℕ) : ℝ)))
          ≤ d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩ :=
      (d1Nge4_Bdiff_bounds (n := n) σ k hk0).1
    have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hdiff :
        d1Nge4_Tminus n i σ k - d1Nge4_Tminus n i σ ⟨k.val - 1, by omega⟩ =
          (4 * (d1Nge4_Aseq n i k - d1Nge4_Aseq n i ⟨k.val - 1, by omega⟩) +
            3 * (d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩)) / 25 := by
      dsimp [d1Nge4_Tminus]
      ring
    have hnum_low :
        4 * d1Nge4_Mseq n + 3 * (-(2 : ℝ) * (((n - 1 : ℕ) : ℝ))) ≤
          4 * d1Nge4_Mseq n +
            3 * (d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩) := by
      nlinarith [hBbounds]
    have hnum_pos :
        0 < 4 * d1Nge4_Mseq n + 3 * (-(2 : ℝ) * (((n - 1 : ℕ) : ℝ))) := by
      have hn1 : 1 ≤ n := by omega
      have hpred_add : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel hn1)
      unfold d1Nge4_Mseq
      nlinarith [hn4r, hpred_add]
    have hnum_pos' :
        0 < 4 * d1Nge4_Mseq n +
          3 * (d1Nge4_Bseq σ k - d1Nge4_Bseq σ ⟨k.val - 1, by omega⟩) :=
      lt_of_lt_of_le hnum_pos hnum_low
    rw [hdiff, hA]
    have h25 : (0 : ℝ) < 25 := by norm_num
    nlinarith [hnum_pos', h25]

end BHW
