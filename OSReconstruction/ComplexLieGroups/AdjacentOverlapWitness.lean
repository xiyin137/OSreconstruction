import OSReconstruction.ComplexLieGroups.BHWCore
import OSReconstruction.ComplexLieGroups.JostPoints

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace BHWCore

namespace BHW

variable {d n : ℕ}

private def e1 (hd : 2 ≤ d) : Fin (d + 1) := ⟨1, by omega⟩
private def e2 (hd : 2 ≤ d) : Fin (d + 1) := ⟨2, by omega⟩

private def swapWitnessReal (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ =>
    if μ = 0 then 0
    else if μ = e1 hd then (k : ℝ) + 1
    else if μ = e2 hd then if k = ⟨i.val + 1, hi⟩ then 1 else 0
    else 0

private lemma swapWitnessReal_mem_forwardJostSet (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    swapWitnessReal (d := d) (n := n) hd i hi ∈
      ForwardJostSet d n (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hd)) := by
  intro k
  let x := swapWitnessReal (d := d) (n := n) hd i hi
  have htime : consecutiveDiff x k 0 = 0 := by
    by_cases hk : (k : ℕ) = 0
    · simp [consecutiveDiff, x, swapWitnessReal, hk]
    · simp [consecutiveDiff, x, swapWitnessReal, hk]
  have hspat : consecutiveDiff x k (e1 hd) = 1 := by
    by_cases hk : (k : ℕ) = 0
    · have he10 : e1 hd ≠ (0 : Fin (d + 1)) := by
        intro h
        have hval : (e1 hd).val ≠ 0 := by simp [e1]
        exact hval (congrArg Fin.val h)
      simp [consecutiveDiff, x, swapWitnessReal, hk, he10]
    · simp [consecutiveDiff, x, swapWitnessReal, e1, hk]
      have hcast : (↑(k.val - 1) : ℝ) + 1 = (k : ℝ) := by
        have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
        have hnat : k.val - 1 + 1 = k.val := Nat.sub_add_cancel hk1
        exact_mod_cast hnat
      linarith [hcast]
  show |consecutiveDiff x k 0| < consecutiveDiff x k (e1 hd)
  rw [htime, hspat]
  norm_num

private lemma swapWitnessReal_mem_extendedTube (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    realEmbed (swapWitnessReal (d := d) (n := n) hd i hi) ∈ ExtendedTube d n := by
  have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hd)
  exact forwardJostSet_subset_extendedTube hd1
    (swapWitnessReal (d := d) (n := n) hd i hi)
    (swapWitnessReal_mem_forwardJostSet (d := d) (n := n) hd i hi)

private lemma swapWitnessReal_swapped_time_zero (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    consecutiveDiff
      (fun j => swapWitnessReal (d := d) (n := n) hd i hi
        (Equiv.swap i ⟨i.val + 1, hi⟩ j))
      k 0 = 0 := by
  let y : Fin n → Fin (d + 1) → ℝ :=
    fun j => swapWitnessReal (d := d) (n := n) hd i hi
      (Equiv.swap i ⟨i.val + 1, hi⟩ j)
  by_cases hk : (k : ℕ) = 0
  · simp [consecutiveDiff, swapWitnessReal, hk]
  · simp [consecutiveDiff, swapWitnessReal, hk]

private def swapWitnessRealSwapped (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) : Fin n → Fin (d + 1) → ℝ :=
  fun j => swapWitnessReal (d := d) (n := n) hd i hi
    (Equiv.swap i ⟨i.val + 1, hi⟩ j)

private lemma e1_ne_zero (hd : 2 ≤ d) : e1 hd ≠ (0 : Fin (d + 1)) := by
  intro h
  simp [e1, Fin.ext_iff] at h

private lemma e2_ne_zero (hd : 2 ≤ d) : e2 hd ≠ (0 : Fin (d + 1)) := by
  intro h
  simp [e2, Fin.ext_iff] at h

private lemma e2_ne_e1 (hd : 2 ≤ d) : e2 hd ≠ e1 hd := by
  intro h
  simp [e1, e2, Fin.ext_iff] at h

private lemma swapWitnessRealSwapped_diff_e1_at_i
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) i (e1 hd) = 2 := by
  let ip1 : Fin n := ⟨i.val + 1, hi⟩
  by_cases hi0 : i.val = 0
  · simp [consecutiveDiff, swapWitnessRealSwapped, swapWitnessReal, e1, ip1, hi0]
    norm_num
  · have hi1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi0
    let im1 : Fin n := ⟨i.val - 1, by omega⟩
    have him1_ne_i : im1 ≠ i := by
      intro h
      have hval : im1.val = i.val := congrArg Fin.val h
      dsimp [im1] at hval
      omega
    have him1_ne_ip1 : im1 ≠ ip1 := by
      intro h
      have hval : im1.val = ip1.val := congrArg Fin.val h
      dsimp [im1, ip1] at hval
      omega
    have hswap_im1 : Equiv.swap i ip1 im1 = im1 :=
      Equiv.swap_apply_of_ne_of_ne him1_ne_i him1_ne_ip1
    have hcast : (im1 : ℝ) + 1 = (i : ℝ) := by
      have hnat : im1.val + 1 = i.val := by
        dsimp [im1]
        exact Nat.sub_add_cancel hi1
      exact_mod_cast hnat
    simp [consecutiveDiff, swapWitnessRealSwapped, swapWitnessReal, e1, ip1, im1, hi0,
      hswap_im1, hcast]
    ring

private lemma swapWitnessRealSwapped_diff_e2_at_i
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) i (e2 hd) = 1 := by
  let ip1 : Fin n := ⟨i.val + 1, hi⟩
  by_cases hi0 : i.val = 0
  ·
    simp [consecutiveDiff, swapWitnessRealSwapped, swapWitnessReal, e1, e2, ip1,
      hi0, e2_ne_zero, e2_ne_e1]
  · have hi1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi0
    let im1 : Fin n := ⟨i.val - 1, by omega⟩
    have him1_ne_i : im1 ≠ i := by
      intro h
      have hval : im1.val = i.val := congrArg Fin.val h
      dsimp [im1] at hval
      omega
    have him1_ne_ip1 : im1 ≠ ip1 := by
      intro h
      have hval : im1.val = ip1.val := congrArg Fin.val h
      dsimp [im1, ip1] at hval
      omega
    have hswap_im1 : Equiv.swap i ip1 im1 = im1 :=
      Equiv.swap_apply_of_ne_of_ne him1_ne_i him1_ne_ip1
    have him1_ne_ip1' : im1 ≠ ip1 := him1_ne_ip1
    have hi_ne_ip1 : i ≠ ip1 := by
      intro h
      have hval : i.val = ip1.val := congrArg Fin.val h
      dsimp [ip1] at hval
      omega
    simp [consecutiveDiff, swapWitnessRealSwapped, swapWitnessReal, e1, e2, ip1, im1, hi0,
      hswap_im1, e2_ne_zero, e2_ne_e1, hi_ne_ip1, him1_ne_ip1']

private lemma swapWitnessRealSwapped_diff_e1_at_ip1
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi)
      ⟨i.val + 1, hi⟩ (e1 hd) = -1 := by
  let ip1 : Fin n := ⟨i.val + 1, hi⟩
  have hip1_ne0 : ¬ (ip1.val = 0) := by
    dsimp [ip1]
    exact Nat.succ_ne_zero i.val
  have hi_ne_ip1 : i ≠ ip1 := by
    intro h
    have hval : i.val = ip1.val := congrArg Fin.val h
    dsimp [ip1] at hval
    omega
  have hprev : (⟨ip1.val - 1, by omega⟩ : Fin n) = i := by
    apply Fin.ext
    dsimp [ip1]
  simp [consecutiveDiff, swapWitnessRealSwapped, swapWitnessReal, e1, e2, ip1, hip1_ne0, hprev,
    e1_ne_zero, hi_ne_ip1]

private lemma swapWitnessRealSwapped_diff_e2_at_ip1
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi)
      ⟨i.val + 1, hi⟩ (e2 hd) = -1 := by
  let ip1 : Fin n := ⟨i.val + 1, hi⟩
  have hip1_ne0 : ¬ (ip1.val = 0) := by
    dsimp [ip1]
    exact Nat.succ_ne_zero i.val
  have hi_ne_ip1 : i ≠ ip1 := by
    intro h
    have hval : i.val = ip1.val := congrArg Fin.val h
    dsimp [ip1] at hval
    omega
  have hprev : (⟨ip1.val - 1, by omega⟩ : Fin n) = i := by
    apply Fin.ext
    dsimp [ip1]
  simp [consecutiveDiff, swapWitnessRealSwapped, swapWitnessReal, e1, e2, ip1, hip1_ne0, hprev,
    e2_ne_zero, e2_ne_e1, hi_ne_ip1]

private lemma swapWitnessRealSwapped_linear_pos_special
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    (3 / 5 : ℝ) * consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) i (e1 hd) +
      (-4 / 5 : ℝ) * consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) i (e2 hd)
      > 0 := by
  rw [swapWitnessRealSwapped_diff_e1_at_i (d := d) (n := n) hd i hi,
      swapWitnessRealSwapped_diff_e2_at_i (d := d) (n := n) hd i hi]
  norm_num

private lemma swapWitnessRealSwapped_linear_pos_ip1
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    (3 / 5 : ℝ) *
      consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) ⟨i.val + 1, hi⟩ (e1 hd) +
      (-4 / 5 : ℝ) *
      consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) ⟨i.val + 1, hi⟩ (e2 hd)
      > 0 := by
  rw [swapWitnessRealSwapped_diff_e1_at_ip1 (d := d) (n := n) hd i hi,
      swapWitnessRealSwapped_diff_e2_at_ip1 (d := d) (n := n) hd i hi]
  norm_num

end BHW
private noncomputable def spatialRotMatrix12 (d : ℕ) (_hd : 2 ≤ d) (a b : ℝ)
    (_hab : 0 < a ^ 2 + b ^ 2) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  let r := Real.sqrt (a ^ 2 + b ^ 2)
  fun μ ν =>
    if μ = ⟨1, by omega⟩ ∧ ν = ⟨1, by omega⟩ then ((a / r : ℝ) : ℂ)
    else if μ = ⟨1, by omega⟩ ∧ ν = ⟨2, by omega⟩ then ((b / r : ℝ) : ℂ)
    else if μ = ⟨2, by omega⟩ ∧ ν = ⟨1, by omega⟩ then -((b / r : ℝ) : ℂ)
    else if μ = ⟨2, by omega⟩ ∧ ν = ⟨2, by omega⟩ then ((a / r : ℝ) : ℂ)
    else if μ = ν then 1
    else 0

-- Row simplification lemmas for the spatial rotation matrix.
private lemma spatialRot12_row0 (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) (ν : Fin (d + 1)) :
    spatialRotMatrix12 d hd a b hab 0 ν = if ν = 0 then 1 else 0 := by
  simp only [spatialRotMatrix12]
  rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by norm_num))]
  rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by norm_num))]
  rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by norm_num))]
  rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by norm_num))]
  -- Goal: (if 0 = ν then 1 else 0) = (if ν = 0 then 1 else 0)
  by_cases hν0 : ν = 0
  · subst hν0; simp
  · rw [if_neg (Ne.symm hν0), if_neg hν0]

private lemma spatialRot12_row1 (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) (ν : Fin (d + 1)) :
    spatialRotMatrix12 d hd a b hab ⟨1, by omega⟩ ν =
      if ν = ⟨1, by omega⟩ then ((a / Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ)
      else if ν = ⟨2, by omega⟩ then ((b / Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ)
      else 0 := by
  simp only [spatialRotMatrix12]
  by_cases hν1 : ν = ⟨1, by omega⟩
  · subst hν1; simp
  · rw [if_neg (by intro ⟨_, h⟩; exact hν1 h)]
    by_cases hν2 : ν = ⟨2, by omega⟩
    · subst hν2; simp
    · rw [if_neg (by intro ⟨_, h⟩; exact hν2 h)]
      rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by norm_num))]
      rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by norm_num))]
      simp only [hν1, hν2, ↓reduceIte]
      rw [if_neg (by intro h; exact hν1 (Fin.ext (by have := congr_arg Fin.val h; omega)))]

private lemma spatialRot12_row2 (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) (ν : Fin (d + 1)) :
    spatialRotMatrix12 d hd a b hab ⟨2, by omega⟩ ν =
      if ν = ⟨1, by omega⟩ then -((b / Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ)
      else if ν = ⟨2, by omega⟩ then ((a / Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ)
      else 0 := by
  simp only [spatialRotMatrix12]
  rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by norm_num))]
  rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by norm_num))]
  by_cases hν1 : ν = ⟨1, by omega⟩
  · subst hν1; simp
  · rw [if_neg (by intro ⟨_, h⟩; exact hν1 h)]
    by_cases hν2 : ν = ⟨2, by omega⟩
    · subst hν2; simp
    · rw [if_neg (by intro ⟨_, h⟩; exact hν2 h)]
      simp only [hν1, hν2, ↓reduceIte]
      rw [if_neg (by intro h; exact hν2 (Fin.ext (by have := congr_arg Fin.val h; omega)))]

private lemma spatialRot12_row_ge3 (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) (μ : Fin (d + 1))
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ ⟨1, by omega⟩) (hμ2 : μ ≠ ⟨2, by omega⟩)
    (ν : Fin (d + 1)) :
    spatialRotMatrix12 d hd a b hab μ ν = if ν = μ then 1 else 0 := by
  simp only [spatialRotMatrix12]
  rw [if_neg (by intro ⟨h, _⟩; exact hμ1 h)]
  rw [if_neg (by intro ⟨h, _⟩; exact hμ1 h)]
  rw [if_neg (by intro ⟨h, _⟩; exact hμ2 h)]
  rw [if_neg (by intro ⟨h, _⟩; exact hμ2 h)]
  by_cases hνμ : ν = μ
  · subst hνμ; simp
  · rw [if_neg (by intro h; exact hνμ h.symm), if_neg hνμ]

-- The spatial rotation preserves the Minkowski metric.
private lemma spatialRotMatrix12_metric (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) :
    ∀ (μ ν : Fin (d + 1)),
    ∑ α : Fin (d + 1),
      (minkowskiSignature d α : ℂ) * spatialRotMatrix12 d hd a b hab α μ *
        spatialRotMatrix12 d hd a b hab α ν =
    if μ = ν then (minkowskiSignature d μ : ℂ) else 0 := by
  set r := Real.sqrt (a ^ 2 + b ^ 2) with hr_def
  have hr_pos : 0 < r := Real.sqrt_pos_of_pos hab
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hR0 := spatialRot12_row0 d hd a b hab
  have hR1 := spatialRot12_row1 d hd a b hab
  have hR2 := spatialRot12_row2 d hd a b hab
  have hRge3 := spatialRot12_row_ge3 d hd a b hab
  -- Key identity: (a/r)² + (b/r)² = 1
  have hcs : ((a / r : ℝ) : ℂ) ^ 2 + ((b / r : ℝ) : ℂ) ^ 2 = 1 := by
    have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hab.le
    have : (a / r) ^ 2 + (b / r) ^ 2 = (1 : ℝ) := by
      rw [div_pow, div_pow, ← add_div, hr2, div_self (ne_of_gt hab)]
    exact_mod_cast this
  -- Fin inequalities (proved once, used throughout)
  have h10 : (⟨1, by omega⟩ : Fin (d+1)) ≠ 0 := by
    intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
  have h20 : (⟨2, by omega⟩ : Fin (d+1)) ≠ 0 := by
    intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
  have h12 : (⟨1, by omega⟩ : Fin (d+1)) ≠ ⟨2, by omega⟩ := by
    intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
  -- η(μ) = 1 for μ ≠ 0
  have hη_ne0 : ∀ (μ : Fin (d+1)), μ ≠ 0 → (minkowskiSignature d μ : ℂ) = 1 := by
    intro μ hμ; simp [minkowskiSignature, hμ]
  intro μ ν
  by_cases hμν : μ = ν
  · -- Diagonal case
    subst hμν; rw [if_pos rfl]
    by_cases hμ0 : μ = 0
    · -- μ = 0: column 0 is e₀
      subst hμ0
      have hcol0 : ∀ α : Fin (d + 1),
          spatialRotMatrix12 d hd a b hab α 0 = if α = 0 then 1 else 0 := by
        intro α
        by_cases hα0 : α = 0
        · subst hα0; rw [hR0]
        · by_cases hα1 : α = ⟨1, by omega⟩
          · subst hα1; rw [hR1]; simp [h10.symm, h20.symm]
          · by_cases hα2 : α = ⟨2, by omega⟩
            · subst hα2; rw [hR2]; simp
            · rw [hRge3 α hα0 hα1 hα2, if_neg (Ne.symm hα0), if_neg hα0]
      simp_rw [hcol0]
      simp [mul_ite, Finset.sum_ite_eq', Finset.mem_univ, minkowskiSignature]
    · by_cases hμ1 : μ = ⟨1, by omega⟩
      · -- μ = 1: sum = (a/r)² + (b/r)² = 1 = η(1)
        subst hμ1
        have hsummand : ∀ α : Fin (d + 1),
            (minkowskiSignature d α : ℂ) *
              spatialRotMatrix12 d hd a b hab α ⟨1, by omega⟩ *
              spatialRotMatrix12 d hd a b hab α ⟨1, by omega⟩ =
            if α = ⟨1, by omega⟩ then ((a / r : ℝ) : ℂ) ^ 2
            else if α = ⟨2, by omega⟩ then ((b / r : ℝ) : ℂ) ^ 2 else 0 := by
          intro α
          by_cases hα0 : α = 0
          · subst hα0; rw [hR0]; simp [h10.symm, h20.symm]
          · by_cases hα1 : α = ⟨1, by omega⟩
            · subst hα1; rw [hR1]; simp only [↓reduceIte]
              rw [hη_ne0 _ h10]; push_cast; ring
            · by_cases hα2 : α = ⟨2, by omega⟩
              · subst hα2; rw [hR2]; simp only [↓reduceIte, hα1]
                rw [hη_ne0 _ h20]; push_cast; ring
              · rw [hRge3 α hα0 hα1 hα2, if_neg (Ne.symm hα1)]; simp [hα1, hα2]
        simp_rw [hsummand]
        have hsplit : ∀ α : Fin (d+1),
            (if α = ⟨1, by omega⟩ then ((a / r : ℝ) : ℂ) ^ 2
             else if α = ⟨2, by omega⟩ then ((b / r : ℝ) : ℂ) ^ 2 else (0 : ℂ)) =
            (if α = ⟨1, by omega⟩ then ((a / r : ℝ) : ℂ) ^ 2 else 0) +
            (if α = ⟨2, by omega⟩ then ((b / r : ℝ) : ℂ) ^ 2 else 0) := by
          intro α; by_cases h1 : α = ⟨1, by omega⟩
          · subst h1; simp [show ⟨1, _⟩ ≠ (⟨2, _⟩ : Fin (d+1)) from h12]
          · simp [h1]
        simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ↓reduceIte]
        rw [hη_ne0 _ h10]; exact_mod_cast hcs
      · by_cases hμ2 : μ = ⟨2, by omega⟩
        · -- μ = 2: sum = (b/r)² + (a/r)² = 1 = η(2)
          subst hμ2
          have hsummand : ∀ α : Fin (d + 1),
              (minkowskiSignature d α : ℂ) *
                spatialRotMatrix12 d hd a b hab α ⟨2, by omega⟩ *
                spatialRotMatrix12 d hd a b hab α ⟨2, by omega⟩ =
              if α = ⟨1, by omega⟩ then ((b / r : ℝ) : ℂ) ^ 2
              else if α = ⟨2, by omega⟩ then ((a / r : ℝ) : ℂ) ^ 2 else 0 := by
            intro α
            by_cases hα0 : α = 0
            · subst hα0; rw [hR0]; simp [h10.symm, h20.symm]
            · by_cases hα1 : α = ⟨1, by omega⟩
              · subst hα1; rw [hR1]; simp only [↓reduceIte, Ne.symm h12]
                rw [hη_ne0 _ h10]; push_cast; ring
              · by_cases hα2 : α = ⟨2, by omega⟩
                · subst hα2; rw [hR2]; simp only [↓reduceIte, hα1]
                  rw [hη_ne0 _ h20]; push_cast; ring
                · rw [hRge3 α hα0 hα1 hα2, if_neg (Ne.symm hα2)]; simp [hα1, hα2]
          simp_rw [hsummand]
          have hsplit : ∀ α : Fin (d+1),
              (if α = ⟨1, by omega⟩ then ((b / r : ℝ) : ℂ) ^ 2
               else if α = ⟨2, by omega⟩ then ((a / r : ℝ) : ℂ) ^ 2 else (0 : ℂ)) =
              (if α = ⟨1, by omega⟩ then ((b / r : ℝ) : ℂ) ^ 2 else 0) +
              (if α = ⟨2, by omega⟩ then ((a / r : ℝ) : ℂ) ^ 2 else 0) := by
            intro α; by_cases h1 : α = ⟨1, by omega⟩
            · subst h1; simp [show ⟨1, _⟩ ≠ (⟨2, _⟩ : Fin (d+1)) from h12]
            · simp [h1]
          simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_univ, ↓reduceIte]
          rw [hη_ne0 _ h20]
          have : ((b / r : ℝ) : ℂ) ^ 2 + ((a / r : ℝ) : ℂ) ^ 2 =
              ((a / r : ℝ) : ℂ) ^ 2 + ((b / r : ℝ) : ℂ) ^ 2 := by ring
          rw [this]; exact_mod_cast hcs
        · -- μ ≥ 3: column μ is δ(·, μ)
          have hcolμ : ∀ α : Fin (d + 1),
              spatialRotMatrix12 d hd a b hab α μ = if α = μ then 1 else 0 := by
            intro α
            by_cases hα0 : α = 0
            · subst hα0; rw [hR0, if_neg hμ0, if_neg (Ne.symm hμ0)]
            · by_cases hα1 : α = ⟨1, by omega⟩
              · subst hα1; rw [hR1, if_neg hμ1, if_neg hμ2, if_neg (fun h => hμ1 h.symm)]
              · by_cases hα2 : α = ⟨2, by omega⟩
                · subst hα2; rw [hR2, if_neg hμ1, if_neg hμ2, if_neg (fun h => hμ2 h.symm)]
                · rw [hRge3 α hα0 hα1 hα2]
                  by_cases hαμ : α = μ
                  · subst hαμ; simp
                  · simp [hαμ, Ne.symm hαμ]
          simp_rw [hcolμ]
          simp [mul_ite, Finset.sum_ite_eq', Finset.mem_univ, minkowskiSignature, hμ0]
  · -- Off-diagonal case: ∑ α, η(α) * R(α,μ) * R(α,ν) = 0
    rw [if_neg hμν]
    -- Characterize each summand: nonzero only for α ∈ {1, 2}
    have hsummand : ∀ α : Fin (d + 1),
        (minkowskiSignature d α : ℂ) *
          spatialRotMatrix12 d hd a b hab α μ *
          spatialRotMatrix12 d hd a b hab α ν =
        if α = ⟨1, by omega⟩ then
          spatialRotMatrix12 d hd a b hab ⟨1, by omega⟩ μ *
            spatialRotMatrix12 d hd a b hab ⟨1, by omega⟩ ν
        else if α = ⟨2, by omega⟩ then
          spatialRotMatrix12 d hd a b hab ⟨2, by omega⟩ μ *
            spatialRotMatrix12 d hd a b hab ⟨2, by omega⟩ ν
        else 0 := by
      intro α
      by_cases hα0 : α = 0
      · subst hα0; simp only [hR0, ↓reduceIte, Ne.symm h10, Ne.symm h20]
        by_cases hμ0 : μ = 0
        · subst hμ0; simp only [↓reduceIte, Ne.symm hμν]; ring
        · rw [if_neg hμ0]; ring
      · by_cases hα1 : α = ⟨1, by omega⟩
        · subst hα1; simp only [↓reduceIte]; rw [hη_ne0 _ h10]; ring
        · by_cases hα2 : α = ⟨2, by omega⟩
          · subst hα2; simp only [↓reduceIte, hα1]; rw [hη_ne0 _ h20]; ring
          · simp only [hRge3 α hα0 hα1 hα2, if_neg hα1, if_neg hα2]
            by_cases hμα : μ = α
            · rw [if_pos hμα, if_neg (fun h => hμν (hμα.trans h.symm))]; ring
            · rw [if_neg hμα]; ring
    simp_rw [hsummand]
    -- Split nested if into sum of two single ifs
    have hsplit : ∀ α : Fin (d+1),
        (if α = ⟨1, by omega⟩ then
          spatialRotMatrix12 d hd a b hab ⟨1, by omega⟩ μ *
            spatialRotMatrix12 d hd a b hab ⟨1, by omega⟩ ν
        else if α = ⟨2, by omega⟩ then
          spatialRotMatrix12 d hd a b hab ⟨2, by omega⟩ μ *
            spatialRotMatrix12 d hd a b hab ⟨2, by omega⟩ ν
        else (0 : ℂ)) =
        (if α = ⟨1, by omega⟩ then
          spatialRotMatrix12 d hd a b hab ⟨1, by omega⟩ μ *
            spatialRotMatrix12 d hd a b hab ⟨1, by omega⟩ ν else 0) +
        (if α = ⟨2, by omega⟩ then
          spatialRotMatrix12 d hd a b hab ⟨2, by omega⟩ μ *
            spatialRotMatrix12 d hd a b hab ⟨2, by omega⟩ ν else 0) := by
      intro α; by_cases h1 : α = ⟨1, by omega⟩
      · subst h1; simp [h12]
      · simp [h1]
    simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    -- Goal: R(1,μ)*R(1,ν) + R(2,μ)*R(2,ν) = 0. Expand using row lemmas.
    simp only [hR1, hR2]
    -- Case split on μ, ν to evaluate the nested ifs
    by_cases hμ1 : μ = ⟨1, by omega⟩
    · subst hμ1; simp only [↓reduceIte]
      by_cases hν2 : ν = ⟨2, by omega⟩
      · subst hν2; simp only [↓reduceIte, Ne.symm h12]; push_cast; ring
      · simp only [if_neg (Ne.symm hμν), if_neg hν2]; ring
    · by_cases hμ2 : μ = ⟨2, by omega⟩
      · subst hμ2; simp only [↓reduceIte]
        by_cases hν1 : ν = ⟨1, by omega⟩
        · subst hν1; simp only [↓reduceIte, Ne.symm h12]; push_cast; ring
        · simp only [if_neg hν1, if_neg (Ne.symm hμν)]; ring
      · -- μ ∉ {1, 2}: R(1,μ) = 0, R(2,μ) = 0
        simp only [if_neg hμ1, if_neg hμ2]; ring

-- The spatial rotation has determinant 1.
-- Strategy: MᵀηM = η gives det²=1. Then we use a continuous path argument:
-- the family M(t) for t ∈ [0,1] where M(0)=I and M(1)=M is continuous
-- with det(M(t))² = 1, so det is constant = det(I) = 1.
-- We implement this via the matrix equation approach and the intermediate value theorem.
private lemma spatialRotMatrix12_det (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) :
    (spatialRotMatrix12 d hd a b hab).det = 1 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  set d : ℕ := d' + 2
  have hd0 : 2 ≤ d := by omega
  set M := spatialRotMatrix12 d hd0 a b hab
  set r := Real.sqrt (a ^ 2 + b ^ 2) with hr_def
  have hR0 := spatialRot12_row0 d hd0 a b hab
  have hR1 := spatialRot12_row1 d hd0 a b hab
  have hR2 := spatialRot12_row2 d hd0 a b hab
  have hRge3 := spatialRot12_row_ge3 d hd0 a b hab
  have hcol0 : ∀ α : Fin (d + 1), M α 0 = if α = 0 then 1 else 0 := by
    intro α
    show spatialRotMatrix12 d hd0 a b hab α 0 = if α = 0 then 1 else 0
    by_cases hα0 : α = 0
    · subst hα0
      simpa using hR0 (0 : Fin (d + 1))
    · by_cases hα1 : α = ⟨1, by omega⟩
      · subst hα1; rw [hR1]
        rw [if_neg (by intro h; exact absurd (congr_arg Fin.val h) (by norm_num))]
        rw [if_neg (by intro h; exact absurd (congr_arg Fin.val h) (by norm_num))]
        rw [if_neg hα0]
      · by_cases hα2 : α = ⟨2, by omega⟩
        · subst hα2; rw [hR2]
          rw [if_neg (by intro h; exact absurd (congr_arg Fin.val h) (by norm_num))]
          rw [if_neg (by intro h; exact absurd (congr_arg Fin.val h) (by norm_num))]
          rw [if_neg hα0]
        · rw [hRge3 α hα0 hα1 hα2, if_neg (Ne.symm hα0), if_neg hα0]
  rw [Matrix.det_succ_column_zero]
  conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (d + 1)))]
  have hrest : ∀ i ∈ Finset.univ.erase (0 : Fin (d + 1)),
      (-1 : ℂ) ^ (i : ℕ) * M (i : Fin (d + 1)) 0 *
        (M.submatrix (Fin.succAbove i) Fin.succ).det = 0 := by
    intro i hi
    rw [hcol0 i, if_neg (Finset.mem_erase.mp hi).1]
    ring
  rw [Finset.sum_eq_zero hrest, add_zero]
  rw [hcol0 0, if_pos rfl]
  simp
  set N := M.submatrix (Fin.succAbove 0) Fin.succ
  have hN_ge2 : ∀ (i : Fin d), (2 : ℕ) ≤ i.val → ∀ j : Fin d,
      N i j = if i = j then 1 else 0 := by
    intro i hi j
    change M (Fin.succ i) (Fin.succ j) = if i = j then 1 else 0
    have hi1 : Fin.succ i ≠ ⟨1, by omega⟩ := by
      intro h
      have hval : i.val + 1 = 1 := by
        exact congr_arg Fin.val h
      omega
    have hi2 : Fin.succ i ≠ ⟨2, by omega⟩ := by
      intro h
      have hval : i.val + 1 = 2 := by
        exact congr_arg Fin.val h
      omega
    have hi0 : Fin.succ i ≠ 0 := Fin.succ_ne_zero i
    have htmp : M (Fin.succ i) (Fin.succ j) = if Fin.succ j = Fin.succ i then 1 else 0 := by
      simpa [M] using (hRge3 (Fin.succ i) hi0 hi1 hi2 (Fin.succ j))
    rw [htmp]
    by_cases hij : i = j
    · subst hij
      simp
    · have hji : ¬j = i := by intro h; exact hij h.symm
      simp [hij, hji]
  change N.det = 1
  have hd1 : 1 < d := by omega
  have hN00 : N 0 0 = ((a / r : ℝ) : ℂ) := by
    change M ⟨1, by omega⟩ ⟨1, by omega⟩ = ((a / r : ℝ) : ℂ)
    change spatialRotMatrix12 d hd0 a b hab ⟨1, by omega⟩ ⟨1, by omega⟩ = ((a / r : ℝ) : ℂ)
    rw [hR1]
    simp [r]
  have hN01 : N 0 ⟨1, hd1⟩ = ((b / r : ℝ) : ℂ) := by
    change M ⟨1, by omega⟩ ⟨2, by omega⟩ = ((b / r : ℝ) : ℂ)
    change spatialRotMatrix12 d hd0 a b hab ⟨1, by omega⟩ ⟨2, by omega⟩ = ((b / r : ℝ) : ℂ)
    rw [hR1]
    simp [r]
  have hN10 : N ⟨1, hd1⟩ 0 = -((b / r : ℝ) : ℂ) := by
    change M ⟨2, by omega⟩ ⟨1, by omega⟩ = -((b / r : ℝ) : ℂ)
    change spatialRotMatrix12 d hd0 a b hab ⟨2, by omega⟩ ⟨1, by omega⟩ = -((b / r : ℝ) : ℂ)
    rw [hR2]
    simp [r]
  have hN11 : N ⟨1, hd1⟩ ⟨1, hd1⟩ = ((a / r : ℝ) : ℂ) := by
    change M ⟨2, by omega⟩ ⟨2, by omega⟩ = ((a / r : ℝ) : ℂ)
    change spatialRotMatrix12 d hd0 a b hab ⟨2, by omega⟩ ⟨2, by omega⟩ = ((a / r : ℝ) : ℂ)
    rw [hR2]
    simp [r]
  let p : Fin d → Prop := fun i => i.val < 2
  have hlower_zero : ∀ i : Fin d, ¬ p i → ∀ j : Fin d, p j → N i j = 0 := by
    intro i hi j hj
    have hi_ge2 : 2 ≤ i.val := by
      have : ¬ i.val < 2 := by simpa [p] using hi
      omega
    have hij : i ≠ j := by
      intro hij
      have : 2 ≤ j.val := by simpa [hij] using hi_ge2
      have hj_lt : j.val < 2 := by simpa [p] using hj
      omega
    rw [hN_ge2 i hi_ge2 j, if_neg hij]
  have hdet_block := Matrix.twoBlockTriangular_det (M := N) (p := p) hlower_zero
  set A : Matrix {i : Fin d // p i} {i : Fin d // p i} ℂ := N.toSquareBlockProp p
  set B : Matrix {i : Fin d // ¬ p i} {i : Fin d // ¬ p i} ℂ := N.toSquareBlockProp (fun i => ¬ p i)
  have hdetN : N.det = A.det * B.det := by
    simpa [A, B] using hdet_block
  rw [hdetN]
  have hB_one : B = 1 := by
    ext i j
    change N (i : Fin d) (j : Fin d) = if i = j then 1 else 0
    have hi_ge2 : 2 ≤ (i : Fin d).val := by
      have : ¬ (i : Fin d).val < 2 := by simpa [p] using i.2
      omega
    rw [hN_ge2 (i : Fin d) hi_ge2 (j : Fin d)]
    by_cases hij : i = j
    · subst hij
      simp
    · have hij' : (i : Fin d) ≠ (j : Fin d) := by
        intro h
        apply hij
        exact Subtype.ext h
      simp [hij, hij']
  have hB_det : B.det = 1 := by
    rw [hB_one, Matrix.det_one]
  have hd2 : 2 ≤ d := by omega
  let e : Fin 2 ≃ {i : Fin d // p i} :=
    { toFun := fun i =>
        ⟨⟨i.val, lt_of_lt_of_le i.isLt hd2⟩, by
          show (⟨i.val, _⟩ : Fin d).val < 2; exact i.isLt⟩
      invFun := fun i => ⟨i.1.val, by
        simpa [p] using i.2⟩
      left_inv := by
        intro i
        ext
        rfl
      right_inv := by
        intro i
        apply Subtype.ext
        ext
        rfl }
  have he0 : ((e 0).1 : Fin d) = 0 := by
    ext
    rfl
  have he1 : ((e 1).1 : Fin d) = ⟨1, hd1⟩ := by
    ext
    rfl
  have hA_det : A.det = ((a / r : ℝ) : ℂ) ^ 2 + ((b / r : ℝ) : ℂ) ^ 2 := by
    have hA_reindex : A.det = (A.submatrix e e).det := by
      exact (Matrix.det_submatrix_equiv_self e A).symm
    rw [hA_reindex, Matrix.det_fin_two]
    have h00 : (A.submatrix e e) 0 0 = ((a / r : ℝ) : ℂ) := by
      change N ((e 0).1) ((e 0).1) = ((a / r : ℝ) : ℂ)
      simpa [he0] using hN00
    have h01 : (A.submatrix e e) 0 1 = ((b / r : ℝ) : ℂ) := by
      change N ((e 0).1) ((e 1).1) = ((b / r : ℝ) : ℂ)
      rw [he0, he1, hN01]
    have h10 : (A.submatrix e e) 1 0 = -((b / r : ℝ) : ℂ) := by
      change N ((e 1).1) ((e 0).1) = -((b / r : ℝ) : ℂ)
      rw [he1, he0, hN10]
    have h11 : (A.submatrix e e) 1 1 = ((a / r : ℝ) : ℂ) := by
      change N ((e 1).1) ((e 1).1) = ((a / r : ℝ) : ℂ)
      simpa [he1] using hN11
    rw [h00, h01, h10, h11]
    ring
  rw [hA_det, hB_det, mul_one]
  have hcsR : (a / r) ^ 2 + (b / r) ^ 2 = (1 : ℝ) := by
    rw [div_pow, div_pow, ← add_div, hr_def, Real.sq_sqrt hab.le, div_self]
    exact ne_of_gt hab
  have hcs : ((a / r : ℝ) : ℂ) ^ 2 + ((b / r : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast hcsR
  simpa using hcs

-- The spatial rotation as a ComplexLorentzGroup element.
private noncomputable def spatialRotCLG12 (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) : ComplexLorentzGroup d where
  val := spatialRotMatrix12 d hd a b hab
  metric_preserving := spatialRotMatrix12_metric d hd a b hab
  proper := spatialRotMatrix12_det d hd a b hab

-- The action of the spatial rotation on a single vector:
-- (R·v)_0 = v_0 (time fixed)
-- (R·v)_1 = c * v_1 + s * v_2  where c = a/r, s = b/r
-- (R·v)_2 = -s * v_1 + c * v_2
-- (R·v)_μ = v_μ  for μ ≥ 3
private lemma spatial_rotation_e12_plane (hd : 2 ≤ d) (a b : ℝ) (hab : 0 < a ^ 2 + b ^ 2) :
    ∃ (R : ComplexLorentzGroup d),
      let r : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
      ∀ (v : Fin (d + 1) → ℂ),
        -- Time component fixed
        (∑ ν, R.val 0 ν * v ν) = v 0 ∧
        -- Spatial component 1: rotated
        (∑ ν, R.val ⟨1, by omega⟩ ν * v ν) =
          ((a / r : ℝ) : ℂ) * v ⟨1, by omega⟩ + ((b / r : ℝ) : ℂ) * v ⟨2, by omega⟩ ∧
        -- Spatial component 2: rotated
        (∑ ν, R.val ⟨2, by omega⟩ ν * v ν) =
          -((b / r : ℝ) : ℂ) * v ⟨1, by omega⟩ + ((a / r : ℝ) : ℂ) * v ⟨2, by omega⟩ ∧
        -- All other components fixed
        (∀ (μ : Fin (d + 1)), μ ≠ 0 → μ ≠ ⟨1, by omega⟩ → μ ≠ ⟨2, by omega⟩ →
          (∑ ν, R.val μ ν * v ν) = v μ) := by
  refine ⟨spatialRotCLG12 d hd a b hab, fun v => ?_⟩
  simp only [spatialRotCLG12]
  have hR0 := spatialRot12_row0 d hd a b hab
  have hR1 := spatialRot12_row1 d hd a b hab
  have hR2 := spatialRot12_row2 d hd a b hab
  have hRge3 := spatialRot12_row_ge3 d hd a b hab
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Time component: ∑ ν, M(0,ν) * v(ν) = v(0)
    simp_rw [hR0]; simp [ite_mul, Finset.sum_ite_eq', Finset.mem_univ]
  · -- Spatial component 1
    simp_rw [hR1]
    simp only [ite_mul, zero_mul]
    conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨1, by omega⟩)]
    simp only [↓reduceIte]
    conv_lhs => rw [← Finset.add_sum_erase _ _
      (Finset.mem_erase.mpr ⟨by intro h; exact absurd (congr_arg Fin.val h) (by norm_num),
        Finset.mem_univ _⟩ : (⟨2, by omega⟩ : Fin (d + 1)) ∈ Finset.univ.erase ⟨1, by omega⟩)]
    simp only [show (⟨2, by omega⟩ : Fin (d + 1)) ≠ ⟨1, by omega⟩ from by
      intro h; exact absurd (congr_arg Fin.val h) (by norm_num), ↓reduceIte]
    have : ∀ x ∈ (Finset.univ.erase ⟨1, by omega⟩).erase (⟨2, by omega⟩ : Fin (d + 1)),
        (if x = ⟨1, by omega⟩ then ((a / Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) * v x
         else if x = ⟨2, by omega⟩ then ((b / Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) * v x
         else (0 : ℂ)) = 0 := by
      intro x hx
      simp only [Finset.mem_erase] at hx
      rw [if_neg hx.2.1, if_neg hx.1]
    rw [Finset.sum_eq_zero this]; ring
  · -- Spatial component 2
    simp_rw [hR2]
    simp only [ite_mul, zero_mul]
    conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨1, by omega⟩)]
    simp only [↓reduceIte]
    conv_lhs => rw [← Finset.add_sum_erase _ _
      (Finset.mem_erase.mpr ⟨by intro h; exact absurd (congr_arg Fin.val h) (by norm_num),
        Finset.mem_univ _⟩ : (⟨2, by omega⟩ : Fin (d + 1)) ∈ Finset.univ.erase ⟨1, by omega⟩)]
    simp only [show (⟨2, by omega⟩ : Fin (d + 1)) ≠ ⟨1, by omega⟩ from by
      intro h; exact absurd (congr_arg Fin.val h) (by norm_num), ↓reduceIte]
    have : ∀ x ∈ (Finset.univ.erase ⟨1, by omega⟩).erase (⟨2, by omega⟩ : Fin (d + 1)),
        (if x = ⟨1, by omega⟩ then -((b / Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) * v x
         else if x = ⟨2, by omega⟩ then ((a / Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) * v x
         else (0 : ℂ)) = 0 := by
      intro x hx
      simp only [Finset.mem_erase] at hx
      rw [if_neg hx.2.1, if_neg hx.1]
    rw [Finset.sum_eq_zero this]; ring
  · -- Other components
    intro μ hμ0 hμ1 hμ2
    simp_rw [hRge3 μ hμ0 hμ1 hμ2]
    simp [ite_mul, Finset.sum_ite_eq', Finset.mem_univ]

namespace BHW

private lemma swapWitnessRealSwapped_apply_e1
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) =
      ((Equiv.swap i ⟨i.val + 1, hi⟩ k : Fin n) : ℝ) + 1 := by
  simp [swapWitnessRealSwapped, swapWitnessReal, e1, e2, e1_ne_zero, e2_ne_e1]

private lemma swapWitnessRealSwapped_apply_e2
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) =
      if Equiv.swap i ⟨i.val + 1, hi⟩ k = ⟨i.val + 1, hi⟩ then 1 else 0 := by
  simp [swapWitnessRealSwapped, swapWitnessReal, e1, e2, e2_ne_zero, e2_ne_e1]

private lemma swapWitnessRealSwapped_diff_e1_other_pos
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n)
    (k : Fin n) (hk_i : k ≠ i) (hk_ip1 : k ≠ ⟨i.val + 1, hi⟩) :
    0 < consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e1 hd) := by
  let ip1 : Fin n := ⟨i.val + 1, hi⟩
  have hk_ip1' : k ≠ ip1 := by
    simpa [ip1] using hk_ip1
  have hswap_k : Equiv.swap i ip1 k = k :=
    Equiv.swap_apply_of_ne_of_ne hk_i hk_ip1'
  by_cases hk0 : (k : ℕ) = 0
  · have hswap_k0 : ((Equiv.swap i ip1 k : Fin n) : ℕ) = 0 := by
      simpa [hswap_k] using hk0
    have hdiff :
        consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e1 hd) =
          ((Equiv.swap i ip1 k : Fin n) : ℝ) + 1 := by
      simp [consecutiveDiff, swapWitnessRealSwapped, swapWitnessReal, e1, ip1, hk0]
    have hswap_k0R : ((Equiv.swap i ip1 k : Fin n) : ℝ) = 0 := by
      exact_mod_cast hswap_k0
    linarith [hdiff, hswap_k0R]
  · have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk0
    let km1 : Fin n := ⟨k.val - 1, by omega⟩
    have hkm1_ne_i : km1 ≠ i := by
      intro h
      have hk_eq_ip1 : k = ip1 := by
        apply Fin.ext
        have hval : km1.val = i.val := congrArg Fin.val h
        dsimp [km1] at hval
        dsimp [ip1]
        omega
      exact hk_ip1' hk_eq_ip1
    by_cases hkm1_ip1 : km1 = ip1
    · have hswap_km1 : Equiv.swap i ip1 km1 = i := by
        simpa [hkm1_ip1] using (Equiv.swap_apply_right i ip1)
      have hk_val : k.val = i.val + 2 := by
        have hval : km1.val = ip1.val := congrArg Fin.val hkm1_ip1
        dsimp [km1, ip1] at hval
        omega
      have hk_eq : Equiv.swap i ⟨i.val + 1, hi⟩ k = k := by
        simpa [ip1] using hswap_k
      have hkm1_eq :
          Equiv.swap i ⟨i.val + 1, hi⟩ (⟨k.val - 1, by omega⟩ : Fin n) = i := by
        simpa [ip1] using hswap_km1
      have hdiff :
          consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e1 hd) =
            ((k : ℝ) + 1) - ((i : ℝ) + 1) := by
        simp [consecutiveDiff, swapWitnessRealSwapped_apply_e1, hk0, hk_eq, hkm1_eq]
      have hki : (i : ℝ) < (k : ℝ) := by
        exact_mod_cast (by omega : i.val < k.val)
      linarith [hdiff, hki]
    · have hswap_km1 : Equiv.swap i ip1 km1 = km1 :=
        Equiv.swap_apply_of_ne_of_ne hkm1_ne_i hkm1_ip1
      have hcast : (km1 : ℝ) + 1 = (k : ℝ) := by
        have hnat : km1.val + 1 = k.val := by
          dsimp [km1]
          exact Nat.sub_add_cancel hk1
        exact_mod_cast hnat
      have hk_eq : Equiv.swap i ⟨i.val + 1, hi⟩ k = k := by
        simpa [ip1] using hswap_k
      have hkm1_eq :
          Equiv.swap i ⟨i.val + 1, hi⟩ (⟨k.val - 1, by omega⟩ : Fin n) = km1 := by
        simpa [ip1] using hswap_km1
      have hdiff :
          consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e1 hd) =
            ((k : ℝ) + 1) - ((km1 : ℝ) + 1) := by
        simp [consecutiveDiff, swapWitnessRealSwapped_apply_e1, hk0, hk_eq, hkm1_eq]
      linarith [hdiff, hcast]

private lemma swapWitnessRealSwapped_diff_e2_other
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n)
    (k : Fin n) (hk_i : k ≠ i) (hk_ip1 : k ≠ ⟨i.val + 1, hi⟩) :
    consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e2 hd) = 0 := by
  let ip1 : Fin n := ⟨i.val + 1, hi⟩
  have hk_ip1' : k ≠ ip1 := by
    simpa [ip1] using hk_ip1
  have hswap_k : Equiv.swap i ip1 k = k :=
    Equiv.swap_apply_of_ne_of_ne hk_i hk_ip1'
  by_cases hk0 : (k : ℕ) = 0
  · have hswap_k_ne_ip1 : Equiv.swap i ip1 k ≠ ip1 := by
      simpa [hswap_k] using hk_ip1'
    have hswap_k_ne_ip1' : Equiv.swap i ip1 k ≠ ⟨i.val + 1, hi⟩ := by
      simpa [ip1] using hswap_k_ne_ip1
    simpa [consecutiveDiff, hk0, swapWitnessRealSwapped_apply_e2, hswap_k_ne_ip1']
  · have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk0
    let km1 : Fin n := ⟨k.val - 1, by omega⟩
    have hkm1_ne_i : km1 ≠ i := by
      intro h
      have hk_eq_ip1 : k = ip1 := by
        apply Fin.ext
        have hval : km1.val = i.val := congrArg Fin.val h
        dsimp [km1] at hval
        dsimp [ip1]
        omega
      exact hk_ip1' hk_eq_ip1
    by_cases hkm1_ip1 : km1 = ip1
    · have hswap_km1 : Equiv.swap i ip1 km1 = i := by
        simpa [hkm1_ip1] using (Equiv.swap_apply_right i ip1)
      have hi_ne_ip1 : i ≠ ip1 := by
        intro h
        have hval : i.val = ip1.val := congrArg Fin.val h
        dsimp [ip1] at hval
        omega
      have hfalse1 : Equiv.swap i ip1 k ≠ ip1 := by
        simpa [hswap_k] using hk_ip1'
      have hfalse2 : Equiv.swap i ip1 km1 ≠ ip1 := by
        simpa [hswap_km1] using hi_ne_ip1
      have hfalse1' : Equiv.swap i ip1 k ≠ ⟨i.val + 1, hi⟩ := by
        simpa [ip1] using hfalse1
      have hfalse2' : Equiv.swap i ip1 km1 ≠ ⟨i.val + 1, hi⟩ := by
        simpa [ip1] using hfalse2
      have hdiff :
          consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e2 hd) =
            ((if Equiv.swap i ip1 k = ip1 then 1 else 0) -
              if Equiv.swap i ip1 km1 = ip1 then 1 else 0) := by
        simpa [ip1, km1] using
          (by simp [consecutiveDiff, hk0, swapWitnessRealSwapped_apply_e2])
      rw [if_neg hfalse1, if_neg hfalse2] at hdiff
      simpa using hdiff
    · have hswap_km1 : Equiv.swap i ip1 km1 = km1 :=
        Equiv.swap_apply_of_ne_of_ne hkm1_ne_i hkm1_ip1
      have hfalse1 : Equiv.swap i ip1 k ≠ ip1 := by
        simpa [hswap_k] using hk_ip1'
      have hfalse2 : Equiv.swap i ip1 km1 ≠ ip1 := by
        simpa [hswap_km1] using hkm1_ip1
      have hfalse1' : Equiv.swap i ip1 k ≠ ⟨i.val + 1, hi⟩ := by
        simpa [ip1] using hfalse1
      have hfalse2' : Equiv.swap i ip1 km1 ≠ ⟨i.val + 1, hi⟩ := by
        simpa [ip1] using hfalse2
      have hdiff :
          consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e2 hd) =
            ((if Equiv.swap i ip1 k = ip1 then 1 else 0) -
              if Equiv.swap i ip1 km1 = ip1 then 1 else 0) := by
        simpa [ip1, km1] using
          (by simp [consecutiveDiff, hk0, swapWitnessRealSwapped_apply_e2])
      rw [if_neg hfalse1, if_neg hfalse2] at hdiff
      simpa using hdiff

private def swapWitnessRealSwappedRot
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ =>
    if μ = 0 then swapWitnessRealSwapped (d := d) (n := n) hd i hi k 0
    else if μ = e1 hd then
      (3 / 5 : ℝ) * swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) +
      (-4 / 5 : ℝ) * swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd)
    else if μ = e2 hd then
      (4 / 5 : ℝ) * swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) +
      (3 / 5 : ℝ) * swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd)
    else swapWitnessRealSwapped (d := d) (n := n) hd i hi k μ

private lemma swapWitnessRealSwappedRot_diff_time
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    consecutiveDiff (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi) k 0 = 0 := by
  simpa [consecutiveDiff, swapWitnessRealSwappedRot] using
    (swapWitnessReal_swapped_time_zero (d := d) (n := n) hd i hi k)

private lemma swapWitnessRealSwappedRot_diff_e1
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    consecutiveDiff (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi) k (e1 hd) =
      (3 / 5 : ℝ) * consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e1 hd) +
      (-4 / 5 : ℝ) * consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e2 hd) := by
  by_cases hk0 : (k : ℕ) = 0
  · simp [consecutiveDiff, swapWitnessRealSwappedRot, e1, hk0, e1_ne_zero, e2_ne_zero, e2_ne_e1]
  · have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk0
    let km1 : Fin n := ⟨k.val - 1, by omega⟩
    simp [consecutiveDiff, swapWitnessRealSwappedRot, e1, hk0, km1, e1_ne_zero, e2_ne_zero,
      e2_ne_e1]
    ring

private lemma swapWitnessRealSwappedRot_mem_forwardJostSet
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    swapWitnessRealSwappedRot (d := d) (n := n) hd i hi ∈
      ForwardJostSet d n (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hd)) := by
  intro k
  have htime : consecutiveDiff (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi) k 0 = 0 :=
    swapWitnessRealSwappedRot_diff_time (d := d) (n := n) hd i hi k
  have hspat :
      0 < consecutiveDiff (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi) k (e1 hd) := by
    by_cases hk_i : k = i
    · subst k
      rw [swapWitnessRealSwappedRot_diff_e1 (d := d) (n := n) hd i hi i,
        swapWitnessRealSwapped_diff_e1_at_i (d := d) (n := n) hd i hi,
        swapWitnessRealSwapped_diff_e2_at_i (d := d) (n := n) hd i hi]
      norm_num
    · by_cases hk_ip1 : k = ⟨i.val + 1, hi⟩
      · subst k
        rw [swapWitnessRealSwappedRot_diff_e1 (d := d) (n := n) hd i hi ⟨i.val + 1, hi⟩,
          swapWitnessRealSwapped_diff_e1_at_ip1 (d := d) (n := n) hd i hi,
          swapWitnessRealSwapped_diff_e2_at_ip1 (d := d) (n := n) hd i hi]
        norm_num
      · have hother_e1 :
          0 < consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e1 hd) :=
          swapWitnessRealSwapped_diff_e1_other_pos (d := d) (n := n) hd i hi k hk_i hk_ip1
        have hother_e2 :
            consecutiveDiff (swapWitnessRealSwapped (d := d) (n := n) hd i hi) k (e2 hd) = 0 :=
          swapWitnessRealSwapped_diff_e2_other (d := d) (n := n) hd i hi k hk_i hk_ip1
        rw [swapWitnessRealSwappedRot_diff_e1 (d := d) (n := n) hd i hi k, hother_e2]
        have h35 : (0 : ℝ) < 3 / 5 := by norm_num
        nlinarith
  change |consecutiveDiff (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi) k 0| <
      consecutiveDiff (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi) k (e1 hd)
  rw [htime]
  simpa using hspat

private lemma realEmbed_swapWitnessRealSwapped_eq_action_rot
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (R : ComplexLorentzGroup d),
      realEmbed (swapWitnessRealSwapped (d := d) (n := n) hd i hi) =
        complexLorentzAction R (realEmbed (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi)) := by
  have hab : (0 : ℝ) < (3 : ℝ) ^ 2 + (4 : ℝ) ^ 2 := by norm_num
  have hsqrt : Real.sqrt ((3 : ℝ) ^ 2 + (4 : ℝ) ^ 2) = 5 := by
    rw [show ((3 : ℝ) ^ 2 + (4 : ℝ) ^ 2) = (5 : ℝ) ^ 2 by norm_num]
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ 5 by norm_num)] using
      (Real.sqrt_sq_eq_abs (5 : ℝ))
  rcases spatial_rotation_e12_plane (d := d) hd (3 : ℝ) (4 : ℝ) hab with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  ext k μ
  rcases hR (fun ν => (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν : ℂ)) with
    ⟨h0, h1, h2, hrest⟩
  by_cases hμ0 : μ = 0
  · subst hμ0
    have h0' :
        (∑ ν, R.val 0 ν * ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν)) =
          (swapWitnessRealSwapped (d := d) (n := n) hd i hi k 0 : ℂ) := by
      simpa [swapWitnessRealSwappedRot] using h0
    simpa [complexLorentzAction, realEmbed] using h0'.symm
  · by_cases hμ1 : μ = e1 hd
    · subst hμ1
      have h1' :
          (∑ ν, R.val (e1 hd) ν * ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν)) =
            ((3 / 5 : ℝ) : ℂ) *
              ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e1 hd)) +
            ((4 / 5 : ℝ) : ℂ) *
              ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e2 hd)) := by
        simpa [e1, e2, hsqrt] using h1
      have hcoord1 :
          (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e1 hd) : ℂ) =
            ((3 / 5 : ℝ) : ℂ) *
              (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) : ℂ) +
            ((-4 / 5 : ℝ) : ℂ) *
              (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) : ℂ) := by
        simp [swapWitnessRealSwappedRot, e1, e2, e1_ne_zero, e2_ne_zero, e2_ne_e1]
      have hcoord2 :
          (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e2 hd) : ℂ) =
            ((4 / 5 : ℝ) : ℂ) *
              (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) : ℂ) +
            ((3 / 5 : ℝ) : ℂ) *
              (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) : ℂ) := by
        simp [swapWitnessRealSwappedRot, e1, e2, e1_ne_zero, e2_ne_zero, e2_ne_e1]
      have hcalc :
          ((3 / 5 : ℝ) : ℂ) *
              (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e1 hd) : ℂ) +
            ((4 / 5 : ℝ) : ℂ) *
              (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e2 hd) : ℂ) =
          (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) : ℂ) := by
        rw [hcoord1, hcoord2]
        set A : ℂ := (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) : ℂ)
        set B : ℂ := (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) : ℂ)
        calc
          ((3 / 5 : ℝ) : ℂ) * (((3 / 5 : ℝ) : ℂ) * A + ((-4 / 5 : ℝ) : ℂ) * B) +
              ((4 / 5 : ℝ) : ℂ) * (((4 / 5 : ℝ) : ℂ) * A + ((3 / 5 : ℝ) : ℂ) * B)
              = ((3 / 5 : ℝ) : ℂ) * ((-4 / 5 : ℝ) : ℂ) * B +
                  ((3 / 5 : ℝ) : ℂ) * B * ((4 / 5 : ℝ) : ℂ) +
                    ((((3 / 5 : ℝ) : ℂ) ^ 2 + (((4 / 5 : ℝ) : ℂ) ^ 2)) * A) := by
                      ring
          _ = A := by
                simp [mul_assoc, mul_left_comm, mul_comm]
                ring_nf
      have hsum :
          (∑ ν, R.val (e1 hd) ν * ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν)) =
            (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) : ℂ) :=
        h1'.trans hcalc
      change (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) : ℂ) =
          ∑ ν, R.val (e1 hd) ν * ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν)
      exact hsum.symm
    · by_cases hμ2 : μ = e2 hd
      · subst hμ2
        have h2' :
            (∑ ν, R.val (e2 hd) ν * ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν)) =
              -((4 / 5 : ℝ) : ℂ) *
                ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e1 hd)) +
              ((3 / 5 : ℝ) : ℂ) *
                ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e2 hd)) := by
          simpa [e1, e2, hsqrt] using h2
        have hcoord1 :
            (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e1 hd) : ℂ) =
              ((3 / 5 : ℝ) : ℂ) *
                (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) : ℂ) +
              ((-4 / 5 : ℝ) : ℂ) *
                (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) : ℂ) := by
          simp [swapWitnessRealSwappedRot, e1, e2, e1_ne_zero, e2_ne_zero, e2_ne_e1]
        have hcoord2 :
            (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e2 hd) : ℂ) =
              ((4 / 5 : ℝ) : ℂ) *
                (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) : ℂ) +
              ((3 / 5 : ℝ) : ℂ) *
                (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) : ℂ) := by
          simp [swapWitnessRealSwappedRot, e1, e2, e1_ne_zero, e2_ne_zero, e2_ne_e1]
        have hcalc :
            -((4 / 5 : ℝ) : ℂ) *
                (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e1 hd) : ℂ) +
              ((3 / 5 : ℝ) : ℂ) *
                (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k (e2 hd) : ℂ) =
            (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) : ℂ) := by
          rw [hcoord1, hcoord2]
          set A : ℂ := (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e1 hd) : ℂ)
          set B : ℂ := (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) : ℂ)
          calc
            -((4 / 5 : ℝ) : ℂ) *
                (((3 / 5 : ℝ) : ℂ) * A + ((-4 / 5 : ℝ) : ℂ) * B) +
              ((3 / 5 : ℝ) : ℂ) *
                (((4 / 5 : ℝ) : ℂ) * A + ((3 / 5 : ℝ) : ℂ) * B)
                = (-(((4 / 5 : ℝ) : ℂ) * ((-4 / 5 : ℝ) : ℂ)) + (((3 / 5 : ℝ) : ℂ) ^ 2)) * B := by
                    ring
            _ = B := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
                  ring_nf
        have hsum :
            (∑ ν, R.val (e2 hd) ν * ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν)) =
              (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) : ℂ) :=
          h2'.trans hcalc
        change (swapWitnessRealSwapped (d := d) (n := n) hd i hi k (e2 hd) : ℂ) =
            ∑ ν, R.val (e2 hd) ν * ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν)
        exact hsum.symm
      · have hμ0' : μ ≠ 0 := by simpa using hμ0
        have hμ1' : μ ≠ ⟨1, by omega⟩ := by
          intro h
          exact hμ1 (by simpa [e1] using h)
        have hμ2' : μ ≠ ⟨2, by omega⟩ := by
          intro h
          exact hμ2 (by simpa [e2] using h)
        have hfix := hrest μ hμ0' hμ1' hμ2'
        have hcoord :
            (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k μ : ℂ) =
              (swapWitnessRealSwapped (d := d) (n := n) hd i hi k μ : ℂ) := by
          simp [swapWitnessRealSwappedRot, hμ0, hμ1, hμ2]
        have hsum :
            (∑ ν, R.val μ ν * ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν)) =
              (swapWitnessRealSwapped (d := d) (n := n) hd i hi k μ : ℂ) :=
          hfix.trans hcoord
        change (swapWitnessRealSwapped (d := d) (n := n) hd i hi k μ : ℂ) =
            ∑ ν, R.val μ ν * ↑(swapWitnessRealSwappedRot (d := d) (n := n) hd i hi k ν)
        exact hsum.symm

private lemma swapWitnessRealSwapped_mem_extendedTube
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    realEmbed (swapWitnessRealSwapped (d := d) (n := n) hd i hi) ∈ ExtendedTube d n := by
  have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hd)
  have hyFT :
      swapWitnessRealSwappedRot (d := d) (n := n) hd i hi ∈ ForwardJostSet d n hd1 :=
    swapWitnessRealSwappedRot_mem_forwardJostSet (d := d) (n := n) hd i hi
  have hyET :
      realEmbed (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi) ∈ ExtendedTube d n :=
    forwardJostSet_subset_extendedTube hd1 _ hyFT
  rcases realEmbed_swapWitnessRealSwapped_eq_action_rot (d := d) (n := n) hd i hi with ⟨R, hR⟩
  rcases Set.mem_iUnion.mp hyET with ⟨Λ, w, hw, hrepr⟩
  refine Set.mem_iUnion.mpr ⟨R * Λ, w, hw, ?_⟩
  calc
    realEmbed (swapWitnessRealSwapped (d := d) (n := n) hd i hi)
        = complexLorentzAction R (realEmbed (swapWitnessRealSwappedRot (d := d) (n := n) hd i hi)) := hR
    _ = complexLorentzAction R (complexLorentzAction Λ w) := by simpa [hrepr]
    _ = complexLorentzAction (R * Λ) w := by
      rw [← complexLorentzAction_mul]

theorem adjacent_overlap_witness_exists
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    ∃ x : Fin n → Fin (d + 1) → ℂ,
      x ∈ ExtendedTube d n ∧
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n := by
  refine ⟨realEmbed (swapWitnessRealSwapped (d := d) (n := n) hd i hi), ?_, ?_⟩
  · exact swapWitnessRealSwapped_mem_extendedTube (d := d) (n := n) hd i hi
  · have hswap :
        (fun k =>
          realEmbed (swapWitnessRealSwapped (d := d) (n := n) hd i hi)
            (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
          realEmbed (swapWitnessReal (d := d) (n := n) hd i hi) := by
      ext k μ
      simp [realEmbed, swapWitnessRealSwapped]
    simpa [hswap] using swapWitnessReal_mem_extendedTube (d := d) (n := n) hd i hi

/-- Real adjacent-overlap witness with explicit spacelike condition at `(i,i+1)`.
    This strengthens `adjacent_overlap_witness_exists` by exposing a real witness
    usable with locality hypotheses of the form `hF_local`. -/
theorem adjacent_overlap_real_spacelike_witness_exists
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
    ∃ x : Fin n → Fin (d + 1) → ℝ,
      (∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0) ∧
      realEmbed x ∈ ExtendedTube d n ∧
      realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n := by
  refine ⟨swapWitnessReal (d := d) (n := n) hd i hi, ?_⟩
  refine ⟨?_, swapWitnessReal_mem_extendedTube (d := d) (n := n) hd i hi, ?_⟩
  · have hd1 : 1 ≤ d :=
      Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hd)
    have hxFJ :
        swapWitnessReal (d := d) (n := n) hd i hi ∈
          ForwardJostSet d n hd1 :=
      swapWitnessReal_mem_forwardJostSet (d := d) (n := n) hd i hi
    have hsp_ip1 :
        IsSpacelike d
          (consecutiveDiff (swapWitnessReal (d := d) (n := n) hd i hi) ⟨i.val + 1, hi⟩) :=
      forwardJostSet_consec_spacelike (d := d) (n := n) hd1 hxFJ ⟨i.val + 1, hi⟩
    have hip1_ne0 : ¬ ((⟨i.val + 1, hi⟩ : Fin n).val = 0) := Nat.succ_ne_zero _
    have hprev : (⟨(⟨i.val + 1, hi⟩ : Fin n).val - 1, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simp
    simpa [IsSpacelike, consecutiveDiff, hip1_ne0, hprev] using hsp_ip1
  · simpa [swapWitnessRealSwapped] using
      (swapWitnessRealSwapped_mem_extendedTube (d := d) (n := n) hd i hi)

/-! ## `d = 1` adjacent-overlap witness -/

private def cdiff2 {n : ℕ} (z : Fin n → Fin 2 → ℂ) (k : Fin n) : Fin 2 → ℂ :=
  fun μ => z k μ - ((if h : k.val = 0 then (0 : Fin 2 → ℂ) else z ⟨k.val - 1, by omega⟩) μ)

private def swapIdx2 {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) : Equiv.Perm (Fin n) :=
  Equiv.swap i ⟨i.val + 1, hi⟩

private def d1WitnessX {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    Fin n → Fin 2 → ℂ :=
  let σ := swapIdx2 i hi
  fun k μ =>
    if μ = 0 then (2 : ℂ) * Complex.I * ((k : ℂ) + 1)
    else (-2 : ℂ) * (((σ k : Fin n) : ℂ) + 1)

private lemma d1WitnessX_cdiff_time {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    cdiff2 (d1WitnessX i hi) k 0 = (2 : ℂ) * Complex.I := by
  by_cases hk0 : k.val = 0
  · simp [cdiff2, d1WitnessX, hk0, swapIdx2]
  · simp [cdiff2, d1WitnessX, hk0, swapIdx2]
    have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk0
    have hnat : k.val - 1 + 1 = k.val := Nat.sub_add_cancel hk1
    have hcast : ((↑(k.val - 1) : ℂ) + 1) = (k : ℂ) := by
      exact_mod_cast hnat
    rw [hcast]
    ring

private lemma d1WitnessX_cdiff_space_im {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    (cdiff2 (d1WitnessX i hi) k 1).im = 0 := by
  by_cases hk0 : k.val = 0
  · simp [cdiff2, d1WitnessX, hk0, swapIdx2]
  · simp [cdiff2, d1WitnessX, hk0, swapIdx2]

private lemma d1WitnessX_mem_forwardTube {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    d1WitnessX i hi ∈ BHWCore.ForwardTube 1 n := by
  intro k
  simpa [BHWCore.ForwardTube, cdiff2] using
    (show InOpenForwardCone 1 (fun μ => (cdiff2 (d1WitnessX i hi) k μ).im) from by
      constructor
      · change (cdiff2 (d1WitnessX i hi) k 0).im > 0
        rw [d1WitnessX_cdiff_time i hi k]
        norm_num
      · rw [Fin.sum_univ_two]
        change minkowskiSignature 1 0 * ((cdiff2 (d1WitnessX i hi) k 0).im) ^ 2 +
            minkowskiSignature 1 1 * ((cdiff2 (d1WitnessX i hi) k 1).im) ^ 2 < 0
        rw [d1WitnessX_cdiff_time i hi k, d1WitnessX_cdiff_space_im i hi k]
        norm_num [minkowskiSignature]
    )

private def swappedX {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) : Fin n → Fin 2 → ℂ :=
  fun k => d1WitnessX i hi (swapIdx2 i hi k)

private lemma swappedX_space_value {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    swappedX i hi k 1 = (-2 : ℂ) * ((k : ℂ) + 1) := by
  simp [swappedX, d1WitnessX, swapIdx2]

private lemma swappedX_cdiff_space {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    cdiff2 (swappedX i hi) k 1 = (-2 : ℂ) := by
  by_cases hk0 : k.val = 0
  · simp [cdiff2, swappedX_space_value, hk0]
  · have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk0
    have hnat : k.val - 1 + 1 = k.val := Nat.sub_add_cancel hk1
    have hcast : ((↑(k.val - 1) : ℂ) + 1) = (k : ℂ) := by
      exact_mod_cast hnat
    simp [cdiff2, swappedX_space_value, hk0]
    rw [hcast]
    ring

private lemma swappedX_cdiff_time_re {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) (k : Fin n) :
    (cdiff2 (swappedX i hi) k 0).re = 0 := by
  by_cases hk0 : k.val = 0
  · simp [cdiff2, swappedX, d1WitnessX, hk0, swapIdx2]
  · simp [cdiff2, swappedX, d1WitnessX, hk0, swapIdx2]

private def wickPlus1 : ComplexLorentzGroup 1 where
  val := fun μ ν =>
    if μ = 0 ∧ ν = (1 : Fin 2) then Complex.I
    else if μ = (1 : Fin 2) ∧ ν = 0 then Complex.I
    else 0
  metric_preserving := by
    intro μ ν
    fin_cases μ <;> fin_cases ν <;>
      simp [minkowskiSignature, Complex.I_mul_I]
  proper := by
    rw [Matrix.det_fin_two]
    simp

private def liftByWick {n : ℕ} (z : Fin n → Fin 2 → ℂ) : Fin n → Fin 2 → ℂ :=
  fun k μ => if μ = 0 then -Complex.I * z k 1 else -Complex.I * z k 0

private lemma liftByWick_cdiff_time {n : ℕ} (z : Fin n → Fin 2 → ℂ) (k : Fin n) :
    cdiff2 (liftByWick z) k 0 = -Complex.I * cdiff2 z k 1 := by
  by_cases hk0 : k.val = 0
  · simp [cdiff2, liftByWick, hk0]
  · simp [cdiff2, liftByWick, hk0]
    ring

private lemma liftByWick_cdiff_space {n : ℕ} (z : Fin n → Fin 2 → ℂ) (k : Fin n) :
    cdiff2 (liftByWick z) k 1 = -Complex.I * cdiff2 z k 0 := by
  by_cases hk0 : k.val = 0
  · simp [cdiff2, liftByWick, hk0]
  · simp [cdiff2, liftByWick, hk0]
    ring

private lemma wickPlus1_action_liftByWick {n : ℕ} (z : Fin n → Fin 2 → ℂ) :
    BHWCore.complexLorentzAction wickPlus1 (liftByWick z) = z := by
  ext k μ
  fin_cases μ
  · simp [BHWCore.complexLorentzAction, wickPlus1, liftByWick, Fin.sum_univ_two]
    rw [← mul_assoc, Complex.I_mul_I]
    simp
  · simp [BHWCore.complexLorentzAction, wickPlus1, liftByWick, Fin.sum_univ_two]
    rw [← mul_assoc, Complex.I_mul_I]
    simp

private lemma liftByWick_swapped_mem_forwardTube {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    liftByWick (swappedX i hi) ∈ BHWCore.ForwardTube 1 n := by
  intro k
  simpa [BHWCore.ForwardTube, cdiff2] using
    (show InOpenForwardCone 1
        (fun μ => (cdiff2 (liftByWick (swappedX i hi)) k μ).im) from by
      constructor
      · change (cdiff2 (liftByWick (swappedX i hi)) k 0).im > 0
        rw [liftByWick_cdiff_time (swappedX i hi) k, swappedX_cdiff_space i hi k]
        norm_num
      · rw [Fin.sum_univ_two]
        change minkowskiSignature 1 0 *
              ((cdiff2 (liftByWick (swappedX i hi)) k 0).im) ^ 2 +
            minkowskiSignature 1 1 *
              ((cdiff2 (liftByWick (swappedX i hi)) k 1).im) ^ 2 < 0
        rw [liftByWick_cdiff_time (swappedX i hi) k, swappedX_cdiff_space i hi k]
        have hspaceIm : (cdiff2 (liftByWick (swappedX i hi)) k 1).im = 0 := by
          rw [liftByWick_cdiff_space (swappedX i hi) k]
          have him :
              ((-Complex.I) * cdiff2 (swappedX i hi) k 0).im = -((cdiff2 (swappedX i hi) k 0).re) := by
            simp [Complex.mul_im]
          rw [him, swappedX_cdiff_time_re i hi k]
          simp
        rw [hspaceIm]
        norm_num [minkowskiSignature]
    )

theorem adjacent_overlap_witness_exists_d1 {n : ℕ}
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ x : Fin n → Fin 2 → ℂ,
      x ∈ BHWCore.ExtendedTube 1 n ∧
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ BHWCore.ExtendedTube 1 n := by
  refine ⟨d1WitnessX i hi, ?_, ?_⟩
  · exact BHWCore.forwardTube_subset_extendedTube (d1WitnessX_mem_forwardTube i hi)
  ·
    let z : Fin n → Fin 2 → ℂ := swappedX i hi
    refine Set.mem_iUnion.mpr ?_
    refine ⟨wickPlus1, liftByWick z, liftByWick_swapped_mem_forwardTube i hi, ?_⟩
    simpa [z] using (wickPlus1_action_liftByWick z).symm

end BHW
