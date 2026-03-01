import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

private def witness_i0_pairA : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 2 * I
  | 0, 1 => -3
  | 1, 0 => 6 * I
  | 1, 1 => 1
  | 2, 0 => 11 * I
  | 2, 1 => 3

private def tau01 : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1
private def sigma120 : Equiv.Perm (Fin 3) :=
  (Equiv.swap (0 : Fin 3) 1) * (Equiv.swap (1 : Fin 3) 2)
private def sigma210 : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 2

private theorem witness_i0_pairA_in_FT : witness_i0_pairA ∈ ForwardTube 1 3 := by
  intro k
  fin_cases k
  · simp
    exact ⟨by simp [witness_i0_pairA],
      by rw [Fin.sum_univ_two]; simp [witness_i0_pairA, minkowskiSignature]⟩
  · simp
    refine ⟨?_, ?_⟩
    · norm_num [witness_i0_pairA]
    · rw [Fin.sum_univ_two]
      norm_num [witness_i0_pairA, minkowskiSignature]
  · simp
    refine ⟨?_, ?_⟩
    · norm_num [witness_i0_pairA]
    · rw [Fin.sum_univ_two]
      norm_num [witness_i0_pairA, minkowskiSignature]

private def boostTauMatrix_i0_pairA : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 3/5
             else if i = 0 ∧ j = 1 then -4*I/5
             else if i = 1 ∧ j = 0 then -4*I/5
             else 3/5

private def boostTau_i0_pairA : ComplexLorentzGroup 1 where
  val := boostTauMatrix_i0_pairA
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boostTauMatrix_i0_pairA, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boostTauMatrix_i0_pairA]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def boost120Matrix_i0_pairA : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 5/13
             else if i = 0 ∧ j = 1 then -12*I/13
             else if i = 1 ∧ j = 0 then -12*I/13
             else 5/13

private def boost120_i0_pairA : ComplexLorentzGroup 1 where
  val := boost120Matrix_i0_pairA
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boost120Matrix_i0_pairA, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boost120Matrix_i0_pairA]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def boost210Matrix_i0_pairA : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 7/25
             else if i = 0 ∧ j = 1 then -24*I/25
             else if i = 1 ∧ j = 0 then -24*I/25
             else 7/25

private def boost210_i0_pairA : ComplexLorentzGroup 1 where
  val := boost210Matrix_i0_pairA
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boost210Matrix_i0_pairA, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boost210Matrix_i0_pairA]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def tauPermWitness_i0_pairA : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 6 * I
  | 0, 1 => 1
  | 1, 0 => 2 * I
  | 1, 1 => -3
  | 2, 0 => 11 * I
  | 2, 1 => 3

private def sigma120PermWitness_i0_pairA : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 6 * I
  | 0, 1 => 1
  | 1, 0 => 11 * I
  | 1, 1 => 3
  | 2, 0 => 2 * I
  | 2, 1 => -3

private def sigma210PermWitness_i0_pairA : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 11 * I
  | 0, 1 => 3
  | 1, 0 => 6 * I
  | 1, 1 => 1
  | 2, 0 => 2 * I
  | 2, 1 => -3

private lemma tauPermWitness_i0_pairA_eq :
    tauPermWitness_i0_pairA = permAct (d := 1) tau01 witness_i0_pairA := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [tauPermWitness_i0_pairA, tau01, witness_i0_pairA, permAct, Equiv.swap_apply_def]

private lemma sigma120PermWitness_i0_pairA_eq :
    sigma120PermWitness_i0_pairA = permAct (d := 1) sigma120 witness_i0_pairA := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [sigma120PermWitness_i0_pairA, sigma120, witness_i0_pairA, permAct,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

private lemma sigma210PermWitness_i0_pairA_eq :
    sigma210PermWitness_i0_pairA = permAct (d := 1) sigma210 witness_i0_pairA := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [sigma210PermWitness_i0_pairA, sigma210, witness_i0_pairA, permAct, Equiv.swap_apply_def]

private theorem boostTau_tauPerm_i0_pairA_in_FT :
    complexLorentzAction boostTau_i0_pairA tauPermWitness_i0_pairA ∈ ForwardTube 1 3 := by
  have hval : boostTau_i0_pairA.val = boostTauMatrix_i0_pairA := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i0_pairA, boostTauMatrix_i0_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i0_pairA, boostTauMatrix_i0_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i0_pairA, boostTauMatrix_i0_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i0_pairA, boostTauMatrix_i0_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i0_pairA, boostTauMatrix_i0_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i0_pairA, boostTauMatrix_i0_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem boost120_sigma120Perm_i0_pairA_in_FT :
    complexLorentzAction boost120_i0_pairA sigma120PermWitness_i0_pairA ∈ ForwardTube 1 3 := by
  have hval : boost120_i0_pairA.val = boost120Matrix_i0_pairA := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma120PermWitness_i0_pairA, boost120Matrix_i0_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma120PermWitness_i0_pairA, boost120Matrix_i0_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma120PermWitness_i0_pairA, boost120Matrix_i0_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma120PermWitness_i0_pairA, boost120Matrix_i0_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma120PermWitness_i0_pairA, boost120Matrix_i0_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma120PermWitness_i0_pairA, boost120Matrix_i0_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem boost210_sigma210Perm_i0_pairA_in_FT :
    complexLorentzAction boost210_i0_pairA sigma210PermWitness_i0_pairA ∈ ForwardTube 1 3 := by
  have hval : boost210_i0_pairA.val = boost210Matrix_i0_pairA := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma210PermWitness_i0_pairA, boost210Matrix_i0_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma210PermWitness_i0_pairA, boost210Matrix_i0_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma210PermWitness_i0_pairA, boost210Matrix_i0_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma210PermWitness_i0_pairA, boost210Matrix_i0_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma210PermWitness_i0_pairA, boost210Matrix_i0_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma210PermWitness_i0_pairA, boost210Matrix_i0_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem tauPermWitness_i0_pairA_in_ET :
    tauPermWitness_i0_pairA ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boostTau_i0_pairA⁻¹, complexLorentzAction boostTau_i0_pairA tauPermWitness_i0_pairA,
    boostTau_tauPerm_i0_pairA_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

private theorem sigma120PermWitness_i0_pairA_in_ET :
    sigma120PermWitness_i0_pairA ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boost120_i0_pairA⁻¹, complexLorentzAction boost120_i0_pairA sigma120PermWitness_i0_pairA,
    boost120_sigma120Perm_i0_pairA_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

private theorem sigma210PermWitness_i0_pairA_in_ET :
    sigma210PermWitness_i0_pairA ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boost210_i0_pairA⁻¹, complexLorentzAction boost210_i0_pairA sigma210PermWitness_i0_pairA,
    boost210_sigma210Perm_i0_pairA_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

/-- Constructive `d=1, n=3` witness for `i=0` (`τ = (01)`) covering two
nontrivial `σ` at once:
`σ = (1,2,0)` and `σ = (2,1,0)`. -/
theorem d1_n3_forward_triple_i0_pairA :
    witness_i0_pairA ∈ ForwardTube 1 3 ∧
    permAct (d := 1) tau01 witness_i0_pairA ∈ ExtendedTube 1 3 ∧
    permAct (d := 1) sigma120 witness_i0_pairA ∈ ExtendedTube 1 3 ∧
    permAct (d := 1) sigma210 witness_i0_pairA ∈ ExtendedTube 1 3 := by
  refine ⟨witness_i0_pairA_in_FT, ?_, ?_, ?_⟩
  · simpa [tauPermWitness_i0_pairA_eq] using tauPermWitness_i0_pairA_in_ET
  · simpa [sigma120PermWitness_i0_pairA_eq] using sigma120PermWitness_i0_pairA_in_ET
  · simpa [sigma210PermWitness_i0_pairA_eq] using sigma210PermWitness_i0_pairA_in_ET

theorem d1_n3_forward_triple_nonempty_i0_pairA :
    ({w : Fin 3 → Fin (1 + 1) → ℂ |
        w ∈ ForwardTube 1 3 ∧
        permAct (d := 1) (Equiv.swap (0 : Fin 3) 1) w ∈ ExtendedTube 1 3 ∧
        permAct (d := 1)
          ((Equiv.swap (0 : Fin 3) 1) * (Equiv.swap (1 : Fin 3) 2)) w ∈ ExtendedTube 1 3 ∧
        permAct (d := 1) (Equiv.swap (0 : Fin 3) 2) w ∈ ExtendedTube 1 3
    }).Nonempty := by
  rcases d1_n3_forward_triple_i0_pairA with ⟨hwFT, hτ, h120, h210⟩
  refine ⟨witness_i0_pairA, hwFT, ?_⟩
  exact ⟨by simpa [tau01] using hτ, by simpa [sigma120] using h120, by simpa [sigma210] using h210⟩

private def sigma021 : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2
private def sigma201 : Equiv.Perm (Fin 3) :=
  (Equiv.swap (0 : Fin 3) 2) * (Equiv.swap (1 : Fin 3) 2)

private def witness_i0_pairB : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 7 * I
  | 0, 1 => -1 - 2 * I
  | 1, 0 => -1 + 9 * I
  | 1, 1 => -4 - 2 * I
  | 2, 0 => -3 + 14 * I
  | 2, 1 => 6 - 5 * I

private theorem witness_i0_pairB_in_FT : witness_i0_pairB ∈ ForwardTube 1 3 := by
  intro k
  fin_cases k
  · simp
    exact ⟨by norm_num [witness_i0_pairB],
      by rw [Fin.sum_univ_two]; norm_num [witness_i0_pairB, minkowskiSignature]⟩
  · simp
    refine ⟨?_, ?_⟩
    · norm_num [witness_i0_pairB]
    · rw [Fin.sum_univ_two]
      norm_num [witness_i0_pairB, minkowskiSignature]
  · simp
    refine ⟨?_, ?_⟩
    · norm_num [witness_i0_pairB]
    · rw [Fin.sum_univ_two]
      norm_num [witness_i0_pairB, minkowskiSignature]

private def boostTauMatrix_i0_pairB : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 3/5
             else if i = 0 ∧ j = 1 then 4*I/5
             else if i = 1 ∧ j = 0 then 4*I/5
             else 3/5

private def boostTau_i0_pairB : ComplexLorentzGroup 1 where
  val := boostTauMatrix_i0_pairB
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boostTauMatrix_i0_pairB, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boostTauMatrix_i0_pairB]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def boost021Matrix_i0_pairB : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 21/29
             else if i = 0 ∧ j = 1 then -20*I/29
             else if i = 1 ∧ j = 0 then -20*I/29
             else 21/29

private def boost021_i0_pairB : ComplexLorentzGroup 1 where
  val := boost021Matrix_i0_pairB
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boost021Matrix_i0_pairB, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boost021Matrix_i0_pairB]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def boost201Matrix_i0_pairB : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 39/89
             else if i = 0 ∧ j = 1 then -80*I/89
             else if i = 1 ∧ j = 0 then -80*I/89
             else 39/89

private def boost201_i0_pairB : ComplexLorentzGroup 1 where
  val := boost201Matrix_i0_pairB
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boost201Matrix_i0_pairB, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boost201Matrix_i0_pairB]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def tauPermWitness_i0_pairB : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => -1 + 9 * I
  | 0, 1 => -4 - 2 * I
  | 1, 0 => 7 * I
  | 1, 1 => -1 - 2 * I
  | 2, 0 => -3 + 14 * I
  | 2, 1 => 6 - 5 * I

private def sigma021PermWitness_i0_pairB : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 7 * I
  | 0, 1 => -1 - 2 * I
  | 1, 0 => -3 + 14 * I
  | 1, 1 => 6 - 5 * I
  | 2, 0 => -1 + 9 * I
  | 2, 1 => -4 - 2 * I

private def sigma201PermWitness_i0_pairB : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => -3 + 14 * I
  | 0, 1 => 6 - 5 * I
  | 1, 0 => 7 * I
  | 1, 1 => -1 - 2 * I
  | 2, 0 => -1 + 9 * I
  | 2, 1 => -4 - 2 * I

private lemma tauPermWitness_i0_pairB_eq :
    tauPermWitness_i0_pairB = permAct (d := 1) tau01 witness_i0_pairB := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [tauPermWitness_i0_pairB, tau01, witness_i0_pairB, permAct, Equiv.swap_apply_def]

private lemma sigma021PermWitness_i0_pairB_eq :
    sigma021PermWitness_i0_pairB = permAct (d := 1) sigma021 witness_i0_pairB := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [sigma021PermWitness_i0_pairB, sigma021, witness_i0_pairB, permAct, Equiv.swap_apply_def]

private lemma sigma201PermWitness_i0_pairB_eq :
    sigma201PermWitness_i0_pairB = permAct (d := 1) sigma201 witness_i0_pairB := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [sigma201PermWitness_i0_pairB, sigma201, witness_i0_pairB, permAct,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

private theorem boostTau_tauPerm_i0_pairB_in_FT :
    complexLorentzAction boostTau_i0_pairB tauPermWitness_i0_pairB ∈ ForwardTube 1 3 := by
  have hval : boostTau_i0_pairB.val = boostTauMatrix_i0_pairB := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i0_pairB, boostTauMatrix_i0_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i0_pairB, boostTauMatrix_i0_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i0_pairB, boostTauMatrix_i0_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i0_pairB, boostTauMatrix_i0_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i0_pairB, boostTauMatrix_i0_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i0_pairB, boostTauMatrix_i0_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem boost021_sigma021Perm_i0_pairB_in_FT :
    complexLorentzAction boost021_i0_pairB sigma021PermWitness_i0_pairB ∈ ForwardTube 1 3 := by
  have hval : boost021_i0_pairB.val = boost021Matrix_i0_pairB := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma021PermWitness_i0_pairB, boost021Matrix_i0_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma021PermWitness_i0_pairB, boost021Matrix_i0_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma021PermWitness_i0_pairB, boost021Matrix_i0_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma021PermWitness_i0_pairB, boost021Matrix_i0_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma021PermWitness_i0_pairB, boost021Matrix_i0_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma021PermWitness_i0_pairB, boost021Matrix_i0_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem boost201_sigma201Perm_i0_pairB_in_FT :
    complexLorentzAction boost201_i0_pairB sigma201PermWitness_i0_pairB ∈ ForwardTube 1 3 := by
  have hval : boost201_i0_pairB.val = boost201Matrix_i0_pairB := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma201PermWitness_i0_pairB, boost201Matrix_i0_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma201PermWitness_i0_pairB, boost201Matrix_i0_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma201PermWitness_i0_pairB, boost201Matrix_i0_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma201PermWitness_i0_pairB, boost201Matrix_i0_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma201PermWitness_i0_pairB, boost201Matrix_i0_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma201PermWitness_i0_pairB, boost201Matrix_i0_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem tauPermWitness_i0_pairB_in_ET :
    tauPermWitness_i0_pairB ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boostTau_i0_pairB⁻¹, complexLorentzAction boostTau_i0_pairB tauPermWitness_i0_pairB,
    boostTau_tauPerm_i0_pairB_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

private theorem sigma021PermWitness_i0_pairB_in_ET :
    sigma021PermWitness_i0_pairB ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boost021_i0_pairB⁻¹, complexLorentzAction boost021_i0_pairB sigma021PermWitness_i0_pairB,
    boost021_sigma021Perm_i0_pairB_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

private theorem sigma201PermWitness_i0_pairB_in_ET :
    sigma201PermWitness_i0_pairB ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boost201_i0_pairB⁻¹, complexLorentzAction boost201_i0_pairB sigma201PermWitness_i0_pairB,
    boost201_sigma201Perm_i0_pairB_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

/-- Constructive `d=1, n=3` witness for `i=0` (`τ = (01)`) covering the other
two nontrivial `σ`:
`σ = (0,2,1)` and `σ = (2,0,1)`. -/
theorem d1_n3_forward_triple_i0_pairB :
    witness_i0_pairB ∈ ForwardTube 1 3 ∧
    permAct (d := 1) tau01 witness_i0_pairB ∈ ExtendedTube 1 3 ∧
    permAct (d := 1) sigma021 witness_i0_pairB ∈ ExtendedTube 1 3 ∧
    permAct (d := 1) sigma201 witness_i0_pairB ∈ ExtendedTube 1 3 := by
  refine ⟨witness_i0_pairB_in_FT, ?_, ?_, ?_⟩
  · simpa [tauPermWitness_i0_pairB_eq] using tauPermWitness_i0_pairB_in_ET
  · simpa [sigma021PermWitness_i0_pairB_eq] using sigma021PermWitness_i0_pairB_in_ET
  · simpa [sigma201PermWitness_i0_pairB_eq] using sigma201PermWitness_i0_pairB_in_ET

theorem d1_n3_forward_triple_nonempty_i0_pairB :
    ({w : Fin 3 → Fin (1 + 1) → ℂ |
        w ∈ ForwardTube 1 3 ∧
        permAct (d := 1) (Equiv.swap (0 : Fin 3) 1) w ∈ ExtendedTube 1 3 ∧
        permAct (d := 1) (Equiv.swap (1 : Fin 3) 2) w ∈ ExtendedTube 1 3 ∧
        permAct (d := 1)
          ((Equiv.swap (0 : Fin 3) 2) * (Equiv.swap (1 : Fin 3) 2)) w ∈ ExtendedTube 1 3
    }).Nonempty := by
  rcases d1_n3_forward_triple_i0_pairB with ⟨hwFT, hτ, h021, h201⟩
  refine ⟨witness_i0_pairB, hwFT, ?_⟩
  exact ⟨by simpa [tau01] using hτ, by simpa [sigma021] using h021, by simpa [sigma201] using h201⟩

private def tau12 : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2
private def sigma102 : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1

private def witness_i1_pairA : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 3 + 11 * I
  | 0, 1 => -8 - 4 * I
  | 1, 0 => -1 + 15 * I
  | 1, 1 => 8 - 5 * I
  | 2, 0 => 1 + 18 * I
  | 2, 1 => -2 - 6 * I

private theorem witness_i1_pairA_in_FT : witness_i1_pairA ∈ ForwardTube 1 3 := by
  intro k
  fin_cases k
  · simp
    exact ⟨by norm_num [witness_i1_pairA],
      by rw [Fin.sum_univ_two]; norm_num [witness_i1_pairA, minkowskiSignature]⟩
  · simp
    refine ⟨?_, ?_⟩
    · norm_num [witness_i1_pairA]
    · rw [Fin.sum_univ_two]
      norm_num [witness_i1_pairA, minkowskiSignature]
  · simp
    refine ⟨?_, ?_⟩
    · norm_num [witness_i1_pairA]
    · rw [Fin.sum_univ_two]
      norm_num [witness_i1_pairA, minkowskiSignature]

private def boostTauMatrix_i1_pairA : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 3/5
             else if i = 0 ∧ j = 1 then 4*I/5
             else if i = 1 ∧ j = 0 then 4*I/5
             else 3/5

private def boostTau_i1_pairA : ComplexLorentzGroup 1 where
  val := boostTauMatrix_i1_pairA
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boostTauMatrix_i1_pairA, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boostTauMatrix_i1_pairA]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def boost102Matrix_i1_pairA : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 65/97
             else if i = 0 ∧ j = 1 then -72*I/97
             else if i = 1 ∧ j = 0 then -72*I/97
             else 65/97

private def boost102_i1_pairA : ComplexLorentzGroup 1 where
  val := boost102Matrix_i1_pairA
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boost102Matrix_i1_pairA, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boost102Matrix_i1_pairA]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def boost120Matrix_i1_pairA : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 3/5
             else if i = 0 ∧ j = 1 then -4*I/5
             else if i = 1 ∧ j = 0 then -4*I/5
             else 3/5

private def boost120_i1_pairA : ComplexLorentzGroup 1 where
  val := boost120Matrix_i1_pairA
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boost120Matrix_i1_pairA, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boost120Matrix_i1_pairA]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def tauPermWitness_i1_pairA : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 3 + 11 * I
  | 0, 1 => -8 - 4 * I
  | 1, 0 => 1 + 18 * I
  | 1, 1 => -2 - 6 * I
  | 2, 0 => -1 + 15 * I
  | 2, 1 => 8 - 5 * I

private def sigma102PermWitness_i1_pairA : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => -1 + 15 * I
  | 0, 1 => 8 - 5 * I
  | 1, 0 => 3 + 11 * I
  | 1, 1 => -8 - 4 * I
  | 2, 0 => 1 + 18 * I
  | 2, 1 => -2 - 6 * I

private def sigma120PermWitness_i1_pairA : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => -1 + 15 * I
  | 0, 1 => 8 - 5 * I
  | 1, 0 => 1 + 18 * I
  | 1, 1 => -2 - 6 * I
  | 2, 0 => 3 + 11 * I
  | 2, 1 => -8 - 4 * I

private lemma tauPermWitness_i1_pairA_eq :
    tauPermWitness_i1_pairA = permAct (d := 1) tau12 witness_i1_pairA := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [tauPermWitness_i1_pairA, tau12, witness_i1_pairA, permAct, Equiv.swap_apply_def]

private lemma sigma102PermWitness_i1_pairA_eq :
    sigma102PermWitness_i1_pairA = permAct (d := 1) sigma102 witness_i1_pairA := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [sigma102PermWitness_i1_pairA, sigma102, witness_i1_pairA, permAct, Equiv.swap_apply_def]

private lemma sigma120PermWitness_i1_pairA_eq :
    sigma120PermWitness_i1_pairA = permAct (d := 1) sigma120 witness_i1_pairA := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [sigma120PermWitness_i1_pairA, sigma120, witness_i1_pairA, permAct,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

private theorem boostTau_tauPerm_i1_pairA_in_FT :
    complexLorentzAction boostTau_i1_pairA tauPermWitness_i1_pairA ∈ ForwardTube 1 3 := by
  have hval : boostTau_i1_pairA.val = boostTauMatrix_i1_pairA := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i1_pairA, boostTauMatrix_i1_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i1_pairA, boostTauMatrix_i1_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i1_pairA, boostTauMatrix_i1_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i1_pairA, boostTauMatrix_i1_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i1_pairA, boostTauMatrix_i1_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i1_pairA, boostTauMatrix_i1_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem boost102_sigma102Perm_i1_pairA_in_FT :
    complexLorentzAction boost102_i1_pairA sigma102PermWitness_i1_pairA ∈ ForwardTube 1 3 := by
  have hval : boost102_i1_pairA.val = boost102Matrix_i1_pairA := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma102PermWitness_i1_pairA, boost102Matrix_i1_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma102PermWitness_i1_pairA, boost102Matrix_i1_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma102PermWitness_i1_pairA, boost102Matrix_i1_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma102PermWitness_i1_pairA, boost102Matrix_i1_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma102PermWitness_i1_pairA, boost102Matrix_i1_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma102PermWitness_i1_pairA, boost102Matrix_i1_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem boost120_sigma120Perm_i1_pairA_in_FT :
    complexLorentzAction boost120_i1_pairA sigma120PermWitness_i1_pairA ∈ ForwardTube 1 3 := by
  have hval : boost120_i1_pairA.val = boost120Matrix_i1_pairA := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma120PermWitness_i1_pairA, boost120Matrix_i1_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma120PermWitness_i1_pairA, boost120Matrix_i1_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma120PermWitness_i1_pairA, boost120Matrix_i1_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma120PermWitness_i1_pairA, boost120Matrix_i1_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma120PermWitness_i1_pairA, boost120Matrix_i1_pairA,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma120PermWitness_i1_pairA, boost120Matrix_i1_pairA,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem tauPermWitness_i1_pairA_in_ET :
    tauPermWitness_i1_pairA ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boostTau_i1_pairA⁻¹, complexLorentzAction boostTau_i1_pairA tauPermWitness_i1_pairA,
    boostTau_tauPerm_i1_pairA_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

private theorem sigma102PermWitness_i1_pairA_in_ET :
    sigma102PermWitness_i1_pairA ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boost102_i1_pairA⁻¹, complexLorentzAction boost102_i1_pairA sigma102PermWitness_i1_pairA,
    boost102_sigma102Perm_i1_pairA_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

private theorem sigma120PermWitness_i1_pairA_in_ET :
    sigma120PermWitness_i1_pairA ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boost120_i1_pairA⁻¹, complexLorentzAction boost120_i1_pairA sigma120PermWitness_i1_pairA,
    boost120_sigma120Perm_i1_pairA_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

theorem d1_n3_forward_triple_nonempty_i1_pairA :
    ({w : Fin 3 → Fin (1 + 1) → ℂ |
        w ∈ ForwardTube 1 3 ∧
        permAct (d := 1) (Equiv.swap (1 : Fin 3) 2) w ∈ ExtendedTube 1 3 ∧
        permAct (d := 1) (Equiv.swap (0 : Fin 3) 1) w ∈ ExtendedTube 1 3 ∧
        permAct (d := 1)
          ((Equiv.swap (0 : Fin 3) 1) * (Equiv.swap (1 : Fin 3) 2)) w ∈ ExtendedTube 1 3
    }).Nonempty := by
  refine ⟨witness_i1_pairA, witness_i1_pairA_in_FT, ?_⟩
  exact ⟨by simpa [tauPermWitness_i1_pairA_eq] using tauPermWitness_i1_pairA_in_ET,
    by simpa [sigma102PermWitness_i1_pairA_eq] using sigma102PermWitness_i1_pairA_in_ET,
    by simpa [sigma120PermWitness_i1_pairA_eq] using sigma120PermWitness_i1_pairA_in_ET⟩

private def witness_i1_pairB : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => -1 + 10 * I
  | 0, 1 => 5 - 3 * I
  | 1, 0 => 1 + 20 * I
  | 1, 1 => 2 - 6 * I
  | 2, 0 => 1 + 24 * I
  | 2, 1 => -1 - 8 * I

private theorem witness_i1_pairB_in_FT : witness_i1_pairB ∈ ForwardTube 1 3 := by
  intro k
  fin_cases k
  · simp
    exact ⟨by norm_num [witness_i1_pairB],
      by rw [Fin.sum_univ_two]; norm_num [witness_i1_pairB, minkowskiSignature]⟩
  · simp
    refine ⟨?_, ?_⟩
    · norm_num [witness_i1_pairB]
    · rw [Fin.sum_univ_two]
      norm_num [witness_i1_pairB, minkowskiSignature]
  · simp
    refine ⟨?_, ?_⟩
    · norm_num [witness_i1_pairB]
    · rw [Fin.sum_univ_two]
      norm_num [witness_i1_pairB, minkowskiSignature]

private def boostTauMatrix_i1_pairB : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 36/85
             else if i = 0 ∧ j = 1 then 77*I/85
             else if i = 1 ∧ j = 0 then 77*I/85
             else 36/85

private def boostTau_i1_pairB : ComplexLorentzGroup 1 where
  val := boostTauMatrix_i1_pairB
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boostTauMatrix_i1_pairB, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boostTauMatrix_i1_pairB]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def boost210Matrix_i1_pairB : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 17/145
             else if i = 0 ∧ j = 1 then 144*I/145
             else if i = 1 ∧ j = 0 then 144*I/145
             else 17/145

private def boost210_i1_pairB : ComplexLorentzGroup 1 where
  val := boost210Matrix_i1_pairB
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boost210Matrix_i1_pairB, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boost210Matrix_i1_pairB]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def boost201Matrix_i1_pairB : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 5/13
             else if i = 0 ∧ j = 1 then 12*I/13
             else if i = 1 ∧ j = 0 then 12*I/13
             else 5/13

private def boost201_i1_pairB : ComplexLorentzGroup 1 where
  val := boost201Matrix_i1_pairB
  metric_preserving := by
    intro μ ν
    rw [Fin.sum_univ_two]
    fin_cases μ <;> fin_cases ν <;>
      simp [boost201Matrix_i1_pairB, minkowskiSignature, Complex.ext_iff, Complex.I_re,
        Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
      ring
  proper := by
    rw [Matrix.det_fin_two]
    simp [boost201Matrix_i1_pairB]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      ring

private def tauPermWitness_i1_pairB : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => -1 + 10 * I
  | 0, 1 => 5 - 3 * I
  | 1, 0 => 1 + 24 * I
  | 1, 1 => -1 - 8 * I
  | 2, 0 => 1 + 20 * I
  | 2, 1 => 2 - 6 * I

private def sigma210PermWitness_i1_pairB : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 1 + 24 * I
  | 0, 1 => -1 - 8 * I
  | 1, 0 => 1 + 20 * I
  | 1, 1 => 2 - 6 * I
  | 2, 0 => -1 + 10 * I
  | 2, 1 => 5 - 3 * I

private def sigma201PermWitness_i1_pairB : Fin 3 → Fin (1 + 1) → ℂ
  | 0, 0 => 1 + 24 * I
  | 0, 1 => -1 - 8 * I
  | 1, 0 => -1 + 10 * I
  | 1, 1 => 5 - 3 * I
  | 2, 0 => 1 + 20 * I
  | 2, 1 => 2 - 6 * I

private lemma tauPermWitness_i1_pairB_eq :
    tauPermWitness_i1_pairB = permAct (d := 1) tau12 witness_i1_pairB := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [tauPermWitness_i1_pairB, tau12, witness_i1_pairB, permAct, Equiv.swap_apply_def]

private lemma sigma210PermWitness_i1_pairB_eq :
    sigma210PermWitness_i1_pairB = permAct (d := 1) sigma210 witness_i1_pairB := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [sigma210PermWitness_i1_pairB, sigma210, witness_i1_pairB, permAct, Equiv.swap_apply_def]

private lemma sigma201PermWitness_i1_pairB_eq :
    sigma201PermWitness_i1_pairB = permAct (d := 1) sigma201 witness_i1_pairB := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [sigma201PermWitness_i1_pairB, sigma201, witness_i1_pairB, permAct,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

private theorem boostTau_tauPerm_i1_pairB_in_FT :
    complexLorentzAction boostTau_i1_pairB tauPermWitness_i1_pairB ∈ ForwardTube 1 3 := by
  have hval : boostTau_i1_pairB.val = boostTauMatrix_i1_pairB := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i1_pairB, boostTauMatrix_i1_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i1_pairB, boostTauMatrix_i1_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i1_pairB, boostTauMatrix_i1_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i1_pairB, boostTauMatrix_i1_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, tauPermWitness_i1_pairB, boostTauMatrix_i1_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, tauPermWitness_i1_pairB, boostTauMatrix_i1_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem boost210_sigma210Perm_i1_pairB_in_FT :
    complexLorentzAction boost210_i1_pairB sigma210PermWitness_i1_pairB ∈ ForwardTube 1 3 := by
  have hval : boost210_i1_pairB.val = boost210Matrix_i1_pairB := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma210PermWitness_i1_pairB, boost210Matrix_i1_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma210PermWitness_i1_pairB, boost210Matrix_i1_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma210PermWitness_i1_pairB, boost210Matrix_i1_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma210PermWitness_i1_pairB, boost210Matrix_i1_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma210PermWitness_i1_pairB, boost210Matrix_i1_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma210PermWitness_i1_pairB, boost210Matrix_i1_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem boost201_sigma201Perm_i1_pairB_in_FT :
    complexLorentzAction boost201_i1_pairB sigma201PermWitness_i1_pairB ∈ ForwardTube 1 3 := by
  have hval : boost201_i1_pairB.val = boost201Matrix_i1_pairB := rfl
  intro k
  fin_cases k
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma201PermWitness_i1_pairB, boost201Matrix_i1_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma201PermWitness_i1_pairB, boost201Matrix_i1_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma201PermWitness_i1_pairB, boost201Matrix_i1_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma201PermWitness_i1_pairB, boost201Matrix_i1_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
  · simp
    refine ⟨?_, ?_⟩
    · simp [complexLorentzAction, hval, sigma201PermWitness_i1_pairB, boost201Matrix_i1_pairB,
        Fin.sum_univ_two, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Fin.sum_univ_two]
      simp [complexLorentzAction, hval, sigma201PermWitness_i1_pairB, boost201Matrix_i1_pairB,
        Fin.sum_univ_two, minkowskiSignature, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num

private theorem tauPermWitness_i1_pairB_in_ET :
    tauPermWitness_i1_pairB ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boostTau_i1_pairB⁻¹, complexLorentzAction boostTau_i1_pairB tauPermWitness_i1_pairB,
    boostTau_tauPerm_i1_pairB_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

private theorem sigma210PermWitness_i1_pairB_in_ET :
    sigma210PermWitness_i1_pairB ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boost210_i1_pairB⁻¹, complexLorentzAction boost210_i1_pairB sigma210PermWitness_i1_pairB,
    boost210_sigma210Perm_i1_pairB_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

private theorem sigma201PermWitness_i1_pairB_in_ET :
    sigma201PermWitness_i1_pairB ∈ ExtendedTube 1 3 := by
  apply Set.mem_iUnion.mpr
  refine ⟨boost201_i1_pairB⁻¹, complexLorentzAction boost201_i1_pairB sigma201PermWitness_i1_pairB,
    boost201_sigma201Perm_i1_pairB_in_FT, ?_⟩
  rw [complexLorentzAction_inv]

theorem d1_n3_forward_triple_nonempty_i1_pairB :
    ({w : Fin 3 → Fin (1 + 1) → ℂ |
        w ∈ ForwardTube 1 3 ∧
        permAct (d := 1) (Equiv.swap (1 : Fin 3) 2) w ∈ ExtendedTube 1 3 ∧
        permAct (d := 1) (Equiv.swap (0 : Fin 3) 2) w ∈ ExtendedTube 1 3 ∧
        permAct (d := 1)
          ((Equiv.swap (0 : Fin 3) 2) * (Equiv.swap (1 : Fin 3) 2)) w ∈ ExtendedTube 1 3
    }).Nonempty := by
  refine ⟨witness_i1_pairB, witness_i1_pairB_in_FT, ?_⟩
  exact ⟨by simpa [tauPermWitness_i1_pairB_eq] using tauPermWitness_i1_pairB_in_ET,
    by simpa [sigma210PermWitness_i1_pairB_eq] using sigma210PermWitness_i1_pairB_in_ET,
    by simpa [sigma201PermWitness_i1_pairB_eq] using sigma201PermWitness_i1_pairB_in_ET⟩

end BHW
