import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankBridge
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexGlobalIdentity

/-!
# Minor equations for the oriented exceptional-rank locus

This file records the finite rank algebra behind the analytic exceptional-rank
input.  The remaining analytic-subvariety theorem can now consume an explicit
determinant-zero-locus statement rather than redoing rank/minor bookkeeping.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- The `0 x 0` source minor is nonzero.  This handles the edge case in which
the maximal minor size `min (d + 1) n` is zero. -/
theorem sourceMatrixMinor_zero_ne_zero
    (n : ℕ) (I J : Fin 0 → Fin n) (Z : Fin n → Fin n → ℂ) :
    sourceMatrixMinor n 0 I J Z ≠ 0 := by
  simp [sourceMatrixMinor]

/-- Strict lower rank is equivalent to vanishing of all maximal source-Gram
minors. -/
theorem sourceOrientedLowerRank_iff_minors_eq_zero
    {G : SourceOrientedGramData d n} :
    sourceGramMatrixRank n G.gram < min (d + 1) n ↔
      ∀ I J : Fin (min (d + 1) n) → Fin n,
        sourceMatrixMinor n (min (d + 1) n) I J G.gram = 0 := by
  by_cases hpos : 0 < min (d + 1) n
  · let k := min (d + 1) n
    have hk : k - 1 + 1 = k := by omega
    constructor
    · intro hlt
      have hle :
          (Matrix.of fun i j : Fin n => G.gram i j).rank ≤ k - 1 := by
        simpa [sourceGramMatrixRank, k] using Nat.le_pred_of_lt hlt
      have hminors := sourceMatrix_minors_eq_zero_of_rank_le n (k - 1) hle
      have hminorsK :
          ∀ I J : Fin k → Fin n,
            sourceMatrixMinor n k I J G.gram = 0 := by
        rw [← hk]
        exact hminors
      simpa [k] using hminorsK
    · intro hminors
      have hminorsK :
          ∀ I J : Fin k → Fin n,
            sourceMatrixMinor n k I J G.gram = 0 := by
        simpa [k] using hminors
      have hminors' :
          ∀ I J : Fin (k - 1 + 1) → Fin n,
            sourceMatrixMinor n (k - 1 + 1) I J G.gram = 0 := by
        rw [hk]
        exact hminorsK
      have hle :
          (Matrix.of fun i j : Fin n => G.gram i j).rank ≤ k - 1 :=
        sourceMatrix_rank_le_of_minors_eq_zero n (k - 1) hminors'
      have hrank : sourceGramMatrixRank n G.gram ≤ k - 1 := by
        simpa [sourceGramMatrixRank, k] using hle
      omega
  · have hk0 : min (d + 1) n = 0 := by omega
    constructor
    · intro hlt
      omega
    · intro hminors
      exfalso
      rw [hk0] at hminors
      have hzero := hminors (Fin.elim0) (Fin.elim0)
      exact
        sourceMatrixMinor_zero_ne_zero n (Fin.elim0) (Fin.elim0)
          G.gram hzero

/-- The exceptional-rank locus is the oriented source variety intersected
with the determinant zero locus for all maximal source-Gram minors. -/
theorem sourceOrientedExceptionalRank_eq_minorsVanishing
    (d n : ℕ) :
    {G | SourceOrientedExceptionalRank d n G} =
      sourceOrientedGramVariety d n ∩
        {G | ∀ I J : Fin (min (d + 1) n) → Fin n,
          sourceMatrixMinor n (min (d + 1) n) I J G.gram = 0} := by
  rw [sourceOrientedExceptionalRank_eq_lowerRank]
  ext G
  constructor
  · rintro ⟨hGvar, hlt⟩
    exact
      ⟨hGvar,
        (sourceOrientedLowerRank_iff_minors_eq_zero
          (d := d) (n := n) (G := G)).1 hlt⟩
  · rintro ⟨hGvar, hminors⟩
    exact
      ⟨hGvar,
        (sourceOrientedLowerRank_iff_minors_eq_zero
          (d := d) (n := n) (G := G)).2 hminors⟩

/-- The common zero locus of all maximal source-Gram minors is closed in the
oriented source-coordinate ambient space. -/
theorem isClosed_sourceOrientedMaximalMinorsVanishing
    (d n : ℕ) :
    IsClosed
      {G : SourceOrientedGramData d n |
        ∀ I J : Fin (min (d + 1) n) → Fin n,
          sourceMatrixMinor n (min (d + 1) n) I J G.gram = 0} := by
  rw [show
      {G : SourceOrientedGramData d n |
        ∀ I J : Fin (min (d + 1) n) → Fin n,
          sourceMatrixMinor n (min (d + 1) n) I J G.gram = 0} =
        ⋂ I : Fin (min (d + 1) n) → Fin n,
          ⋂ J : Fin (min (d + 1) n) → Fin n,
            {G : SourceOrientedGramData d n |
              sourceMatrixMinor n (min (d + 1) n) I J G.gram = 0} by
    ext G
    simp]
  apply isClosed_iInter
  intro I
  apply isClosed_iInter
  intro J
  exact isClosed_eq
    ((continuous_sourceMatrixMinor n (min (d + 1) n) I J).comp
      continuous_sourceOrientedGramData_gram)
    continuous_const

end BHW
