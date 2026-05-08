import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedCauchyBinet

/-!
# Linear syzygies for oriented source determinant coordinates

This file records the vector-bracket linear syzygies missing from the
pairing/determinant presentation of the special orthogonal invariant ring.
The proof is elementary determinant algebra: expand a square matrix whose
first row is a linear combination of the remaining rows.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Delete the `k`-th entry from an embedded ordered `(m + 1)`-tuple. -/
def finDeleteEmbedding {m n : ℕ}
    (k : Fin (m + 1)) (ι : Fin (m + 1) ↪ Fin n) :
    Fin m ↪ Fin n where
  toFun a := ι (k.succAbove a)
  inj' := by
    intro a b h
    exact (Fin.succAbove_right_injective (p := k)) (ι.injective h)

/-- The determinant linear-dependence identity behind the SO vector-bracket
relations.  It is the Laplace expansion of a square matrix whose first row is
a linear combination of the remaining rows. -/
theorem coordinateVolume_linearSyzygy
    (m n : ℕ)
    (z : Fin n → Fin m → ℂ)
    (w : Fin m → ℂ)
    (ι : Fin (m + 1) ↪ Fin n) :
    (∑ k : Fin (m + 1),
      ((-1 : ℂ) ^ (k : ℕ)) *
        (∑ μ : Fin m, w μ * z (ι k) μ) *
        Matrix.det (fun a μ : Fin m => z (ι (k.succAbove a)) μ)) = 0 := by
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    fun r c =>
      if hr : r = 0 then
        ∑ μ : Fin m, w μ * z (ι c) μ
      else
        z (ι c) (Fin.pred r hr)
  let coeff : Fin (m + 1) → ℂ :=
    fun r => if hr : r = 0 then 0 else w (Fin.pred r hr)
  have hrow : (∑ r : Fin (m + 1), coeff r • A r) = A 0 := by
    ext c
    rw [Fin.sum_univ_succ]
    simp [coeff, A]
  have hupdate : A.updateRow 0 (∑ r : Fin (m + 1), coeff r • A r) = A := by
    ext r c
    by_cases hr : r = 0
    · subst r
      simp [hrow]
    · simp [Matrix.updateRow_ne hr]
  have hdetUpdate := Matrix.det_updateRow_sum A 0 coeff
  have hdet : A.det = 0 := by
    calc
      A.det = (A.updateRow 0 (∑ r : Fin (m + 1), coeff r • A r)).det := by
        rw [hupdate]
      _ = coeff 0 • A.det := hdetUpdate
      _ = 0 := by simp [coeff]
  calc
    (∑ k : Fin (m + 1),
      ((-1 : ℂ) ^ (k : ℕ)) *
        (∑ μ : Fin m, w μ * z (ι k) μ) *
        Matrix.det (fun a μ : Fin m => z (ι (k.succAbove a)) μ))
        = A.det := by
          rw [Matrix.det_succ_row_zero A]
          apply Finset.sum_congr rfl
          intro k _hk
          have hsubmat :
              A.submatrix Fin.succ k.succAbove =
                (fun μ a : Fin m => z (ι (k.succAbove a)) μ) := by
            ext μ a
            simp [A]
          have hsub :
              (A.submatrix Fin.succ k.succAbove).det =
                Matrix.det (fun a μ : Fin m => z (ι (k.succAbove a)) μ) := by
            rw [hsubmat]
            rw [← Matrix.det_transpose]
            rfl
          rw [hsub]
          simp [A]
    _ = 0 := hdet

/-- Actual oriented source invariants satisfy the linear vector-bracket
relations. -/
theorem sourceOrientedInvariant_linearSyzygy_fullFrame
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (i : Fin n)
    (ι : Fin (d + 2) ↪ Fin n) :
    (∑ k : Fin (d + 2),
      ((-1 : ℂ) ^ (k : ℕ)) *
        (sourceOrientedMinkowskiInvariant d n z).gram i (ι k) *
        (sourceOrientedMinkowskiInvariant d n z).det
          (finDeleteEmbedding k ι)) = 0 := by
  simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram,
    SourceOrientedGramData.det, sourceMinkowskiGram, sourceFullFrameDet,
    sourceFullFrameMatrix, mul_assoc] using
    coordinateVolume_linearSyzygy (d + 1) n z
      (fun μ : Fin (d + 1) =>
        (MinkowskiSpace.metricSignature d μ : ℂ) * z i μ) ι

end BHW
