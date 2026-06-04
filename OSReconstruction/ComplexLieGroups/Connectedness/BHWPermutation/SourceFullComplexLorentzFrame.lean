import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceFullComplexLorentz
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameMaxRankProducer

/-!
# Full-complex Lorentz determinant action on selected source frames

This companion file keeps the determinant-unrestricted Lorentz group algebra
separate from the selected full-frame determinant bookkeeping used by the
high-rank Hall-Wightman source route.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Selected full-frame matrices transform on the right by the transpose of a
full complex Lorentz matrix. -/
theorem sourceFullFrameMatrix_fullComplexLorentzAction
    {d n : ℕ}
    (A : HallWightmanFullComplexLorentzGroup d)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameMatrix d n ι
        (hallWightmanFullComplexLorentzAction A z) =
      sourceFullFrameMatrix d n ι z * A.val.transpose := by
  ext a μ
  simp [sourceFullFrameMatrix, hallWightmanFullComplexLorentzAction,
    hallWightmanFullComplexLorentzVectorAction, Matrix.mul_apply,
    Matrix.transpose_apply, mul_comm]

/-- A full complex Lorentz transformation scales each selected full-frame
determinant by its determinant. -/
theorem sourceFullFrameDet_fullComplexLorentzAction
    {d n : ℕ}
    (A : HallWightmanFullComplexLorentzGroup d)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameDet d n ι
        (hallWightmanFullComplexLorentzAction A z) =
      hallWightmanFullComplexLorentzDet A *
        sourceFullFrameDet d n ι z := by
  rw [sourceFullFrameDet, sourceFullFrameMatrix_fullComplexLorentzAction,
    sourceFullFrameDet, Matrix.det_mul, Matrix.det_transpose,
    hallWightmanFullComplexLorentzDet]
  ring

/-- In full ambient rank, any full-complex Lorentz same-Gram extension has
determinant equal to the selected-frame determinant ratio. -/
theorem fullComplexLorentz_det_eq_frameMapDet_of_fullRank
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hfull :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1)
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (A : HallWightmanFullComplexLorentzGroup d)
    (hA :
      ∀ i,
        hallWightmanFullComplexLorentzVectorAction A (z i) = w i) :
    hallWightmanFullComplexLorentzDet A =
      HWFullRankSameGramFrameMapDet d n z w := by
  rcases
    exists_sourceFullFrameDet_ne_zero_of_sourceGramRank_eq_spacetime
      d n z hfull with
  ⟨ι, hι⟩
  have hdet_action :
      sourceFullFrameDet d n ι w =
        hallWightmanFullComplexLorentzDet A *
          sourceFullFrameDet d n ι z := by
    calc
      sourceFullFrameDet d n ι w =
          sourceFullFrameDet d n ι
            (hallWightmanFullComplexLorentzAction A z) := by
            congr
            funext i μ
            exact congrFun (hA i).symm μ
      _ = hallWightmanFullComplexLorentzDet A *
            sourceFullFrameDet d n ι z :=
            sourceFullFrameDet_fullComplexLorentzAction A ι z
  have hratio :
      HWFullRankSameGramFrameMapDet d n z w =
        sourceFullFrameDet d n ι w /
          sourceFullFrameDet d n ι z :=
    hwFullRankSameGramFrameMapDet_eq_det_ratio_of_fullFrame
      d n hfull hgram ι hι
  calc
    hallWightmanFullComplexLorentzDet A =
        (hallWightmanFullComplexLorentzDet A *
            sourceFullFrameDet d n ι z) /
          sourceFullFrameDet d n ι z := by
          rw [mul_div_cancel_right₀ _ hι]
    _ = sourceFullFrameDet d n ι w /
          sourceFullFrameDet d n ι z := by
          rw [← hdet_action]
    _ = HWFullRankSameGramFrameMapDet d n z w := hratio.symm

/-- Ambient-linear-equivalence version of
`fullComplexLorentz_det_eq_frameMapDet_of_fullRank`. -/
theorem linearEquiv_det_eq_frameMapDet_of_fullRank
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hfull :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1)
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (E : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hpres :
      ∀ x y,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d x y)
    (hE : ∀ i, E (z i) = w i) :
    LinearMap.det E.toLinearMap =
      HWFullRankSameGramFrameMapDet d n z w := by
  let A : HallWightmanFullComplexLorentzGroup d :=
    HallWightmanFullComplexLorentzGroup.ofLinearMap E.toLinearMap hpres
  have hA :
      ∀ i,
        hallWightmanFullComplexLorentzVectorAction A (z i) = w i := by
    intro i
    calc
      hallWightmanFullComplexLorentzVectorAction A (z i) =
          E.toLinearMap (z i) := by
          exact
            HallWightmanFullComplexLorentzGroup.ofLinearMap_vectorAction
              E.toLinearMap hpres (z i)
      _ = w i := hE i
  have hdetA :=
    fullComplexLorentz_det_eq_frameMapDet_of_fullRank
      d n hfull hgram A hA
  simpa [A, hallWightmanFullComplexLorentzDet,
    HallWightmanFullComplexLorentzGroup.ofLinearMap,
    LinearMap.det_toMatrix'] using hdetA

/-- In full scalar rank, equality of oriented source invariants forces any
ambient same-tuple form-preserving equivalence to have determinant `1`. -/
theorem linearEquiv_det_one_of_same_sourceOrientedInvariant_fullRank
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hfull :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1)
    (horiented :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w)
    (E : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hpres :
      ∀ x y,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d x y)
    (hE : ∀ i, E (z i) = w i) :
    LinearMap.det E.toLinearMap = 1 := by
  have hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w :=
    same_sourceOrientedInvariant_sourceGram horiented
  have hdet :
      LinearMap.det E.toLinearMap =
        HWFullRankSameGramFrameMapDet d n z w :=
    linearEquiv_det_eq_frameMapDet_of_fullRank
      d n hfull hgram E hpres hE
  have hSO : HWSameSourceGramSOOrientationCompatible d n z w :=
    sourceOriented_soCompatible_of_sameInvariant d n hgram horiented
  have hone : HWFullRankSameGramFrameMapDet d n z w = 1 := by
    rcases hSO with hlt | hone
    · have hnot :
          ¬ sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1 := by
        rw [hfull]
        exact Nat.lt_irrefl _
      exact False.elim (hnot hlt)
    · exact hone
  exact hdet.trans hone

end BHW
