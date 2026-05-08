import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexCone
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedLowRankDeterminants

/-!
# Adapted algebraic representatives for low-rank source data

This file supplies the finite-dimensional replacement for the false shortcut
that an arbitrary source realization has source-span dimension equal to its
ordinary Gram rank.  In low rank we first choose a same-Gram representative
whose coefficient span has the correct dimension; the oriented determinant
coordinates then agree automatically by the low-rank determinant theorem.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- `Fin.castLE` as an embedding. -/
def finCastLEEmbedding {r D : ℕ} (h : r ≤ D) : Fin r ↪ Fin D where
  toFun := Fin.castLE h
  inj' := Fin.castLE_injective h

/-- Pad an ordinary rank-coordinate dot source tuple into the first `r`
coordinates of `Fin (d + 1)`, extending by zero off the embedded range. -/
def sourceComplexPad
    (d n r : ℕ)
    (hrD : r ≤ d + 1)
    (A : Fin n → Fin r → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i μ =>
    if hμ : μ ∈ Set.range (finCastLEEmbedding hrD) then
      A i (Classical.choose hμ)
    else
      0

/-- Padding a dot-Gram representative by zero coordinates does not change its
ordinary dot Gram matrix. -/
theorem sourceComplexDotGram_padded_eq
    (d n r : ℕ)
    (hrD : r ≤ d + 1)
    (A : Fin n → Fin r → ℂ) :
    sourceComplexDotGram (d + 1) n (sourceComplexPad d n r hrD A) =
      sourceComplexDotGram r n A := by
  ext i j
  simpa [sourceComplexDotGram, sourceComplexPad] using
    (sum_mul_indicator_embedding
      (e := finCastLEEmbedding hrD)
      (U := fun a => A i a)
      (V := fun a => A j a))

/-- The source Gram rank of a realized source tuple is bounded by the
coefficient-span dimension of that tuple. -/
theorem sourceGramMatrixRank_le_finrank_sourceCoefficientEval_range
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceGramMatrixRank n (sourceMinkowskiGram d n z) ≤
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) := by
  rw [sourceGramMatrixRank_eq_restrictedMinkowskiRank_range]
  simp [restrictedMinkowskiRank]

/-- A source complex Gram-variety point has ordinary rank at most the
spacetime source dimension. -/
theorem sourceGramMatrixRank_le_spacetime_of_mem_sourceComplexGramVariety
    (d n : ℕ)
    {G : Fin n → Fin n → ℂ}
    (hG : G ∈ sourceComplexGramVariety d n) :
    sourceGramMatrixRank n G ≤ d + 1 := by
  have h := hG
  rw [sourceComplexGramVariety_eq_rank_le] at h
  simpa [sourceGramMatrixRank] using h.2

/-- The coefficient span of a Minkowski tuple obtained from padded dot
coordinates is contained in the `r`-dimensional padded coordinate subspace. -/
theorem finrank_sourceCoefficientEval_range_le_of_paddedDot
    (d n r : ℕ)
    (hrD : r ≤ d + 1)
    (A : Fin n → Fin r → ℂ) :
    Module.finrank ℂ
        (LinearMap.range
          (sourceCoefficientEval d n
            (fun i =>
              (complexMinkowskiToDotLinearEquiv d).symm
                (sourceComplexPad d n r hrD A i)))) ≤ r := by
  let padLinear : (Fin r → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    { toFun := fun v μ =>
        if hμ : μ ∈ Set.range (finCastLEEmbedding hrD) then
          v (Classical.choose hμ)
        else
          0
      map_add' := by
        intro v w
        ext μ
        by_cases hμ : μ.val < r
        · simp [finCastLEEmbedding, hμ]
        · simp [finCastLEEmbedding, hμ]
      map_smul' := by
        intro c v
        ext μ
        by_cases hμ : μ.val < r
        · simp [finCastLEEmbedding, hμ]
        · simp [finCastLEEmbedding, hμ] }
  let embedLinear : (Fin r → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    (complexMinkowskiToDotLinearEquiv d).symm.toLinearMap.comp padLinear
  have hpad :
      ∀ i : Fin n, padLinear (A i) = sourceComplexPad d n r hrD A i := by
    intro i
    rfl
  have hrange :
      LinearMap.range
          (sourceCoefficientEval d n
            (fun i =>
              (complexMinkowskiToDotLinearEquiv d).symm
                (sourceComplexPad d n r hrD A i))) ≤
        LinearMap.range embedLinear := by
    rintro x ⟨a, rfl⟩
    refine ⟨fun ρ => ∑ i : Fin n, a i * A i ρ, ?_⟩
    have hv :
        (fun ρ : Fin r => ∑ i : Fin n, a i * A i ρ) =
          ∑ i : Fin n, a i • A i := by
      ext ρ
      simp [Pi.smul_apply]
    change
      embedLinear (fun ρ => ∑ i : Fin n, a i * A i ρ) =
        sourceCoefficientEval d n
          (fun i =>
            (complexMinkowskiToDotLinearEquiv d).symm
              (sourceComplexPad d n r hrD A i)) a
    rw [hv]
    simp [embedLinear, sourceCoefficientEval, hpad, map_sum]
  calc
    Module.finrank ℂ
        (LinearMap.range
          (sourceCoefficientEval d n
            (fun i =>
              (complexMinkowskiToDotLinearEquiv d).symm
                (sourceComplexPad d n r hrD A i))))
        ≤ Module.finrank ℂ (LinearMap.range embedLinear) :=
          Submodule.finrank_mono hrange
    _ ≤ Module.finrank ℂ (Fin r → ℂ) :=
          LinearMap.finrank_range_le embedLinear
    _ = r := by simp

/-- Every algebraic source Gram point has a same-Gram source representative
whose coefficient span dimension equals the ordinary Gram rank. -/
theorem sourceComplexGramVariety_exists_adaptedSourceRepresentative
    (d n : ℕ)
    {G : Fin n → Fin n → ℂ}
    (hG : G ∈ sourceComplexGramVariety d n) :
    ∃ z : Fin n → Fin (d + 1) → ℂ,
      sourceMinkowskiGram d n z = G ∧
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) =
        sourceGramMatrixRank n G := by
  classical
  let r := sourceGramMatrixRank n G
  have hGsym : G ∈ sourceSymmetricMatrixSpace n :=
    sourceComplexGramVariety_subset_sourceSymmetricMatrixSpace d n hG
  have hr_exact : G ∈ sourceSymmetricRankExactStratum n r := by
    refine ⟨hGsym, ?_⟩
    have hM : (Matrix.of fun i j : Fin n => G i j) = G := by
      ext i j
      rfl
    simp [r, sourceGramMatrixRank, hM]
  have hrD : r ≤ d + 1 :=
    sourceGramMatrixRank_le_spacetime_of_mem_sourceComplexGramVariety d n hG
  rcases exists_fullRank_sourceComplexDotGram_of_rankExact
      (m := n) (r := r) hr_exact with
    ⟨A, _hA_full, hA_gram⟩
  let Apad : Fin n → Fin (d + 1) → ℂ := sourceComplexPad d n r hrD A
  let z : Fin n → Fin (d + 1) → ℂ :=
    fun i => (complexMinkowskiToDotLinearEquiv d).symm (Apad i)
  have hzGram : sourceMinkowskiGram d n z = G := by
    rw [sourceMinkowskiGram_eq_dotGram_after_equiv]
    have hrow :
        (fun i =>
          complexMinkowskiToDotLinearEquiv d
            ((complexMinkowskiToDotLinearEquiv d).symm (Apad i))) = Apad := by
      ext i μ
      exact congrFun
        ((complexMinkowskiToDotLinearEquiv d).apply_symm_apply (Apad i)) μ
    rw [hrow]
    rw [show sourceComplexDotGram (d + 1) n Apad =
        sourceComplexDotGram r n A by
      simpa [Apad] using sourceComplexDotGram_padded_eq d n r hrD A]
    exact hA_gram
  have hspan_le :
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) ≤ r := by
    simpa [z, Apad] using
      finrank_sourceCoefficientEval_range_le_of_paddedDot d n r hrD A
  have hrank_eq :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = r := by
    simp [hzGram, r]
  have hrank_le_span :
      r ≤ Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) := by
    simpa [hrank_eq] using
      sourceGramMatrixRank_le_finrank_sourceCoefficientEval_range d n z
  exact ⟨z, hzGram, by
    simpa [r] using le_antisymm hspan_le hrank_le_span⟩

/-- In strict oriented low rank, the adapted ordinary-Gram representative can
be chosen to realize the original full oriented invariant. -/
theorem sourceOriented_lowRank_exists_adaptedRepresentative
    (d n : ℕ)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hlow : ¬ SourceOrientedMaxRankAt d n G0) :
    ∃ z0 : Fin n → Fin (d + 1) → ℂ,
      sourceOrientedMinkowskiInvariant d n z0 = G0 ∧
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z0)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n z0) := by
  classical
  rcases hG0 with ⟨zRaw, rfl⟩
  have hraw_low :
      sourceGramMatrixRank n (sourceMinkowskiGram d n zRaw) < d + 1 :=
    sourceOriented_notMaxRank_sourceGramMatrixRank_lt_fullFrame
      d n zRaw hlow
  have hGvar :
      sourceMinkowskiGram d n zRaw ∈ sourceComplexGramVariety d n :=
    ⟨zRaw, rfl⟩
  rcases sourceComplexGramVariety_exists_adaptedSourceRepresentative
      (d := d) (n := n) hGvar with
    ⟨z0, hz0Gram, hz0span⟩
  have hsame :
      sourceOrientedMinkowskiInvariant d n zRaw =
        sourceOrientedMinkowskiInvariant d n z0 :=
    sourceOrientedMinkowskiInvariant_eq_of_sameGram_rank_lt
      d n (z := zRaw) (w := z0) hz0Gram.symm hraw_low
  exact ⟨z0, hsame.symm, by simpa [hz0Gram] using hz0span⟩

end BHW
