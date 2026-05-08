import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWTubeCoefficient

/-!
# Extended-tube adapted representatives

This file packages the checked selected-projection residual frame with the
Hall-Wightman coefficient-freedom theorem.  The result replaces an arbitrary
extended-tube source tuple by a same-Gram extended-tube tuple whose source span
dimension equals the scalar Gram rank.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Hall-Wightman Lemma-3 adapted representative inside the ordinary extended
tube.  It keeps the scalar source Gram matrix fixed and makes the source-vector
span dimension equal to the scalar Gram rank. -/
theorem hwLemma3_extendedTube_adaptedRankRepresentative
    [NeZero d]
    (hd : 2 ≤ d)
    {n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n) :
    ∃ ζ0 : Fin n → Fin (d + 1) → ℂ,
      ζ0 ∈ ExtendedTube d n ∧
      sourceMinkowskiGram d n ζ0 = sourceMinkowskiGram d n z0 ∧
      Module.finrank ℂ
        (LinearMap.range (sourceCoefficientEval d n ζ0)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n z0) := by
  classical
  by_cases hn : n = 0
  · subst hn
    refine ⟨z0, hz0, rfl, ?_⟩
    have hmap0 : sourceCoefficientEval d 0 z0 = 0 := by
      ext a μ
      simp [sourceCoefficientEval]
    have hrange0 :
        LinearMap.range (sourceCoefficientEval d 0 z0) = ⊥ := by
      rw [hmap0]
      simp
    have hfin0 :
        Module.finrank ℂ
          (LinearMap.range (sourceCoefficientEval d 0 z0)) = 0 := by
      rw [hrange0]
      simp
    have hrank0 :
        sourceGramMatrixRank 0 (sourceMinkowskiGram d 0 z0) = 0 := by
      have hle :=
        Matrix.rank_le_width (A := sourceMinkowskiGram d 0 z0)
      exact Nat.eq_zero_of_le_zero (by simpa [sourceGramMatrixRank] using hle)
    rw [hfin0, hrank0]
  · haveI : NeZero n := ⟨hn⟩
    let G : Fin n → Fin n → ℂ := sourceMinkowskiGram d n z0
    let r : ℕ := sourceGramMatrixRank n G
    have hr_pos : 0 < r := by
      simpa [r, G] using
        sourceGramMatrixRank_pos_of_mem_extendedTube
          (d := d) hd (n := n) hz0
    have hGsym : G ∈ sourceSymmetricMatrixSpace n := by
      intro i j
      exact sourceMinkowskiGram_symm d n z0 i j
    have hrank : (Matrix.of fun i j : Fin n => G i j).rank = r := by
      have hM : (Matrix.of fun i j : Fin n => G i j) = G := by
        ext i j
        rfl
      rw [hM]
      simp [sourceGramMatrixRank, r]
    rcases exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank
        hGsym hrank with
      ⟨I, _hI_inj, hminor⟩
    let ξ : Fin n → Fin (d + 1) → ℂ :=
      hwLemma3_selectedProjection d n r I G z0
    rcases hwLemma3_selectedResidual_isotropicFrameData
        d n r I z0 (by simp [G, r]) (by simpa [G] using hminor) with
      ⟨s, q, a, _hq_li, hq_pair, hq_orth, _hres_coeff, hz0_decomp⟩
    have hdecomp_fun :
        (fun i => ξ i + ∑ c : Fin s, a i c • q c) = z0 := by
      ext i μ
      simpa [ξ, G, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun (congrFun hz0_decomp i) μ
    have hendpoint :
        (fun i => ξ i + ∑ c : Fin s, a i c • q c) ∈
          ExtendedTube d n := by
      rw [hdecomp_fun]
      exact hz0
    rcases hw_isotropicFrame_allCoefficients_mem_extendedTube
        (d := d) hd hendpoint hq_pair hq_orth with
      ⟨hbase_mem, _hall_coefficients⟩
    refine ⟨ξ, hbase_mem, ?_, ?_⟩
    · ext i j
      simpa [ξ, G, sourceMinkowskiGram_apply_eq_complexInner] using
        hwLemma3_selectedProjection_gram_eq
          d n r I z0 (by simp [G, r]) (by simpa [G] using hminor) i j
    · simpa [ξ, G, r] using
        hwLemma3_selectedProjection_span_finrank_eq_rank
          d n r I z0 (by simp [G, r]) (by simpa [G] using hminor)

end BHW
