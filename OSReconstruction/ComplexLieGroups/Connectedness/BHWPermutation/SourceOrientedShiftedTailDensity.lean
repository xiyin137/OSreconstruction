import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalImage
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedTailSmallRealization

/-!
# Density support for shifted residual-tail max rank

This file starts the finite-dimensional density support needed by the
rank-deficient residual-polydisc producer.  It records the rank bound for the
shifted-tail Gram map and the selected-minor criterion for shifted-tail
max-rank.  The remaining density theorem is the polynomial-line argument
showing that the selected-minor nonvanishing locus is dense in every open
parameter neighborhood.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Product-coordinate topology on shifted-tail oriented data. -/
instance instTopologicalSpaceSourceShiftedTailOrientedData
    (d r m : ℕ)
    (hrD : r < d + 1) :
    TopologicalSpace (SourceShiftedTailOrientedData d r hrD m) :=
  TopologicalSpace.induced
    (fun T : SourceShiftedTailOrientedData d r hrD m => (T.gram, T.det))
    inferInstance

/-- Canonical shifted-tail template whose first maximal selected rows are the
coordinate basis vectors and whose remaining rows are zero. -/
def sourceShiftedTailFullRankTemplate
    (d r m : ℕ)
    (_hrD : r < d + 1) :
    Fin m → Fin (d + 1 - r) → ℂ :=
  fun u μ => if u.val = μ.val then 1 else 0

@[simp]
theorem sourceShiftedTailFullRankTemplate_selected_apply
    (d r m : ℕ)
    (hrD : r < d + 1)
    (a : Fin (min (d + 1 - r) m))
    (μ : Fin (d + 1 - r)) :
    sourceShiftedTailFullRankTemplate d r m hrD
        (Fin.castLE (min_le_right (d + 1 - r) m) a) μ =
      if μ = Fin.castLE (min_le_left (d + 1 - r) m) a then 1 else 0 := by
  by_cases hμ : μ = Fin.castLE (min_le_left (d + 1 - r) m) a
  · subst μ
    simp [sourceShiftedTailFullRankTemplate]
  · have hval : a.val ≠ μ.val := by
      intro h
      apply hμ
      exact Fin.ext h.symm
    simp [sourceShiftedTailFullRankTemplate, hval, hμ]

theorem sourceShiftedTailFullRankTemplate_selectedGram
    (d r m : ℕ)
    (hrD : r < d + 1) :
    (fun a b : Fin (min (d + 1 - r) m) =>
      sourceShiftedTailGram d r hrD m
        (sourceShiftedTailFullRankTemplate d r m hrD)
        (Fin.castLE (min_le_right (d + 1 - r) m) a)
        (Fin.castLE (min_le_right (d + 1 - r) m) b)) =
      Matrix.diagonal (fun a =>
        (MinkowskiSpace.metricSignature d
          (finSourceTail (Nat.le_of_lt hrD)
            (Fin.castLE (min_le_left (d + 1 - r) m) a)) : ℂ)) := by
  funext a b
  rw [sourceShiftedTailGram_apply,
    sourceVectorMinkowskiInner_sourceTailEmbed_tail]
  by_cases hab : a = b
  · subst b
    rw [Matrix.diagonal_apply_eq]
    rw [Finset.sum_eq_single (Fin.castLE (min_le_left (d + 1 - r) m) a)]
    · simp
    · intro μ _hμ hμa
      have hne : μ ≠ Fin.castLE (min_le_left (d + 1 - r) m) a := hμa
      simp [hne]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  · rw [Matrix.diagonal_apply_ne _ hab]
    rw [Finset.sum_eq_zero]
    intro μ _hμ
    by_cases hμa : μ = Fin.castLE (min_le_left (d + 1 - r) m) a
    · subst μ
      have hne : Fin.castLE (min_le_left (d + 1 - r) m) a ≠
          Fin.castLE (min_le_left (d + 1 - r) m) b := by
        intro h
        exact hab (Fin.castLE_injective _ h)
      simp [hne]
    · simp [hμa]

/-- The selected shifted Gram block of the canonical template is invertible. -/
theorem sourceShiftedTailFullRankTemplate_selectedGram_det_ne_zero
    (d r m : ℕ)
    (hrD : r < d + 1) :
    Matrix.det (fun a b : Fin (min (d + 1 - r) m) =>
      sourceShiftedTailGram d r hrD m
        (sourceShiftedTailFullRankTemplate d r m hrD)
        (Fin.castLE (min_le_right (d + 1 - r) m) a)
        (Fin.castLE (min_le_right (d + 1 - r) m) b)) ≠ 0 := by
  rw [sourceShiftedTailFullRankTemplate_selectedGram]
  rw [Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro a _ha
  by_cases hzero :
      finSourceTail (Nat.le_of_lt hrD)
        (Fin.castLE (min_le_left (d + 1 - r) m) a) =
          (0 : Fin (d + 1))
  · simp [MinkowskiSpace.metricSignature, hzero]
  · simp [MinkowskiSpace.metricSignature, hzero]

/-- The selected shifted Gram determinant along the affine line from `q` to
the canonical full-rank template, as a one-variable polynomial. -/
noncomputable def sourceShiftedTailSelectedGramLinePolynomial
    (d r m : ℕ)
    (hrD : r < d + 1)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    Polynomial ℂ :=
  Matrix.det (fun a b : Fin (min (d + 1 - r) m) =>
    ∑ μ : Fin (d + 1 - r),
      Polynomial.C
          (MinkowskiSpace.metricSignature d
            (finSourceTail (Nat.le_of_lt hrD) μ) : ℂ) *
        (Polynomial.C (q (Fin.castLE (min_le_right (d + 1 - r) m) a) μ) +
          Polynomial.X *
            Polynomial.C
              (sourceShiftedTailFullRankTemplate d r m hrD
                  (Fin.castLE (min_le_right (d + 1 - r) m) a) μ -
                q (Fin.castLE (min_le_right (d + 1 - r) m) a) μ)) *
        (Polynomial.C (q (Fin.castLE (min_le_right (d + 1 - r) m) b) μ) +
          Polynomial.X *
            Polynomial.C
              (sourceShiftedTailFullRankTemplate d r m hrD
                  (Fin.castLE (min_le_right (d + 1 - r) m) b) μ -
                q (Fin.castLE (min_le_right (d + 1 - r) m) b) μ)))

theorem sourceShiftedTailSelectedGramLinePolynomial_eval
    (d r m : ℕ)
    (hrD : r < d + 1)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (t : ℂ) :
    (sourceShiftedTailSelectedGramLinePolynomial d r m hrD q).eval t =
      Matrix.det (fun a b : Fin (min (d + 1 - r) m) =>
        sourceShiftedTailGram d r hrD m
          (q + t • (sourceShiftedTailFullRankTemplate d r m hrD - q))
          (Fin.castLE (min_le_right (d + 1 - r) m) a)
          (Fin.castLE (min_le_right (d + 1 - r) m) b)) := by
  unfold sourceShiftedTailSelectedGramLinePolynomial
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  funext a b
  change Polynomial.eval t _ = _
  simp only [sourceShiftedTailGram,
    sourceVectorMinkowskiInner_sourceTailEmbed_tail, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- The selected-minor line polynomial is not the zero polynomial: at `t = 1`
it is the selected Gram determinant of the canonical template. -/
theorem sourceShiftedTailSelectedGramLinePolynomial_ne_zero
    (d r m : ℕ)
    (hrD : r < d + 1)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    sourceShiftedTailSelectedGramLinePolynomial d r m hrD q ≠ 0 := by
  intro hzero
  have hEval :=
    congrArg (fun p : Polynomial ℂ => p.eval (1 : ℂ)) hzero
  change
    (sourceShiftedTailSelectedGramLinePolynomial d r m hrD q).eval (1 : ℂ) =
      (0 : Polynomial ℂ).eval (1 : ℂ) at hEval
  rw [sourceShiftedTailSelectedGramLinePolynomial_eval] at hEval
  simp only [Polynomial.eval_zero] at hEval
  have hline :
      q + (1 : ℂ) •
          (sourceShiftedTailFullRankTemplate d r m hrD - q) =
        sourceShiftedTailFullRankTemplate d r m hrD := by
    ext u μ
    simp
  rw [hline] at hEval
  exact sourceShiftedTailFullRankTemplate_selectedGram_det_ne_zero d r m hrD hEval

/-- The complement of the finite root set of the selected-minor line
polynomial is dense in the complex line. -/
theorem dense_compl_sourceShiftedTailSelectedGramLineRoots
    (d r m : ℕ)
    (hrD : r < d + 1)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    Dense
      ((sourceShiftedTailSelectedGramLinePolynomial d r m hrD q).rootSet ℂ)ᶜ := by
  have hfinite :
      ((sourceShiftedTailSelectedGramLinePolynomial d r m hrD q).rootSet ℂ).Finite :=
    Polynomial.rootSet_finite
      (sourceShiftedTailSelectedGramLinePolynomial d r m hrD q) ℂ
  simpa [Set.diff_eq] using (dense_univ.diff_finite hfinite)

/-- The shifted-tail oriented invariant is continuous in finite tail
coordinates. -/
theorem continuous_sourceShiftedTailOrientedInvariant
    (d r m : ℕ)
    (hrD : r < d + 1) :
    Continuous (sourceShiftedTailOrientedInvariant d r hrD m) := by
  rw [continuous_induced_rng]
  have hg := continuous_sourceShiftedTailGram d r m hrD
  have hdet : Continuous (fun q : Fin m → Fin (d + 1 - r) → ℂ =>
      fun lam : Fin (d + 1 - r) ↪ Fin m =>
        Matrix.det (fun u μ : Fin (d + 1 - r) => q (lam u) μ)) := by
    apply continuous_pi
    intro lam
    exact (continuous_matrix fun u μ =>
      (continuous_apply μ).comp (continuous_apply (lam u))).matrix_det
  change Continuous (fun q : Fin m → Fin (d + 1 - r) → ℂ =>
    (sourceShiftedTailGram d r hrD m q,
      fun lam : Fin (d + 1 - r) ↪ Fin m =>
        Matrix.det (fun u μ : Fin (d + 1 - r) => q (lam u) μ)))
  exact Continuous.prodMk hg hdet

/-- The shifted-tail Gram matrix has rank at most the residual spacetime
dimension and at most the number of tail labels. -/
theorem sourceShiftedTailGram_rank_le_max
    (d r m : ℕ)
    (hrD : r < d + 1)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    sourceGramMatrixRank m (sourceShiftedTailGram d r hrD m q) ≤
      min (d + 1 - r) m := by
  let N := sourceShiftedTailMetricNormalization d r hrD
  let T := sourceShiftedTailOrientedInvariant d r hrD m q
  have hTvar : T ∈ sourceShiftedTailOrientedVariety d r hrD m := ⟨q, rfl⟩
  have hEvar :
      sourceShiftedTailDataToEuclidean d r m hrD N T ∈
        sourceTailOrientedVariety (d + 1 - r) m := by
    exact
      (sourceShiftedTailVariety_toEuclidean_iff d r m hrD N T).2 hTvar
  have hD :
      sourceGramMatrixRank m (sourceShiftedTailGram d r hrD m q) ≤
        d + 1 - r := by
    have h :=
      sourceTailOrientedVariety_rank_le (d + 1 - r) m hEvar
    simpa [sourceGramMatrixRank, sourceShiftedTailDataToEuclidean, T,
      sourceShiftedTailOrientedInvariant] using h
  have hm :
      sourceGramMatrixRank m (sourceShiftedTailGram d r hrD m q) ≤ m := by
    simpa [sourceGramMatrixRank] using
      (Matrix.rank_le_card_height (sourceShiftedTailGram d r hrD m q))
  exact le_min hD hm

/-- A nonzero selected maximal shifted-tail Gram minor forces shifted-tail
max rank. -/
theorem sourceShiftedTail_maxRank_of_selectedGram_det_ne_zero
    (d r m : ℕ)
    (hrD : r < d + 1)
    {q : Fin m → Fin (d + 1 - r) → ℂ}
    (hdet :
      Matrix.det (fun a b : Fin (min (d + 1 - r) m) =>
        sourceShiftedTailGram d r hrD m q
          (Fin.castLE (min_le_right (d + 1 - r) m) a)
          (Fin.castLE (min_le_right (d + 1 - r) m) b)) ≠ 0) :
    SourceShiftedTailOrientedMaxRankAt d r hrD m
      (sourceShiftedTailOrientedInvariant d r hrD m q) := by
  let k := min (d + 1 - r) m
  let G : Matrix (Fin m) (Fin m) ℂ := sourceShiftedTailGram d r hrD m q
  let emb : Fin k → Fin m := Fin.castLE (min_le_right (d + 1 - r) m)
  let B : Matrix (Fin k) (Fin k) ℂ := fun a b => G (emb a) (emb b)
  let R : Matrix (Fin k) (Fin m) ℂ := fun a j => G (emb a) j
  have hdetB : B.det ≠ 0 := by
    simpa [B, G, emb, k] using hdet
  have hB_li : LinearIndependent ℂ B.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdetB
  have hR_li : LinearIndependent ℂ R.row := by
    rw [Fintype.linearIndependent_iff] at hB_li ⊢
    intro coeff hsum a
    have hsumB : (∑ x : Fin k, coeff x • B.row x) = 0 := by
      funext b
      have hrow := congrFun hsum (emb b)
      simpa [R, B, Matrix.row] using hrow
    exact hB_li coeff hsumB a
  have hR_rank : R.rank = k := by
    simpa [Fintype.card_fin] using hR_li.rank_matrix (M := R)
  have hR_le_G : R.rank ≤ G.rank := by
    simpa [R, G, Matrix.submatrix] using
      Matrix.rank_submatrix_le emb (Equiv.refl (Fin m)) G
  have hge : k ≤ sourceGramMatrixRank m (sourceShiftedTailGram d r hrD m q) := by
    simpa [sourceGramMatrixRank, G] using hR_rank.symm ▸ hR_le_G
  have hle :=
    sourceShiftedTailGram_rank_le_max d r m hrD q
  exact le_antisymm hle hge

/-- Shifted-tail max-rank parameters are dense in every open parameter
neighborhood.  The proof perturbs along the affine line to the canonical
full-rank template and avoids the finite root set of the selected Gram
determinant polynomial. -/
theorem sourceShiftedTailOrientedMaxRank_dense_in_parameterOpen
    (d r m : ℕ)
    (hrD : r < d + 1)
    {P : Set (Fin m → Fin (d + 1 - r) → ℂ)}
    (hP_open : IsOpen P) :
    ∀ q ∈ P,
      sourceShiftedTailOrientedInvariant d r hrD m q ∈
        closure
          (sourceShiftedTailOrientedInvariant d r hrD m ''
            {q' | q' ∈ P ∧
              SourceShiftedTailOrientedMaxRankAt d r hrD m
                (sourceShiftedTailOrientedInvariant d r hrD m q')}) := by
  intro q hqP
  let τ : Fin m → Fin (d + 1 - r) → ℂ :=
    sourceShiftedTailFullRankTemplate d r m hrD
  let line : ℂ → Fin m → Fin (d + 1 - r) → ℂ :=
    fun t => q + t • (τ - q)
  let poly : Polynomial ℂ :=
    sourceShiftedTailSelectedGramLinePolynomial d r m hrD q
  let S : Set (Fin m → Fin (d + 1 - r) → ℂ) :=
    {q' | q' ∈ P ∧
      SourceShiftedTailOrientedMaxRankAt d r hrD m
        (sourceShiftedTailOrientedInvariant d r hrD m q')}
  have hline_cont : Continuous line := by
    dsimp [line]
    fun_prop
  have hA_open : IsOpen (line ⁻¹' P) :=
    hP_open.preimage hline_cont
  have h0A : (0 : ℂ) ∈ line ⁻¹' P := by
    dsimp [line, τ]
    simpa using hqP
  have hroots_dense : Dense (poly.rootSet ℂ)ᶜ := by
    simpa [poly] using
      dense_compl_sourceShiftedTailSelectedGramLineRoots d r m hrD q
  have h0_closure :
      (0 : ℂ) ∈ closure ((line ⁻¹' P) ∩ (poly.rootSet ℂ)ᶜ) :=
    (hroots_dense.open_subset_closure_inter hA_open) h0A
  have hmaps : Set.MapsTo line ((line ⁻¹' P) ∩ (poly.rootSet ℂ)ᶜ) S := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    have ht_not_root : t ∉ poly.rootSet ℂ := ht.2
    have hEval_ne : poly.eval t ≠ 0 := by
      intro hEval
      apply ht_not_root
      have hroot_iff :
          t ∈ poly.rootSet ℂ ↔ Polynomial.aeval t poly = 0 := by
        exact Polynomial.mem_rootSet_of_ne
          (sourceShiftedTailSelectedGramLinePolynomial_ne_zero d r m hrD q)
      rw [hroot_iff]
      simpa [poly] using hEval
    have hdet :
        Matrix.det (fun a b : Fin (min (d + 1 - r) m) =>
          sourceShiftedTailGram d r hrD m (line t)
            (Fin.castLE (min_le_right (d + 1 - r) m) a)
            (Fin.castLE (min_le_right (d + 1 - r) m) b)) ≠ 0 := by
      have hEval' := hEval_ne
      change
        (sourceShiftedTailSelectedGramLinePolynomial d r m hrD q).eval t ≠ 0
        at hEval'
      rw [sourceShiftedTailSelectedGramLinePolynomial_eval] at hEval'
      simpa [line, τ] using hEval'
    exact sourceShiftedTail_maxRank_of_selectedGram_det_ne_zero d r m hrD hdet
  have hF_cont :
      Continuous (fun t =>
        sourceShiftedTailOrientedInvariant d r hrD m (line t)) :=
    (continuous_sourceShiftedTailOrientedInvariant d r m hrD).comp hline_cont
  have hmapsF : Set.MapsTo
      (fun t => sourceShiftedTailOrientedInvariant d r hrD m (line t))
      ((line ⁻¹' P) ∩ (poly.rootSet ℂ)ᶜ)
      (sourceShiftedTailOrientedInvariant d r hrD m '' S) := by
    intro t ht
    exact ⟨line t, hmaps ht, rfl⟩
  have hclose := map_mem_closure hF_cont h0_closure hmapsF
  simpa [line, τ, S] using hclose

/-- Shifted-tail max-rank parameters are dense in every open parameter
domain.  This is the parameter-space version of
`sourceShiftedTailOrientedMaxRank_dense_in_parameterOpen`; it uses the same
selected-minor polynomial line but does not push forward by the invariant
map. -/
theorem sourceShiftedTailOrientedMaxRank_parameter_dense_in_open
    (d r m : ℕ)
    (hrD : r < d + 1)
    {P : Set (Fin m → Fin (d + 1 - r) → ℂ)}
    (hP_open : IsOpen P) :
    ∀ q ∈ P,
      q ∈ closure
        {q' | q' ∈ P ∧
          SourceShiftedTailOrientedMaxRankAt d r hrD m
            (sourceShiftedTailOrientedInvariant d r hrD m q')} := by
  intro q hqP
  let τ : Fin m → Fin (d + 1 - r) → ℂ :=
    sourceShiftedTailFullRankTemplate d r m hrD
  let line : ℂ → Fin m → Fin (d + 1 - r) → ℂ :=
    fun t => q + t • (τ - q)
  let poly : Polynomial ℂ :=
    sourceShiftedTailSelectedGramLinePolynomial d r m hrD q
  let S : Set (Fin m → Fin (d + 1 - r) → ℂ) :=
    {q' | q' ∈ P ∧
      SourceShiftedTailOrientedMaxRankAt d r hrD m
        (sourceShiftedTailOrientedInvariant d r hrD m q')}
  have hline_cont : Continuous line := by
    dsimp [line]
    fun_prop
  have hA_open : IsOpen (line ⁻¹' P) :=
    hP_open.preimage hline_cont
  have h0A : (0 : ℂ) ∈ line ⁻¹' P := by
    dsimp [line, τ]
    simpa using hqP
  have hroots_dense : Dense (poly.rootSet ℂ)ᶜ := by
    simpa [poly] using
      dense_compl_sourceShiftedTailSelectedGramLineRoots d r m hrD q
  have h0_closure :
      (0 : ℂ) ∈ closure ((line ⁻¹' P) ∩ (poly.rootSet ℂ)ᶜ) :=
    (hroots_dense.open_subset_closure_inter hA_open) h0A
  have hmaps : Set.MapsTo line ((line ⁻¹' P) ∩ (poly.rootSet ℂ)ᶜ) S := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    have ht_not_root : t ∉ poly.rootSet ℂ := ht.2
    have hEval_ne : poly.eval t ≠ 0 := by
      intro hEval
      apply ht_not_root
      have hroot_iff :
          t ∈ poly.rootSet ℂ ↔ Polynomial.aeval t poly = 0 := by
        exact Polynomial.mem_rootSet_of_ne
          (sourceShiftedTailSelectedGramLinePolynomial_ne_zero d r m hrD q)
      rw [hroot_iff]
      simpa [poly] using hEval
    have hdet :
        Matrix.det (fun a b : Fin (min (d + 1 - r) m) =>
          sourceShiftedTailGram d r hrD m (line t)
            (Fin.castLE (min_le_right (d + 1 - r) m) a)
            (Fin.castLE (min_le_right (d + 1 - r) m) b)) ≠ 0 := by
      have hEval' := hEval_ne
      change
        (sourceShiftedTailSelectedGramLinePolynomial d r m hrD q).eval t ≠ 0
        at hEval'
      rw [sourceShiftedTailSelectedGramLinePolynomial_eval] at hEval'
      simpa [line, τ] using hEval'
    exact sourceShiftedTail_maxRank_of_selectedGram_det_ne_zero d r m hrD hdet
  have hclose := map_mem_closure hline_cont h0_closure hmaps
  simpa [line, τ, S] using hclose

end BHW
