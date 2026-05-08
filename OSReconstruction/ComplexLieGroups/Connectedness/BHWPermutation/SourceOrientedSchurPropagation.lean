import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameMaxRankProducer
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurResidual

/-!
# Source-oriented Schur determinant propagation

This companion file isolates the oriented determinant propagation theorem that
remains after the Schur residual packet has reduced the normal-form
reconstruction to head-tail determinant calibration.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- For an actual source tuple, invertibility of the selected Schur head Gram
block implies linear independence of the selected head source rows. -/
theorem sourceHeadRows_linearIndependent_of_schurHeadBlock_isUnit
    (d n r : ℕ)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hA :
      IsUnit
        (sourceOrientedSchurHeadBlock n r hrn
          (sourceOrientedMinkowskiInvariant d n z)).det) :
    LinearIndependent ℂ (fun a : Fin r => z (finSourceHead hrn a)) := by
  let A :=
    sourceOrientedSchurHeadBlock n r hrn
      (sourceOrientedMinkowskiInvariant d n z)
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum a
  let row : Matrix (Fin 1) (Fin r) ℂ := fun _ b => coeff b
  have hrowA : row * A = 0 := by
    ext _ b
    have hinner :
        sourceVectorMinkowskiInner d
            (∑ c : Fin r, coeff c • z (finSourceHead hrn c))
            (z (finSourceHead hrn b)) = 0 := by
      rw [hsum]
      simp [sourceVectorMinkowskiInner]
    calc
      (row * A) (0 : Fin 1) b =
          ∑ c : Fin r, coeff c *
            sourceVectorMinkowskiInner d
              (z (finSourceHead hrn c)) (z (finSourceHead hrn b)) := by
        simp [Matrix.mul_apply, row, A, sourceOrientedSchurHeadBlock,
          sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram,
          sourceMinkowskiGram, sourceVectorMinkowskiInner]
      _ = sourceVectorMinkowskiInner d
            (∑ c : Fin r, coeff c • z (finSourceHead hrn c))
            (z (finSourceHead hrn b)) := by
        rw [show
          (∑ c : Fin r, coeff c • z (finSourceHead hrn c)) =
            (fun μ =>
              ∑ c : Fin r, coeff c * z (finSourceHead hrn c) μ) by
            ext μ
            simp [Pi.smul_apply, smul_eq_mul]]
        rw [sourceVectorMinkowskiInner_sum_left]
        simp [sourceVectorMinkowskiInner_smul_left]
      _ = 0 := hinner
  have hrow : row = 0 := by
    have hcancel : row * A * A⁻¹ = row :=
      Matrix.mul_nonsing_inv_cancel_right (A := A) row (by simpa [A] using hA)
    rw [← hcancel, hrowA]
    simp
  have hentry := congrFun (congrFun hrow (0 : Fin 1)) a
  simpa [row] using hentry

/-- Finite basis extension with prescribed head rows.  If the selected head
rows are linearly independent and all source rows span spacetime, then some
ordered full frame containing the whole head block and `d + 1 - r` tail rows
has nonzero determinant. -/
theorem exists_headTail_fullFrameDet_ne_zero_of_headRows_linearIndependent_span_top
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hheadLI :
      LinearIndependent ℂ (fun a : Fin r => z (finSourceHead hrn a)))
    (hspan :
      Submodule.span ℂ (Set.range z) = ⊤) :
    ∃ lam : Fin (d + 1 - r) ↪ Fin (n - r),
      sourceFullFrameDet d n
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) z ≠ 0 := by
  let V := Fin (d + 1) → ℂ
  let U : Submodule ℂ V :=
    Submodule.span ℂ (Set.range (fun a : Fin r => z (finSourceHead hrn a)))
  let q : V →ₗ[ℂ] V ⧸ U := U.mkQ
  let tailQ : Fin (n - r) → V ⧸ U :=
    fun u => q (z (finSourceTail hrn u))
  have htail_span :
      Submodule.span ℂ (Set.range tailQ) = ⊤ := by
    apply eq_top_iff.mpr
    intro y _hy
    rcases U.mkQ_surjective y with ⟨x, rfl⟩
    have hx : x ∈ Submodule.span ℂ (Set.range z) := by
      rw [hspan]
      trivial
    refine Submodule.span_induction ?base ?zero ?add ?smul hx
    · rintro v ⟨i, rfl⟩
      rcases finSourceHead_tail_cases hrn i with ⟨a, hi⟩ | ⟨u, hi⟩
      · have hqzero : q (z i) = 0 := by
          rw [hi]
          rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
          exact Submodule.subset_span ⟨a, rfl⟩
        rw [hqzero]
        exact Submodule.zero_mem _
      · rw [hi]
        exact Submodule.subset_span ⟨u, rfl⟩
    · exact Submodule.zero_mem _
    · intro x y _hx _hy hxq hyq
      simpa using Submodule.add_mem _ hxq hyq
    · intro c x _hx hxq
      simpa using Submodule.smul_mem _ c hxq
  have hUfin : Module.finrank ℂ U = r := by
    have hcard :=
      (linearIndependent_iff_card_eq_finrank_span.mp hheadLI)
    simpa [U] using hcard.symm
  have hVfin : Module.finrank ℂ V = d + 1 := by
    simp [V]
  have hqfin : Module.finrank ℂ (V ⧸ U) = d + 1 - r := by
    have hsum := U.finrank_quotient_add_finrank
    have hsum' :
        Module.finrank ℂ (V ⧸ U) + r = d + 1 := by
      simpa [V, hUfin, hVfin] using hsum
    omega
  have htail_fin :
      Module.finrank ℂ (Submodule.span ℂ (Set.range tailQ)) =
        d + 1 - r := by
    rw [htail_span]
    simpa using hqfin
  rcases Submodule.exists_fun_fin_finrank_span_eq
      (K := ℂ) (s := Set.range tailQ) with
    ⟨f, hf_mem, _hf_span, hf_li⟩
  let e :
      Fin (d + 1 - r) ≃
        Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range tailQ))) :=
    finCongr htail_fin.symm
  let lamFun : Fin (d + 1 - r) → Fin (n - r) :=
    fun μ => Classical.choose (hf_mem (e μ))
  have hlam_spec (μ : Fin (d + 1 - r)) :
      tailQ (lamFun μ) = f (e μ) :=
    Classical.choose_spec (hf_mem (e μ))
  have hlam_inj : Function.Injective lamFun := by
    intro μ ν hμν
    apply e.injective
    apply hf_li.injective
    calc
      f (e μ) = tailQ (lamFun μ) := (hlam_spec μ).symm
      _ = tailQ (lamFun ν) := by rw [hμν]
      _ = f (e ν) := hlam_spec ν
  let lam : Fin (d + 1 - r) ↪ Fin (n - r) :=
    { toFun := lamFun
      inj' := hlam_inj }
  have htailLI :
      LinearIndependent ℂ (fun μ : Fin (d + 1 - r) =>
        q (z (finSourceTail hrn (lam μ)))) := by
    have hcomp : LinearIndependent ℂ (fun μ : Fin (d + 1 - r) => f (e μ)) :=
      hf_li.comp e e.injective
    convert hcomp using 1
    ext μ
    exact hlam_spec μ
  let headInU : Fin r → U :=
    fun a => ⟨z (finSourceHead hrn a), Submodule.subset_span ⟨a, rfl⟩⟩
  have hheadLI_U : LinearIndependent ℂ headInU := by
    apply LinearIndependent.of_comp U.subtype
    simpa [headInU, Function.comp_def] using hheadLI
  let tailSel : Fin (d + 1 - r) → V :=
    fun μ => z (finSourceTail hrn (lam μ))
  have hsumLI :
      LinearIndependent ℂ
        (Sum.elim (fun a : Fin r => (headInU a : V)) tailSel) :=
    LinearIndependent.sumElim_of_quotient hheadLI_U tailSel (by
      simpa [tailSel, q] using htailLI)
  have hframeLI :
      LinearIndependent ℂ (fun k : Fin (d + 1) =>
        z (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam k)) := by
    let eHT := sourceHeadTailSumEquiv d r hrD
    have hcomp :
        LinearIndependent ℂ
          (fun k : Fin (d + 1) =>
            Sum.elim (fun a : Fin r => (headInU a : V)) tailSel
              (eHT.symm k)) :=
      hsumLI.comp eHT.symm eHT.symm.injective
    convert hcomp using 1
    ext k μ
    cases hsplit : eHT.symm k with
    | inl a =>
        have hk : k = eHT (Sum.inl a) := by
          have h := congrArg eHT hsplit
          simpa [eHT] using h
        subst hk
        simp [eHT, headInU, tailSel,
          sourceFullFrameEmbeddingOfHeadTail_head]
    | inr u =>
        have hk : k = eHT (Sum.inr u) := by
          have h := congrArg eHT hsplit
          simpa [eHT] using h
        subst hk
        simp [eHT, headInU, tailSel,
          sourceFullFrameEmbeddingOfHeadTail_tail]
  refine ⟨lam, ?_⟩
  let η := sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam
  let M := sourceFullFrameMatrix d n η z
  have hrows : LinearIndependent ℂ M.row := by
    simpa [M, η, sourceFullFrameMatrix, Matrix.row] using hframeLI
  have hMunit : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.1 hrows
  have hdetunit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hMunit
  simpa [M, η, sourceFullFrameDet] using hdetunit.ne_zero

/-- Hard-range low branch for head-tail propagation: if the selected head Gram
block is invertible and all selected head-tail full-frame determinants vanish,
then the oriented source point is not max-rank.  The proof is the contrapositive
finite basis-extension argument. -/
theorem sourceOrientedGramVariety_notMaxRank_of_headTailDet_eq_zero
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hA : IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det)
    (hzero :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) = 0) :
    ¬ SourceOrientedMaxRankAt d n G := by
  intro hmax
  rcases hG with ⟨z, rfl⟩
  have hheadLI :
      LinearIndependent ℂ (fun a : Fin r => z (finSourceHead hrn a)) :=
    sourceHeadRows_linearIndependent_of_schurHeadBlock_isUnit
      d n r hrn z hA
  rcases exists_selectedDetNonzero_of_sourceOrientedMaxRankAt
      hn (by exact ⟨z, rfl⟩) hmax with
    ⟨ι, hdetι⟩
  have hMdet : (sourceFullFrameMatrix d n ι z).det ≠ 0 := by
    simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det,
      sourceFullFrameDet] using hdetι
  have hspan_selected :
      Submodule.span ℂ
          (Set.range (fun a : Fin (d + 1) =>
            sourceFullFrameMatrix d n ι z a)) = ⊤ :=
    sourceFullFrameMatrix_rows_span_top_of_det_ne_zero d n ι z hMdet
  have hspan_all :
      Submodule.span ℂ (Set.range z) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hspan_selected]
    apply Submodule.span_mono (R := ℂ)
    rintro v ⟨a, rfl⟩
    exact ⟨ι a, rfl⟩
  rcases
      exists_headTail_fullFrameDet_ne_zero_of_headRows_linearIndependent_span_top
        d n r hrD hrn z hheadLI hspan_all with
    ⟨lam, hdet_lam⟩
  exact hdet_lam (by
    simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det,
      sourceFullFrameDet] using hzero lam)

/-- On the oriented source variety, a point outside the max-rank locus has no
nonzero ordered full-frame determinant coordinate. -/
theorem sourceOrientedGramVariety_det_eq_zero_of_not_maxRank
    (d n : ℕ)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hlow : ¬ SourceOrientedMaxRankAt d n G) :
    G.det = 0 := by
  funext ι
  by_contra hdet
  exact hlow (sourceOrientedMaxRankAt_of_selectedDet_ne_zero d n ι hG hdet)

/-- If two source-variety points have the same ordinary Gram coordinate and
one is outside the max-rank locus, then both determinant coordinate families
vanish, hence agree. -/
theorem sourceOrientedGramVariety_det_eq_of_gram_eq_of_not_maxRank
    (d n : ℕ)
    {G H : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hH : H ∈ sourceOrientedGramVariety d n)
    (hgram : H.gram = G.gram)
    (hlowG : ¬ SourceOrientedMaxRankAt d n G) :
    H.det = G.det := by
  have hlowH : ¬ SourceOrientedMaxRankAt d n H := by
    intro hHmax
    exact hlowG
      ((sourceOrientedMaxRankAt_iff_of_gram_eq
        (d := d) (n := n) hgram.symm).2 hHmax)
  rw [sourceOrientedGramVariety_det_eq_zero_of_not_maxRank d n hH hlowH,
    sourceOrientedGramVariety_det_eq_zero_of_not_maxRank d n hG hlowG]

/-- Nonzero selected-head-tail branch of the oriented determinant propagation
theorem.  Once one selected `head ∪ lam` full-frame determinant is nonzero, the
checked full-frame chart identity theorem determines all determinant
coordinates from the selected full-frame coordinate and the mixed rows; both
are read from the ordinary Gram coordinate plus the calibrated selected
determinant. -/
theorem sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_exists_nonzero
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G H : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hH : H ∈ sourceOrientedGramVariety d n)
    (hgram : H.gram = G.gram)
    (hheadTail :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam))
    (hNZ : ∃ lam : Fin (d + 1 - r) ↪ Fin (n - r),
      G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) ≠ 0) :
    H.det = G.det := by
  rcases hNZ with ⟨lam, hdetG⟩
  let η := sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam
  have hsel :
      sourceFullFrameOrientedCoordOfSource d n η H =
        sourceFullFrameOrientedCoordOfSource d n η G := by
    ext a b
    · exact congrFun (congrFun hgram (η a)) (η b)
    · exact hheadTail lam
  have hmixed :
      sourceSelectedMixedRows d n η H =
        sourceSelectedMixedRows d n η G := by
    funext k a
    exact congrFun (congrFun hgram k.1) (η a)
  have hHG : H = G :=
    sourceOrientedGramData_eq_of_selectedCoord_eq_mixedRows_eq
      d n η hH hG hdetG hsel hmixed
  rw [hHG]

/-- Checked assembly of the oriented determinant propagation theorem from the
remaining low-rank lemma: if every point with invertible head block and all
selected head-tail determinants zero is non-max-rank, then calibrated
head-tail determinant agreement propagates to all ordered full-frame
determinant coordinates. -/
theorem sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_allZero_notMaxRank
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (hallZero_notMax :
      ∀ {K : SourceOrientedGramData d n},
        K ∈ sourceOrientedGramVariety d n →
        IsUnit (sourceOrientedSchurHeadBlock n r hrn K).det →
        (∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
          K.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) = 0) →
        ¬ SourceOrientedMaxRankAt d n K)
    {G H : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hH : H ∈ sourceOrientedGramVariety d n)
    (hA : IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det)
    (hgram : H.gram = G.gram)
    (hheadTail :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)) :
    H.det = G.det := by
  by_cases hNZ : ∃ lam : Fin (d + 1 - r) ↪ Fin (n - r),
      G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) ≠ 0
  · exact
      sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_exists_nonzero
        d n r hrD hrn hG hH hgram hheadTail hNZ
  · have hzero :
        ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) = 0 := by
      intro lam
      by_contra hne
      exact hNZ ⟨lam, hne⟩
    have hlowG : ¬ SourceOrientedMaxRankAt d n G :=
      hallZero_notMax hG hA hzero
    exact
      sourceOrientedGramVariety_det_eq_of_gram_eq_of_not_maxRank
        d n hG hH hgram hlowG

/-- Hard-range oriented determinant propagation from selected head-tail
determinants.  The nonzero selected head-tail branch is the full-frame chart;
the all-zero branch is the finite basis-extension theorem, which forces both
points outside max-rank and hence all determinant coordinates to vanish. -/
theorem sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G H : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hH : H ∈ sourceOrientedGramVariety d n)
    (hA : IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det)
    (hgram : H.gram = G.gram)
    (hheadTail :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)) :
    H.det = G.det :=
  sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_allZero_notMaxRank
    d n r hrD hrn
    (fun {_K} hK hA hzero =>
      sourceOrientedGramVariety_notMaxRank_of_headTailDet_eq_zero
        d n r hn hrD hrn hK hA hzero)
    hG hH hA hgram hheadTail

/-- Hard-range full-frame Schur determinant reconstruction over the original
oriented source datum. -/
theorem sourceOrientedSchur_fullFrameDet_reconstruct
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    (ι : Fin (d + 1) ↪ Fin n) :
    sourceNormalFullFrameDetFromSchur d n r hrD hrn
        R.headFactor R.L R.tail ι = G.det ι :=
  sourceOrientedSchur_fullFrameDet_reconstruct_of_headTailPropagation
    d n r hrD hrn
    (fun {_G _H} hG hH hA hgram hheadTail =>
      sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq
        d n r hn hrD hrn hG hH hA hgram hheadTail)
    hGvar R ι

/-- Hard-range determinant-coordinate realization for the normal-parameter
Schur tuple. -/
theorem sourceOrientedNormalParameterVector_realizes_schur_det
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead : p.head = R.headFactor)
    (hmixed : p.mixed = R.L)
    (htail :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail = R.tail) :
    (sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn p)).det = G.det :=
  sourceOrientedNormalParameterVector_realizes_schur_det_of_fullFrameReconstruct
    d n r hrD hrn R hhead hmixed htail
    (sourceOrientedSchur_fullFrameDet_reconstruct
      d n r hn hrD hrn hGvar R)

/-- Hard-range full oriented-data realization for the normal-parameter Schur
tuple. -/
theorem sourceOrientedNormalParameterVector_realizes_schur
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead : p.head = R.headFactor)
    (hmixed : p.mixed = R.L)
    (htail :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail = R.tail) :
    sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn p) = G :=
  sourceOrientedNormalParameterVector_realizes_schur_of_fullFrameReconstruct
    d n r hrD hrn hGvar R hhead hmixed htail
    (sourceOrientedSchur_fullFrameDet_reconstruct
      d n r hn hrD hrn hGvar R)

end BHW
