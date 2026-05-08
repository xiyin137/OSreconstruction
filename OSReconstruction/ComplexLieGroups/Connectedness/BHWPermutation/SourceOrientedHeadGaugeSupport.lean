import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGauge
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurPropagation

/-!
# Source-oriented head-gauge support lemmas

This small companion specializes the checked Schur determinant propagation
theorems to the local head-gauge interface.  These are the finite-dimensional
facts consumed by the remaining local Witt/head-normal-form producer: once the
selected head block lies in a signature-relative gauge chart, the head rows are
linearly independent, and max-rank source-variety points have a nonzero
selected head-tail full-frame determinant.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- A local head-gauge factor is continuous at the chart center, because the
chart domain is open and contains the center. -/
theorem sourceRankDeficientHeadGauge_factor_continuousAt_center
    (d r : ℕ)
    (hrD : r < d + 1)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    ContinuousAt Head.factor (sourceHeadMetricSymmCoord d r hrD) := by
  exact
    Head.factor_continuousOn.continuousAt
      (Head.U_open.mem_nhds Head.center_mem)

/-- Any neighborhood of the identity factor can be enforced by shrinking the
head-gauge chart around the canonical head metric. -/
theorem sourceRankDeficientHeadGauge_exists_factor_nhds
    (d r : ℕ)
    (hrD : r < d + 1)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {V : Set (Matrix (Fin r) (Fin r) ℂ)}
    (hV : V ∈ 𝓝 (1 : Matrix (Fin r) (Fin r) ℂ)) :
    ∃ W : Set (SourceSymmetricMatrixCoord r),
      W ∈ 𝓝 (sourceHeadMetricSymmCoord d r hrD) ∧
        W ⊆ Head.U ∧
        ∀ A ∈ W, Head.factor A ∈ V := by
  let A0 := sourceHeadMetricSymmCoord d r hrD
  have hV' : V ∈ 𝓝 (Head.factor A0) := by
    simpa [A0, Head.factor_center] using hV
  have hpre : Head.factor ⁻¹' V ∈ 𝓝 A0 :=
    (sourceRankDeficientHeadGauge_factor_continuousAt_center d r hrD Head) hV'
  have hU : Head.U ∈ 𝓝 A0 := by
    simpa [A0] using Head.U_open.mem_nhds Head.center_mem
  refine ⟨Head.U ∩ Head.factor ⁻¹' V, Filter.inter_mem hU hpre, ?_, ?_⟩
  · exact Set.inter_subset_left
  · intro A hA
    exact hA.2

/-- Coordinate form of the head-gauge factor shrink: the factor matrix can be
kept entrywise close to the identity after shrinking the gauge chart. -/
theorem sourceRankDeficientHeadGauge_exists_factor_coordinate_bound
    (d r : ℕ)
    (hrD : r < d + 1)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ W : Set (SourceSymmetricMatrixCoord r),
      W ∈ 𝓝 (sourceHeadMetricSymmCoord d r hrD) ∧
        W ⊆ Head.U ∧
        ∀ A ∈ W,
          ∀ a b,
            ‖Head.factor A a b -
              (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ρ := by
  have hV :
      {M : Matrix (Fin r) (Fin r) ℂ |
        ∀ a b, ‖M a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ρ} ∈
        𝓝 (1 : Matrix (Fin r) (Fin r) ℂ) := by
    have hopen :
        IsOpen
          {M : Matrix (Fin r) (Fin r) ℂ |
            ∀ a b, ‖M a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ρ} := by
      simp only [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro a
      apply isOpen_iInter_of_finite
      intro b
      exact isOpen_lt (by fun_prop) continuous_const
    exact hopen.mem_nhds (by intro a b; simpa using hρ)
  simpa using
    sourceRankDeficientHeadGauge_exists_factor_nhds
      d r hrD Head hV

/-- Full-matrix form of the head-gauge shrink.  It converts the symmetric
subtype neighborhood supplied by the head-gauge chart into an ordinary matrix
neighborhood, so later normal-Schur shrink lemmas can use it as their head
coordinate neighborhood. -/
theorem sourceRankDeficientHeadGauge_exists_matrix_nhds_factor_coordinate_bound
    (d r : ℕ)
    (hrD : r < d + 1)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ Uh : Set (Matrix (Fin r) (Fin r) ℂ),
      Uh ∈ 𝓝 (sourceHeadMetric d r hrD) ∧
        ∀ A (_hAUh : A ∈ Uh) (hAsym : Aᵀ = A),
          (⟨A, hAsym⟩ : SourceSymmetricMatrixCoord r) ∈ Head.U ∧
            ∀ a b,
              ‖Head.factor (⟨A, hAsym⟩ : SourceSymmetricMatrixCoord r) a b -
                (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ρ := by
  rcases sourceRankDeficientHeadGauge_exists_factor_coordinate_bound
      d r hrD Head hρ with
    ⟨W, hW_nhds, hW_sub, hW_factor⟩
  let Sym : Set (Matrix (Fin r) (Fin r) ℂ) := {A | Aᵀ = A}
  have hW_within :
      ((fun A : SourceSymmetricMatrixCoord r =>
          (A : Matrix (Fin r) (Fin r) ℂ)) '' W) ∈
        𝓝[Sym] (sourceHeadMetric d r hrD) := by
    simpa [Sym, sourceHeadMetricSymmCoord] using
      (mem_nhds_subtype_iff_nhdsWithin
        (s := Sym)
        (a := sourceHeadMetricSymmCoord d r hrD)
        (t := W)).mp hW_nhds
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hW_within with
    ⟨Uh, hUh_nhds, hUh_sub⟩
  refine ⟨Uh, hUh_nhds, ?_⟩
  intro A hAUh hAsym
  have hA_image :
      A ∈
        (fun A : SourceSymmetricMatrixCoord r =>
          (A : Matrix (Fin r) (Fin r) ℂ)) '' W :=
    hUh_sub ⟨hAUh, hAsym⟩
  rcases hA_image with ⟨Acoord, hAcoordW, hAcoord_eq⟩
  have hcoord_eq :
      Acoord = (⟨A, hAsym⟩ : SourceSymmetricMatrixCoord r) := by
    exact Subtype.ext hAcoord_eq
  have hAw : (⟨A, hAsym⟩ : SourceSymmetricMatrixCoord r) ∈ W := by
    simpa [hcoord_eq] using hAcoordW
  exact ⟨hW_sub hAw, hW_factor (⟨A, hAsym⟩ : SourceSymmetricMatrixCoord r) hAw⟩

/-- A local head factor makes the actual selected head rows linearly
independent for every realizing source tuple. -/
theorem sourceHeadRows_linearIndependent_of_headFactor
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) :
    LinearIndependent ℂ (fun a : Fin r => z (finSourceHead hrn a)) := by
  have hA : IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det :=
    sourceOrientedSchurHeadBlock_det_isUnit_of_headFactor
      d n r hrD hrn hGvar Head hHead
  subst G
  exact sourceHeadRows_linearIndependent_of_schurHeadBlock_isUnit
    d n r hrn z (by simpa using hA)

/-- Legacy full-gauge specialization of
`sourceHeadRows_linearIndependent_of_headFactor`. -/
theorem sourceHeadRows_linearIndependent_of_headGauge
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) :
    LinearIndependent ℂ (fun a : Fin r => z (finSourceHead hrn a)) :=
  sourceHeadRows_linearIndependent_of_headFactor
    d n r hrD hrn hGvar Head.toHeadFactorData hHead hz

/-- Head-gauge specialization of the all-zero head-tail determinant
contrapositive: if every selected head-tail determinant vanishes, the point is
not in the max-rank stratum. -/
theorem sourceOrientedGramVariety_notMaxRank_of_headGauge_headTailDet_eq_zero
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (hzero :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) = 0) :
    ¬ SourceOrientedMaxRankAt d n G := by
  exact
    sourceOrientedGramVariety_notMaxRank_of_headTailDet_eq_zero
      d n r hn hrD hrn hGvar
      (sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
        d n r hrD hrn hGvar Head hHead)
      hzero

/-- At a max-rank source-variety point with a local head gauge, some selected
head-tail full-frame determinant is nonzero. -/
theorem exists_headTail_fullFrameDet_ne_zero_of_headGauge_maxRank
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (hmax : SourceOrientedMaxRankAt d n G) :
    ∃ lam : Fin (d + 1 - r) ↪ Fin (n - r),
      G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) ≠ 0 := by
  by_contra hnone
  have hzero :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) = 0 := by
    intro lam
    by_contra hne
    exact hnone ⟨lam, hne⟩
  exact
    (sourceOrientedGramVariety_notMaxRank_of_headGauge_headTailDet_eq_zero
      d n r hn hrD hrn hGvar Head hHead hzero) hmax

/-- Head-gauge specialization of determinant propagation from selected
head-tail determinants. -/
theorem sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_headGauge
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G H : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHvar : H ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (hgram : H.gram = G.gram)
    (hheadTail :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)) :
    H.det = G.det :=
  sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq
    d n r hn hrD hrn hGvar hHvar
    (sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
      d n r hrD hrn hGvar Head hHead)
    hgram hheadTail

/-- Full oriented-data equality from ordinary Gram equality and selected
head-tail determinant equality, specialized to a source point in a local head
gauge. -/
theorem sourceOrientedGramData_eq_of_gram_eq_headTailDet_eq_of_headGauge
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G H : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHvar : H ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (hgram : H.gram = G.gram)
    (hheadTail :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)) :
    H = G := by
  apply SourceOrientedGramData.ext
  · exact hgram
  · exact
      sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_headGauge
        d n r hn hrD hrn hGvar hHvar Head hHead hgram hheadTail

end BHW
