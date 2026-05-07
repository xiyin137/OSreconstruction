import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedCauchyBinet

/-!
# Algebraic relations for oriented source invariants

This file records the explicit closed algebraic relation set used by the
oriented normality route.  It proves only the forward, actual-tuple direction:
oriented source invariants satisfy the symmetric rank bound, ordered-frame
alternation, and Cauchy-Binet determinant relations.  The converse/equality
with the oriented source variety is the invariant-theory kernel theorem and is
not asserted here.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Ordered full-frame determinant coordinates alternate under reindexing of
the selected spacetime-size source frame. -/
def sourceOrientedDetAlternating
    (d n : ℕ) (G : SourceOrientedGramData d n) : Prop :=
  ∀ (ι : Fin (d + 1) ↪ Fin n) (ρ : Equiv.Perm (Fin (d + 1))),
    G.det (ρ.toEmbedding.trans ι) = (ρ.sign : ℂ) * G.det ι

/-- Cauchy-Binet determinant relations between source Gram minors and ordered
full-frame determinant coordinates. -/
def sourceOrientedCauchyBinetRelations
    (d n : ℕ) (G : SourceOrientedGramData d n) : Prop :=
  ∀ ι κ : Fin (d + 1) ↪ Fin n,
    sourceMatrixMinor n (d + 1) ι κ G.gram =
      minkowskiMetricDet d * G.det ι * G.det κ

/-- The explicit algebraic relation predicate for oriented source coordinates:
the ordinary Gram coordinates lie in the symmetric rank-`≤ d + 1` variety, the
ordered determinant coordinates alternate, and the Cauchy-Binet determinant
relations hold. -/
def sourceOrientedAlgebraicRelations
    (d n : ℕ) (G : SourceOrientedGramData d n) : Prop :=
  G.gram ∈ sourceSymmetricRankLEVariety n (d + 1) ∧
    sourceOrientedDetAlternating d n G ∧
      sourceOrientedCauchyBinetRelations d n G

/-- The closed algebraic model cut out by the explicit oriented source
relations. -/
def sourceOrientedAlgebraicVariety
    (d n : ℕ) : Set (SourceOrientedGramData d n) :=
  {G | sourceOrientedAlgebraicRelations d n G}

/-- Actual oriented source invariants satisfy the explicit algebraic
relations.  This is only the forward direction of the later algebraic-model
identification. -/
theorem sourceOrientedMinkowskiInvariant_mem_algebraicRelations
    (d n : ℕ) (z : Fin n → Fin (d + 1) → ℂ) :
    sourceOrientedAlgebraicRelations d n
      (sourceOrientedMinkowskiInvariant d n z) := by
  refine ⟨?_, ?_, ?_⟩
  · have hgram_var :
        (sourceOrientedMinkowskiInvariant d n z).gram ∈
          sourceComplexGramVariety d n := by
      exact
        ⟨z, by
          simp [sourceOrientedMinkowskiInvariant,
            SourceOrientedGramData.gram]⟩
    exact
      sourceComplexGramVariety_subset_sourceSymmetricRankLEVariety
        d n hgram_var
  · intro ι ρ
    exact sourceOrientedInvariant_det_reindex_selectedFrame d n ι ρ z
  · intro ι κ
    exact sourceMatrixMinor_sourceOrientedInvariant_fullFrame d n ι κ z

/-- The oriented source variety is contained in the explicit algebraic model.
The reverse inclusion is the invariant-theory kernel theorem, not this
forward Cauchy-Binet support. -/
theorem sourceOrientedGramVariety_subset_algebraicVariety
    (d n : ℕ) :
    sourceOrientedGramVariety d n ⊆ sourceOrientedAlgebraicVariety d n := by
  rintro G ⟨z, rfl⟩
  exact sourceOrientedMinkowskiInvariant_mem_algebraicRelations d n z

/-- Alternation is a closed condition in oriented source coordinates. -/
theorem isClosed_sourceOrientedDetAlternating
    (d n : ℕ) :
    IsClosed
      {G : SourceOrientedGramData d n |
        sourceOrientedDetAlternating d n G} := by
  rw [show
      {G : SourceOrientedGramData d n |
        sourceOrientedDetAlternating d n G} =
        ⋂ ι : Fin (d + 1) ↪ Fin n,
          ⋂ ρ : Equiv.Perm (Fin (d + 1)),
            {G : SourceOrientedGramData d n |
              G.det (ρ.toEmbedding.trans ι) =
                (ρ.sign : ℂ) * G.det ι} by
    ext G
    simp [sourceOrientedDetAlternating]]
  apply isClosed_iInter
  intro ι
  apply isClosed_iInter
  intro ρ
  exact isClosed_eq
    ((continuous_apply (ρ.toEmbedding.trans ι)).comp
      continuous_sourceOrientedGramData_det)
    (continuous_const.mul
      ((continuous_apply ι).comp continuous_sourceOrientedGramData_det))

/-- The Cauchy-Binet equations are a closed condition in oriented source
coordinates. -/
theorem isClosed_sourceOrientedCauchyBinetRelations
    (d n : ℕ) :
    IsClosed
      {G : SourceOrientedGramData d n |
        sourceOrientedCauchyBinetRelations d n G} := by
  rw [show
      {G : SourceOrientedGramData d n |
        sourceOrientedCauchyBinetRelations d n G} =
        ⋂ ι : Fin (d + 1) ↪ Fin n,
          ⋂ κ : Fin (d + 1) ↪ Fin n,
            {G : SourceOrientedGramData d n |
              sourceMatrixMinor n (d + 1) ι κ G.gram =
                minkowskiMetricDet d * G.det ι * G.det κ} by
    ext G
    simp [sourceOrientedCauchyBinetRelations]]
  apply isClosed_iInter
  intro ι
  apply isClosed_iInter
  intro κ
  exact isClosed_eq
    ((continuous_sourceMatrixMinor n (d + 1) ι κ).comp
      continuous_sourceOrientedGramData_gram)
    ((continuous_const.mul
      ((continuous_apply ι).comp continuous_sourceOrientedGramData_det)).mul
        ((continuous_apply κ).comp continuous_sourceOrientedGramData_det))

/-- The explicit oriented algebraic relation set is closed. -/
theorem isClosed_sourceOrientedAlgebraicVariety
    (d n : ℕ) :
    IsClosed (sourceOrientedAlgebraicVariety d n) := by
  have hRank :
      IsClosed
        {G : SourceOrientedGramData d n |
          G.gram ∈ sourceSymmetricRankLEVariety n (d + 1)} :=
    (isClosed_sourceSymmetricRankLEVariety n (d + 1)).preimage
      continuous_sourceOrientedGramData_gram
  have hAlt := isClosed_sourceOrientedDetAlternating d n
  have hCB := isClosed_sourceOrientedCauchyBinetRelations d n
  simpa [sourceOrientedAlgebraicVariety,
    sourceOrientedAlgebraicRelations, Set.setOf_and] using
    hRank.inter (hAlt.inter hCB)

end BHW
