import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedInvariantCoordinateRing

/-!
# Evaluation of source-oriented invariant-coordinate relations

This file connects the source-side polynomial relation generators to the
checked pointwise algebraic relation predicate.  It proves the forward
zero-locus direction: if an oriented coordinate point satisfies
`sourceOrientedAlgebraicRelations`, then every explicit generator of
`sourceOrientedAlgebraicRelationIdeal` evaluates to zero at that point.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Evaluation of source-oriented invariant-coordinate polynomials at an
oriented source-coordinate point. -/
def sourceOrientedCoordinateEval
    (d n : ℕ) (G : SourceOrientedGramData d n) :
    sourceOrientedInvariantCoordinateRing d n →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval
    (fun x : (Fin n × Fin n) ⊕ (Fin (d + 1) ↪ Fin n) =>
      match x with
      | Sum.inl ij => G.gram ij.1 ij.2
      | Sum.inr ι => G.det ι)

/-- The rank/symmetric component of `sourceOrientedAlgebraicRelations` always
implies symmetry of the Gram coordinates. -/
theorem sourceOrientedAlgebraicRelations_gram_symm
    {G : SourceOrientedGramData d n}
    (hG : sourceOrientedAlgebraicRelations d n G) :
    ∀ i j : Fin n, G.gram i j = G.gram j i := by
  have hrank := hG.1
  unfold sourceSymmetricRankLEVariety at hrank
  by_cases hD : d + 1 < n
  · rw [if_pos hD] at hrank
    exact hrank.1
  · rw [if_neg hD] at hrank
    exact hrank

/-- Symmetry relation generators evaluate to zero at points satisfying the
explicit source-oriented algebraic relations. -/
theorem sourceOrientedCoordinateEval_symmetryRelation
    {G : SourceOrientedGramData d n}
    (hG : sourceOrientedAlgebraicRelations d n G)
    (ij : Fin n × Fin n) :
    sourceOrientedCoordinateEval d n G
      (MvPolynomial.X (Sum.inl ij) -
        MvPolynomial.X (Sum.inl (ij.2, ij.1))) = 0 := by
  simp [sourceOrientedCoordinateEval,
    sourceOrientedAlgebraicRelations_gram_symm hG]

/-- Rank-minor relation generators evaluate to zero at points satisfying the
explicit source-oriented algebraic relations. -/
theorem sourceOrientedCoordinateEval_rankMinorRelation
    {G : SourceOrientedGramData d n}
    (hG : sourceOrientedAlgebraicRelations d n G)
    (ι : Fin (d + 2) ↪ Fin n) :
    sourceOrientedCoordinateEval d n G
      (Matrix.det
        (fun a b : Fin (d + 2) =>
          MvPolynomial.X (Sum.inl (ι a, ι b)))) = 0 := by
  have hrank := hG.1
  unfold sourceSymmetricRankLEVariety at hrank
  by_cases hD : d + 1 < n
  · rw [if_pos hD] at hrank
    have hminor := hrank.2 ι ι
    unfold sourceMatrixMinor at hminor
    rw [AlgHom.map_det]
    have hmat :
        (sourceOrientedCoordinateEval d n G).mapMatrix
            (fun a b : Fin (d + 2) =>
              MvPolynomial.X (Sum.inl (ι a, ι b))) =
          (fun a b : Fin (d + 2) => G.gram (ι a) (ι b)) := by
      ext a b
      simp [sourceOrientedCoordinateEval]
    rw [hmat]
    exact hminor
  · have hle : d + 2 ≤ n := by
      simpa using Fintype.card_le_of_injective ι ι.injective
    omega

/-- Ordered determinant alternation relation generators evaluate to zero at
points satisfying the explicit source-oriented algebraic relations. -/
theorem sourceOrientedCoordinateEval_alternationRelation
    {G : SourceOrientedGramData d n}
    (hG : sourceOrientedAlgebraicRelations d n G)
    (p : (Fin (d + 1) ↪ Fin n) × Equiv.Perm (Fin (d + 1))) :
    sourceOrientedCoordinateEval d n G
      (MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
        MvPolynomial.C (p.2.sign : ℂ) *
          (MvPolynomial.X (Sum.inr p.1) :
            sourceOrientedInvariantCoordinateRing d n)) = 0 := by
  simp [sourceOrientedCoordinateEval]
  rw [hG.2.1 p.1 p.2]
  ring

/-- Cauchy-Binet relation generators evaluate to zero at points satisfying the
explicit source-oriented algebraic relations. -/
theorem sourceOrientedCoordinateEval_cauchyBinetRelation
    {G : SourceOrientedGramData d n}
    (hG : sourceOrientedAlgebraicRelations d n G)
    (p : (Fin (d + 1) ↪ Fin n) × (Fin (d + 1) ↪ Fin n)) :
    sourceOrientedCoordinateEval d n G
      (Matrix.det
          (fun a b : Fin (d + 1) =>
            MvPolynomial.X (Sum.inl (p.1 a, p.2 b))) -
        MvPolynomial.C (BHW.minkowskiMetricDet d) *
          (MvPolynomial.X (Sum.inr p.1) :
            sourceOrientedInvariantCoordinateRing d n) *
            (MvPolynomial.X (Sum.inr p.2) :
              sourceOrientedInvariantCoordinateRing d n)) = 0 := by
  rw [map_sub]
  rw [AlgHom.map_det]
  have hmat :
      (sourceOrientedCoordinateEval d n G).mapMatrix
          (fun a b : Fin (d + 1) =>
            MvPolynomial.X (Sum.inl (p.1 a, p.2 b))) =
        (fun a b : Fin (d + 1) => G.gram (p.1 a) (p.2 b)) := by
    ext a b
    simp [sourceOrientedCoordinateEval]
  rw [hmat]
  simp [sourceOrientedCoordinateEval]
  have h := hG.2.2.1 p.1 p.2
  unfold sourceMatrixMinor at h
  rw [h]
  ring

/-- Linear vector-bracket syzygy relation generators evaluate to zero at
points satisfying the explicit source-oriented algebraic relations. -/
theorem sourceOrientedCoordinateEval_linearSyzygyRelation
    {G : SourceOrientedGramData d n}
    (hG : sourceOrientedAlgebraicRelations d n G)
    (p : Fin n × (Fin (d + 2) ↪ Fin n)) :
    sourceOrientedCoordinateEval d n G
      (sourceOrientedLinearSyzygyRelation d n p.1 p.2) = 0 := by
  simpa [sourceOrientedCoordinateEval, sourceOrientedLinearSyzygyRelation] using
    hG.2.2.2 p.1 p.2

/-- Every explicit source-oriented relation generator evaluates to zero at a
point satisfying `sourceOrientedAlgebraicRelations`. -/
theorem sourceOrientedAlgebraicRelationGenerators_eval_eq_zero_of_relations
    {G : SourceOrientedGramData d n}
    (hG : sourceOrientedAlgebraicRelations d n G)
    {p : sourceOrientedInvariantCoordinateRing d n}
    (hp : p ∈ sourceOrientedAlgebraicRelationGenerators d n) :
    sourceOrientedCoordinateEval d n G p = 0 := by
  unfold sourceOrientedAlgebraicRelationGenerators at hp
  rcases hp with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · rcases hp with hp | hp
        · rcases hp with ⟨ij, rfl⟩
          exact sourceOrientedCoordinateEval_symmetryRelation hG ij
        · rcases hp with ⟨ι, rfl⟩
          exact sourceOrientedCoordinateEval_rankMinorRelation hG ι
      · rcases hp with ⟨p, rfl⟩
        exact sourceOrientedCoordinateEval_alternationRelation hG p
    · rcases hp with ⟨p, rfl⟩
      exact sourceOrientedCoordinateEval_cauchyBinetRelation hG p
  · rcases hp with ⟨p, rfl⟩
    exact sourceOrientedCoordinateEval_linearSyzygyRelation hG p

/-- Every polynomial in the explicit source-oriented relation ideal evaluates
to zero at a point satisfying `sourceOrientedAlgebraicRelations`. -/
theorem sourceOrientedAlgebraicRelationIdeal_eval_eq_zero_of_relations
    {G : SourceOrientedGramData d n}
    (hG : sourceOrientedAlgebraicRelations d n G)
    {p : sourceOrientedInvariantCoordinateRing d n}
    (hp : p ∈ sourceOrientedAlgebraicRelationIdeal d n) :
    sourceOrientedCoordinateEval d n G p = 0 := by
  unfold sourceOrientedAlgebraicRelationIdeal at hp
  exact
    Submodule.span_induction
      (s := sourceOrientedAlgebraicRelationGenerators d n)
      (p := fun q _ => sourceOrientedCoordinateEval d n G q = 0)
      (mem := by
        intro q hq
        exact sourceOrientedAlgebraicRelationGenerators_eval_eq_zero_of_relations hG hq)
      (zero := by simp)
      (add := by
        intro p q _hp _hq hp_zero hq_zero
        simp [hp_zero, hq_zero])
      (smul := by
        intro a q _hq hq_zero
        simp [hq_zero])
      hp

end BHW
