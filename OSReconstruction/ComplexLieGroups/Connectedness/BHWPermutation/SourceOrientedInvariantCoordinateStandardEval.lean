import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedInvariantCoordinateRing

/-!
# Evaluation of standard-dot invariant-coordinate relations

This file proves the forward zero-locus direction for the standard-dot
pairing/volume coordinate presentation.  Actual `n`-tuples in `ℂ^D` satisfy
the explicit symmetry, rank-minor, alternation, Cauchy-Binet, and linear
vector-bracket syzygy generators, and hence every polynomial in the generated
standard `SO` relation ideal evaluates to zero on such a tuple.

This is not the `SO` second fundamental theorem: it proves only vanishing of
the displayed relations on actual tuple invariants, not equality with the
kernel of the invariant-coordinate map.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {D n : ℕ}

/-- Evaluation of standard-dot invariant-coordinate polynomials at an actual
tuple in `(ℂ^D)^n`. -/
def standardSOCoordinateEval
    (D n : ℕ) (z : Fin n → Fin D → ℂ) :
    standardSOInvariantCoordinateRing D n →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval
    (fun x : (Fin n × Fin n) ⊕ (Fin D ↪ Fin n) =>
      match x with
      | Sum.inl ij => sourceComplexDotGram D n z ij.1 ij.2
      | Sum.inr ι =>
          Matrix.det (fun a μ : Fin D => z (ι a) μ))

/-- Cauchy-Binet for two selected standard-dot full-frame matrices:
`det(A Bᵀ) = det(A) det(B)`. -/
theorem sourceMatrixMinor_sourceComplexDotGram_standardFullFrame
    (D n : ℕ)
    (ι κ : Fin D ↪ Fin n)
    (z : Fin n → Fin D → ℂ) :
    sourceMatrixMinor n D ι κ (sourceComplexDotGram D n z) =
      Matrix.det (fun a μ : Fin D => z (ι a) μ) *
        Matrix.det (fun a μ : Fin D => z (κ a) μ) := by
  let A : Matrix (Fin D) (Fin D) ℂ :=
    fun a μ => z (ι a) μ
  let B : Matrix (Fin D) (Fin D) ℂ :=
    fun a μ => z (κ a) μ
  have hmat :
      (fun a b : Fin D => sourceComplexDotGram D n z (ι a) (κ b)) =
        A * B.transpose := by
    ext a b
    simp [A, B, sourceComplexDotGram, Matrix.mul_apply]
  rw [sourceMatrixMinor]
  change
    Matrix.det
      (fun a b : Fin D => sourceComplexDotGram D n z (ι a) (κ b)) = _
  rw [hmat]
  simp [A, B, Matrix.det_mul, Matrix.det_transpose]

/-- Symmetry relation generators evaluate to zero on actual standard-dot
tuple invariants. -/
theorem standardSOCoordinateEval_symmetryRelation
    (z : Fin n → Fin D → ℂ)
    (ij : Fin n × Fin n) :
    standardSOCoordinateEval D n z
      (MvPolynomial.X (Sum.inl ij) -
        MvPolynomial.X (Sum.inl (ij.2, ij.1))) = 0 := by
  simp [standardSOCoordinateEval, sourceComplexDotGram_symm]

/-- Rank-minor relation generators evaluate to zero on actual standard-dot
tuple invariants. -/
theorem standardSOCoordinateEval_rankMinorRelation
    (z : Fin n → Fin D → ℂ)
    (ι : Fin (D + 1) ↪ Fin n) :
    standardSOCoordinateEval D n z
      (Matrix.det
        (fun a b : Fin (D + 1) =>
          MvPolynomial.X (Sum.inl (ι a, ι b)))) = 0 := by
  rw [AlgHom.map_det]
  have hmat :
      (standardSOCoordinateEval D n z).mapMatrix
          (fun a b : Fin (D + 1) =>
            MvPolynomial.X (Sum.inl (ι a, ι b))) =
        (fun a b : Fin (D + 1) => sourceComplexDotGram D n z (ι a) (ι b)) := by
    ext a b
    simp [standardSOCoordinateEval]
  rw [hmat]
  exact sourceComplexDotGram_minor_eq_zero D n z ι ι

/-- Ordered volume alternation relation generators evaluate to zero on actual
standard-dot tuple invariants. -/
theorem standardSOCoordinateEval_alternationRelation
    (z : Fin n → Fin D → ℂ)
    (p : (Fin D ↪ Fin n) × Equiv.Perm (Fin D)) :
    standardSOCoordinateEval D n z
      (MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
        MvPolynomial.C (p.2.sign : ℂ) *
          (MvPolynomial.X (Sum.inr p.1) :
            standardSOInvariantCoordinateRing D n)) = 0 := by
  simp [standardSOCoordinateEval]
  have hperm :=
    Matrix.det_permute p.2 (fun a μ : Fin D => z (p.1 a) μ)
  have hdet :
      Matrix.det (fun a μ : Fin D => z (p.1 (p.2 a)) μ) =
        (p.2.sign : ℂ) * Matrix.det (fun a μ : Fin D => z (p.1 a) μ) := by
    simpa [Matrix.submatrix, Function.comp_def] using hperm
  rw [hdet]
  ring

/-- Cauchy-Binet relation generators evaluate to zero on actual standard-dot
tuple invariants. -/
theorem standardSOCoordinateEval_cauchyBinetRelation
    (z : Fin n → Fin D → ℂ)
    (p : (Fin D ↪ Fin n) × (Fin D ↪ Fin n)) :
    standardSOCoordinateEval D n z
      (Matrix.det
          (fun a b : Fin D =>
            MvPolynomial.X (Sum.inl (p.1 a, p.2 b))) -
        (MvPolynomial.X (Sum.inr p.1) :
          standardSOInvariantCoordinateRing D n) *
          (MvPolynomial.X (Sum.inr p.2) :
            standardSOInvariantCoordinateRing D n)) = 0 := by
  rw [map_sub]
  rw [AlgHom.map_det]
  have hmat :
      (standardSOCoordinateEval D n z).mapMatrix
          (fun a b : Fin D =>
            MvPolynomial.X (Sum.inl (p.1 a, p.2 b))) =
        (fun a b : Fin D => sourceComplexDotGram D n z (p.1 a) (p.2 b)) := by
    ext a b
    simp [standardSOCoordinateEval]
  rw [hmat]
  simp [standardSOCoordinateEval]
  have h :=
    sourceMatrixMinor_sourceComplexDotGram_standardFullFrame
      D n p.1 p.2 z
  unfold sourceMatrixMinor at h
  rw [h]
  ring

/-- Linear vector-bracket syzygy generators evaluate to zero on actual
standard-dot tuple invariants. -/
theorem standardSOCoordinateEval_linearSyzygyRelation
    (z : Fin n → Fin D → ℂ)
    (p : Fin n × (Fin (D + 1) ↪ Fin n)) :
    standardSOCoordinateEval D n z
      (standardSOLinearSyzygyRelation D n p.1 p.2) = 0 := by
  simpa [standardSOCoordinateEval, standardSOLinearSyzygyRelation,
    sourceComplexDotGram] using
    coordinateVolume_linearSyzygy D n z (fun μ : Fin D => z p.1 μ) p.2

/-- Every explicit standard-dot relation generator evaluates to zero on actual
standard-dot tuple invariants. -/
theorem standardSOAlgebraicRelationGenerators_eval_eq_zero
    (z : Fin n → Fin D → ℂ)
    {p : standardSOInvariantCoordinateRing D n}
    (hp : p ∈ standardSOAlgebraicRelationGenerators D n) :
    standardSOCoordinateEval D n z p = 0 := by
  unfold standardSOAlgebraicRelationGenerators at hp
  rcases hp with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · rcases hp with hp | hp
        · rcases hp with ⟨ij, rfl⟩
          exact standardSOCoordinateEval_symmetryRelation z ij
        · rcases hp with ⟨ι, rfl⟩
          exact standardSOCoordinateEval_rankMinorRelation z ι
      · rcases hp with ⟨p, rfl⟩
        exact standardSOCoordinateEval_alternationRelation z p
    · rcases hp with ⟨p, rfl⟩
      exact standardSOCoordinateEval_cauchyBinetRelation z p
  · rcases hp with ⟨p, rfl⟩
    exact standardSOCoordinateEval_linearSyzygyRelation z p

/-- Every polynomial in the explicit standard-dot relation ideal evaluates to
zero on actual standard-dot tuple invariants. -/
theorem standardSOAlgebraicRelationIdeal_eval_eq_zero
    (z : Fin n → Fin D → ℂ)
    {p : standardSOInvariantCoordinateRing D n}
    (hp : p ∈ standardSOAlgebraicRelationIdeal D n) :
    standardSOCoordinateEval D n z p = 0 := by
  unfold standardSOAlgebraicRelationIdeal at hp
  exact
    Submodule.span_induction
      (s := standardSOAlgebraicRelationGenerators D n)
      (p := fun q _ => standardSOCoordinateEval D n z q = 0)
      (mem := by
        intro q hq
        exact standardSOAlgebraicRelationGenerators_eval_eq_zero z hq)
      (zero := by simp)
      (add := by
        intro p q _hp _hq hp_zero hq_zero
        simp [hp_zero, hq_zero])
      (smul := by
        intro a q _hq hq_zero
        simp [hq_zero])
      hp

end BHW
