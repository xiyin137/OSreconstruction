import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalDeterminant

/-!
# Source-oriented Schur residual coordinates

This file records the rank-deficient Schur residual data used by the
source-oriented normal-parameter route.  It deliberately does not store the
full-frame determinant reconstruction theorem as data; that remains the
separate Plucker/Cauchy-Binet reconstruction step over the original oriented
datum.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Principal head block of the ordinary source Gram coordinate. -/
def sourceOrientedSchurHeadBlock
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun a b => G.gram (finSourceHead hrn a) (finSourceHead hrn b)

@[simp]
theorem sourceOrientedSchurHeadBlock_apply
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (a b : Fin r) :
    sourceOrientedSchurHeadBlock n r hrn G a b =
      G.gram (finSourceHead hrn a) (finSourceHead hrn b) := by
  rfl

/-- Tail/head mixed block of the ordinary source Gram coordinate. -/
def sourceOrientedSchurMixedBlock
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n) :
    Matrix (Fin (n - r)) (Fin r) ℂ :=
  fun u a => G.gram (finSourceTail hrn u) (finSourceHead hrn a)

/-- Tail/tail block of the ordinary source Gram coordinate. -/
def sourceOrientedSchurTailBlock
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n) :
    Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
  fun u v => G.gram (finSourceTail hrn u) (finSourceTail hrn v)

/-- Mixed coefficient matrix in the principal Schur chart. -/
def sourceSchurMixedCoeff
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (A : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin (n - r)) (Fin r) ℂ :=
  sourceOrientedSchurMixedBlock n r hrn G * A⁻¹

/-- Residual Schur-complement Gram block in the principal Schur chart. -/
def sourceSchurComplement
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (A : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
  let L := sourceSchurMixedCoeff n r hrn G A
  sourceOrientedSchurTailBlock n r hrn G - L * A * L.transpose

/-- Selected residual-tail full-frame determinant coordinates extracted from
the original oriented determinant coordinate and the chosen head factor. -/
def sourceSchurResidualDeterminants
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (headFactor : Matrix (Fin r) (Fin r) ℂ) :
    (Fin (d + 1 - r) ↪ Fin (n - r)) → ℂ :=
  fun lam =>
    G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) /
      headFactor.det

/-- Shifted-tail oriented data lying on the shifted-tail source variety. -/
def sourceShiftedTailOrientedVariety
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ) :
    Set (SourceShiftedTailOrientedData d r hrD m) :=
  Set.range (sourceShiftedTailOrientedInvariant d r hrD m)

/-- Schur residual data attached to an oriented source datum and a chosen
rank-deficient principal head block. -/
structure SourceOrientedSchurResidualData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n) where
  A : Matrix (Fin r) (Fin r) ℂ
  A_eq : A = sourceOrientedSchurHeadBlock n r hrn G
  A_unit : IsUnit A.det
  headFactor : Matrix (Fin r) (Fin r) ℂ
  headFactor_gram :
    headFactor * sourceHeadMetric d r hrD * headFactor.transpose = A
  headFactor_det_unit : IsUnit headFactor.det
  L : Matrix (Fin (n - r)) (Fin r) ℂ
  L_eq : L = sourceSchurMixedCoeff n r hrn G A
  tail : SourceShiftedTailOrientedData d r hrD (n - r)
  tail_gram_eq : tail.gram = sourceSchurComplement n r hrn G A
  tail_det_eq :
    tail.det = sourceSchurResidualDeterminants d n r hrD hrn G headFactor
  tail_mem : tail ∈ sourceShiftedTailOrientedVariety d r hrD (n - r)

/-- Mechanical determinant-coordinate consumer for the normal-parameter Schur
route.  The hard input is the genuine full-frame reconstruction theorem over
the original oriented datum `G`, supplied as `hdet`. -/
theorem sourceOrientedNormalParameterVector_realizes_schur_det_of_fullFrameReconstruct
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead : p.head = R.headFactor)
    (hmixed : p.mixed = R.L)
    (htail :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail = R.tail)
    (hdet :
      ∀ ι : Fin (d + 1) ↪ Fin n,
        sourceNormalFullFrameDetFromSchur d n r hrD hrn
          R.headFactor R.L R.tail ι = G.det ι) :
    (sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn p)).det = G.det := by
  funext ι
  change
    sourceFullFrameDet d n ι
        (sourceOrientedNormalParameterVector d n r hrD hrn p) =
      G.det ι
  calc
    sourceFullFrameDet d n ι
        (sourceOrientedNormalParameterVector d n r hrD hrn p)
        = sourceNormalFullFrameDetFromSchur d n r hrD hrn
            p.head p.mixed
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail)
            ι :=
          sourceFullFrameDet_normalParameter_eq_schurFormula
            d n r hrD hrn p ι
    _ = sourceNormalFullFrameDetFromSchur d n r hrD hrn
            R.headFactor R.L R.tail ι := by
          rw [hhead, hmixed, htail]
    _ = G.det ι := hdet ι

end BHW

