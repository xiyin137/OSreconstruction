import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurResidual

/-!
# Source-oriented rank-deficient head gauge interface

This file isolates the local head-gauge surface used by the Schur residual
producer.  The analytic existence of the gauge is a later inverse-function
theorem; here we record the exact data interface and the checked algebraic
constructor reducing Schur residual production to the shifted residual-tail
membership statement.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Symmetric complex square matrices, as a subtype carrying the inherited
finite-dimensional topology. -/
abbrev SourceSymmetricMatrixCoord (r : ℕ) :=
  {A : Matrix (Fin r) (Fin r) ℂ // Aᵀ = A}

/-- The canonical source head metric as a symmetric coordinate. -/
def sourceHeadMetricSymmCoord
    (d r : ℕ)
    (hrD : r < d + 1) :
    SourceSymmetricMatrixCoord r :=
  ⟨sourceHeadMetric d r hrD, sourceHeadMetric_transpose d r hrD⟩

/-- The signature Gram block of a candidate head factor, bundled as a
symmetric coordinate. -/
def sourceHeadFactorGramSymmCoord
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : Matrix (Fin r) (Fin r) ℂ) :
    SourceSymmetricMatrixCoord r :=
  ⟨H * sourceHeadMetric d r hrD * Hᵀ, by
    simp [Matrix.transpose_mul, sourceHeadMetric_transpose d r hrD,
      Matrix.mul_assoc]⟩

/-- Entrywise coordinate window around the identity head factor.  This is
kept in the head-gauge interface so the gauge constructor can record a
concrete near-identity domain shrink without depending on the later Schur
parameter-window files. -/
def sourceHeadFactorCoordinateWindow
    (r : ℕ)
    (ρ : ℝ) :
    Set (Matrix (Fin r) (Fin r) ℂ) :=
  {H | ∀ a b, ‖H a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ρ}

/-- The selected Schur head block of a source-variety point, bundled with its
symmetry. -/
def sourceOrientedSchurHeadBlockSymm
    (d n r : ℕ)
    (_hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n) :
    SourceSymmetricMatrixCoord r :=
  ⟨sourceOrientedSchurHeadBlock n r hrn G, by
    rcases hGvar with ⟨z, rfl⟩
    ext a b
    simpa [sourceOrientedSchurHeadBlock, sourceOrientedMinkowskiInvariant,
      SourceOrientedGramData.gram] using
      sourceMinkowskiGram_symm d n z (finSourceHead hrn b)
        (finSourceHead hrn a)⟩

@[simp]
theorem sourceOrientedSchurHeadBlockSymm_coe
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n) :
    (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar :
        Matrix (Fin r) (Fin r) ℂ) =
      sourceOrientedSchurHeadBlock n r hrn G := by
  rfl

/-- Local head-gauge data for the signature-relative factorization
`A = H * η * Hᵀ` near the canonical head metric. -/
structure SourceRankDeficientHeadGaugeData
    (d r : ℕ)
    (hrD : r < d + 1) where
  factorDomain : Set (Matrix (Fin r) (Fin r) ℂ)
  factorDomain_open : IsOpen factorDomain
  factorDomain_center_mem : (1 : Matrix (Fin r) (Fin r) ℂ) ∈ factorDomain
  factorDomain_coordinate :
    ∃ ρ : ℝ, 0 < ρ ∧ sourceHeadFactorCoordinateWindow r ρ ⊆ factorDomain
  U : Set (SourceSymmetricMatrixCoord r)
  U_open : IsOpen U
  center_mem : sourceHeadMetricSymmCoord d r hrD ∈ U
  factor : SourceSymmetricMatrixCoord r → Matrix (Fin r) (Fin r) ℂ
  factor_continuousOn : ContinuousOn factor U
  factor_center : factor (sourceHeadMetricSymmCoord d r hrD) = 1
  factor_gram :
    ∀ A ∈ U,
      factor A * sourceHeadMetric d r hrD * (factor A)ᵀ =
        (A : Matrix (Fin r) (Fin r) ℂ)
  factorDomain_mem :
    ∀ H ∈ factorDomain, sourceHeadFactorGramSymmCoord d r hrD H ∈ U
  factor_left_inverse :
    ∀ H ∈ factorDomain,
      factor (sourceHeadFactorGramSymmCoord d r hrD H) = H
  factor_det_unit : ∀ A ∈ U, IsUnit (factor A).det

/-- The explicit residual-tail datum associated to a selected head factor. -/
def sourceOrientedSchurResidualTailData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (headFactor : Matrix (Fin r) (Fin r) ℂ) :
    SourceShiftedTailOrientedData d r hrD (n - r) where
  gram := sourceSchurComplement n r hrn G
    (sourceOrientedSchurHeadBlock n r hrn G)
  det := sourceSchurResidualDeterminants d n r hrD hrn G headFactor

@[simp]
theorem sourceOrientedSchurResidualTailData_gram
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (headFactor : Matrix (Fin r) (Fin r) ℂ) :
    (sourceOrientedSchurResidualTailData d n r hrD hrn G headFactor).gram =
      sourceSchurComplement n r hrn G
        (sourceOrientedSchurHeadBlock n r hrn G) := by
  rfl

@[simp]
theorem sourceOrientedSchurResidualTailData_det
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (headFactor : Matrix (Fin r) (Fin r) ℂ)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    (sourceOrientedSchurResidualTailData d n r hrD hrn G headFactor).det lam =
      sourceSchurResidualDeterminants d n r hrD hrn G headFactor lam := by
  rfl

/-- A signature-relative head gauge makes the selected Schur head block
invertible. -/
theorem sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det := by
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar
  let H := Head.factor Acoord
  have hH : IsUnit H.det := Head.factor_det_unit Acoord hHead
  have hHt : IsUnit Hᵀ.det := Matrix.isUnit_det_transpose H hH
  have hη : IsUnit (sourceHeadMetric d r hrD).det :=
    sourceHeadMetric_det_isUnit d r hrD
  have hprod : IsUnit (H * sourceHeadMetric d r hrD * Hᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hH.mul hη).mul hHt
  have hgram :
      H * sourceHeadMetric d r hrD * Hᵀ =
        sourceOrientedSchurHeadBlock n r hrn G := by
    simpa [Acoord, H] using Head.factor_gram Acoord hHead
  simpa [hgram] using hprod

/-- Once the shifted residual-tail datum is known to lie on the shifted-tail
oriented variety, the full Schur residual packet is just algebra. -/
def sourceOriented_schurResidualData_of_tail_mem
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (htail_mem :
      sourceOrientedSchurResidualTailData d n r hrD hrn G
          (Head.factor
            (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)) ∈
        sourceShiftedTailOrientedVariety d r hrD (n - r)) :
    SourceOrientedSchurResidualData d n r hrD hrn G := by
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar
  let H := Head.factor Acoord
  exact
    { A := sourceOrientedSchurHeadBlock n r hrn G
      A_eq := rfl
      A_unit :=
        sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
          d n r hrD hrn hGvar Head hHead
      headFactor := H
      headFactor_gram := by
        simpa [Acoord, H] using Head.factor_gram Acoord hHead
      headFactor_det_unit := Head.factor_det_unit Acoord hHead
      L := sourceSchurMixedCoeff n r hrn G
        (sourceOrientedSchurHeadBlock n r hrn G)
      L_eq := rfl
      tail := sourceOrientedSchurResidualTailData d n r hrD hrn G H
      tail_gram_eq := rfl
      tail_det_eq := rfl
      tail_mem := by
        simpa [Acoord, H] using htail_mem }

end BHW
