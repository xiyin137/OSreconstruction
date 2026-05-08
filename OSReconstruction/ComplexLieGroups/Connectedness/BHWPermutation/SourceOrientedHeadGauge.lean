import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurResidual

/-!
# Source-oriented rank-deficient head gauge interface

This file isolates the local head-gauge surface used by the Schur residual
producer.  The mathematically viable gauge is a local inverse-function chart on
a transverse slice through the `H ↦ H * η * Hᵀ` map; a full-matrix open
neighborhood cannot carry a left inverse because of the local complex
orthogonal stabilizer.
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

/-- The honest local head-gauge source is a slice through the
`H ↦ H * η * Hᵀ` map, not an open set in the full matrix space.  We use the
linear slice `H * η` symmetric, which is transverse to the local complex
orthogonal stabilizer at the identity. -/
abbrev SourceHeadGaugeSlice
    (d r : ℕ)
    (hrD : r < d + 1) :=
  {H : Matrix (Fin r) (Fin r) ℂ //
    H * sourceHeadMetric d r hrD =
      (H * sourceHeadMetric d r hrD)ᵀ}

/-- The identity head factor as a point of the slice. -/
def sourceHeadGaugeSliceCenter
    (d r : ℕ)
    (hrD : r < d + 1) :
    SourceHeadGaugeSlice d r hrD :=
  ⟨1, by simp [sourceHeadMetric_transpose d r hrD]⟩

/-- Entrywise window in the slice topology. -/
def sourceHeadGaugeSliceCoordinateWindow
    (d r : ℕ)
    (hrD : r < d + 1)
    (ρ : ℝ) :
    Set (SourceHeadGaugeSlice d r hrD) :=
  {H | H.1 ∈ sourceHeadFactorCoordinateWindow r ρ}

/-- The slice-coordinate window is open in the slice topology. -/
theorem isOpen_sourceHeadGaugeSliceCoordinateWindow
    (d r : ℕ)
    (hrD : r < d + 1)
    (ρ : ℝ) :
    IsOpen (sourceHeadGaugeSliceCoordinateWindow d r hrD ρ) := by
  have hfull :
      IsOpen
        {H : Matrix (Fin r) (Fin r) ℂ |
          ∀ a b, ‖H a b -
            (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ρ} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b =>
        isOpen_lt
          (by
            fun_prop)
          continuous_const
  exact hfull.preimage continuous_subtype_val

/-- The slice center belongs to every positive slice-coordinate window. -/
theorem sourceHeadGaugeSliceCenter_mem_coordinateWindow
    (d r : ℕ)
    (hrD : r < d + 1)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    sourceHeadGaugeSliceCenter d r hrD ∈
      sourceHeadGaugeSliceCoordinateWindow d r hrD ρ := by
  intro a b
  simpa [sourceHeadGaugeSliceCenter, sourceHeadGaugeSliceCoordinateWindow,
    sourceHeadFactorCoordinateWindow] using hρ

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

/-- Legacy full-matrix head-gauge data for the signature-relative
factorization.  This interface is too strong to be constructible for
`r >= 2`: the map `H ↦ H * η * Hᵀ` is not locally injective on the full matrix
space.  New route code should use `SourceRankDeficientHeadSliceGaugeData`
below, where the source domain is a transverse slice. -/
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

/-- Corrected local head-gauge data on a transverse slice.  This is the
mathematically viable replacement for trying to invert
`H ↦ H * η * Hᵀ` on an open neighborhood in the full matrix space: the
complex orthogonal stabilizer prevents full-space local injectivity when
`r >= 2`, but the slice admits an inverse-function chart. -/
structure SourceRankDeficientHeadSliceGaugeData
    (d r : ℕ)
    (hrD : r < d + 1) where
  factorDomain : Set (SourceHeadGaugeSlice d r hrD)
  factorDomain_open : IsOpen factorDomain
  factorDomain_center_mem : sourceHeadGaugeSliceCenter d r hrD ∈ factorDomain
  factorDomain_coordinate :
    ∃ ρ : ℝ, 0 < ρ ∧
      sourceHeadGaugeSliceCoordinateWindow d r hrD ρ ⊆ factorDomain
  U : Set (SourceSymmetricMatrixCoord r)
  U_open : IsOpen U
  center_mem : sourceHeadMetricSymmCoord d r hrD ∈ U
  factor : SourceSymmetricMatrixCoord r → SourceHeadGaugeSlice d r hrD
  factor_mem_domain : ∀ A ∈ U, factor A ∈ factorDomain
  factor_continuousOn : ContinuousOn factor U
  factor_center : factor (sourceHeadMetricSymmCoord d r hrD) =
    sourceHeadGaugeSliceCenter d r hrD
  factor_gram :
    ∀ A ∈ U,
      (factor A).1 * sourceHeadMetric d r hrD * (factor A).1ᵀ =
        (A : Matrix (Fin r) (Fin r) ℂ)
  factorDomain_mem :
    ∀ H ∈ factorDomain, sourceHeadFactorGramSymmCoord d r hrD H.1 ∈ U
  factor_left_inverse :
    ∀ H ∈ factorDomain,
      factor (sourceHeadFactorGramSymmCoord d r hrD H.1) = H
  factor_det_unit : ∀ A ∈ U, IsUnit ((factor A).1).det

/-- Minimal head-factor data used by the Witt/head-normalizer.

The residual-tail membership proof uses only the symmetric-head neighborhood,
the selected factor, the signature-relative Gram identity, and determinant
invertibility.  Keeping these fields separate lets the same proof consume the
correct sliced head gauge without requiring the impossible full-matrix local
left inverse. -/
structure SourceRankDeficientHeadFactorData
    (d r : ℕ)
    (hrD : r < d + 1) where
  U : Set (SourceSymmetricMatrixCoord r)
  U_open : IsOpen U
  factor : SourceSymmetricMatrixCoord r → Matrix (Fin r) (Fin r) ℂ
  factor_continuousOn : ContinuousOn factor U
  factor_gram :
    ∀ A ∈ U,
      factor A * sourceHeadMetric d r hrD * (factor A)ᵀ =
        (A : Matrix (Fin r) (Fin r) ℂ)
  factor_det_unit : ∀ A ∈ U, IsUnit (factor A).det

namespace SourceRankDeficientHeadGaugeData

/-- The legacy full-matrix gauge supplies the minimal head-factor interface. -/
def toHeadFactorData
    {d r : ℕ}
    {hrD : r < d + 1}
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    SourceRankDeficientHeadFactorData d r hrD where
  U := Head.U
  U_open := Head.U_open
  factor := Head.factor
  factor_continuousOn := Head.factor_continuousOn
  factor_gram := Head.factor_gram
  factor_det_unit := Head.factor_det_unit

end SourceRankDeficientHeadGaugeData

namespace SourceRankDeficientHeadSliceGaugeData

/-- The corrected sliced gauge supplies the same minimal head-factor interface
by forgetting the slice proof on the selected factor. -/
def toHeadFactorData
    {d r : ℕ}
    {hrD : r < d + 1}
    (Head : SourceRankDeficientHeadSliceGaugeData d r hrD) :
    SourceRankDeficientHeadFactorData d r hrD where
  U := Head.U
  U_open := Head.U_open
  factor := fun A => (Head.factor A).1
  factor_continuousOn := by
    exact continuous_subtype_val.comp_continuousOn Head.factor_continuousOn
  factor_gram := Head.factor_gram
  factor_det_unit := Head.factor_det_unit

end SourceRankDeficientHeadSliceGaugeData

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

/-- A signature-relative head factor makes the selected Schur head block
invertible. -/
theorem sourceOrientedSchurHeadBlock_det_isUnit_of_headFactor
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
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

/-- Legacy full-gauge specialization of
`sourceOrientedSchurHeadBlock_det_isUnit_of_headFactor`. -/
theorem sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det :=
  sourceOrientedSchurHeadBlock_det_isUnit_of_headFactor
    d n r hrD hrn hGvar Head.toHeadFactorData hHead

/-- Once the shifted residual-tail datum is known to lie on the shifted-tail
oriented variety, the full Schur residual packet is just algebra. -/
def sourceOriented_schurResidualData_of_tail_mem_headFactor
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
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
        sourceOrientedSchurHeadBlock_det_isUnit_of_headFactor
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

/-- Legacy full-gauge specialization of
`sourceOriented_schurResidualData_of_tail_mem_headFactor`. -/
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
    SourceOrientedSchurResidualData d n r hrD hrn G :=
  sourceOriented_schurResidualData_of_tail_mem_headFactor
    d n r hrD hrn hGvar Head.toHeadFactorData hHead htail_mem

/-- Sliced-gauge specialization of
`sourceOriented_schurResidualData_of_tail_mem_headFactor`. -/
def sourceOriented_schurResidualData_of_tail_mem_headSliceGauge
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadSliceGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (htail_mem :
      sourceOrientedSchurResidualTailData d n r hrD hrn G
          ((Head.factor
            (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)).1) ∈
        sourceShiftedTailOrientedVariety d r hrD (n - r)) :
    SourceOrientedSchurResidualData d n r hrD hrn G :=
  sourceOriented_schurResidualData_of_tail_mem_headFactor
    d n r hrD hrn hGvar Head.toHeadFactorData hHead htail_mem

end BHW
