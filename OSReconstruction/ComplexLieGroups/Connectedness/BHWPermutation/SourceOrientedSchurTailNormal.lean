import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGauge
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedTailEuclidean

/-!
# Schur residual tail for normal parameters

This file checks the forward normal-parameter sanity statement for the
source-oriented Schur residual interface: when the oriented datum is already
written in normal parameters and the head factor is the parameter head, the
explicit Schur residual tail datum is exactly the shifted-tail invariant of the
parameter tail.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The Schur head block of a normal-parameter invariant is the
signature-relative head Gram `H η Hᵀ`. -/
theorem sourceOrientedSchurHeadBlock_normalParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    sourceOrientedSchurHeadBlock n r hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p)) =
      p.head * sourceHeadMetric d r hrD * p.headᵀ := by
  ext a b
  change
    sourceVectorMinkowskiInner d
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceHead hrn a))
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceHead hrn b)) =
      (p.head * sourceHeadMetric d r hrD * p.headᵀ) a b
  rw [sourceOrientedNormalParameterVector_head,
    sourceOrientedNormalParameterVector_head,
    sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector]

/-- The Schur mixed block of a normal-parameter invariant is `mixed * A`,
where `A` is the normal head Gram. -/
theorem sourceOrientedSchurMixedBlock_normalParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    sourceOrientedSchurMixedBlock n r hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p)) =
      p.mixed * (p.head * sourceHeadMetric d r hrD * p.headᵀ) := by
  ext u a
  change
    sourceVectorMinkowskiInner d
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceTail hrn u))
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceHead hrn a)) =
      (p.mixed * (p.head * sourceHeadMetric d r hrD * p.headᵀ)) u a
  rw [sourceOrientedNormalParameterVector_head,
    sourceVectorMinkowskiInner_tailParameterVector_head]

/-- In a normal-parameter invariant, the Schur mixed coefficient recovers the
stored mixed matrix. -/
theorem sourceSchurMixedCoeff_normalParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hA :
      IsUnit (p.head * sourceHeadMetric d r hrD * p.headᵀ).det) :
    sourceSchurMixedCoeff n r hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        (p.head * sourceHeadMetric d r hrD * p.headᵀ) =
      p.mixed := by
  rw [sourceSchurMixedCoeff, sourceOrientedSchurMixedBlock_normalParameter]
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]

/-- The Schur complement of a normal-parameter invariant is the shifted tail
Gram. -/
theorem sourceSchurComplement_normalParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hA :
      IsUnit (p.head * sourceHeadMetric d r hrD * p.headᵀ).det) :
    sourceSchurComplement n r hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        (p.head * sourceHeadMetric d r hrD * p.headᵀ) =
      sourceShiftedTailGram d r hrD (n - r) p.tail := by
  ext u v
  have hL :=
    sourceSchurMixedCoeff_normalParameter d n r hrD hrn p hA
  rw [sourceSchurComplement]
  rw [hL]
  change
    sourceVectorMinkowskiInner d
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceTail hrn u))
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceTail hrn v)) -
        (p.mixed * (p.head * sourceHeadMetric d r hrD * p.headᵀ) *
          p.mixedᵀ) u v =
      sourceShiftedTailGram d r hrD (n - r) p.tail u v
  rw [sourceVectorMinkowskiInner_tailParameterVector_tail]
  simp [sourceShiftedTailGram]

/-- The explicit Schur residual tail datum of a normal-parameter invariant is
the shifted-tail invariant of the parameter tail. -/
theorem sourceOrientedSchurResidualTailData_normalParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hH : IsUnit p.head.det)
    (hhead :
      p.head * sourceHeadMetric d r hrD * p.headᵀ =
        sourceOrientedSchurHeadBlock n r hrn
          (sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p)) := by
      exact (sourceOrientedSchurHeadBlock_normalParameter d n r hrD hrn p).symm) :
    sourceOrientedSchurResidualTailData d n r hrD hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        p.head =
      sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail := by
  have hA :
      IsUnit (p.head * sourceHeadMetric d r hrD * p.headᵀ).det := by
    have hη : IsUnit (sourceHeadMetric d r hrD).det :=
      sourceHeadMetric_det_isUnit d r hrD
    have hHt : IsUnit p.headᵀ.det := Matrix.isUnit_det_transpose p.head hH
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hH.mul hη).mul hHt
  apply SourceShiftedTailOrientedData.ext
  · rw [sourceOrientedSchurResidualTailData_gram]
    rw [← hhead]
    exact sourceSchurComplement_normalParameter d n r hrD hrn p hA
  · funext lam
    rw [sourceOrientedSchurResidualTailData_det,
      sourceShiftedTailOrientedInvariant_det]
    simp only [sourceSchurResidualDeterminants,
      sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det]
    rw [sourceFullFrameDet_normalParameter_headTail]
    field_simp [hH.ne_zero]
    rfl

/-- Normal-parameter residual tails lie on the shifted-tail variety. -/
theorem sourceOrientedSchurResidualTailData_normalParameter_mem_variety
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hH : IsUnit p.head.det) :
    sourceOrientedSchurResidualTailData d n r hrD hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        p.head ∈
      sourceShiftedTailOrientedVariety d r hrD (n - r) := by
  refine ⟨p.tail, ?_⟩
  exact (sourceOrientedSchurResidualTailData_normalParameter d n r hrD hrn p hH).symm

end BHW
