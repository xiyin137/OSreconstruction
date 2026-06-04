import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurTailNormal

/-!
# Schur residual tails for sliced head gauges

The constructible head gauge is a local inverse on a transverse slice through
`H ↦ H * η * Hᵀ`, not on an open neighborhood in the full matrix space.  This
file ports the forward normal-parameter extraction lemmas to the sliced gauge
interface.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- A sliced head factor in the remembered source domain is invertible. -/
theorem sourceRankDeficientHeadSliceGauge_factor_det_unit_of_domain
    (d r : ℕ)
    (hrD : r < d + 1)
    (Head : SourceRankDeficientHeadSliceGaugeData d r hrD)
    (H : SourceHeadGaugeSlice d r hrD)
    (hH : H ∈ Head.factorDomain) :
    IsUnit H.1.det := by
  have hU : sourceHeadFactorGramSymmCoord d r hrD H.1 ∈ Head.U :=
    Head.factorDomain_mem H hH
  have hunit :=
    Head.factor_det_unit (sourceHeadFactorGramSymmCoord d r hrD H.1) hU
  have hfactor :
      (Head.factor (sourceHeadFactorGramSymmCoord d r hrD H.1)).1 = H.1 :=
    congrArg Subtype.val (Head.factor_left_inverse H hH)
  simpa [hfactor] using hunit

/-- If a normal parameter uses a head matrix coming from the sliced gauge
domain, then the gauge-selected residual tail of its normal image is the stored
shifted-tail invariant. -/
theorem sourceOrientedSchurResidualTailData_normalParameter_headSliceGauge
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadSliceGaugeData d r hrD)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (H : SourceHeadGaugeSlice d r hrD)
    (hH : H ∈ Head.factorDomain)
    (hphead : p.head = H.1) :
    sourceOrientedSchurResidualTailData d n r hrD hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn
            (G := sourceOrientedMinkowskiInvariant d n
              (sourceOrientedNormalParameterVector d n r hrD hrn p))
            ⟨sourceOrientedNormalParameterVector d n r hrD hrn p, rfl⟩)).1 =
      sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail := by
  let Acoord :=
    sourceOrientedSchurHeadBlockSymm d n r hrD hrn
      (G := sourceOrientedMinkowskiInvariant d n
        (sourceOrientedNormalParameterVector d n r hrD hrn p))
      ⟨sourceOrientedNormalParameterVector d n r hrD hrn p, rfl⟩
  have hAeq :
      Acoord = sourceHeadFactorGramSymmCoord d r hrD H.1 := by
    dsimp [Acoord]
    rw [sourceOrientedSchurHeadBlockSymm_normalParameter, hphead]
  have hfactor :
      (Head.factor Acoord).1 = p.head := by
    have hslice : Head.factor Acoord = H := by
      rw [hAeq]
      exact Head.factor_left_inverse H hH
    rw [hslice, hphead]
  have hdet : IsUnit p.head.det := by
    simpa [hphead] using
      sourceRankDeficientHeadSliceGauge_factor_det_unit_of_domain
        d r hrD Head H hH
  rw [hfactor]
  exact sourceOrientedSchurResidualTailData_normalParameter d n r hrD hrn p hdet

/-- With a sliced gauge-domain head, the Schur mixed coefficient extracted
from a normal image is the stored mixed coordinate. -/
theorem sourceSchurMixedCoeff_normalParameter_headSliceGauge
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadSliceGaugeData d r hrD)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (H : SourceHeadGaugeSlice d r hrD)
    (hH : H ∈ Head.factorDomain)
    (hphead : p.head = H.1) :
    sourceSchurMixedCoeff n r hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        (sourceOrientedSchurHeadBlock n r hrn
          (sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p))) =
      p.mixed := by
  have hHdet : IsUnit p.head.det := by
    simpa [hphead] using
      sourceRankDeficientHeadSliceGauge_factor_det_unit_of_domain
        d r hrD Head H hH
  have hA :
      IsUnit (p.head * sourceHeadMetric d r hrD * p.headᵀ).det := by
    have hη : IsUnit (sourceHeadMetric d r hrD).det :=
      sourceHeadMetric_det_isUnit d r hrD
    have hHt : IsUnit p.headᵀ.det := Matrix.isUnit_det_transpose p.head hHdet
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hHdet.mul hη).mul hHt
  rw [sourceOrientedSchurHeadBlock_normalParameter]
  exact sourceSchurMixedCoeff_normalParameter d n r hrD hrn p hA

/-- Gauge-selected residual tails of sliced-domain normal images lie on the
shifted-tail variety. -/
theorem sourceOrientedSchurResidualTailData_normalParameter_headSliceGauge_mem_variety
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadSliceGaugeData d r hrD)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (H : SourceHeadGaugeSlice d r hrD)
    (hH : H ∈ Head.factorDomain)
    (hphead : p.head = H.1) :
    sourceOrientedSchurResidualTailData d n r hrD hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn
            (G := sourceOrientedMinkowskiInvariant d n
              (sourceOrientedNormalParameterVector d n r hrD hrn p))
            ⟨sourceOrientedNormalParameterVector d n r hrD hrn p, rfl⟩)).1 ∈
      sourceShiftedTailOrientedVariety d r hrD (n - r) := by
  refine ⟨p.tail, ?_⟩
  exact
    (sourceOrientedSchurResidualTailData_normalParameter_headSliceGauge
      d n r hrD hrn Head p H hH hphead).symm

end BHW
