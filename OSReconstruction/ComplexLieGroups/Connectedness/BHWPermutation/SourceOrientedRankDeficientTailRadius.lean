import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedTailEuclidean
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurTailNormal

/-!
# Tail-radius data for rank-deficient source Schur charts

This file records a conditional tail-radius adapter.  It does not construct
same-radius compatible tail estimates; in general tail dimension that is not
the active local-image shape.  The current route uses a target-shaped
tail-window parameter set built from the one-way shifted realization theorem.
This adapter remains useful only when an external compatible packet has
already been supplied.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Smallness of the explicit Schur residual-tail datum for a fixed source
point and selected head factor. -/
structure SourceOrientedSchurTailSmallFor
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (η : ℝ)
    (G : SourceOrientedGramData d n)
    (headFactor : Matrix (Fin r) (Fin r) ℂ) where
  gram_bound :
    ∀ u v,
      ‖(sourceOrientedSchurResidualTailData d n r hrD hrn G headFactor).gram
        u v‖ < η
  det_bound :
    ∀ ι,
      ‖(sourceOrientedSchurResidualTailData d n r hrD hrn G headFactor).det
        ι‖ < η

/-- Tail-radius choice for the source-oriented rank-deficient normal
parameters.  The forward smallness direction needs invertibility of the
normal head, which is supplied by the normal-ball shrink in the local-image
proof. -/
structure SourceOrientedRankDeficientTailRadiusChoice
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) where
  tailEpsilon : ℝ
  tailEpsilon_pos : 0 < tailEpsilon
  tailEta : ℝ
  tailEta_pos : 0 < tailEta
  tailRealize :
    ∀ T : SourceShiftedTailOrientedData d r hrD (n - r),
      T ∈ sourceShiftedTailOrientedVariety d r hrD (n - r) →
      (∀ u v, ‖T.gram u v‖ < tailEta) →
      (∀ ι, ‖T.det ι‖ < tailEta) →
      ∃ q : Fin (n - r) → Fin (d + 1 - r) → ℂ,
        (∀ u μ, ‖q u μ‖ < tailEpsilon) ∧
        sourceShiftedTailOrientedInvariant d r hrD (n - r) q = T
  normalParam_tail_small :
    ∀ p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn,
      IsUnit p.head.det →
      (∀ u μ, ‖p.tail u μ‖ < tailEpsilon) →
      SourceOrientedSchurTailSmallFor d n r hrD hrn tailEta
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        p.head

namespace SourceOrientedRankDeficientTailRadiusChoice

/-- A compatible shifted-tail small-realization packet supplies the
source-oriented rank-deficient tail-radius choice. -/
def ofShiftedCompatible
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (C : SourceShiftedTailCompatibleSmallRealization d r hrD (n - r)) :
    SourceOrientedRankDeficientTailRadiusChoice d n r hrD hrn where
  tailEpsilon := C.epsilon
  tailEpsilon_pos := C.epsilon_pos
  tailEta := C.eta
  tailEta_pos := C.eta_pos
  tailRealize := C.realize
  normalParam_tail_small := by
    intro p hH hp_tail
    have hsmall := C.self_image_small p.tail hp_tail
    have htail_eq :
        sourceOrientedSchurResidualTailData d n r hrD hrn
            (sourceOrientedMinkowskiInvariant d n
              (sourceOrientedNormalParameterVector d n r hrD hrn p))
            p.head =
          sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail :=
      sourceOrientedSchurResidualTailData_normalParameter
        d n r hrD hrn p hH
    exact
      { gram_bound := by
          intro u v
          have h := hsmall.1 u v
          simpa [htail_eq] using h
        det_bound := by
          intro ι
          have h := hsmall.2 ι
          simpa [htail_eq] using h }

end SourceOrientedRankDeficientTailRadiusChoice

end BHW
