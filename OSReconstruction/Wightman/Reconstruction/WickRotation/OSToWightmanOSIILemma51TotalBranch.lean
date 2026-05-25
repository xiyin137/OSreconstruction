import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51CoordinateEstimate
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIParametricFlatTubeBranch

/-!
# OS II Lemma 5.1 Total Branch Pullback

This small companion composes the neutral Lemma 5.1 coefficient estimate with
the explicit OS-II total log semigroup branch.  It keeps the coordinate
estimate file independent of the OS semigroup payload while exposing the
paper-step theorem needed by the E-to-R route.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- OS II Lemma 5.1 applied to the explicit total log semigroup branch.

Near any positive physical time coordinate, the coefficient chart from
`(5.11)`--`(5.12)` pulls the log-domain semigroup representative back to a
holomorphic local polydisc. -/
theorem osiiLemma51_totalLogSemigroupBranch_local_polydisc
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T) (ξ : Fin 4 → ℝ) (hξ0 : 0 < ξ 0)
    (η : ℝ) (hη : 0 < η)
    (hηsum : (4 : ℝ) * Real.arctan η < Real.pi / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin 4 → ℂ =>
          osiiTotalLogSemigroupBranch (d := d) OS lgc F G
            (fun μ : Fin 4 =>
              Complex.log (osiiLemma51CoeffMap4 T ξ ζ μ)))
        {ζ : Fin 4 → ℂ | ∀ ν : Fin 4, ‖ζ ν‖ < ρ} := by
  exact
    osiiLemma51_local_polydisc_logDomain_extension_differentiableOn
      T hT ξ hξ0 η hη hηsum
      (osiiTotalLogSemigroupBranch (d := d) OS lgc F G)
      (differentiableOn_osiiTotalLogSemigroupBranch_l1
        (d := d) (m := 4) OS lgc F G)

end OSReconstruction
