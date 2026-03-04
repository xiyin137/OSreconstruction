import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlowBlockers.Tail

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

example
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hanchor : d1N2PairedChartAnchorConnected (Classical.choose hsource)) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantLightConeWitness q0 q1 p s →
      d1N2InvariantLightConeWitness q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0 :=
  d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_of_pairedChartAnchorConnected
    f hsource hanchor

example
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hBoundaryId :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        ∃ x : Fin 2 → Fin (1 + 1) → ℝ,
          d1InvariantQuad (realEmbed x) = (q0, q1, p, s) ∧
          f q0 q1 p s = (Classical.choose hsource) (realEmbed x) ∧
          f q1 q0 p (-s) =
            (Classical.choose hsource)
              (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ))) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f :=
  blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred
    f hsource hBoundaryId

example
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hBoundaryId :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        ∃ x : Fin 2 → Fin (1 + 1) → ℝ,
          d1InvariantQuad (realEmbed x) = (q0, q1, p, s) ∧
          f q0 q1 p s = (Classical.choose hsource) (realEmbed x) ∧
          f q1 q0 p (-s) =
            (Classical.choose hsource)
              (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ)))
    (q0 q1 p s : ℂ)
    (hquad : s ^ 2 = 4 * (p ^ 2 - q0 * q1))
    (hreal : d1N2InvariantRealizable q0 q1 p s)
    (hswapReal : d1N2InvariantRealizable q1 q0 p (-s)) :
    f q0 q1 p s - f q1 q0 p (-s) = 0 :=
by
  have hfw : d1N2InvariantForwardizableSwap q0 q1 p s :=
    d1N2InvariantForwardizable_of_realizable_pair hreal hswapReal
  exact
    blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred
      f hsource hBoundaryId q0 q1 p s hquad hfw

end BHW
