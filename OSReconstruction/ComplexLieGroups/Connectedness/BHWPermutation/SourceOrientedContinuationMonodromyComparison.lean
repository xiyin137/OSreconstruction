import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuationProducers
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedBHWFiniteOverlap

/-!
# Closed-loop monodromy to terminal-chain comparison

This file contains small bridges from the checked closed-loop source monodromy
consumers to the terminal-chain comparison API used by the source-patch atlas.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

namespace BHWJostOrientedClosedContinuationLoop

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}

/-- The normalized zero-step base chain associated with the initial chart of a
closed continuation loop. -/
def normalizedBaseChain
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
    BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 p0 :=
  BHWJostOrientedSourcePatchContinuationChain.base
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    (p0 := p0) (L.chain.localChart 0) L.chain.base_mem
    (by
      have hnode : L.chain.node 0 ∈ L.chain.chart 0 := L.chain.node_mem 0
      have hzero : L.chain.node 0 = p0 := L.chain.node_zero
      rw [hzero] at hnode
      simpa [L.chain.chart_eq_local 0] using hnode)
    L.chain.start_patch L.chain.start_patch_open
    L.chain.start_patch_preconnected L.chain.start_patch_nonempty
    L.chain.start_mem
    (by
      intro y hy
      have hyStart := L.chain.start_patch_sub hy
      exact ⟨hyStart.1, by
        simpa [L.chain.chart_eq_local 0] using hyStart.2⟩)
    (by
      intro y hy
      have hyChart : y ∈ L.chain.chart 0 :=
        (L.chain.start_patch_sub hy).2
      have hlocal :
          L.chain.branch 0 y = (L.chain.localChart 0).branch y :=
        L.chain.branch_eq_local 0 y hyChart
      exact hlocal.symm.trans (L.chain.start_agree y hy))

/-- Source monodromy on the closing source patch packages as terminal-chain
comparison between the closed-loop chain and its normalized zero-step base
chain. -/
def terminalChainComparison_base_of_sourceMonodromy
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    (hmon :
      Set.EqOn
        (L.chain.branch (Fin.last L.chain.m))
        B0
        L.closing_patch) :
    BHWOrientedTerminalChainComparisonData
      L.chain L.normalizedBaseChain where
  terminalPatch := L.closing_patch
  endpoint_mem := L.closing_patch_mem
  terminalPatch_open := L.closing_patch_open
  terminalPatch_preconnected := L.closing_patch_preconnected
  terminalPatch_sub_left := L.closing_patch_sub_final
  terminalPatch_sub_right := by
    intro y hy
    have hyStartPatch : y ∈ L.chain.start_patch :=
      L.closing_patch_sub_start hy
    have hyChart : y ∈ L.chain.chart 0 :=
      (L.chain.start_patch_sub hyStartPatch).2
    have hyLocal : y ∈ (L.chain.localChart 0).carrier := by
      simpa [L.chain.chart_eq_local 0] using hyChart
    simpa [normalizedBaseChain,
      BHWJostOrientedSourcePatchContinuationChain.base] using hyLocal
  terminal_branches_eq := by
    intro y hy
    have hyStartPatch : y ∈ L.chain.start_patch :=
      L.closing_patch_sub_start hy
    have hyChart : y ∈ L.chain.chart 0 :=
      (L.chain.start_patch_sub hyStartPatch).2
    have hlocal :
        L.chain.branch 0 y = (L.chain.localChart 0).branch y :=
      L.chain.branch_eq_local 0 y hyChart
    have hbaseB0 :
        L.normalizedBaseChain.branch
            (Fin.last L.normalizedBaseChain.m) y = B0 y := by
      have hchartB0 :
          (L.chain.localChart 0).branch y = B0 y :=
        hlocal.symm.trans (L.chain.start_agree y hyStartPatch)
      simpa [normalizedBaseChain,
        BHWJostOrientedSourcePatchContinuationChain.base] using hchartB0
    exact (hmon hy).trans hbaseB0.symm

/-- Closing-patch terminal-seed data packages as terminal-chain comparison
between the closed-loop chain and its normalized zero-step base chain. -/
def terminalChainComparison_base_of_closingPatchTerminalSeedData
    {L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}
    (P : BHWJostOrientedClosingPatchTerminalSeedData L) :
    BHWOrientedTerminalChainComparisonData
      L.chain L.normalizedBaseChain :=
  L.terminalChainComparison_base_of_sourceMonodromy
    P.to_sourceMonodromy_headSliceIFT

end BHWJostOrientedClosedContinuationLoop

end BHW
