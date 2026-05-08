import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuationTrace

/-!
# Finite uniqueness propagation for source-oriented transfer skeletons

This file contains the purely finite induction that propagates one-step
Hall-Wightman/Jost uniqueness along a fixed transfer-control skeleton.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- If two chart sequences are built over the same source nodes and the same
branch-free transfer controls, and every stored control has the one-step
uniqueness property, then equality of the initial branches on a source seed
propagates to a local terminal comparison at the last node.

This is the finite induction layer behind the certified trace comparison: the
remaining closed-path theorem must still provide the correct shared skeleton or
closed-return seed, but the repeated one-step propagation is mechanical. -/
noncomputable def bhw_jost_orientedTerminalComparison_of_sharedTransferSkeleton
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    {m : ℕ}
    (node : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ)
    (nodeU : ∀ j, node j ∈ U)
    (stepControl :
      ∀ _ : Fin m,
        BHWJostOrientedBranchFreeTransferControl hd n τ U)
    (step_left_mem :
      ∀ j, node (Fin.castSucc j) ∈ (stepControl j).N)
    (step_right_mem :
      ∀ j, node j.succ ∈ (stepControl j).N)
    (step_unique :
      ∀ j, BHWJostOrientedTransferControlHasUniqueNext (stepControl j))
    (CA CB :
      Fin (m + 1) → BHWJostLocalOrientedContinuationChart hd n τ U)
    (node_mem_A : ∀ j, node j ∈ (CA j).carrier)
    (node_mem_B : ∀ j, node j ∈ (CB j).carrier)
    (step_chart_A :
      ∀ j,
        (stepControl j).transferChart
          (node (Fin.castSucc j)) (node j.succ)
          (step_left_mem j) (nodeU (Fin.castSucc j))
          (step_right_mem j) (nodeU j.succ)
          (CA (Fin.castSucc j)) (node_mem_A (Fin.castSucc j)) =
          CA j.succ)
    (step_chart_B :
      ∀ j,
        (stepControl j).transferChart
          (node (Fin.castSucc j)) (node j.succ)
          (step_left_mem j) (nodeU (Fin.castSucc j))
          (step_right_mem j) (nodeU j.succ)
          (CB (Fin.castSucc j)) (node_mem_B (Fin.castSucc j)) =
          CB j.succ)
    (sourceSeed : Set (Fin n → Fin (d + 1) → ℂ))
    (sourceSeed_mem : node 0 ∈ sourceSeed)
    (sourceSeed_open : IsOpen sourceSeed)
    (sourceSeed_preconnected : IsPreconnected sourceSeed)
    (sourceSeed_sub_A : sourceSeed ⊆ (CA 0).carrier)
    (sourceSeed_sub_B : sourceSeed ⊆ (CB 0).carrier)
    (sourceSeed_eq : Set.EqOn (CA 0).branch (CB 0).branch sourceSeed) :
    BHWLocalChartTerminalComparisonData
      (CA (Fin.last m)) (CB (Fin.last m)) (node (Fin.last m)) := by
  induction m generalizing sourceSeed with
  | zero =>
      let P :
          BHWLocalChartTerminalComparisonData
            (CA 0) (CB 0) (node 0) :=
        {
        terminalPatch := sourceSeed
        endpoint_mem := sourceSeed_mem
        terminalPatch_open := sourceSeed_open
        terminalPatch_preconnected := sourceSeed_preconnected
        terminalPatch_sub_left := sourceSeed_sub_A
        terminalPatch_sub_right := sourceSeed_sub_B
        terminal_branches_eq := sourceSeed_eq }
      simpa using P
  | succ m ih =>
      let nodePrefix : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ :=
        fun j => node (Fin.castSucc j)
      let stepControlPrefix :
          ∀ _ : Fin m,
            BHWJostOrientedBranchFreeTransferControl hd n τ U :=
        fun j => stepControl (Fin.castSucc j)
      let CAPrefix :
          Fin (m + 1) → BHWJostLocalOrientedContinuationChart hd n τ U :=
        fun j => CA (Fin.castSucc j)
      let CBPrefix :
          Fin (m + 1) → BHWJostLocalOrientedContinuationChart hd n τ U :=
        fun j => CB (Fin.castSucc j)
      have nodeU_prefix : ∀ j, nodePrefix j ∈ U := by
        intro j
        exact nodeU (Fin.castSucc j)
      have step_left_mem_prefix :
          ∀ j, nodePrefix (Fin.castSucc j) ∈ (stepControlPrefix j).N := by
        intro j
        simpa [nodePrefix, stepControlPrefix] using
          step_left_mem (Fin.castSucc j)
      have step_right_mem_prefix :
          ∀ j, nodePrefix j.succ ∈ (stepControlPrefix j).N := by
        intro j
        have hidx :
            (Fin.castSucc j).succ = (j.succ).castSucc := by
          ext
          rfl
        change node ((j.succ).castSucc) ∈
          (stepControl (Fin.castSucc j)).N
        rw [← hidx]
        exact step_right_mem (Fin.castSucc j)
      have step_unique_prefix :
          ∀ j,
            BHWJostOrientedTransferControlHasUniqueNext
              (stepControlPrefix j) := by
        intro j
        exact step_unique (Fin.castSucc j)
      have node_mem_A_prefix :
          ∀ j, nodePrefix j ∈ (CAPrefix j).carrier := by
        intro j
        exact node_mem_A (Fin.castSucc j)
      have node_mem_B_prefix :
          ∀ j, nodePrefix j ∈ (CBPrefix j).carrier := by
        intro j
        exact node_mem_B (Fin.castSucc j)
      have step_chart_A_prefix :
          ∀ j,
            (stepControlPrefix j).transferChart
              (nodePrefix (Fin.castSucc j)) (nodePrefix j.succ)
              (step_left_mem_prefix j) (nodeU_prefix (Fin.castSucc j))
              (step_right_mem_prefix j) (nodeU_prefix j.succ)
              (CAPrefix (Fin.castSucc j))
              (node_mem_A_prefix (Fin.castSucc j)) =
              CAPrefix j.succ := by
        intro j
        dsimp [nodePrefix, stepControlPrefix, CAPrefix, nodeU_prefix,
          node_mem_A_prefix]
        exact step_chart_A (Fin.castSucc j)
      have step_chart_B_prefix :
          ∀ j,
            (stepControlPrefix j).transferChart
              (nodePrefix (Fin.castSucc j)) (nodePrefix j.succ)
              (step_left_mem_prefix j) (nodeU_prefix (Fin.castSucc j))
              (step_right_mem_prefix j) (nodeU_prefix j.succ)
              (CBPrefix (Fin.castSucc j))
              (node_mem_B_prefix (Fin.castSucc j)) =
              CBPrefix j.succ := by
        intro j
        dsimp [nodePrefix, stepControlPrefix, CBPrefix, nodeU_prefix,
          node_mem_B_prefix]
        exact step_chart_B (Fin.castSucc j)
      have Pprev :
          BHWLocalChartTerminalComparisonData
            (CAPrefix (Fin.last m)) (CBPrefix (Fin.last m))
            (nodePrefix (Fin.last m)) :=
        ih nodePrefix nodeU_prefix stepControlPrefix
          step_left_mem_prefix step_right_mem_prefix step_unique_prefix
          CAPrefix CBPrefix node_mem_A_prefix node_mem_B_prefix
          step_chart_A_prefix step_chart_B_prefix sourceSeed
          (by simpa [nodePrefix] using sourceSeed_mem)
          sourceSeed_open sourceSeed_preconnected
          (by simpa [CAPrefix] using sourceSeed_sub_A)
          (by simpa [CBPrefix] using sourceSeed_sub_B)
          (by simpa [CAPrefix, CBPrefix] using sourceSeed_eq)
      have Pstep :
          BHWLocalChartTerminalComparisonData
            ((stepControl (Fin.last m)).transferChart
              (node (Fin.castSucc (Fin.last m))) (node (Fin.last m).succ)
              (step_left_mem (Fin.last m))
              (nodeU (Fin.castSucc (Fin.last m)))
              (step_right_mem (Fin.last m))
              (nodeU (Fin.last m).succ)
              (CA (Fin.castSucc (Fin.last m)))
              (node_mem_A (Fin.castSucc (Fin.last m))))
            ((stepControl (Fin.last m)).transferChart
              (node (Fin.castSucc (Fin.last m))) (node (Fin.last m).succ)
              (step_left_mem (Fin.last m))
              (nodeU (Fin.castSucc (Fin.last m)))
              (step_right_mem (Fin.last m))
              (nodeU (Fin.last m).succ)
              (CB (Fin.castSucc (Fin.last m)))
              (node_mem_B (Fin.castSucc (Fin.last m))))
            (node (Fin.last m).succ) :=
        step_unique (Fin.last m)
          (step_left_mem (Fin.last m))
          (nodeU (Fin.castSucc (Fin.last m)))
          (step_right_mem (Fin.last m))
          (nodeU (Fin.last m).succ)
          (node_mem_A (Fin.castSucc (Fin.last m)))
          (node_mem_B (Fin.castSucc (Fin.last m)))
          Pprev.terminalPatch
          (by simpa [nodePrefix, CAPrefix, CBPrefix] using Pprev.endpoint_mem)
          (by
            intro x hx
            exact ⟨
              by
                simpa [CAPrefix] using Pprev.terminalPatch_sub_left hx,
              by
                simpa [CBPrefix] using Pprev.terminalPatch_sub_right hx⟩)
          (by simpa [CAPrefix, CBPrefix] using Pprev.terminal_branches_eq)
      have hlast_succ :
          (Fin.last m).succ = Fin.last (m + 1) := by
        ext
        rfl
      have hA := step_chart_A (Fin.last m)
      have hB := step_chart_B (Fin.last m)
      rw [← hlast_succ]
      rw [← hA, ← hB]
      exact Pstep

end BHW
