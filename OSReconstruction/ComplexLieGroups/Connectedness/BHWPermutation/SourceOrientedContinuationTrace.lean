import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation

/-!
# Transfer-provenance continuation traces

Recursive constructors for transfer traces.  These are kept separate from the
base continuation carriers so the hard comparison frontier stays small.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- One-step uniqueness property for a center-forgotten branch-free transfer
control.  This is the exact local Hall-Wightman/Jost theorem the strict route
must prove for controls produced by source-normal-form descent: if two
previous local branches agree on a source seed at the old node, then the two
next charts produced by the same transfer control agree on a target patch. -/
def BHWJostOrientedTransferControlHasUniqueNext
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (K : BHWJostOrientedBranchFreeTransferControl hd n τ U) : Type _ :=
  ∀ {p q : Fin n → Fin (d + 1) → ℂ}
    (hpN : p ∈ K.N) (hpU : p ∈ U)
    (hqN : q ∈ K.N) (hqU : q ∈ U)
    {CprevA CprevB : BHWJostLocalOrientedContinuationChart hd n τ U}
    (hpA : p ∈ CprevA.carrier) (hpB : p ∈ CprevB.carrier)
    (sourceSeed : Set (Fin n → Fin (d + 1) → ℂ))
    (_hsourceSeed_mem : p ∈ sourceSeed)
    (_hsourceSeed_sub : sourceSeed ⊆ CprevA.carrier ∩ CprevB.carrier)
    (_hsourceSeed_eq :
      Set.EqOn CprevA.branch CprevB.branch sourceSeed),
      BHWLocalChartTerminalComparisonData
        (K.transferChart p q hpN hpU hqN hqU CprevA hpA)
        (K.transferChart p q hpN hpU hqN hqU CprevB hpB) q

namespace BHWJostOrientedTransferContinuationTrace

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 p q center : Fin n → Fin (d + 1) → ℂ}

/-- Append one branch-free transfer step to a transfer trace. -/
def snocAtTerminalNode
    (Tr :
      BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 p)
    (N : BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    (hpN : Tr.chain.node (Fin.last Tr.chain.m) ∈ N.N)
    (hpU : Tr.chain.node (Fin.last Tr.chain.m) ∈ U)
    (hqN : q ∈ N.N) (hqU : q ∈ U) :
    BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 q :=
  let hpC :
      Tr.chain.node (Fin.last Tr.chain.m) ∈
        (Tr.chain.localChart (Fin.last Tr.chain.m)).carrier := by
    simpa [Tr.chain.chart_eq_local (Fin.last Tr.chain.m)]
      using Tr.chain.node_mem (Fin.last Tr.chain.m)
  let R :=
    N.transfer (Tr.chain.node (Fin.last Tr.chain.m)) q hpN hpU hqN hqU
      (Tr.chain.localChart (Fin.last Tr.chain.m)) hpC
  let Control :=
    BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl N
  let Cnext :=
    BHWJostOrientedSourcePatchContinuationChain.snoc
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) Tr.chain R.1 R.2
  { chain := Cnext
    stepControl := by
      intro j
      refine Fin.lastCases ?_ ?_ j
      · exact Control
      · intro i
        exact Tr.stepControl i
    step_left_mem := by
      intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa [Cnext, Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          BHWJostOrientedSourcePatchContinuationChain.snoc,
          Fin.snoc_castSucc] using hpN
      · intro i
        simpa [Cnext, Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          BHWJostOrientedSourcePatchContinuationChain.snoc,
          Fin.snoc_castSucc] using Tr.step_left_mem i
    step_right_mem := by
      intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa [Cnext, Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          BHWJostOrientedSourcePatchContinuationChain.snoc,
          Fin.snoc_last] using hqN
      · intro i
        have hidx :
            (i.castSucc : Fin (Tr.chain.m + 1)).succ =
              (i.succ).castSucc := by
          ext
          rfl
        have hnode :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q i.castSucc.succ) =
              Tr.chain.node i.succ := by
          rw [hidx]
          simpa using
            (Fin.snoc_castSucc
              (α := fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              (x := q) (p := Tr.chain.node) i.succ)
        simpa [Cnext, Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          BHWJostOrientedSourcePatchContinuationChain.snoc,
          Fin.snoc_castSucc, hnode] using Tr.step_right_mem i
    step_transfer_chart_eq := by
      intro j
      refine Fin.lastCases ?_ ?_ j
      · have hnode_left :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q (Fin.last Tr.chain.m).castSucc) =
              Tr.chain.node (Fin.last Tr.chain.m) := by
          simp
        have hnode_right :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q (Fin.last (Tr.chain.m + 1))) =
              q := by
          simp
        have hchart_left :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              Tr.chain.localChart R.1 (Fin.last Tr.chain.m).castSucc) =
              Tr.chain.localChart (Fin.last Tr.chain.m) := by
          simp
        have hchart_right :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              Tr.chain.localChart R.1 (Fin.last (Tr.chain.m + 1))) =
              R.1 := by
          simp
        dsimp [Cnext, BHWJostOrientedSourcePatchContinuationChain.snoc]
        convert
          (show
            (N.transfer (Tr.chain.node (Fin.last Tr.chain.m)) q hpN hpU
              hqN hqU (Tr.chain.localChart (Fin.last Tr.chain.m)) hpC).1 =
              R.1 by
            rfl)
          using 2
        · simp [Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          hnode_left, hnode_right, hchart_left]
      · intro i
        have hidx :
            (i.castSucc : Fin (Tr.chain.m + 1)).succ =
              (i.succ).castSucc := by
          ext
          rfl
        have hnode_right :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q i.castSucc.succ) =
              Tr.chain.node i.succ := by
          rw [hidx]
          simpa using
            (Fin.snoc_castSucc
              (α := fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              (x := q) (p := Tr.chain.node) i.succ)
        have hnode_left :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q i.castSucc.castSucc) =
              Tr.chain.node i.castSucc := by
          simp
        have hchart_right :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              Tr.chain.localChart R.1 i.castSucc.succ) =
              Tr.chain.localChart i.succ := by
          rw [hidx]
          simpa using
            (Fin.snoc_castSucc
              (α := fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              (x := R.1) (p := Tr.chain.localChart) i.succ)
        have hchart_left :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              Tr.chain.localChart R.1 i.castSucc.castSucc) =
              Tr.chain.localChart i.castSucc := by
          simp
        dsimp [Cnext, BHWJostOrientedSourcePatchContinuationChain.snoc]
        convert Tr.step_transfer_chart_eq i using 2
        · simp [Control, Fin.lastCases_castSucc] }

/-- A finite sequence of source nodes, together with centered branch-free
transfer neighborhoods controlling every adjacent pair, produces a transfer
trace. -/
theorem exists_of_nodeTransferSteps
    {m : ℕ}
    (node : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ)
    (hnode_zero : node 0 = p0)
    (hnodeU : ∀ j, node j ∈ U)
    (stepControl :
      ∀ _ : Fin m,
        Σ center : Fin n → Fin (d + 1) → ℂ,
          BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    (step_left_mem :
      ∀ j, node (Fin.castSucc j) ∈ (stepControl j).2.N)
    (step_right_mem :
      ∀ j, node j.succ ∈ (stepControl j).2.N)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    Nonempty
      (BHWJostOrientedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 (node (Fin.last m))) := by
  induction m with
  | zero =>
      have hlast : node (Fin.last 0) = p0 := by
        simpa using hnode_zero
      refine ⟨?_⟩
      rw [hlast]
      exact
        base (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
          (p0 := p0) C0 hbase hp0C start_patch hstart_open
          hstart_preconnected hstart_nonempty hstart_mem hstart_sub
          hstart_agree
  | succ m ih =>
      let nodePrefix : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ :=
        fun i => node (Fin.castSucc i)
      have hnode_zero_prefix : nodePrefix 0 = p0 := by
        simpa [nodePrefix] using hnode_zero
      have hnodeU_prefix : ∀ j, nodePrefix j ∈ U := by
        intro j
        exact hnodeU (Fin.castSucc j)
      let stepControlPrefix :
          ∀ j : Fin m,
            Σ center : Fin n → Fin (d + 1) → ℂ,
              BHWJostOrientedBranchFreeTransferNeighborhood
                hd n τ U center :=
        fun j => stepControl (Fin.castSucc j)
      have step_left_mem_prefix :
          ∀ j, nodePrefix (Fin.castSucc j) ∈
            (stepControlPrefix j).2.N := by
        intro j
        simpa [nodePrefix, stepControlPrefix] using
          step_left_mem (Fin.castSucc j)
      have step_right_mem_prefix :
          ∀ j, nodePrefix j.succ ∈ (stepControlPrefix j).2.N := by
        intro j
        have hidx :
            (Fin.castSucc j).succ = (j.succ).castSucc := by
          ext
          rfl
        change node ((j.succ).castSucc) ∈
          (stepControl (Fin.castSucc j)).2.N
        rw [← hidx]
        exact step_right_mem (Fin.castSucc j)
      rcases ih nodePrefix hnode_zero_prefix hnodeU_prefix
        stepControlPrefix step_left_mem_prefix step_right_mem_prefix with
        ⟨Trprev⟩
      let lastStep := stepControl (Fin.last m)
      have hterminal :
          Trprev.chain.node (Fin.last Trprev.chain.m) =
            node (Fin.castSucc (Fin.last m)) := by
        simpa [nodePrefix] using Trprev.chain.node_last
      have hpN :
          Trprev.chain.node (Fin.last Trprev.chain.m) ∈ lastStep.2.N := by
        rw [hterminal]
        simpa [lastStep] using step_left_mem (Fin.last m)
      have hpU :
          Trprev.chain.node (Fin.last Trprev.chain.m) ∈ U := by
        rw [hterminal]
        exact hnodeU (Fin.castSucc (Fin.last m))
      have hqN :
          node (Fin.last m).succ ∈ lastStep.2.N := by
        simpa [lastStep] using step_right_mem (Fin.last m)
      have hqU :
          node (Fin.last m).succ ∈ U :=
        hnodeU (Fin.last m).succ
      have hlast_succ :
          (Fin.last m).succ = Fin.last (m + 1) := by
        ext
        rfl
      refine ⟨?_⟩
      simpa [hlast_succ, lastStep] using
        snocAtTerminalNode
          (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
          (p0 := p0) (q := node (Fin.last m).succ)
          Trprev lastStep.2 hpN hpU hqN hqU

/-- Noncomputably select the transfer trace produced from finite node/control
data. -/
noncomputable def ofNodeTransferSteps
    {m : ℕ}
    (node : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ)
    (hnode_zero : node 0 = p0)
    (hnodeU : ∀ j, node j ∈ U)
    (stepControl :
      ∀ _ : Fin m,
        Σ center : Fin n → Fin (d + 1) → ℂ,
          BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    (step_left_mem :
      ∀ j, node (Fin.castSucc j) ∈ (stepControl j).2.N)
    (step_right_mem :
      ∀ j, node j.succ ∈ (stepControl j).2.N)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 (node (Fin.last m)) :=
  Classical.choice
    (exists_of_nodeTransferSteps
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) node hnode_zero hnodeU stepControl
      step_left_mem step_right_mem C0 hbase hp0C start_patch
      hstart_open hstart_preconnected hstart_nonempty hstart_mem
      hstart_sub hstart_agree)

/-- A source path with a subdivision subordinate to branch-free transfer
neighborhoods produces a transfer trace from the initial to the terminal
endpoint. -/
theorem exists_of_subdivision
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (S :
      UnitIntervalOrderedSubdivision
        (fun t : unitInterval => γ ⁻¹' (T t).N))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    Nonempty
      (BHWJostOrientedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 (γ 1)) := by
  let node : Fin (S.m + 1) → Fin n → Fin (d + 1) → ℂ :=
    fun j => γ (S.t j)
  have hnode_zero : node 0 = p0 := by
    simpa [node, S.t_zero] using hγ_zero
  have hnodeU : ∀ j, node j ∈ U := by
    intro j
    exact hγU (S.t j)
  let stepControl :
      ∀ _ : Fin S.m,
        Σ center : Fin n → Fin (d + 1) → ℂ,
          BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center :=
    fun j =>
      let t : unitInterval := Classical.choose (S.interval_endpoints_mem_cover j)
      ⟨γ t, T t⟩
  have step_left_mem :
      ∀ j, node (Fin.castSucc j) ∈ (stepControl j).2.N := by
    intro j
    let t : unitInterval := Classical.choose (S.interval_endpoints_mem_cover j)
    have ht := Classical.choose_spec (S.interval_endpoints_mem_cover j)
    change γ (S.t (Fin.castSucc j)) ∈ (T t).N
    exact ht.1
  have step_right_mem :
      ∀ j, node j.succ ∈ (stepControl j).2.N := by
    intro j
    let t : unitInterval := Classical.choose (S.interval_endpoints_mem_cover j)
    have ht := Classical.choose_spec (S.interval_endpoints_mem_cover j)
    change γ (S.t j.succ) ∈ (T t).N
    exact ht.2
  have htrace :=
    exists_of_nodeTransferSteps
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) node hnode_zero hnodeU stepControl
      step_left_mem step_right_mem C0 hbase hp0C start_patch
      hstart_open hstart_preconnected hstart_nonempty hstart_mem
      hstart_sub hstart_agree
  simpa [node, S.t_last] using htrace

/-- Noncomputably select the transfer trace produced from a path subdivision
and its branch-free transfer neighborhoods. -/
noncomputable def ofSubdivision
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (S :
      UnitIntervalOrderedSubdivision
        (fun t : unitInterval => γ ⁻¹' (T t).N))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 (γ 1) :=
  Classical.choice
    (exists_of_subdivision
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) γ hγ_zero hγU T S C0 hbase hp0C
      start_patch hstart_open hstart_preconnected hstart_nonempty
      hstart_mem hstart_sub hstart_agree)

/-- A continuous source path with branch-free transfer neighborhoods along
the path produces a transfer trace after selecting the compact subdivision of
the transfer cover. -/
theorem exists_of_transferCover
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ : Continuous γ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    Nonempty
      (BHWJostOrientedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 (γ 1)) := by
  exact
    exists_of_subdivision
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) γ hγ_zero hγU T
      (unitInterval_orderedSubdivision_of_orientedTransferCover
        (hd := hd) (τ := τ) γ hγ T)
      C0 hbase hp0C start_patch hstart_open hstart_preconnected
      hstart_nonempty hstart_mem hstart_sub hstart_agree

/-- Noncomputably select the transfer trace produced by the compact
transfer-cover subdivision of a continuous source path. -/
noncomputable def ofTransferCover
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ : Continuous γ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 (γ 1) :=
  Classical.choice
    (exists_of_transferCover
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) γ hγ hγ_zero hγU T C0 hbase hp0C
      start_patch hstart_open hstart_preconnected hstart_nonempty
      hstart_mem hstart_sub hstart_agree)

/-- A transfer trace has uniqueness-certified steps when every stored
center-forgotten transfer control satisfies the one-step uniqueness property. -/
def HasUniqueSteps
    {z : Fin n → Fin (d + 1) → ℂ}
    (Tr :
      BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 z) :
    Type _ :=
  ∀ j, BHWJostOrientedTransferControlHasUniqueNext (Tr.stepControl j)

/-- The zero-step trace has uniqueness-certified steps vacuously. -/
def hasUniqueSteps_base
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    HasUniqueSteps
      (base (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
        (p0 := p0) C0 hbase hp0C start_patch hstart_open
        hstart_preconnected hstart_nonempty hstart_mem hstart_sub
        hstart_agree) := by
  intro j
  exact Fin.elim0 j

end BHWJostOrientedTransferContinuationTrace

/-- A transfer trace bundled with certified one-step uniqueness for every
stored transfer control.  This is the trace object consumed by the future
finite uniqueness induction. -/
structure BHWJostOrientedCertifiedTransferContinuationTrace
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (p0 z : Fin n → Fin (d + 1) → ℂ) where
  trace :
    BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 z
  stepUnique :
    BHWJostOrientedTransferContinuationTrace.HasUniqueSteps trace

namespace BHWJostOrientedCertifiedTransferContinuationTrace

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 z y : Fin n → Fin (d + 1) → ℂ}

/-- Forget the certified-step proof and retain only the underlying
continuation chain. -/
def chain
    (T :
      BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 z) :
    BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z :=
  T.trace.chain

/-- The zero-step transfer trace is certified vacuously. -/
def base
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedCertifiedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 p0 where
  trace :=
    BHWJostOrientedTransferContinuationTrace.base
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) C0 hbase hp0C start_patch hstart_open
      hstart_preconnected hstart_nonempty hstart_mem hstart_sub
      hstart_agree
  stepUnique :=
    BHWJostOrientedTransferContinuationTrace.hasUniqueSteps_base
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) C0 hbase hp0C start_patch hstart_open
      hstart_preconnected hstart_nonempty hstart_mem hstart_sub
      hstart_agree

/-- Append one uniqueness-certified transfer step to a certified transfer
trace. -/
def snocAtTerminalNode
    (T :
      BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 p)
    (N : BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    (hpN : T.trace.chain.node (Fin.last T.trace.chain.m) ∈ N.N)
    (hpU : T.trace.chain.node (Fin.last T.trace.chain.m) ∈ U)
    (hqN : q ∈ N.N) (hqU : q ∈ U)
    (hN_unique :
      BHWJostOrientedTransferControlHasUniqueNext
        (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl N)) :
    BHWJostOrientedCertifiedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 q where
  trace :=
    BHWJostOrientedTransferContinuationTrace.snocAtTerminalNode
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) (q := q) T.trace N hpN hpU hqN hqU
  stepUnique := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · have hstep :
        ((T.trace.snocAtTerminalNode N hpN hpU hqN hqU).stepControl
          (Fin.last T.trace.chain.m)) =
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl N := by
        change Fin.lastCases
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl N)
          (fun i => T.trace.stepControl i) (Fin.last T.trace.chain.m) =
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl N
        exact Fin.lastCases_last
      rw [hstep]
      exact hN_unique
    · intro i
      have hstep :
        ((T.trace.snocAtTerminalNode N hpN hpU hqN hqU).stepControl
          i.castSucc) = T.trace.stepControl i := by
        change Fin.lastCases
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl N)
          (fun i => T.trace.stepControl i) i.castSucc =
          T.trace.stepControl i
        exact Fin.lastCases_castSucc i
      rw [hstep]
      exact T.stepUnique i

/-- A finite sequence of source nodes, together with centered branch-free
transfer neighborhoods whose center-forgotten controls have one-step
uniqueness, produces a certified transfer trace. -/
theorem exists_of_nodeTransferSteps
    {m : ℕ}
    (node : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ)
    (hnode_zero : node 0 = p0)
    (hnodeU : ∀ j, node j ∈ U)
    (stepControl :
      ∀ _ : Fin m,
        Σ center : Fin n → Fin (d + 1) → ℂ,
          BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    (step_left_mem :
      ∀ j, node (Fin.castSucc j) ∈ (stepControl j).2.N)
    (step_right_mem :
      ∀ j, node j.succ ∈ (stepControl j).2.N)
    (step_unique :
      ∀ j,
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (stepControl j).2))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    Nonempty
      (BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 (node (Fin.last m))) := by
  induction m with
  | zero =>
      have hlast : node (Fin.last 0) = p0 := by
        simpa using hnode_zero
      refine ⟨?_⟩
      rw [hlast]
      exact
        base (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
          (p0 := p0) C0 hbase hp0C start_patch hstart_open
          hstart_preconnected hstart_nonempty hstart_mem hstart_sub
          hstart_agree
  | succ m ih =>
      let nodePrefix : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ :=
        fun i => node (Fin.castSucc i)
      have hnode_zero_prefix : nodePrefix 0 = p0 := by
        simpa [nodePrefix] using hnode_zero
      have hnodeU_prefix : ∀ j, nodePrefix j ∈ U := by
        intro j
        exact hnodeU (Fin.castSucc j)
      let stepControlPrefix :
          ∀ j : Fin m,
            Σ center : Fin n → Fin (d + 1) → ℂ,
              BHWJostOrientedBranchFreeTransferNeighborhood
                hd n τ U center :=
        fun j => stepControl (Fin.castSucc j)
      have step_left_mem_prefix :
          ∀ j, nodePrefix (Fin.castSucc j) ∈
            (stepControlPrefix j).2.N := by
        intro j
        simpa [nodePrefix, stepControlPrefix] using
          step_left_mem (Fin.castSucc j)
      have step_right_mem_prefix :
          ∀ j, nodePrefix j.succ ∈ (stepControlPrefix j).2.N := by
        intro j
        have hidx :
            (Fin.castSucc j).succ = (j.succ).castSucc := by
          ext
          rfl
        change node ((j.succ).castSucc) ∈
          (stepControl (Fin.castSucc j)).2.N
        rw [← hidx]
        exact step_right_mem (Fin.castSucc j)
      have step_unique_prefix :
          ∀ j,
            BHWJostOrientedTransferControlHasUniqueNext
              (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
                (stepControlPrefix j).2) := by
        intro j
        change BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (stepControl (Fin.castSucc j)).2)
        exact step_unique (Fin.castSucc j)
      rcases ih nodePrefix hnode_zero_prefix hnodeU_prefix
        stepControlPrefix step_left_mem_prefix step_right_mem_prefix
        step_unique_prefix with
        ⟨Tprev⟩
      let lastStep := stepControl (Fin.last m)
      have hterminal :
          Tprev.trace.chain.node (Fin.last Tprev.trace.chain.m) =
            node (Fin.castSucc (Fin.last m)) := by
        simpa [nodePrefix] using Tprev.trace.chain.node_last
      have hpN :
          Tprev.trace.chain.node (Fin.last Tprev.trace.chain.m) ∈
            lastStep.2.N := by
        rw [hterminal]
        simpa [lastStep] using step_left_mem (Fin.last m)
      have hpU :
          Tprev.trace.chain.node (Fin.last Tprev.trace.chain.m) ∈ U := by
        rw [hterminal]
        exact hnodeU (Fin.castSucc (Fin.last m))
      have hqN :
          node (Fin.last m).succ ∈ lastStep.2.N := by
        simpa [lastStep] using step_right_mem (Fin.last m)
      have hqU :
          node (Fin.last m).succ ∈ U :=
        hnodeU (Fin.last m).succ
      have hlast_succ :
          (Fin.last m).succ = Fin.last (m + 1) := by
        ext
        rfl
      refine ⟨?_⟩
      simpa [hlast_succ, lastStep] using
        snocAtTerminalNode
          (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
          (p0 := p0) (q := node (Fin.last m).succ)
          Tprev lastStep.2 hpN hpU hqN hqU (step_unique (Fin.last m))

/-- Noncomputably select the certified transfer trace produced from finite
node/control data. -/
noncomputable def ofNodeTransferSteps
    {m : ℕ}
    (node : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ)
    (hnode_zero : node 0 = p0)
    (hnodeU : ∀ j, node j ∈ U)
    (stepControl :
      ∀ _ : Fin m,
        Σ center : Fin n → Fin (d + 1) → ℂ,
          BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    (step_left_mem :
      ∀ j, node (Fin.castSucc j) ∈ (stepControl j).2.N)
    (step_right_mem :
      ∀ j, node j.succ ∈ (stepControl j).2.N)
    (step_unique :
      ∀ j,
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (stepControl j).2))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedCertifiedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 (node (Fin.last m)) :=
  Classical.choice
    (exists_of_nodeTransferSteps
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) node hnode_zero hnodeU stepControl
      step_left_mem step_right_mem step_unique C0 hbase hp0C start_patch
      hstart_open hstart_preconnected hstart_nonempty hstart_mem
      hstart_sub hstart_agree)

/-- A source path with a subdivision subordinate to uniqueness-certified
branch-free transfer neighborhoods produces a certified transfer trace from the
initial to the terminal endpoint. -/
theorem exists_of_subdivision
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (T_unique :
      ∀ t,
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (T t)))
    (S :
      UnitIntervalOrderedSubdivision
        (fun t : unitInterval => γ ⁻¹' (T t).N))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    Nonempty
      (BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 (γ 1)) := by
  let node : Fin (S.m + 1) → Fin n → Fin (d + 1) → ℂ :=
    fun j => γ (S.t j)
  have hnode_zero : node 0 = p0 := by
    simpa [node, S.t_zero] using hγ_zero
  have hnodeU : ∀ j, node j ∈ U := by
    intro j
    exact hγU (S.t j)
  let stepControl :
      ∀ _ : Fin S.m,
        Σ center : Fin n → Fin (d + 1) → ℂ,
          BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center :=
    fun j =>
      let t : unitInterval := Classical.choose (S.interval_endpoints_mem_cover j)
      ⟨γ t, T t⟩
  have step_left_mem :
      ∀ j, node (Fin.castSucc j) ∈ (stepControl j).2.N := by
    intro j
    let t : unitInterval := Classical.choose (S.interval_endpoints_mem_cover j)
    have ht := Classical.choose_spec (S.interval_endpoints_mem_cover j)
    change γ (S.t (Fin.castSucc j)) ∈ (T t).N
    exact ht.1
  have step_right_mem :
      ∀ j, node j.succ ∈ (stepControl j).2.N := by
    intro j
    let t : unitInterval := Classical.choose (S.interval_endpoints_mem_cover j)
    have ht := Classical.choose_spec (S.interval_endpoints_mem_cover j)
    change γ (S.t j.succ) ∈ (T t).N
    exact ht.2
  have step_unique :
      ∀ j,
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (stepControl j).2) := by
    intro j
    let t : unitInterval := Classical.choose (S.interval_endpoints_mem_cover j)
    change BHWJostOrientedTransferControlHasUniqueNext
      (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl (T t))
    exact T_unique t
  have htrace :=
    exists_of_nodeTransferSteps
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) node hnode_zero hnodeU stepControl
      step_left_mem step_right_mem step_unique C0 hbase hp0C start_patch
      hstart_open hstart_preconnected hstart_nonempty hstart_mem
      hstart_sub hstart_agree
  simpa [node, S.t_last] using htrace

/-- Noncomputably select the certified transfer trace produced from a path
subdivision and uniqueness-certified branch-free transfer neighborhoods. -/
noncomputable def ofSubdivision
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (T_unique :
      ∀ t,
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (T t)))
    (S :
      UnitIntervalOrderedSubdivision
        (fun t : unitInterval => γ ⁻¹' (T t).N))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedCertifiedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 (γ 1) :=
  Classical.choice
    (exists_of_subdivision
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) γ hγ_zero hγU T T_unique S C0 hbase hp0C
      start_patch hstart_open hstart_preconnected hstart_nonempty
      hstart_mem hstart_sub hstart_agree)

/-- A continuous source path with uniqueness-certified branch-free transfer
neighborhoods along the path produces a certified transfer trace after
selecting the compact subdivision of the transfer cover. -/
theorem exists_of_transferCover
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ : Continuous γ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (T_unique :
      ∀ t,
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (T t)))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    Nonempty
      (BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 (γ 1)) := by
  exact
    exists_of_subdivision
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) γ hγ_zero hγU T T_unique
      (unitInterval_orderedSubdivision_of_orientedTransferCover
        (hd := hd) (τ := τ) γ hγ T)
      C0 hbase hp0C start_patch hstart_open hstart_preconnected
      hstart_nonempty hstart_mem hstart_sub hstart_agree

/-- Noncomputably select the certified transfer trace produced by the compact
transfer-cover subdivision of a continuous source path. -/
noncomputable def ofTransferCover
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ : Continuous γ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (T_unique :
      ∀ t,
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (T t)))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedCertifiedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 (γ 1) :=
  Classical.choice
    (exists_of_transferCover
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) γ hγ hγ_zero hγU T T_unique C0 hbase hp0C
      start_patch hstart_open hstart_preconnected hstart_nonempty
      hstart_mem hstart_sub hstart_agree)

/-- Observe a certified transfer trace at any point of its terminal chart. -/
def toTerminalPointTrace
    (T :
      BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 z)
    (hy : y ∈ T.trace.chain.chart (Fin.last T.trace.chain.m)) :
    BHWJostOrientedTransferTerminalPointTrace
      hd n τ Ω0 U B0 p0 y :=
  BHWJostOrientedTransferTerminalPointTrace.ofTracePoint T.trace hy

/-- Observe a certified transfer trace at its own endpoint. -/
def atEndpoint
    (T :
      BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 z) :
    BHWJostOrientedTransferTerminalPointTrace
      hd n τ Ω0 U B0 p0 z :=
  BHWJostOrientedTransferTerminalPointTrace.atEndpoint T.trace

end BHWJostOrientedCertifiedTransferContinuationTrace

/-- A certified transfer trace observed at an arbitrary point of its terminal
chart.  This is the certified version of
`BHWJostOrientedTransferTerminalPointTrace`; it preserves the one-step
uniqueness certificates needed by terminal trace comparison. -/
structure BHWJostOrientedCertifiedTransferTerminalPointTrace
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (p0 y : Fin n → Fin (d + 1) → ℂ) where
  endpoint : Fin n → Fin (d + 1) → ℂ
  trace :
    BHWJostOrientedCertifiedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 endpoint
  point_mem : y ∈ trace.trace.chain.chart (Fin.last trace.trace.chain.m)

namespace BHWJostOrientedCertifiedTransferTerminalPointTrace

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 y : Fin n → Fin (d + 1) → ℂ}

/-- Forget the certified-step proof and retain the ordinary terminal-point
trace. -/
def toTerminalPointTrace
    (T :
      BHWJostOrientedCertifiedTransferTerminalPointTrace
        hd n τ Ω0 U B0 p0 y) :
    BHWJostOrientedTransferTerminalPointTrace hd n τ Ω0 U B0 p0 y :=
  BHWJostOrientedTransferTerminalPointTrace.ofTracePoint
    T.trace.trace T.point_mem

/-- Observe a certified transfer trace at any point of its terminal chart. -/
def ofTracePoint
    {endpoint : Fin n → Fin (d + 1) → ℂ}
    (T :
      BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 endpoint)
    (hy : y ∈ T.trace.chain.chart (Fin.last T.trace.chain.m)) :
    BHWJostOrientedCertifiedTransferTerminalPointTrace
      hd n τ Ω0 U B0 p0 y where
  endpoint := endpoint
  trace := T
  point_mem := hy

/-- Observe a certified transfer trace at its own endpoint. -/
def atEndpoint
    {endpoint : Fin n → Fin (d + 1) → ℂ}
    (T :
      BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 endpoint) :
    BHWJostOrientedCertifiedTransferTerminalPointTrace
      hd n τ Ω0 U B0 p0 endpoint :=
  ofTracePoint T T.trace.chain.final_mem

/-- The observed point lies in the terminal local chart carrier. -/
theorem point_mem_terminalLocalChart
    (T :
      BHWJostOrientedCertifiedTransferTerminalPointTrace
        hd n τ Ω0 U B0 p0 y) :
    y ∈ (T.trace.trace.chain.localChart
      (Fin.last T.trace.trace.chain.m)).carrier := by
  simpa [T.trace.trace.chain.chart_eq_local
    (Fin.last T.trace.trace.chain.m)] using T.point_mem

end BHWJostOrientedCertifiedTransferTerminalPointTrace

end BHW
