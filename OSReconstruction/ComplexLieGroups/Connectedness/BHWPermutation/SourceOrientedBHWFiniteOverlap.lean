import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedBHWInvariance
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientLocalImage
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientCanonicalImage

/-!
# Finite-overlap terminal data for the BHW/Jost source route

This file isolates the exact terminal data that the remaining
Hall-Wightman/Jost finite-overlap argument must produce.  The consumer theorem
below is deliberately mechanical: once the ordered overlap propagation has
reached a terminal equality seed in a connected closing domain, the existing
closing-domain theorem packages it as the closed-loop max-rank seed.
-/

noncomputable section

open Complex Topology Classical

namespace BHW

variable {d n : ℕ}

/-- Topological assembly for connected max-rank strata in the oriented source
variety.  If the max-rank stratum is dense in a connected relatively open
domain and every point has arbitrarily small relatively open neighborhoods
whose max-rank part is connected, then the whole max-rank part of the domain is
connected.

This is the oriented-source analogue of the rank-exact assembly theorem in
`SourceComplexDensity.lean`.  The genuine geometric work for later BHW/Jost
domains is therefore local: provide the small connected max-rank neighborhoods
near both max-rank and exceptional-rank oriented source points. -/
theorem sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_local_basis
    {U : Set (SourceOrientedGramData d n)}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hU_conn : IsConnected U)
    (hdense :
      U ⊆ closure (U ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hlocal :
      ∀ G, G ∈ U →
        ∀ N0 : Set (SourceOrientedGramData d n), IsOpen N0 → G ∈ N0 →
          ∃ V : Set (SourceOrientedGramData d n),
            G ∈ V ∧
            IsRelOpenInSourceOrientedGramVariety d n V ∧
            V ⊆ U ∩ N0 ∧
            IsConnected (V ∩ {G | SourceOrientedMaxRankAt d n G})) :
    IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  let R : Set (SourceOrientedGramData d n) :=
    {G | SourceOrientedMaxRankAt d n G}
  let S : Set (SourceOrientedGramData d n) := U ∩ R
  refine ⟨?_, ?_⟩
  · rcases hU_conn.1 with ⟨G, hGU⟩
    rcases hlocal G hGU Set.univ isOpen_univ trivial with
      ⟨V, _hGV, _hV_rel, hV_sub, hVmax_conn⟩
    rcases hVmax_conn.1 with ⟨Y, hYV, hYR⟩
    exact ⟨Y, (hV_sub hYV).1, hYR⟩
  · intro O1 O2 hO1 hO2 hS_cover hS_O1 hS_O2
    let A : Set (SourceOrientedGramData d n) := S ∩ O1
    let B : Set (SourceOrientedGramData d n) := S ∩ O2
    have hS_subset_AB : S ⊆ A ∪ B := by
      intro Y hYS
      rcases hS_cover hYS with hYO1 | hYO2
      · exact Or.inl ⟨hYS, hYO1⟩
      · exact Or.inr ⟨hYS, hYO2⟩
    have hU_subset_closure_AB : U ⊆ closure A ∪ closure B := by
      intro G hGU
      have hGclS : G ∈ closure S := by
        simpa [S, R] using hdense hGU
      have hGclUnion : G ∈ closure (A ∪ B) :=
        closure_mono hS_subset_AB hGclS
      simpa [closure_union] using hGclUnion
    have hclosure_inter_nonempty :
        (U ∩ closure A ∩ closure B).Nonempty := by
      by_cases hinter : (U ∩ closure A ∩ closure B).Nonempty
      · exact hinter
      · have hno :
          ∀ G, G ∈ U → G ∈ closure A → G ∈ closure B → False := by
          intro G hGU hGA hGB
          exact hinter ⟨G, ⟨hGU, hGA⟩, hGB⟩
        let OA : Set (SourceOrientedGramData d n) := (closure B)ᶜ
        let OB : Set (SourceOrientedGramData d n) := (closure A)ᶜ
        have hOA_open : IsOpen OA := isClosed_closure.isOpen_compl
        have hOB_open : IsOpen OB := isClosed_closure.isOpen_compl
        have hU_sub_open : U ⊆ OA ∪ OB := by
          intro G hGU
          rcases hU_subset_closure_AB hGU with hGA | hGB
          · have hGnotB : G ∉ closure B :=
              fun hGB => hno G hGU hGA hGB
            exact Or.inl hGnotB
          · have hGnotA : G ∉ closure A :=
              fun hGA => hno G hGU hGA hGB
            exact Or.inr hGnotA
        have hU_OA_nonempty : (U ∩ OA).Nonempty := by
          rcases hS_O1 with ⟨Y, hYS, hYO1⟩
          have hYA : Y ∈ A := ⟨hYS, hYO1⟩
          have hYclA : Y ∈ closure A := subset_closure hYA
          have hYnotB : Y ∉ closure B :=
            fun hYB => hno Y hYS.1 hYclA hYB
          exact ⟨Y, hYS.1, hYnotB⟩
        have hU_OB_nonempty : (U ∩ OB).Nonempty := by
          rcases hS_O2 with ⟨Y, hYS, hYO2⟩
          have hYB : Y ∈ B := ⟨hYS, hYO2⟩
          have hYclB : Y ∈ closure B := subset_closure hYB
          have hYnotA : Y ∉ closure A :=
            fun hYA => hno Y hYS.1 hYA hYclB
          exact ⟨Y, hYS.1, hYnotA⟩
        exfalso
        rcases hU_conn.2 OA OB hOA_open hOB_open hU_sub_open
            hU_OA_nonempty hU_OB_nonempty with
          ⟨G, hGU, hGOA, hGOB⟩
        rcases hU_subset_closure_AB hGU with hGA | hGB
        · exact hGOB hGA
        · exact hGOA hGB
    rcases hclosure_inter_nonempty with ⟨G0, hG0U_clA, hG0clB⟩
    have hG0U : G0 ∈ U := hG0U_clA.1
    have hG0clA : G0 ∈ closure A := hG0U_clA.2
    rcases hlocal G0 hG0U Set.univ isOpen_univ trivial with
      ⟨V, hG0V, hV_rel, hV_sub, hVmax_conn⟩
    rcases hV_rel with ⟨V0, hV0_open, hV_eq⟩
    have hG0V0 : G0 ∈ V0 := by
      rw [hV_eq] at hG0V
      exact hG0V.1
    have hVmax_sub_S : V ∩ R ⊆ S := by
      intro Y hY
      exact ⟨(hV_sub hY.1).1, hY.2⟩
    have hVmax_cover : V ∩ R ⊆ O1 ∪ O2 :=
      hVmax_sub_S.trans hS_cover
    have hVmax_O1_nonempty : ((V ∩ R) ∩ O1).Nonempty := by
      rw [mem_closure_iff] at hG0clA
      rcases hG0clA V0 hV0_open hG0V0 with ⟨Y, hYV0, hYA⟩
      have hYR : Y ∈ R := hYA.1.2
      have hYU : Y ∈ U := hYA.1.1
      have hYvar : Y ∈ sourceOrientedGramVariety d n :=
        IsRelOpenInSourceOrientedGramVariety.subset hU_rel hYU
      have hYV : Y ∈ V := by
        rw [hV_eq]
        exact ⟨hYV0, hYvar⟩
      exact ⟨Y, ⟨hYV, hYR⟩, hYA.2⟩
    have hVmax_O2_nonempty : ((V ∩ R) ∩ O2).Nonempty := by
      rw [mem_closure_iff] at hG0clB
      rcases hG0clB V0 hV0_open hG0V0 with ⟨Y, hYV0, hYB⟩
      have hYR : Y ∈ R := hYB.1.2
      have hYU : Y ∈ U := hYB.1.1
      have hYvar : Y ∈ sourceOrientedGramVariety d n :=
        IsRelOpenInSourceOrientedGramVariety.subset hU_rel hYU
      have hYV : Y ∈ V := by
        rw [hV_eq]
        exact ⟨hYV0, hYvar⟩
      exact ⟨Y, ⟨hYV, hYR⟩, hYB.2⟩
    rcases hVmax_conn.2 O1 O2 hO1 hO2 hVmax_cover
        hVmax_O1_nonempty hVmax_O2_nonempty with
      ⟨Y, hYVmax, hYO1O2⟩
    exact ⟨Y, hVmax_sub_S hYVmax, hYO1O2⟩

/-- Hard-range connected max-rank assembly in a connected relatively open
oriented source domain, with only the local connected max-rank basis left as
input. -/
theorem sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected
    (hn : d + 1 ≤ n)
    {U : Set (SourceOrientedGramData d n)}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hU_conn : IsConnected U)
    (hlocal :
      ∀ G, G ∈ U →
        ∀ N0 : Set (SourceOrientedGramData d n), IsOpen N0 → G ∈ N0 →
          ∃ V : Set (SourceOrientedGramData d n),
            G ∈ V ∧
            IsRelOpenInSourceOrientedGramVariety d n V ∧
            V ⊆ U ∩ N0 ∧
            IsConnected (V ∩ {G | SourceOrientedMaxRankAt d n G})) :
    IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}) :=
  sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_local_basis
    (d := d) (n := n) hU_rel hU_conn
    (sourceOrientedMaxRank_dense_in_relOpen_inter
      (d := d) (n := n) hn hU_rel)
    hlocal

/-- Max-rank centers have the local connected max-rank basis required by the
oriented max-rank connectedness assembly theorem.  The proof is the full-frame
chart shrinker: shrink inside `U ∩ N0` and use that the produced patch lies
entirely in the max-rank stratum. -/
theorem sourceOrientedMaxRank_local_connectedMaxRank_basis_fullFrame
    (hn : d + 1 ≤ n)
    {U : Set (SourceOrientedGramData d n)}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    {G0 : SourceOrientedGramData d n}
    (hG0U : G0 ∈ U)
    (hG0max : SourceOrientedMaxRankAt d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      V ⊆ U ∩ N0 ∧
      IsConnected (V ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  let Nrel : Set (SourceOrientedGramData d n) :=
    N0 ∩ sourceOrientedGramVariety d n
  have hNrel_rel : IsRelOpenInSourceOrientedGramVariety d n Nrel :=
    ⟨N0, hN0_open, rfl⟩
  let W : Set (SourceOrientedGramData d n) := U ∩ Nrel
  have hW_rel : IsRelOpenInSourceOrientedGramVariety d n W :=
    IsRelOpenInSourceOrientedGramVariety.inter hU_rel hNrel_rel
  have hG0var : G0 ∈ sourceOrientedGramVariety d n :=
    IsRelOpenInSourceOrientedGramVariety.subset hU_rel hG0U
  have hG0W : G0 ∈ W := ⟨hG0U, hG0N0, hG0var⟩
  rcases sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame
      (d := d) (n := n) hn hG0var hG0max with
    ⟨_m, C⟩
  rcases C.connectedMaxRankPatch_inside_relOpen hW_rel hG0W with
    ⟨P, hP_sub⟩
  refine ⟨P.V, P.center_mem, P.V_relOpen, ?_, ?_⟩
  · intro G hG
    have hGW : G ∈ W := (hP_sub hG).1
    exact ⟨hGW.1, hGW.2.1⟩
  · have hV_inter :
        P.V ∩ {G | SourceOrientedMaxRankAt d n G} = P.V := by
      ext G
      constructor
      · intro hG
        exact hG.1
      · intro hG
        exact ⟨hG, (hP_sub hG).2⟩
    simpa [hV_inter] using P.V_connected

/-- Hard-range connected max-rank assembly with the max-rank local case
discharged by full-frame charts.  The only remaining local input is the
exceptional-rank case. -/
theorem sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_exceptionalLocalBasis
    (hn : d + 1 ≤ n)
    {U : Set (SourceOrientedGramData d n)}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hU_conn : IsConnected U)
    (hexceptional :
      ∀ G, G ∈ U →
        SourceOrientedExceptionalRank d n G →
          ∀ N0 : Set (SourceOrientedGramData d n), IsOpen N0 → G ∈ N0 →
            ∃ V : Set (SourceOrientedGramData d n),
              G ∈ V ∧
              IsRelOpenInSourceOrientedGramVariety d n V ∧
              V ⊆ U ∩ N0 ∧
              IsConnected (V ∩ {G | SourceOrientedMaxRankAt d n G})) :
    IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}) :=
  sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected
    (d := d) (n := n) hn hU_rel hU_conn
    (by
      intro G hGU N0 hN0_open hGN0
      by_cases hGmax : SourceOrientedMaxRankAt d n G
      · exact
          sourceOrientedMaxRank_local_connectedMaxRank_basis_fullFrame
            (d := d) (n := n) hn hU_rel hGU hGmax hN0_open hGN0
      · have hGvar : G ∈ sourceOrientedGramVariety d n :=
          IsRelOpenInSourceOrientedGramVariety.subset hU_rel hGU
        exact hexceptional G hGU ⟨hGvar, hGmax⟩ N0 hN0_open hGN0)

/-- Max-rank connectedness of a connected relatively open oriented source
domain follows from the strengthened rank-deficient local-image producer. -/
theorem sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_rankDeficientMaxRankLocalImageProducer
    (hn : d + 1 ≤ n)
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientMaxRankLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {U : Set (SourceOrientedGramData d n)}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hU_conn : IsConnected U) :
    IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}) :=
  sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_exceptionalLocalBasis
    (d := d) (n := n) hn hU_rel hU_conn
    (by
      intro G hGU hex N0 hN0_open hGN0
      exact
        sourceOrientedRankDeficientConnectedMaxRankPatchAt_of_localImageProducer
          (d := d) (n := n) rankDeficientLocalImageAt
          hU_rel hGU hex hN0_open hGN0)

/-- Unconditional hard-range connectedness of the max-rank part of a connected
relatively open oriented source patch, using the checked sliced-head IFT
rank-deficient local-image producer. -/
theorem sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : d + 1 ≤ n)
    {U : Set (SourceOrientedGramData d n)}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hU_conn : IsConnected U) :
    IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}) :=
  sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_rankDeficientMaxRankLocalImageProducer
    (d := d) (n := n) hn
    (fun {_G0} hG0 hex {_N0} hN0_open hG0N0 =>
      BHW.sourceOrientedRankDeficientMaxRankLocalImageData_of_headSliceIFT
        (d := d) (n := n) hd hn hG0 hex hN0_open hG0N0)
    hU_rel hU_conn

/-- Every nonempty relatively open source-oriented patch contains a nonempty
preconnected relatively open seed in the max-rank stratum, in the hard range
`d + 1 ≤ n`.  This is the seed-extraction helper used at the start and close
of finite-overlap propagation arguments. -/
theorem exists_preconnectedRelOpen_maxRankSeed_inside
    (hn : d + 1 ≤ n)
    {W : Set (SourceOrientedGramData d n)}
    (hW_rel : IsRelOpenInSourceOrientedGramVariety d n W)
    (hW_nonempty : W.Nonempty) :
    ∃ seed : Set (SourceOrientedGramData d n),
      IsRelOpenInSourceOrientedGramVariety d n seed ∧
      IsPreconnected seed ∧
      seed.Nonempty ∧
      seed ⊆ W ∩ {G | SourceOrientedMaxRankAt d n G} := by
  let Wmax : Set (SourceOrientedGramData d n) :=
    W ∩ {G | SourceOrientedMaxRankAt d n G}
  have hWmax_rel : IsRelOpenInSourceOrientedGramVariety d n Wmax :=
    sourceOrientedRelOpen_inter_maxRank_relOpen
      (d := d) (n := n) hn hW_rel
  have hWmax_nonempty : Wmax.Nonempty :=
    sourceOrientedRelOpen_inter_maxRank_nonempty
      (d := d) (n := n) hn hW_rel hW_nonempty
  rcases hWmax_nonempty with ⟨G0, hG0Wmax⟩
  have hG0var : G0 ∈ sourceOrientedGramVariety d n :=
    IsRelOpenInSourceOrientedGramVariety.subset hW_rel hG0Wmax.1
  rcases sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame
      (d := d) (n := n) hn hG0var hG0Wmax.2 with
    ⟨_m, C⟩
  rcases C.connectedMaxRankPatch_inside_relOpen hWmax_rel hG0Wmax with
    ⟨P, hP_sub⟩
  refine ⟨P.V, P.V_relOpen, P.V_connected.isPreconnected,
    ⟨G0, P.center_mem⟩, ?_⟩
  intro G hG
  exact (hP_sub hG).1

/-- Terminal finite-overlap propagation data for a closed oriented BHW/Jost
continuation loop.  This is the honest output expected from the remaining
Hall-Wightman/Jost finite-overlap construction: a connected max-rank terminal
domain containing the closing patch, together with a nonempty max-rank seed on
which the terminal and initial oriented germs agree. -/
structure BHWJostOrientedFiniteOverlapPropagationData
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) where
  hn : d + 1 ≤ n
  terminalDomain : Set (SourceOrientedGramData d n)
  terminalDomain_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n terminalDomain
  terminalDomain_maxRank_connected :
    IsConnected (terminalDomain ∩ {G | SourceOrientedMaxRankAt d n G})
  terminalDomain_sub_final :
    terminalDomain ⊆
      (L.chain.localChart (Fin.last L.chain.m)).orientedDomain
  terminalDomain_sub_start :
    terminalDomain ⊆ (L.chain.localChart 0).orientedDomain
  terminalSeed : Set (SourceOrientedGramData d n)
  terminalSeed_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n terminalSeed
  terminalSeed_nonempty : terminalSeed.Nonempty
  terminalSeed_sub_domain : terminalSeed ⊆ terminalDomain
  terminalSeed_sub_max :
    terminalSeed ⊆ {G | SourceOrientedMaxRankAt d n G}
  terminalSeed_eq :
    Set.EqOn
      (L.chain.localChart (Fin.last L.chain.m)).Psi
      (L.chain.localChart 0).Psi
      terminalSeed
  closingPatch_sub_terminalDomain :
    L.closing_orientedPatch ⊆ terminalDomain

namespace BHWJostOrientedFiniteOverlapPropagationData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}
variable {L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}

/-- The terminal finite-overlap data packages directly into the closed-loop
max-rank seed consumed by the identity-principle monodromy layer. -/
theorem to_closedLoopSeed
    (P : BHWJostOrientedFiniteOverlapPropagationData L) :
    Nonempty (BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) :=
  BHWJostOrientedMaxRankClosedLoopSeed.exists_of_connectedDomainPropagation
    (d := d) (n := n) (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U)
    (B0 := B0) (p0 := p0) (L := L)
    P.hn
    P.terminalDomain_relOpen
    P.terminalDomain_maxRank_connected
    P.terminalDomain_sub_final
    P.terminalDomain_sub_start
    P.terminalSeed_relOpen
    P.terminalSeed_nonempty
    P.terminalSeed_sub_domain
    P.terminalSeed_sub_max
    P.terminalSeed_eq
    P.closingPatch_sub_terminalDomain

/-- Terminal finite-overlap propagation data gives oriented monodromy on the
closing patch once the closing max-rank stratum is connected. -/
theorem to_orientedMonodromy
    (P : BHWJostOrientedFiniteOverlapPropagationData L)
    (hclosing_max_conn :
      IsConnected
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G})) :
    Set.EqOn
      (L.chain.localChart (Fin.last L.chain.m)).Psi
      (L.chain.localChart 0).Psi
      L.closing_orientedPatch := by
  rcases P.to_closedLoopSeed with ⟨S⟩
  exact
    bhw_jost_closedChain_orientedMonodromy_of_seed
      (d := d) (n := n) P.hn L hclosing_max_conn S

/-- Terminal finite-overlap propagation data gives source-branch monodromy on
the closing source patch once the closing max-rank stratum is connected. -/
theorem to_sourceMonodromy
    (P : BHWJostOrientedFiniteOverlapPropagationData L)
    (hclosing_max_conn :
      IsConnected
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G})) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      L.closing_patch := by
  rcases P.to_closedLoopSeed with ⟨S⟩
  exact
    bhw_jost_closedChain_sourceMonodromy_of_seed
      (d := d) (n := n) P.hn L hclosing_max_conn S

/-- Terminal finite-overlap propagation data gives oriented monodromy with no
extra closing-patch connectedness hypothesis.  The stored closing oriented
patch is nonempty and preconnected, and the checked sliced-head IFT producer
turns that into connectedness of its max-rank part. -/
theorem to_orientedMonodromy_headSliceIFT
    (P : BHWJostOrientedFiniteOverlapPropagationData L) :
    Set.EqOn
      (L.chain.localChart (Fin.last L.chain.m)).Psi
      (L.chain.localChart 0).Psi
      L.closing_orientedPatch :=
  P.to_orientedMonodromy
    (sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT
      (d := d) (n := n) hd P.hn L.closing_orientedPatch_relOpen
      ⟨L.closing_orientedPatch_nonempty,
        L.closing_orientedPatch_preconnected⟩)

/-- Terminal finite-overlap propagation data gives source-branch monodromy
with no extra closing-patch connectedness hypothesis. -/
theorem to_sourceMonodromy_headSliceIFT
    (P : BHWJostOrientedFiniteOverlapPropagationData L) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      L.closing_patch :=
  P.to_sourceMonodromy
    (sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT
      (d := d) (n := n) hd P.hn L.closing_orientedPatch_relOpen
      ⟨L.closing_orientedPatch_nonempty,
        L.closing_orientedPatch_preconnected⟩)

end BHWJostOrientedFiniteOverlapPropagationData

namespace BHWJostOrientedSourcePatchContinuationChain

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 z : Fin n → Fin (d + 1) → ℂ}

/-- Iterate the checked one-step propagated-seed theorem across an ordered
finite-overlap family of connected max-rank domains.  The data `D` are the
domains supplied by the genuine Hall-Wightman/Jost overlap construction: each
step domain contains the current transition patch, and the next step domain
contains the previous transition patch so that the newly produced seed is an
admissible incoming seed for the following step. -/
theorem exists_terminalSeed_of_finiteOverlapDomains
    (C : BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z)
    (hn : d + 1 ≤ n)
    {seed0 : Set (SourceOrientedGramData d n)}
    (hseed0_rel : IsRelOpenInSourceOrientedGramVariety d n seed0)
    (hseed0_pre : IsPreconnected seed0)
    (hseed0_nonempty : seed0.Nonempty)
    (hseed0_sub_max : seed0 ⊆ {G | SourceOrientedMaxRankAt d n G})
    (D : (j : Fin C.m) → Set (SourceOrientedGramData d n))
    (hD_rel : ∀ j, IsRelOpenInSourceOrientedGramVariety d n (D j))
    (hDmax_conn :
      ∀ j, IsConnected (D j ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hD_sub_start :
      ∀ j, D j ⊆ (C.localChart 0).orientedDomain)
    (hD_sub_left :
      ∀ j, D j ⊆ (C.localChart (Fin.castSucc j)).orientedDomain)
    (hT_sub_D :
      ∀ j, (C.oriented_transition j).orientedPatch ⊆ D j)
    (hseed0_sub_D0 :
      ∀ h0 : 0 < C.m, seed0 ⊆ D ⟨0, h0⟩)
    (hT_sub_nextD :
      ∀ (j : Fin C.m) (hnext : j.val + 1 < C.m),
        (C.oriented_transition j).orientedPatch ⊆ D ⟨j.val + 1, hnext⟩) :
    ∃ terminalSeed : Set (SourceOrientedGramData d n),
      IsRelOpenInSourceOrientedGramVariety d n terminalSeed ∧
      IsPreconnected terminalSeed ∧
      terminalSeed.Nonempty ∧
      terminalSeed ⊆ {G | SourceOrientedMaxRankAt d n G} ∧
      Set.EqOn
        (C.localChart (Fin.last C.m)).Psi
        (C.localChart 0).Psi
        terminalSeed ∧
      (C.m = 0 → terminalSeed ⊆ seed0) ∧
      (∀ hpos : C.m ≠ 0,
        terminalSeed ⊆
          (C.oriented_transition
            ⟨C.m.pred, Nat.pred_lt hpos⟩).orientedPatch) := by
  let Φ : SourceOrientedGramData d n → ℂ := (C.localChart 0).Psi
  let state (i : ℕ) : Prop :=
    ∀ hi : i ≤ C.m,
      ∃ seed : Set (SourceOrientedGramData d n),
        IsRelOpenInSourceOrientedGramVariety d n seed ∧
        IsPreconnected seed ∧
        seed.Nonempty ∧
        seed ⊆ {G | SourceOrientedMaxRankAt d n G} ∧
        Set.EqOn Φ (C.localChart ⟨i, Nat.lt_succ_of_le hi⟩).Psi seed ∧
        (∀ hlt : i < C.m, seed ⊆ D ⟨i, hlt⟩) ∧
        (i = 0 → seed ⊆ seed0) ∧
        (∀ hpos : i ≠ 0,
          seed ⊆
            (C.oriented_transition
              ⟨i.pred, Nat.lt_of_lt_of_le (Nat.pred_lt hpos) hi⟩).orientedPatch)
  have hstate : ∀ i, state i := by
    intro i
    induction i with
    | zero =>
        intro hi
        refine ⟨seed0, hseed0_rel, hseed0_pre, hseed0_nonempty,
          hseed0_sub_max, ?_, ?_, ?_, ?_⟩
        · intro G _hG
          rfl
        · intro hlt
          exact hseed0_sub_D0 hlt
        · intro _hzero G hG
          exact hG
        · intro hpos
          simp at hpos
    | succ i ih =>
        intro hi_succ
        have hi_lt : i < C.m := Nat.lt_of_succ_le hi_succ
        have hi_le : i ≤ C.m := Nat.le_trans (Nat.le_succ i) hi_succ
        rcases ih hi_le with
          ⟨seed, hseed_rel, _hseed_pre, hseed_nonempty, hseed_sub_max,
            hseed_eq, hseed_sub_D, _hseed_sub_zero, _hseed_sub_prev⟩
        let j : Fin C.m := ⟨i, hi_lt⟩
        have hΦ_holo :
            SourceOrientedVarietyGermHolomorphicOn d n Φ (D j) :=
          SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen
            (d := d) (n := n) (C.localChart 0).Psi_holo
            (hD_rel j) (hD_sub_start j)
        have hseed_eq_left :
            Set.EqOn Φ (C.localChart (Fin.castSucc j)).Psi seed := by
          simpa [j, Φ] using hseed_eq
        rcases
          (C.oriented_transition j).exists_propagatedSeed_to_right
            (d := d) (n := n) hn (hD_rel j) (hDmax_conn j)
            (hD_sub_left j) hΦ_holo hseed_rel hseed_nonempty
            (hseed_sub_D hi_lt) hseed_sub_max hseed_eq_left
            (hT_sub_D j) with
          ⟨seedNext, hseedNext_rel, hseedNext_pre, hseedNext_nonempty,
            hseedNext_sub, hseedNext_eq⟩
        refine ⟨seedNext, hseedNext_rel, hseedNext_pre,
          hseedNext_nonempty, ?_, ?_, ?_, ?_, ?_⟩
        · intro G hG
          exact (hseedNext_sub hG).2
        · have hidx :
              (C.localChart j.succ).Psi =
                (C.localChart ⟨i + 1, Nat.lt_succ_of_le hi_succ⟩).Psi := by
            congr
          simpa [j, Φ, hidx] using hseedNext_eq
        · intro hnext
          exact fun G hG => hT_sub_nextD j hnext (hseedNext_sub hG).1
        · intro hzero
          omega
        · intro _hpos G hG
          simpa [j] using (hseedNext_sub hG).1
  rcases hstate C.m le_rfl with
    ⟨terminalSeed, hterminal_rel, hterminal_pre, hterminal_nonempty,
      hterminal_sub_max, hterminal_eq, _hterminal_sub_nextD,
      hterminal_sub_zero, hterminal_sub_prev⟩
  refine ⟨terminalSeed, hterminal_rel, hterminal_pre, hterminal_nonempty,
    hterminal_sub_max, ?_, hterminal_sub_zero, hterminal_sub_prev⟩
  · intro G hG
    have h :
        (C.localChart 0).Psi G =
          (C.localChart (Fin.last C.m)).Psi G := by
      simpa [Φ, Fin.last] using (hterminal_eq hG)
    exact h.symm

end BHWJostOrientedSourcePatchContinuationChain

/-- The geometric finite-overlap data for a closed oriented loop.  This is the
remaining BHW/Jost producer target after the propagation and packaging layers
have been checked: provide the initial max-rank seed, the ordered domains
whose max-rank parts are connected for every transition, and a closing domain
that contains the terminal seed by provenance. -/
structure BHWJostOrientedClosedLoopFiniteOverlapDomainData
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) where
  hn : d + 1 ≤ n
  initialSeed : Set (SourceOrientedGramData d n)
  initialSeed_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n initialSeed
  initialSeed_preconnected : IsPreconnected initialSeed
  initialSeed_nonempty : initialSeed.Nonempty
  initialSeed_sub_max :
    initialSeed ⊆ {G | SourceOrientedMaxRankAt d n G}
  stepDomain : (j : Fin L.chain.m) → Set (SourceOrientedGramData d n)
  stepDomain_relOpen :
    ∀ j, IsRelOpenInSourceOrientedGramVariety d n (stepDomain j)
  stepDomain_maxRank_connected :
    ∀ j, IsConnected (stepDomain j ∩ {G | SourceOrientedMaxRankAt d n G})
  stepDomain_sub_start :
    ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain
  stepDomain_sub_left :
    ∀ j,
      stepDomain j ⊆
        (L.chain.localChart (Fin.castSucc j)).orientedDomain
  transition_sub_stepDomain :
    ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆ stepDomain j
  initialSeed_sub_firstDomain :
    ∀ h0 : 0 < L.chain.m, initialSeed ⊆ stepDomain ⟨0, h0⟩
  transition_sub_nextDomain :
    ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
      (L.chain.oriented_transition j).orientedPatch ⊆
        stepDomain ⟨j.val + 1, hnext⟩
  closingDomain : Set (SourceOrientedGramData d n)
  closingDomain_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n closingDomain
  closingDomain_maxRank_connected :
    IsConnected (closingDomain ∩ {G | SourceOrientedMaxRankAt d n G})
  closingDomain_sub_final :
    closingDomain ⊆
      (L.chain.localChart (Fin.last L.chain.m)).orientedDomain
  closingDomain_sub_start :
    closingDomain ⊆ (L.chain.localChart 0).orientedDomain
  closingPatch_sub_closingDomain :
    L.closing_orientedPatch ⊆ closingDomain
  closingDomain_contains_initialSeed_of_zero :
    L.chain.m = 0 → initialSeed ⊆ closingDomain
  closingDomain_contains_lastTransition_of_pos :
    ∀ hpos : L.chain.m ≠ 0,
      (L.chain.oriented_transition
        ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
          closingDomain

namespace BHWJostOrientedClosedLoopFiniteOverlapDomainData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}
variable {L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}

/-- Closed-loop finite-overlap domain data produces the terminal
finite-overlap propagation data.  The proof runs the checked ordered
propagation induction on `L.chain`, then uses the zero/positive provenance
fields to put the terminal seed in the closing domain. -/
theorem to_finiteOverlapPropagationData
    (P : BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :
    Nonempty (BHWJostOrientedFiniteOverlapPropagationData L) := by
  rcases
    L.chain.exists_terminalSeed_of_finiteOverlapDomains
      (d := d) (n := n) P.hn
      P.initialSeed_relOpen
      P.initialSeed_preconnected
      P.initialSeed_nonempty
      P.initialSeed_sub_max
      P.stepDomain
      P.stepDomain_relOpen
      P.stepDomain_maxRank_connected
      P.stepDomain_sub_start
      P.stepDomain_sub_left
      P.transition_sub_stepDomain
      P.initialSeed_sub_firstDomain
      P.transition_sub_nextDomain with
    ⟨terminalSeed, hterminal_rel, _hterminal_pre, hterminal_nonempty,
      hterminal_sub_max, hterminal_eq, hterminal_sub_initial_of_zero,
      hterminal_sub_last_of_pos⟩
  have hterminal_sub_closing : terminalSeed ⊆ P.closingDomain := by
    by_cases hm : L.chain.m = 0
    · exact fun G hG =>
        P.closingDomain_contains_initialSeed_of_zero hm
          (hterminal_sub_initial_of_zero hm hG)
    · exact fun G hG =>
        P.closingDomain_contains_lastTransition_of_pos hm
          (hterminal_sub_last_of_pos hm hG)
  refine ⟨?Pterminal⟩
  exact
    { hn := P.hn
      terminalDomain := P.closingDomain
      terminalDomain_relOpen := P.closingDomain_relOpen
      terminalDomain_maxRank_connected := P.closingDomain_maxRank_connected
      terminalDomain_sub_final := P.closingDomain_sub_final
      terminalDomain_sub_start := P.closingDomain_sub_start
      terminalSeed := terminalSeed
      terminalSeed_relOpen := hterminal_rel
      terminalSeed_nonempty := hterminal_nonempty
      terminalSeed_sub_domain := hterminal_sub_closing
      terminalSeed_sub_max := hterminal_sub_max
      terminalSeed_eq := hterminal_eq
      closingPatch_sub_terminalDomain := P.closingPatch_sub_closingDomain }

/-- Closed-loop finite-overlap domain data packages all the way into the
closed-loop max-rank seed consumed by the monodromy identity-principle layer. -/
theorem to_closedLoopSeed
    (P : BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :
    Nonempty (BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) := by
  rcases P.to_finiteOverlapPropagationData with ⟨Pterminal⟩
  exact Pterminal.to_closedLoopSeed

/-- Closed-loop finite-overlap domain data gives oriented monodromy on the
closing patch once the closing max-rank stratum is connected. -/
theorem to_orientedMonodromy
    (P : BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
    (hclosing_max_conn :
      IsConnected
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G})) :
    Set.EqOn
      (L.chain.localChart (Fin.last L.chain.m)).Psi
      (L.chain.localChart 0).Psi
      L.closing_orientedPatch := by
  rcases P.to_closedLoopSeed with ⟨S⟩
  exact
    bhw_jost_closedChain_orientedMonodromy_of_seed
      (d := d) (n := n) P.hn L hclosing_max_conn S

/-- Closed-loop finite-overlap domain data gives source-branch monodromy on
the closing source patch once the closing max-rank stratum is connected. -/
theorem to_sourceMonodromy
    (P : BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
    (hclosing_max_conn :
      IsConnected
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G})) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      L.closing_patch := by
  rcases P.to_closedLoopSeed with ⟨S⟩
  exact
    bhw_jost_closedChain_sourceMonodromy_of_seed
      (d := d) (n := n) P.hn L hclosing_max_conn S

/-- Closed-loop finite-overlap domain data gives oriented monodromy with no
extra closing-patch connectedness hypothesis.  The stored closing oriented
patch is nonempty and preconnected, and the checked sliced-head IFT producer
turns that into connectedness of its max-rank part. -/
theorem to_orientedMonodromy_headSliceIFT
    (P : BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :
    Set.EqOn
      (L.chain.localChart (Fin.last L.chain.m)).Psi
      (L.chain.localChart 0).Psi
      L.closing_orientedPatch :=
  P.to_orientedMonodromy
    (sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT
      (d := d) (n := n) hd P.hn L.closing_orientedPatch_relOpen
      ⟨L.closing_orientedPatch_nonempty,
        L.closing_orientedPatch_preconnected⟩)

/-- Closed-loop finite-overlap domain data gives source-branch monodromy with
no extra closing-patch connectedness hypothesis. -/
theorem to_sourceMonodromy_headSliceIFT
    (P : BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      L.closing_patch :=
  P.to_sourceMonodromy
    (sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT
      (d := d) (n := n) hd P.hn L.closing_orientedPatch_relOpen
      ⟨L.closing_orientedPatch_nonempty,
        L.closing_orientedPatch_preconnected⟩)

/-- Positive-length closed loops produce finite-overlap domain data from the
ordered overlap domains and the closing domain.  The initial max-rank seed is
extracted automatically from the first connected overlap domain. -/
theorem exists_of_positiveDomains
    (hn : d + 1 ≤ n)
    (hpos : L.chain.m ≠ 0)
    (stepDomain : (j : Fin L.chain.m) → Set (SourceOrientedGramData d n))
    (stepDomain_relOpen :
      ∀ j, IsRelOpenInSourceOrientedGramVariety d n (stepDomain j))
    (stepDomain_maxRank_connected :
      ∀ j, IsConnected (stepDomain j ∩ {G | SourceOrientedMaxRankAt d n G}))
    (stepDomain_sub_start :
      ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain)
    (stepDomain_sub_left :
      ∀ j,
        stepDomain j ⊆
          (L.chain.localChart (Fin.castSucc j)).orientedDomain)
    (transition_sub_stepDomain :
      ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆ stepDomain j)
    (transition_sub_nextDomain :
      ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
        (L.chain.oriented_transition j).orientedPatch ⊆
          stepDomain ⟨j.val + 1, hnext⟩)
    (closingDomain : Set (SourceOrientedGramData d n))
    (closingDomain_relOpen :
      IsRelOpenInSourceOrientedGramVariety d n closingDomain)
    (closingDomain_maxRank_connected :
      IsConnected (closingDomain ∩ {G | SourceOrientedMaxRankAt d n G}))
    (closingDomain_sub_final :
      closingDomain ⊆
        (L.chain.localChart (Fin.last L.chain.m)).orientedDomain)
    (closingDomain_sub_start :
      closingDomain ⊆ (L.chain.localChart 0).orientedDomain)
    (closingPatch_sub_closingDomain :
      L.closing_orientedPatch ⊆ closingDomain)
    (closingDomain_contains_lastTransition_of_pos :
      ∀ hpos : L.chain.m ≠ 0,
        (L.chain.oriented_transition
          ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
            closingDomain) :
    Nonempty (BHWJostOrientedClosedLoopFiniteOverlapDomainData L) := by
  let j0 : Fin L.chain.m := ⟨0, Nat.pos_of_ne_zero hpos⟩
  have hD0_nonempty : (stepDomain j0).Nonempty := by
    rcases (stepDomain_maxRank_connected j0).nonempty with ⟨G, hG⟩
    exact ⟨G, hG.1⟩
  rcases exists_preconnectedRelOpen_maxRankSeed_inside
      (d := d) (n := n) hn (stepDomain_relOpen j0) hD0_nonempty with
    ⟨seed0, hseed0_rel, hseed0_pre, hseed0_nonempty, hseed0_sub⟩
  refine ⟨?P⟩
  exact
    { hn := hn
      initialSeed := seed0
      initialSeed_relOpen := hseed0_rel
      initialSeed_preconnected := hseed0_pre
      initialSeed_nonempty := hseed0_nonempty
      initialSeed_sub_max := by
        intro G hG
        exact (hseed0_sub hG).2
      stepDomain := stepDomain
      stepDomain_relOpen := stepDomain_relOpen
      stepDomain_maxRank_connected := stepDomain_maxRank_connected
      stepDomain_sub_start := stepDomain_sub_start
      stepDomain_sub_left := stepDomain_sub_left
      transition_sub_stepDomain := transition_sub_stepDomain
      initialSeed_sub_firstDomain := by
        intro h0 G hG
        have hG0 : G ∈ stepDomain j0 := (hseed0_sub hG).1
        have hj : (⟨0, h0⟩ : Fin L.chain.m) = j0 := by
          apply Fin.ext
          rfl
        simpa [hj]
          using hG0
      transition_sub_nextDomain := transition_sub_nextDomain
      closingDomain := closingDomain
      closingDomain_relOpen := closingDomain_relOpen
      closingDomain_maxRank_connected := closingDomain_maxRank_connected
      closingDomain_sub_final := closingDomain_sub_final
      closingDomain_sub_start := closingDomain_sub_start
      closingPatch_sub_closingDomain := closingPatch_sub_closingDomain
      closingDomain_contains_initialSeed_of_zero := by
        intro hm
        exact False.elim (hpos hm)
      closingDomain_contains_lastTransition_of_pos :=
        closingDomain_contains_lastTransition_of_pos }

/-- Positive-length closed loops produce finite-overlap domain data from
connected ordered overlap domains and a connected closing domain.  The
max-rank connectedness hypotheses are discharged by the checked sliced-head
IFT rank-deficient local-image producer. -/
theorem exists_of_positiveConnectedDomains_headSliceIFT
    (hn : d + 1 ≤ n)
    (hpos : L.chain.m ≠ 0)
    (stepDomain : (j : Fin L.chain.m) → Set (SourceOrientedGramData d n))
    (stepDomain_relOpen :
      ∀ j, IsRelOpenInSourceOrientedGramVariety d n (stepDomain j))
    (stepDomain_connected :
      ∀ j, IsConnected (stepDomain j))
    (stepDomain_sub_start :
      ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain)
    (stepDomain_sub_left :
      ∀ j,
        stepDomain j ⊆
          (L.chain.localChart (Fin.castSucc j)).orientedDomain)
    (transition_sub_stepDomain :
      ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆ stepDomain j)
    (transition_sub_nextDomain :
      ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
        (L.chain.oriented_transition j).orientedPatch ⊆
          stepDomain ⟨j.val + 1, hnext⟩)
    (closingDomain : Set (SourceOrientedGramData d n))
    (closingDomain_relOpen :
      IsRelOpenInSourceOrientedGramVariety d n closingDomain)
    (closingDomain_connected : IsConnected closingDomain)
    (closingDomain_sub_final :
      closingDomain ⊆
        (L.chain.localChart (Fin.last L.chain.m)).orientedDomain)
    (closingDomain_sub_start :
      closingDomain ⊆ (L.chain.localChart 0).orientedDomain)
    (closingPatch_sub_closingDomain :
      L.closing_orientedPatch ⊆ closingDomain)
    (closingDomain_contains_lastTransition_of_pos :
      ∀ hpos : L.chain.m ≠ 0,
        (L.chain.oriented_transition
          ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
            closingDomain) :
    Nonempty (BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :=
  exists_of_positiveDomains
    (d := d) (n := n) hn hpos
    stepDomain stepDomain_relOpen
    (fun j =>
      sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT
        (d := d) (n := n) hd hn (stepDomain_relOpen j)
        (stepDomain_connected j))
    stepDomain_sub_start stepDomain_sub_left
    transition_sub_stepDomain transition_sub_nextDomain
    closingDomain closingDomain_relOpen
    (sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT
      (d := d) (n := n) hd hn closingDomain_relOpen closingDomain_connected)
    closingDomain_sub_final closingDomain_sub_start closingPatch_sub_closingDomain
    closingDomain_contains_lastTransition_of_pos

/-- Positive-length closed loops produce finite-overlap domain data from
nonempty preconnected ordered overlap domains and a nonempty preconnected
closing domain.  This is the source-normal-form-friendly surface: the
max-rank connectedness hypotheses are discharged by first promoting
`Nonempty + IsPreconnected` to `IsConnected`, then applying the checked
sliced-head IFT local-image producer. -/
theorem exists_of_positivePreconnectedDomains_headSliceIFT
    (hn : d + 1 ≤ n)
    (hpos : L.chain.m ≠ 0)
    (stepDomain : (j : Fin L.chain.m) → Set (SourceOrientedGramData d n))
    (stepDomain_relOpen :
      ∀ j, IsRelOpenInSourceOrientedGramVariety d n (stepDomain j))
    (stepDomain_preconnected :
      ∀ j, IsPreconnected (stepDomain j))
    (stepDomain_nonempty :
      ∀ j, (stepDomain j).Nonempty)
    (stepDomain_sub_start :
      ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain)
    (stepDomain_sub_left :
      ∀ j,
        stepDomain j ⊆
          (L.chain.localChart (Fin.castSucc j)).orientedDomain)
    (transition_sub_stepDomain :
      ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆ stepDomain j)
    (transition_sub_nextDomain :
      ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
        (L.chain.oriented_transition j).orientedPatch ⊆
          stepDomain ⟨j.val + 1, hnext⟩)
    (closingDomain : Set (SourceOrientedGramData d n))
    (closingDomain_relOpen :
      IsRelOpenInSourceOrientedGramVariety d n closingDomain)
    (closingDomain_preconnected : IsPreconnected closingDomain)
    (closingDomain_nonempty : closingDomain.Nonempty)
    (closingDomain_sub_final :
      closingDomain ⊆
        (L.chain.localChart (Fin.last L.chain.m)).orientedDomain)
    (closingDomain_sub_start :
      closingDomain ⊆ (L.chain.localChart 0).orientedDomain)
    (closingPatch_sub_closingDomain :
      L.closing_orientedPatch ⊆ closingDomain)
    (closingDomain_contains_lastTransition_of_pos :
      ∀ hpos : L.chain.m ≠ 0,
        (L.chain.oriented_transition
          ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
            closingDomain) :
    Nonempty (BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :=
  exists_of_positiveConnectedDomains_headSliceIFT
    (d := d) (n := n) hn hpos
    stepDomain stepDomain_relOpen
    (fun j => ⟨stepDomain_nonempty j, stepDomain_preconnected j⟩)
    stepDomain_sub_start stepDomain_sub_left
    transition_sub_stepDomain transition_sub_nextDomain
    closingDomain closingDomain_relOpen
    ⟨closingDomain_nonempty, closingDomain_preconnected⟩
    closingDomain_sub_final closingDomain_sub_start closingPatch_sub_closingDomain
    closingDomain_contains_lastTransition_of_pos

/-- Zero-transition closed loops produce finite-overlap domain data directly
from the closing oriented patch, provided its max-rank part is connected. -/
theorem exists_of_zeroTransitions
    (hn : d + 1 ≤ n)
    (hm : L.chain.m = 0)
    (hclosing_max_connected :
      IsConnected
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G})) :
    Nonempty (BHWJostOrientedClosedLoopFiniteOverlapDomainData L) := by
  rcases exists_preconnectedRelOpen_maxRankSeed_inside
      (d := d) (n := n) hn L.closing_orientedPatch_relOpen
      L.closing_orientedPatch_nonempty with
    ⟨seed0, hseed0_rel, hseed0_pre, hseed0_nonempty, hseed0_sub⟩
  have helim (j : Fin L.chain.m) : False :=
    Nat.not_lt_zero j.val (by simpa [hm] using j.isLt)
  refine ⟨?P⟩
  exact
    { hn := hn
      initialSeed := seed0
      initialSeed_relOpen := hseed0_rel
      initialSeed_preconnected := hseed0_pre
      initialSeed_nonempty := hseed0_nonempty
      initialSeed_sub_max := by
        intro G hG
        exact (hseed0_sub hG).2
      stepDomain := fun j => False.elim (helim j)
      stepDomain_relOpen := fun j => False.elim (helim j)
      stepDomain_maxRank_connected := fun j => False.elim (helim j)
      stepDomain_sub_start := fun j => False.elim (helim j)
      stepDomain_sub_left := fun j => False.elim (helim j)
      transition_sub_stepDomain := fun j => False.elim (helim j)
      initialSeed_sub_firstDomain := by
        intro h0
        exact False.elim (by omega)
      transition_sub_nextDomain := fun j => False.elim (helim j)
      closingDomain := L.closing_orientedPatch
      closingDomain_relOpen := L.closing_orientedPatch_relOpen
      closingDomain_maxRank_connected := hclosing_max_connected
      closingDomain_sub_final := L.closing_orientedPatch_sub_final
      closingDomain_sub_start := L.closing_orientedPatch_sub_start
      closingPatch_sub_closingDomain := fun _ hG => hG
      closingDomain_contains_initialSeed_of_zero := by
        intro _hm0 G hG
        exact (hseed0_sub hG).1
      closingDomain_contains_lastTransition_of_pos := by
        intro hpos
        exact False.elim (hpos hm) }

/-- Zero-transition closed loops produce finite-overlap domain data directly
from a connected closing oriented patch.  The max-rank connectedness input is
derived by the checked sliced-head IFT rank-deficient local-image producer. -/
theorem exists_of_zeroTransitions_headSliceIFT
    (hn : d + 1 ≤ n)
    (hm : L.chain.m = 0)
    (hclosing_connected : IsConnected L.closing_orientedPatch) :
    Nonempty (BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :=
  exists_of_zeroTransitions
    (d := d) (n := n) hn hm
    (sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT
      (d := d) (n := n) hd hn L.closing_orientedPatch_relOpen
      hclosing_connected)

/-- Zero-transition closed loops require no extra geometric input beyond the
stored closing oriented patch.  The closed-loop structure already carries
nonemptiness and preconnectedness of that patch, and the checked sliced-head
IFT producer turns this into connectedness of its max-rank part. -/
theorem exists_of_zeroTransitions_closedLoop_headSliceIFT
    (hn : d + 1 ≤ n)
    (hm : L.chain.m = 0) :
    Nonempty (BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :=
  exists_of_zeroTransitions_headSliceIFT
    (d := d) (n := n) hn hm
    ⟨L.closing_orientedPatch_nonempty, L.closing_orientedPatch_preconnected⟩

/-- Unified preconnected-domain consumer for the remaining source-backed
finite-overlap producer.  In the zero-transition case the stored closing patch
already supplies the whole construction; in the positive-length case this
calls the ordered preconnected-domain constructor. -/
theorem exists_of_preconnectedDomains_headSliceIFT
    (hn : d + 1 ≤ n)
    (stepDomain : (j : Fin L.chain.m) → Set (SourceOrientedGramData d n))
    (stepDomain_relOpen :
      ∀ j, IsRelOpenInSourceOrientedGramVariety d n (stepDomain j))
    (stepDomain_preconnected :
      ∀ j, IsPreconnected (stepDomain j))
    (stepDomain_nonempty :
      ∀ j, (stepDomain j).Nonempty)
    (stepDomain_sub_start :
      ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain)
    (stepDomain_sub_left :
      ∀ j,
        stepDomain j ⊆
          (L.chain.localChart (Fin.castSucc j)).orientedDomain)
    (transition_sub_stepDomain :
      ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆ stepDomain j)
    (transition_sub_nextDomain :
      ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
        (L.chain.oriented_transition j).orientedPatch ⊆
          stepDomain ⟨j.val + 1, hnext⟩)
    (closingDomain : Set (SourceOrientedGramData d n))
    (closingDomain_relOpen :
      IsRelOpenInSourceOrientedGramVariety d n closingDomain)
    (closingDomain_preconnected : IsPreconnected closingDomain)
    (closingDomain_nonempty : closingDomain.Nonempty)
    (closingDomain_sub_final :
      closingDomain ⊆
        (L.chain.localChart (Fin.last L.chain.m)).orientedDomain)
    (closingDomain_sub_start :
      closingDomain ⊆ (L.chain.localChart 0).orientedDomain)
    (closingPatch_sub_closingDomain :
      L.closing_orientedPatch ⊆ closingDomain)
    (closingDomain_contains_lastTransition_of_pos :
      ∀ hpos : L.chain.m ≠ 0,
        (L.chain.oriented_transition
          ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
            closingDomain) :
    Nonempty (BHWJostOrientedClosedLoopFiniteOverlapDomainData L) := by
  by_cases hm : L.chain.m = 0
  · exact exists_of_zeroTransitions_closedLoop_headSliceIFT
      (d := d) (n := n) hn hm
  · exact
      exists_of_positivePreconnectedDomains_headSliceIFT
        (d := d) (n := n) hn hm
        stepDomain stepDomain_relOpen stepDomain_preconnected
        stepDomain_nonempty stepDomain_sub_start stepDomain_sub_left
        transition_sub_stepDomain transition_sub_nextDomain
        closingDomain closingDomain_relOpen closingDomain_preconnected
        closingDomain_nonempty closingDomain_sub_final closingDomain_sub_start
        closingPatch_sub_closingDomain
        closingDomain_contains_lastTransition_of_pos

end BHWJostOrientedClosedLoopFiniteOverlapDomainData

/-- Producer-facing finite-overlap data for the remaining strict
Hall-Wightman/Jost source-patch construction.  This structure contains only
the ordinary topological domains that local source-normal-form shrinkage is
expected to produce: relatively open, nonempty, preconnected step and closing
domains, together with the ordered containment transcript.  The checked
consumer below converts these fields to the max-rank-connected closed-loop
finite-overlap data using the sliced-head IFT local-image theorem.

The fields `stepDomain_sub_start` and `closingDomain_sub_start` are
load-bearing: they assert that the starting oriented branch is defined on the
whole finite-overlap ribbon.  They are not consequences of an arbitrary closed
loop of local charts; the strict source-backed BHW/Jost producer must either
construct such a large starting domain explicitly or use a different
accumulated-germ monodromy surface. -/
structure BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) where
  hn : d + 1 ≤ n
  stepDomain : (j : Fin L.chain.m) → Set (SourceOrientedGramData d n)
  stepDomain_relOpen :
    ∀ j, IsRelOpenInSourceOrientedGramVariety d n (stepDomain j)
  stepDomain_preconnected :
    ∀ j, IsPreconnected (stepDomain j)
  stepDomain_nonempty :
    ∀ j, (stepDomain j).Nonempty
  stepDomain_sub_start :
    ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain
  stepDomain_sub_left :
    ∀ j,
      stepDomain j ⊆
        (L.chain.localChart (Fin.castSucc j)).orientedDomain
  transition_sub_stepDomain :
    ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆ stepDomain j
  transition_sub_nextDomain :
    ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
      (L.chain.oriented_transition j).orientedPatch ⊆
        stepDomain ⟨j.val + 1, hnext⟩
  closingDomain : Set (SourceOrientedGramData d n)
  closingDomain_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n closingDomain
  closingDomain_preconnected : IsPreconnected closingDomain
  closingDomain_nonempty : closingDomain.Nonempty
  closingDomain_sub_final :
    closingDomain ⊆
      (L.chain.localChart (Fin.last L.chain.m)).orientedDomain
  closingDomain_sub_start :
    closingDomain ⊆ (L.chain.localChart 0).orientedDomain
  closingPatch_sub_closingDomain :
    L.closing_orientedPatch ⊆ closingDomain
  closingDomain_contains_lastTransition_of_pos :
    ∀ hpos : L.chain.m ≠ 0,
      (L.chain.oriented_transition
        ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
          closingDomain

namespace BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}
variable {L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}

/-- Zero-transition closed loops have producer-facing preconnected
finite-overlap data with no further geometric input: there are no step
domains, and the stored closing oriented patch is the closing domain. -/
theorem exists_of_zeroTransitions
    (hn : d + 1 ≤ n)
    (hm : L.chain.m = 0) :
    Nonempty
      (BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L) := by
  have helim (j : Fin L.chain.m) : False :=
    Nat.not_lt_zero j.val (by simpa [hm] using j.isLt)
  refine ⟨?P⟩
  exact
    { hn := hn
      stepDomain := fun j => False.elim (helim j)
      stepDomain_relOpen := fun j => False.elim (helim j)
      stepDomain_preconnected := fun j => False.elim (helim j)
      stepDomain_nonempty := fun j => False.elim (helim j)
      stepDomain_sub_start := fun j => False.elim (helim j)
      stepDomain_sub_left := fun j => False.elim (helim j)
      transition_sub_stepDomain := fun j => False.elim (helim j)
      transition_sub_nextDomain := fun j => False.elim (helim j)
      closingDomain := L.closing_orientedPatch
      closingDomain_relOpen := L.closing_orientedPatch_relOpen
      closingDomain_preconnected := L.closing_orientedPatch_preconnected
      closingDomain_nonempty := L.closing_orientedPatch_nonempty
      closingDomain_sub_final := L.closing_orientedPatch_sub_final
      closingDomain_sub_start := L.closing_orientedPatch_sub_start
      closingPatch_sub_closingDomain := fun _ hG => hG
      closingDomain_contains_lastTransition_of_pos := by
        intro hpos
        exact False.elim (hpos hm) }

/-- Producer-facing preconnected finite-overlap data converts mechanically to
the checked closed-loop finite-overlap data.  The zero-transition case is
handled by the closed-loop constructor from the stored closing patch; the
positive case promotes every supplied preconnected domain to the required
max-rank-connected domain using the sliced-head IFT theorem. -/
theorem to_finiteOverlapDomainData
    (P : BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L) :
    Nonempty (BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :=
  BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_preconnectedDomains_headSliceIFT
      (d := d) (n := n) P.hn
      P.stepDomain P.stepDomain_relOpen P.stepDomain_preconnected
      P.stepDomain_nonempty P.stepDomain_sub_start P.stepDomain_sub_left
      P.transition_sub_stepDomain P.transition_sub_nextDomain
      P.closingDomain P.closingDomain_relOpen P.closingDomain_preconnected
      P.closingDomain_nonempty P.closingDomain_sub_final
      P.closingDomain_sub_start P.closingPatch_sub_closingDomain
      P.closingDomain_contains_lastTransition_of_pos

/-- Producer-facing data gives the terminal finite-overlap propagation packet
consumed by the closed-loop seed layer. -/
theorem to_finiteOverlapPropagationData
    (P : BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L) :
    Nonempty (BHWJostOrientedFiniteOverlapPropagationData L) := by
  rcases P.to_finiteOverlapDomainData with ⟨Q⟩
  exact Q.to_finiteOverlapPropagationData

/-- Producer-facing data gives the closed-loop max-rank seed consumed by the
monodromy identity-principle layer. -/
theorem to_closedLoopSeed
    (P : BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L) :
    Nonempty (BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) := by
  rcases P.to_finiteOverlapDomainData with ⟨Q⟩
  exact Q.to_closedLoopSeed

/-- Producer-facing data gives oriented closed-loop monodromy with no exposed
max-rank-connectedness hypothesis. -/
theorem to_orientedMonodromy_headSliceIFT
    (P : BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L) :
    Set.EqOn
      (L.chain.localChart (Fin.last L.chain.m)).Psi
      (L.chain.localChart 0).Psi
      L.closing_orientedPatch := by
  rcases P.to_finiteOverlapDomainData with ⟨Q⟩
  exact Q.to_orientedMonodromy_headSliceIFT

/-- Producer-facing data gives source-branch closed-loop monodromy with no
exposed max-rank-connectedness hypothesis. -/
theorem to_sourceMonodromy_headSliceIFT
    (P : BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      L.closing_patch := by
  rcases P.to_finiteOverlapDomainData with ⟨Q⟩
  exact Q.to_sourceMonodromy_headSliceIFT

end BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData

/-- Stable public consumer for the source-backed finite-overlap producer.  The
remaining BHW/Jost geometric theorem should output the preconnected
finite-overlap data `P`; this theorem is then the whole source-monodromy
consumer. -/
theorem bhw_jost_closedChain_sourceMonodromy_of_preconnectedFiniteOverlapData
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    {L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}
    (P : BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      L.closing_patch :=
  P.to_sourceMonodromy_headSliceIFT

/-- Zero-transition closed loops have source monodromy with no finite-overlap
geometric input.  This is the degenerate closed-loop branch of the
producer-facing finite-overlap route. -/
theorem bhw_jost_closedChain_sourceMonodromy_of_zeroTransitions
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    {L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}
    (hn : d + 1 ≤ n)
    (hm : L.chain.m = 0) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      L.closing_patch := by
  rcases
    BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.exists_of_zeroTransitions
      (d := d) (n := n) (L := L) hn hm with
    ⟨P⟩
  exact bhw_jost_closedChain_sourceMonodromy_of_preconnectedFiniteOverlapData P

end BHW
