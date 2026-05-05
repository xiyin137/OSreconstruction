import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedBHWInvariance

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
have been checked: provide the initial max-rank seed, the ordered connected
overlap domains for every transition, and a closing domain that contains the
terminal seed by provenance. -/
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

end BHWJostOrientedClosedLoopFiniteOverlapDomainData

end BHW
