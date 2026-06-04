import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameMaxRankProducer

/-!
# Max-rank identity principle for the oriented source variety

This file proves the max-rank identity propagation used after the BHW/Jost
closed-loop seed.  The generic theorem only assumes finite-coordinate
max-rank charts; the hard-range specialization supplies those charts from the
full-frame producer.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- In the hard range, intersecting a relatively open oriented-source patch
with the max-rank locus is relatively open in the oriented source variety.
The proof uses the full-frame determinant characterization of max rank on the
source variety. -/
theorem sourceOrientedRelOpen_inter_maxRank_relOpen
    (hn : d + 1 ≤ n)
    {W : Set (SourceOrientedGramData d n)}
    (hW_rel : IsRelOpenInSourceOrientedGramVariety d n W) :
    IsRelOpenInSourceOrientedGramVariety d n
      (W ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  classical
  rcases hW_rel with ⟨W0, hW0_open, hW_eq⟩
  let Omax : Set (SourceOrientedGramData d n) :=
    ⋃ ι : Fin (d + 1) ↪ Fin n,
      sourceFullFrameSelectedDetNonzeroDomain d n ι
  refine ⟨W0 ∩ Omax, hW0_open.inter ?_, ?_⟩
  · exact
      isOpen_iUnion fun ι =>
        sourceFullFrameSelectedDetNonzeroDomain_open d n ι
  · ext G
    constructor
    · intro hG
      have hGW_decomp : G ∈ W0 ∩ sourceOrientedGramVariety d n := by
        simpa [hW_eq] using hG.1
      rcases exists_selectedDetNonzero_of_sourceOrientedMaxRankAt
          (d := d) (n := n) hn hGW_decomp.2 hG.2 with
        ⟨ι, hdet⟩
      refine ⟨⟨hGW_decomp.1, ?_⟩, hGW_decomp.2⟩
      exact Set.mem_iUnion.mpr ⟨ι, by simpa [sourceFullFrameSelectedDetNonzeroDomain] using hdet⟩
    · intro hG
      rcases hG with ⟨⟨hGW0, hGOmax⟩, hGvar⟩
      constructor
      · rw [hW_eq]
        exact ⟨hGW0, hGvar⟩
      · rcases Set.mem_iUnion.mp hGOmax with ⟨ι, hGι⟩
        exact
          sourceOrientedMaxRankAt_of_selectedDet_ne_zero d n ι hGvar
            (by simpa [sourceFullFrameSelectedDetNonzeroDomain] using hGι)

/-- In the hard range, max-rank oriented source points are dense inside every
relatively open oriented source-variety domain. -/
theorem sourceOrientedMaxRank_dense_in_relOpen_inter
    (hn : d + 1 ≤ n)
    {U : Set (SourceOrientedGramData d n)}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U) :
    U ⊆ closure (U ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  classical
  rcases hU_rel with ⟨U0, hU0_open, hU_eq⟩
  intro G hGU
  rw [mem_closure_iff]
  intro O hO_open hGO
  have hGU0_var :
      G ∈ U0 ∩ sourceOrientedGramVariety d n := by
    simpa [hU_eq] using hGU
  rcases hGU0_var.2 with ⟨z, rfl⟩
  let P : Set (Fin n → Fin (d + 1) → ℂ) :=
    (sourceOrientedMinkowskiInvariant d n) ⁻¹' (O ∩ U0)
  have hP_open : IsOpen P := by
    exact (hO_open.inter hU0_open).preimage
      (continuous_sourceOrientedMinkowskiInvariant (d := d) (n := n))
  have hP_nonempty : P.Nonempty := by
    exact ⟨z, hGO, hGU0_var.1⟩
  obtain ⟨z', hz'reg, hz'P⟩ :=
    (dense_sourceComplexGramRegularAt d n).exists_mem_open hP_open hP_nonempty
  have hz'max :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z') := by
    have hge :
        min (d + 1) n ≤
          sourceGramMatrixRank n (sourceMinkowskiGram d n z') := by
      simpa [Nat.min_eq_left hn, sourceGramMatrixRank] using
        sourceMinkowskiGram_rank_ge_of_sourceComplexGramRegularAt
          d n hn hz'reg
    have hHW : HWSourceGramMaxRankAt d n z' := by
      simpa [HWSourceGramMaxRankAt, HWSourceGramMaxRank] using hge
    exact
      (sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt
        d n z').2 hHW
  refine ⟨sourceOrientedMinkowskiInvariant d n z', hz'P.1, ?_⟩
  constructor
  · rw [hU_eq]
    exact ⟨hz'P.2, ⟨z', rfl⟩⟩
  · exact hz'max

/-- Every nonempty relatively open oriented source-variety domain meets the
max-rank locus in the hard range. -/
theorem sourceOrientedRelOpen_inter_maxRank_nonempty
    (hn : d + 1 ≤ n)
    {W : Set (SourceOrientedGramData d n)}
    (hW_rel : IsRelOpenInSourceOrientedGramVariety d n W)
    (hW_ne : W.Nonempty) :
    (W ∩ {G | SourceOrientedMaxRankAt d n G}).Nonempty := by
  rcases hW_ne with ⟨G0, hG0W⟩
  have hG0cl :
      G0 ∈ closure (W ∩ {G | SourceOrientedMaxRankAt d n G}) :=
    sourceOrientedMaxRank_dense_in_relOpen_inter hn hW_rel hG0W
  by_contra hEmpty
  have hSet_empty :
      W ∩ {G | SourceOrientedMaxRankAt d n G} = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hEmpty
  simp [hSet_empty] at hG0cl

/-- Connected max-rank identity principle on the oriented source variety.

If a germ-holomorphic oriented scalar vanishes on a nonempty relatively open
seed contained in the max-rank stratum, then it vanishes on the whole connected
max-rank part of the domain.  The only geometric input is the local max-rank
chart producer. -/
theorem sourceOrientedGramVariety_maxRank_identity_principle_of_connected
    (maxRankChartAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedMaxRankAt d n G0 →
        Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0)
    {U W : Set (SourceOrientedGramData d n)}
    {H : SourceOrientedGramData d n → ℂ}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hUmax_conn : IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hW_rel : IsRelOpenInSourceOrientedGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub_U : W ⊆ U)
    (hW_sub_max : W ⊆ {G | SourceOrientedMaxRankAt d n G})
    (hH : SourceOrientedVarietyGermHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0 (U ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  classical
  let R : Set (SourceOrientedGramData d n) :=
    {G | SourceOrientedMaxRankAt d n G}
  let Umax : Set (SourceOrientedGramData d n) := U ∩ R
  let A0 : Set (SourceOrientedGramData d n) :=
    {G | ∃ O : Set (SourceOrientedGramData d n),
      IsOpen O ∧ G ∈ O ∧ Set.EqOn H 0 (O ∩ Umax)}
  let A : Set (SourceOrientedGramData d n) := A0 ∩ Umax
  have hA0_open : IsOpen A0 := by
    rw [isOpen_iff_forall_mem_open]
    intro G hGA0
    rcases hGA0 with ⟨O, hO_open, hGO, hO_zero⟩
    refine ⟨O, ?_, hO_open, hGO⟩
    intro G' hG'O
    exact ⟨O, hO_open, hG'O, hO_zero⟩
  have hA_rel :
      ∃ A0', IsOpen A0' ∧
        A = A0' ∩ (U ∩ {G | SourceOrientedMaxRankAt d n G}) := by
    refine ⟨A0, hA0_open, ?_⟩
    rfl
  have hA_zero : Set.EqOn H 0 A := by
    intro G hGA
    rcases hGA.1 with ⟨O, _hO_open, hGO, hO_zero⟩
    exact hO_zero ⟨hGO, hGA.2⟩
  have hA_nonempty : A.Nonempty := by
    rcases hW_rel with ⟨W0, hW0_open, hW_eq⟩
    rcases hW_ne with ⟨G, hGW⟩
    have hGW0 : G ∈ W0 := by
      rw [hW_eq] at hGW
      exact hGW.1
    have hGU : G ∈ U := hW_sub_U hGW
    have hGmax : SourceOrientedMaxRankAt d n G := hW_sub_max hGW
    refine ⟨G, ?_⟩
    refine ⟨?_, ⟨hGU, by simpa [R] using hGmax⟩⟩
    refine ⟨W0, hW0_open, hGW0, ?_⟩
    intro G' hG'
    have hG'U : G' ∈ U := hG'.2.1
    have hG'var : G' ∈ sourceOrientedGramVariety d n :=
      IsRelOpenInSourceOrientedGramVariety.subset hU_rel hG'U
    have hG'W : G' ∈ W := by
      rw [hW_eq]
      exact ⟨hG'.1, hG'var⟩
    exact hW_zero hG'W
  let Asub : Set Umax := {x | (x : SourceOrientedGramData d n) ∈ A}
  have hAsub_open : IsOpen Asub := by
    have hpre : Asub = Subtype.val ⁻¹' A0 := by
      ext x
      simp [Asub, A]
    rw [hpre]
    exact hA0_open.preimage continuous_subtype_val
  have hAsub_nonempty : Asub.Nonempty := by
    rcases hA_nonempty with ⟨G, hGA⟩
    exact ⟨⟨G, by simpa [Umax, R] using hGA.2⟩, hGA⟩
  have hAsub_compl_open : IsOpen (Asubᶜ) := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx_not
    have hx_not_A : (x : SourceOrientedGramData d n) ∉ A := by
      simpa [Asub] using hx_not
    have hx_not_closure : (x : SourceOrientedGramData d n) ∉ closure A := by
      intro hx_closure
      have hxU : (x : SourceOrientedGramData d n) ∈ U := x.property.1
      have hxMax : SourceOrientedMaxRankAt d n
          (x : SourceOrientedGramData d n) := by
        simpa [Umax, R] using x.property.2
      have hxVar : (x : SourceOrientedGramData d n) ∈
          sourceOrientedGramVariety d n :=
        IsRelOpenInSourceOrientedGramVariety.subset hU_rel hxU
      rcases maxRankChartAt hxVar hxMax with ⟨m, C⟩
      rcases C.local_identity_near_point hU_rel hH hxU hA_rel
          hx_closure hA_zero with
        ⟨V, hxV, hV_rel, _hV_sub, hV_zero⟩
      rcases hV_rel with ⟨V0, hV0_open, hV_eq⟩
      have hxV0 : (x : SourceOrientedGramData d n) ∈ V0 := by
        rw [hV_eq] at hxV
        exact hxV.1
      have hxA0 : (x : SourceOrientedGramData d n) ∈ A0 := by
        refine ⟨V0, hV0_open, hxV0, ?_⟩
        intro G hG
        have hGU : G ∈ U := hG.2.1
        have hGvar : G ∈ sourceOrientedGramVariety d n :=
          IsRelOpenInSourceOrientedGramVariety.subset hU_rel hGU
        have hGV : G ∈ V := by
          rw [hV_eq]
          exact ⟨hG.1, hGvar⟩
        exact hV_zero hGV
      have hxA : (x : SourceOrientedGramData d n) ∈ A :=
        ⟨hxA0, x.property⟩
      exact hx_not_A hxA
    let Nsub : Set Umax := Subtype.val ⁻¹' ((closure A)ᶜ)
    refine ⟨Nsub, ?_, ?_, ?_⟩
    · intro y hyN hyA
      have hyA_ambient : (y : SourceOrientedGramData d n) ∈ A := by
        simpa [Asub] using hyA
      exact hyN (subset_closure hyA_ambient)
    · exact isClosed_closure.isOpen_compl.preimage continuous_subtype_val
    · exact hx_not_closure
  have hAsub_clopen : IsClopen Asub :=
    ⟨⟨hAsub_compl_open⟩, hAsub_open⟩
  have hUmax_conn' : IsConnected Umax := by
    simpa [Umax, R] using hUmax_conn
  haveI : ConnectedSpace Umax :=
    isConnected_iff_connectedSpace.mp hUmax_conn'
  have hAsub_univ : Asub = Set.univ :=
    IsClopen.eq_univ hAsub_clopen hAsub_nonempty
  intro G hGUmax
  have hGA : G ∈ A := by
    have hx : (⟨G, by simpa [Umax, R] using hGUmax⟩ : Umax) ∈
        Asub := by
      rw [hAsub_univ]
      trivial
    simpa [Asub] using hx
  exact hA_zero hGA

/-- Hard-range max-rank identity principle using the full-frame chart
producer. -/
theorem sourceOrientedGramVariety_maxRank_identity_principle_of_connected_fullFrame
    (hn : d + 1 ≤ n)
    {U W : Set (SourceOrientedGramData d n)}
    {H : SourceOrientedGramData d n → ℂ}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hUmax_conn : IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hW_rel : IsRelOpenInSourceOrientedGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub_U : W ⊆ U)
    (hW_sub_max : W ⊆ {G | SourceOrientedMaxRankAt d n G})
    (hH : SourceOrientedVarietyGermHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0 (U ∩ {G | SourceOrientedMaxRankAt d n G}) :=
  sourceOrientedGramVariety_maxRank_identity_principle_of_connected
    (d := d) (n := n)
    (fun {_G0} hG hmax =>
      sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame hn hG hmax)
    hU_rel hUmax_conn hW_rel hW_ne hW_sub_U hW_sub_max hH hW_zero

/-- A continuous function which vanishes on a dense subset of a domain
vanishes on the whole domain. -/
theorem continuousOn_eqOn_zero_of_subset_closure
    {E : Type*} [TopologicalSpace E]
    {f : E → ℂ}
    {U S : Set E}
    (hf : ContinuousOn f U)
    (hS_sub : S ⊆ U)
    (hdense : U ⊆ closure S)
    (hzero : Set.EqOn f 0 S) :
    Set.EqOn f 0 U := by
  intro x hxU
  by_contra hx_ne
  have hx_cl : x ∈ closure S := hdense hxU
  rcases (continuousOn_iff.mp hf) x hxU {w : ℂ | w ≠ 0}
      isOpen_ne hx_ne with
    ⟨O, hO_open, hxO, hO_sub⟩
  rw [mem_closure_iff] at hx_cl
  rcases hx_cl O hO_open hxO with ⟨y, hyO, hyS⟩
  have hyU : y ∈ U := hS_sub hyS
  have hfy_ne : f y ≠ 0 := hO_sub ⟨hyO, hyU⟩
  exact hfy_ne (hzero hyS)

/-- Extend zero from the dense max-rank part of a relatively open oriented
source-variety domain to the whole domain by continuity. -/
theorem sourceOrientedGramVariety_relOpen_eqOn_zero_of_eqOn_maxRank
    (hn : d + 1 ≤ n)
    {U : Set (SourceOrientedGramData d n)}
    {H : SourceOrientedGramData d n → ℂ}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hH_cont : ContinuousOn H U)
    (hzero :
      Set.EqOn H 0 (U ∩ {G | SourceOrientedMaxRankAt d n G})) :
    Set.EqOn H 0 U := by
  exact
    continuousOn_eqOn_zero_of_subset_closure
      (f := H)
      (U := U)
      (S := U ∩ {G | SourceOrientedMaxRankAt d n G})
      hH_cont
      (by intro G hG; exact hG.1)
      (sourceOrientedMaxRank_dense_in_relOpen_inter hn hU_rel)
      hzero

/-- Hard-range oriented source-variety identity principle once the max-rank
part of the domain is connected.  This theorem still leaves the connectedness
of `U ∩ MaxRank` as an explicit geometric input. -/
theorem sourceOrientedGramVariety_identity_principle_of_connected_maxRank_fullFrame
    (hn : d + 1 ≤ n)
    {U W : Set (SourceOrientedGramData d n)}
    {H : SourceOrientedGramData d n → ℂ}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hUmax_conn : IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hW_rel : IsRelOpenInSourceOrientedGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub_U : W ⊆ U)
    (hH : SourceOrientedVarietyGermHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0 U := by
  let Wmax : Set (SourceOrientedGramData d n) :=
    W ∩ {G | SourceOrientedMaxRankAt d n G}
  have hWmax_rel :
      IsRelOpenInSourceOrientedGramVariety d n Wmax :=
    sourceOrientedRelOpen_inter_maxRank_relOpen hn hW_rel
  have hWmax_ne : Wmax.Nonempty :=
    sourceOrientedRelOpen_inter_maxRank_nonempty hn hW_rel hW_ne
  have hzero_max :
      Set.EqOn H 0 (U ∩ {G | SourceOrientedMaxRankAt d n G}) :=
    sourceOrientedGramVariety_maxRank_identity_principle_of_connected_fullFrame
      (d := d) (n := n) hn hU_rel hUmax_conn hWmax_rel hWmax_ne
      (by intro G hG; exact hW_sub_U hG.1)
      (by intro G hG; exact hG.2)
      hH
      (by intro G hG; exact hW_zero hG.1)
  exact
    sourceOrientedGramVariety_relOpen_eqOn_zero_of_eqOn_maxRank
      (d := d) (n := n) hn hU_rel
      (SourceOrientedVarietyGermHolomorphicOn.continuousOn hH
        (IsRelOpenInSourceOrientedGramVariety.subset hU_rel))
      hzero_max

/-- Equality form of the hard-range oriented source-variety identity
principle, still with connectedness of the max-rank part supplied as an
explicit input. -/
theorem sourceOrientedGramVariety_eqOn_of_connected_maxRank_fullFrame
    (hn : d + 1 ≤ n)
    {U W : Set (SourceOrientedGramData d n)}
    {Φ Ψ : SourceOrientedGramData d n → ℂ}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hUmax_conn : IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hW_rel : IsRelOpenInSourceOrientedGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub_U : W ⊆ U)
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ U)
    (hΨ : SourceOrientedVarietyGermHolomorphicOn d n Ψ U)
    (hW_eq : Set.EqOn Φ Ψ W) :
    Set.EqOn Φ Ψ U := by
  have hH :
      SourceOrientedVarietyGermHolomorphicOn d n (fun G => Φ G - Ψ G) U :=
    SourceOrientedVarietyGermHolomorphicOn.sub (d := d) (n := n) hΦ hΨ
  have hW_zero : Set.EqOn (fun G => Φ G - Ψ G) 0 W := by
    intro G hGW
    exact sub_eq_zero.mpr (hW_eq hGW)
  have hzero :=
    sourceOrientedGramVariety_identity_principle_of_connected_maxRank_fullFrame
      (d := d) (n := n) hn hU_rel hUmax_conn hW_rel hW_ne hW_sub_U
      hH hW_zero
  intro G hGU
  exact sub_eq_zero.mp (hzero hGU)

/-- Equality form of the hard-range max-rank identity principle.  This is the
form consumed by closed-loop BHW/Jost branch propagation. -/
theorem sourceOrientedGramVariety_maxRank_eqOn_of_connected_fullFrame
    (hn : d + 1 ≤ n)
    {U W : Set (SourceOrientedGramData d n)}
    {Φ Ψ : SourceOrientedGramData d n → ℂ}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hUmax_conn : IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hW_rel : IsRelOpenInSourceOrientedGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub_U : W ⊆ U)
    (hW_sub_max : W ⊆ {G | SourceOrientedMaxRankAt d n G})
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ U)
    (hΨ : SourceOrientedVarietyGermHolomorphicOn d n Ψ U)
    (hW_eq : Set.EqOn Φ Ψ W) :
    Set.EqOn Φ Ψ (U ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  have hH :
      SourceOrientedVarietyGermHolomorphicOn d n (fun G => Φ G - Ψ G) U :=
    SourceOrientedVarietyGermHolomorphicOn.sub (d := d) (n := n) hΦ hΨ
  have hW_zero : Set.EqOn (fun G => Φ G - Ψ G) 0 W := by
    intro G hGW
    exact sub_eq_zero.mpr (hW_eq hGW)
  have hzero :=
    sourceOrientedGramVariety_maxRank_identity_principle_of_connected_fullFrame
      (d := d) (n := n) hn hU_rel hUmax_conn hW_rel hW_ne
      hW_sub_U hW_sub_max hH hW_zero
  intro G hGU
  exact sub_eq_zero.mp (hzero hGU)

/-- A stored BHW/Jost max-rank closed-loop seed propagates to the whole
connected max-rank part of the closing oriented patch.  This theorem is only
the identity-principle propagation step; the genuine Hall-Wightman/Jost input
is the seed `S`. -/
theorem bhw_jost_closedChain_orientedMaxRankMonodromy_of_seed
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (hn : d + 1 ≤ n)
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    (hclosing_max_conn :
      IsConnected
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}))
    (S : BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) :
    Set.EqOn
      (L.chain.localChart (Fin.last L.chain.m)).Psi
      (L.chain.localChart 0).Psi
      (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  have hFinal :
      SourceOrientedVarietyGermHolomorphicOn d n
        (L.chain.localChart (Fin.last L.chain.m)).Psi
        L.closing_orientedPatch :=
    SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen
      (d := d) (n := n)
      (L.chain.localChart (Fin.last L.chain.m)).Psi_holo
      L.closing_orientedPatch_relOpen
      L.closing_orientedPatch_sub_final
  have hStart :
      SourceOrientedVarietyGermHolomorphicOn d n
        (L.chain.localChart 0).Psi
        L.closing_orientedPatch :=
    SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen
      (d := d) (n := n)
      (L.chain.localChart 0).Psi_holo
      L.closing_orientedPatch_relOpen
      L.closing_orientedPatch_sub_start
  exact
    sourceOrientedGramVariety_maxRank_eqOn_of_connected_fullFrame
      (d := d) (n := n) hn
      L.closing_orientedPatch_relOpen hclosing_max_conn
      S.seed_relOpen S.seed_nonempty
      (by
        intro G hG
        exact (S.seed_sub hG).1)
      (by
        intro G hG
        exact (S.seed_sub hG).2)
      hFinal hStart S.seed_eq

/-- Source-branch form of max-rank closed-loop propagation from a stored
BHW/Jost seed.  The conclusion is deliberately restricted to source points
whose oriented invariant is maximal rank; extending across exceptional rank is
a separate density/continuity step. -/
theorem bhw_jost_closedChain_sourceMonodromy_on_maxRankClosingPatch_of_seed
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (hn : d + 1 ≤ n)
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    (hclosing_max_conn :
      IsConnected
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}))
    (S : BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      {y | y ∈ L.closing_patch ∧
        SourceOrientedMaxRankAt d n
          (sourceOrientedMinkowskiInvariant d n y)} := by
  have hmon :
      Set.EqOn
        (L.chain.localChart (Fin.last L.chain.m)).Psi
        (L.chain.localChart 0).Psi
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}) :=
    bhw_jost_closedChain_orientedMaxRankMonodromy_of_seed
      (d := d) (n := n) hn L hclosing_max_conn S
  intro y hy
  rcases hy with ⟨hyClosing, hyMax⟩
  have hyFinalChart : y ∈ L.chain.chart (Fin.last L.chain.m) :=
    L.closing_patch_sub_final hyClosing
  have hyFinalLocal :
      y ∈ (L.chain.localChart (Fin.last L.chain.m)).carrier := by
    simpa [L.chain.chart_eq_local (Fin.last L.chain.m)] using hyFinalChart
  have hyStartPatch : y ∈ L.chain.start_patch :=
    L.closing_patch_sub_start hyClosing
  have hyStartChart : y ∈ L.chain.chart 0 :=
    (L.chain.start_patch_sub hyStartPatch).2
  have hyStartLocal : y ∈ (L.chain.localChart 0).carrier := by
    simpa [L.chain.chart_eq_local 0] using hyStartChart
  calc
    L.chain.branch (Fin.last L.chain.m) y =
        L.chain.branch 0 y := by
      rw [L.chain.branch_eq_local (Fin.last L.chain.m) y hyFinalChart,
        L.chain.branch_eq_local 0 y hyStartChart,
        (L.chain.localChart (Fin.last L.chain.m)).branch_eq_orientedPullback
          y hyFinalLocal,
        (L.chain.localChart 0).branch_eq_orientedPullback y hyStartLocal]
      exact hmon ⟨L.closing_patch_oriented_mem y hyClosing, hyMax⟩
    _ = B0 y := L.chain.start_agree y hyStartPatch

/-- A stored BHW/Jost max-rank closed-loop seed propagates to the whole
closing oriented patch, once the max-rank part of that patch is connected.
The passage from max rank to all ranks is the checked density/continuity
extension for oriented germ-holomorphic functions. -/
theorem bhw_jost_closedChain_orientedMonodromy_of_seed
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (hn : d + 1 ≤ n)
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    (hclosing_max_conn :
      IsConnected
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}))
    (S : BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) :
    Set.EqOn
      (L.chain.localChart (Fin.last L.chain.m)).Psi
      (L.chain.localChart 0).Psi
      L.closing_orientedPatch := by
  have hFinal :
      SourceOrientedVarietyGermHolomorphicOn d n
        (L.chain.localChart (Fin.last L.chain.m)).Psi
        L.closing_orientedPatch :=
    SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen
      (d := d) (n := n)
      (L.chain.localChart (Fin.last L.chain.m)).Psi_holo
      L.closing_orientedPatch_relOpen
      L.closing_orientedPatch_sub_final
  have hStart :
      SourceOrientedVarietyGermHolomorphicOn d n
        (L.chain.localChart 0).Psi
        L.closing_orientedPatch :=
    SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen
      (d := d) (n := n)
      (L.chain.localChart 0).Psi_holo
      L.closing_orientedPatch_relOpen
      L.closing_orientedPatch_sub_start
  exact
    sourceOrientedGramVariety_eqOn_of_connected_maxRank_fullFrame
      (d := d) (n := n) hn
      L.closing_orientedPatch_relOpen hclosing_max_conn
      S.seed_relOpen S.seed_nonempty
      (by
        intro G hG
        exact (S.seed_sub hG).1)
      hFinal hStart S.seed_eq

/-- Source-branch form of closed-loop monodromy from a stored BHW/Jost
max-rank seed. -/
theorem bhw_jost_closedChain_sourceMonodromy_of_seed
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (hn : d + 1 ≤ n)
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    (hclosing_max_conn :
      IsConnected
        (L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}))
    (S : BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      L.closing_patch :=
  BHWJostOrientedClosedContinuationLoop.terminal_branch_eq_B0_of_orientedMonodromy
    L (bhw_jost_closedChain_orientedMonodromy_of_seed
      (d := d) (n := n) hn L hclosing_max_conn S)

end BHW
