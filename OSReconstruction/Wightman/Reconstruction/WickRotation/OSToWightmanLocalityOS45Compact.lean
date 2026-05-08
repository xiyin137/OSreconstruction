import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Figure24
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceDistributionalUniqueness

noncomputable section

open Complex Topology

namespace BHW

variable {d n : ℕ} [NeZero d]

/-- Compact Figure-2-4 Wick pairing packet for one adjacent transposition.

The packet stores the `π`-labelled real Jost patches used to compare the
ordinary selected `extendF` branch with its adjacent relabelling.  The branch
equality field is the hard OS I §4.5/BHW-Jost input; the remaining fields are
finite-dimensional patch geometry. -/
structure OS45CompactFigure24WickPairingEq
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) where
  realPatch :
    Equiv.Perm (Fin n) → Set (NPointDomain d n)
  realPatch_open :
    ∀ π, IsOpen (realPatch π)
  realPatch_nonempty :
    ∀ π, (realPatch π).Nonempty
  realPatch_jost :
    ∀ π, realPatch π ⊆ BHW.JostSet d n
  realPatch_left_sector :
    ∀ π x, x ∈ realPatch π →
      BHW.realEmbed x ∈ BHW.permutedExtendedTubeSector d n π
  realPatch_right_sector :
    ∀ π x, x ∈ realPatch π →
      BHW.realEmbed x ∈
        BHW.permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩)
  realPatch_commonEdge_contact :
    ∀ π, ∃ x0 ∈ realPatch π,
      ∃ u ∈ BHW.os45Figure24SourcePatch (d := d) (n := n) i hi,
        (fun k => x0 (π k)) =
          BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u
  compact_branch_eq :
    ∀ π (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ realPatch π →
      (∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (fun k => BHW.realEmbed x (π k)) * φ x)
        =
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (fun k => BHW.realEmbed x
              ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) *
            φ x

/-- The canonical source-patch compact equality packages into the
`π`-labelled compact Figure-2-4 Wick pairing packet.

This constructor is purely mechanical: it uses the checked canonical patch
geometry and `os45CompactRealPatch_pullbackSchwartz` to reduce arbitrary
`π`-labelled compact tests to the canonical source patch. -/
def os45CompactFigure24WickPairingEq_of_sourcePatchPairing
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hPairing :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        (∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u)
          =
        ∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed
                (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc where
  realPatch := BHW.os45Figure24CompactRealPatch (d := d) n i hi
  realPatch_open :=
    BHW.os45Figure24CompactRealPatch_open (d := d) n i hi
  realPatch_nonempty :=
    BHW.os45Figure24CompactRealPatch_nonempty (d := d) hd n i hi
  realPatch_jost :=
    BHW.os45Figure24CompactRealPatch_jost (d := d) hd n i hi
  realPatch_left_sector :=
    BHW.os45Figure24CompactRealPatch_left_sector (d := d) hd n i hi
  realPatch_right_sector :=
    BHW.os45Figure24CompactRealPatch_right_sector (d := d) hd n i hi
  realPatch_commonEdge_contact :=
    BHW.os45Figure24CompactRealPatch_commonEdge_contact (d := d) hd n i hi
  compact_branch_eq := by
    intro π φ hφ_comp hφ_supp
    let A : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
      BHW.extendF (bvt_F OS lgc n)
    rcases BHW.os45CompactRealPatch_pullbackSchwartz
        (d := d) (n := n) A i hi π φ hφ_comp hφ_supp with
      ⟨ψ, hψ_comp, hψ_supp, _hψ_apply, hleft_pullback,
        hright_pullback⟩
    exact hleft_pullback.trans
      ((hPairing ψ hψ_comp hψ_supp).trans hright_pullback.symm)

/-- The left source patch obtained from a `π`-labelled compact Figure-2-4
real patch by undoing the public PET label. -/
def OS45CompactFigure24WickPairingEq.leftSourcePatch
    {i : Fin n} {hi : i.val + 1 < n}
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    (P : BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc)
    (π : Equiv.Perm (Fin n)) :
    Set (NPointDomain d n) :=
  BHW.os45SourcePermutationHomeomorph d n π.symm '' P.realPatch π

namespace OS45CompactFigure24WickPairingEq

variable {i : Fin n} {hi : i.val + 1 < n}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable (P : BHW.OS45CompactFigure24WickPairingEq
  (d := d) n i hi OS lgc)

/-- The unlabelled left source patch is open. -/
theorem leftSourcePatch_open
    (π : Equiv.Perm (Fin n)) :
    IsOpen (P.leftSourcePatch (d := d) (n := n) π) := by
  rw [BHW.OS45CompactFigure24WickPairingEq.leftSourcePatch]
  exact
    (BHW.os45SourcePermutationHomeomorph d n π.symm).isOpenMap _
      (P.realPatch_open π)

/-- The unlabelled left source patch is nonempty. -/
theorem leftSourcePatch_nonempty
    (π : Equiv.Perm (Fin n)) :
    (P.leftSourcePatch (d := d) (n := n) π).Nonempty := by
  rcases P.realPatch_nonempty π with ⟨x, hx⟩
  exact ⟨BHW.os45SourcePermutationHomeomorph d n π.symm x, x, hx, rfl⟩

/-- The unlabelled left source patch stays in the Jost set. -/
theorem leftSourcePatch_jost
    (π : Equiv.Perm (Fin n)) :
    P.leftSourcePatch (d := d) (n := n) π ⊆ BHW.JostSet d n := by
  rintro y ⟨x, hx, rfl⟩
  simpa [BHW.os45SourcePermutationHomeomorph] using
    BHW.jostSet_permutation_invariant
      (d := d) (n := n) π (P.realPatch_jost π hx)

omit [NeZero d] in
/-- The source Gram of the right adjacent real trace is the adjacent
permutation of the source Gram of the left trace. -/
theorem right_sourceGram_eq_perm_left
    (π : Equiv.Perm (Fin n)) (x : NPointDomain d n) :
    BHW.sourceRealMinkowskiGram d n
        (fun k => x ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
      BHW.sourcePermuteGram n (Equiv.swap i ⟨i.val + 1, hi⟩)
        (BHW.sourceRealMinkowskiGram d n (fun k => x (π k))) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  simpa [τ, Equiv.Perm.mul_apply] using
    BHW.sourceRealMinkowskiGram_perm
      (d := d) (n := n) τ (fun k => x (π k))

end OS45CompactFigure24WickPairingEq

/-- A full family of compact Figure-2-4 Wick pairing packets supplies the
distributional adjacent tube anchor consumed by the source-side theorem-2
route.

No branch equality is proved here.  The equality is copied from the compact
packets; the source Gram uniqueness environments are the Gram images of the
unlabelled left source patches, using the checked Hall-Wightman real-environment
uniqueness theorem for open Jost patches. -/
def sourceDistributionalAdjacentTubeAnchor_of_compactWickPairingEq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hCompact :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45CompactFigure24WickPairingEq
          (d := d) n i hi OS lgc) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) where
  realPatch := fun π i hi => (hCompact i hi).realPatch π
  realPatch_open := fun π i hi => (hCompact i hi).realPatch_open π
  realPatch_nonempty := fun π i hi => (hCompact i hi).realPatch_nonempty π
  realPatch_jost := fun π i hi => (hCompact i hi).realPatch_jost π
  realPatch_left_sector := fun π i hi => (hCompact i hi).realPatch_left_sector π
  realPatch_right_sector := fun π i hi => (hCompact i hi).realPatch_right_sector π
  gramEnvironment := fun π i hi =>
    BHW.sourceRealMinkowskiGram d n ''
      (hCompact i hi).leftSourcePatch (d := d) (n := n) π
  gramEnvironment_unique := by
    intro π i hi
    exact
      BHW.sourceDistributionalUniquenessSetOnVariety_of_open_jost_patch
        (d := d) n
        ((hCompact i hi).leftSourcePatch_open (d := d) (n := n) π)
        ((hCompact i hi).leftSourcePatch_nonempty (d := d) (n := n) π)
        ((hCompact i hi).leftSourcePatch_jost (d := d) (n := n) π)
  gram_left_mem := by
    intro π i hi x hx
    refine ⟨BHW.os45SourcePermutationHomeomorph d n π.symm x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [BHW.os45SourcePermutationHomeomorph]
  gram_environment_realized := by
    intro π i hi G hG
    rcases hG with ⟨y, hy, hGy⟩
    rcases hy with ⟨x, hx, hxy⟩
    rw [← hxy] at hGy
    refine ⟨x, hx, ?_⟩
    simpa [BHW.os45SourcePermutationHomeomorph] using hGy
  gram_right_eq_perm_left := by
    intro π i hi x _hx
    exact
      BHW.OS45CompactFigure24WickPairingEq.right_sourceGram_eq_perm_left
        (d := d) (n := n) (i := i) (hi := hi) π x
  compact_branch_eq := by
    intro π i hi φ hφ_comp hφ_supp
    exact (hCompact i hi).compact_branch_eq π φ hφ_comp hφ_supp

/-- A full compact Figure-2-4 Wick-pairing family supplies the older
selected-adjacent Jost anchor packet by taking the identity-labelled compact
real patch as the base patch.

This keeps the checked compact packet compatible with the existing selected
OS witness API without adding an import cycle back into
`OSToWightmanSelectedWitness.lean`. -/
def bvt_F_selectedAdjacentDistributionalJostAnchorData_of_compactWickPairingEq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hCompact :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45CompactFigure24WickPairingEq
          (d := d) n i hi OS lgc) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n where
  basePatch := fun i hi => (hCompact i hi).realPatch 1
  basePatch_open := fun i hi => (hCompact i hi).realPatch_open 1
  basePatch_nonempty := fun i hi => (hCompact i hi).realPatch_nonempty 1
  basePatch_jost := by
    intro i hi x hx
    exact (hCompact i hi).realPatch_jost 1 hx
  basePatch_left_ET := by
    intro i hi x hx
    simpa [BHW.permutedExtendedTubeSector] using
      (hCompact i hi).realPatch_left_sector 1 x hx
  basePatch_right_ET := by
    intro i hi x hx
    simpa [BHW.permutedExtendedTubeSector, BHW.realEmbed,
      Equiv.Perm.mul_apply] using
      (hCompact i hi).realPatch_right_sector 1 x hx
  baseGramEnvironment := fun i hi =>
    BHW.sourceRealMinkowskiGram d n '' (hCompact i hi).realPatch 1
  baseGramEnvironment_unique := by
    intro i hi
    exact
      BHW.sourceDistributionalUniquenessSetOnVariety_of_open_jost_patch
        (d := d) n
        ((hCompact i hi).realPatch_open 1)
        ((hCompact i hi).realPatch_nonempty 1)
        ((hCompact i hi).realPatch_jost 1)
  baseGram_left_mem := by
    intro i hi x hx
    exact ⟨x, hx, rfl⟩
  baseGram_realized := by
    intro i hi G hG
    rcases hG with ⟨x, hx, hGx⟩
    exact ⟨x, hx, hGx⟩
  baseCompactEq := by
    intro i hi φ hφ_comp hφ_supp
    simpa [BHW.realEmbed, Equiv.Perm.mul_apply] using
      (hCompact i hi).compact_branch_eq 1 φ hφ_comp hφ_supp

/-- Conditional OS45 envelope constructor for the selected adjacent Jost data.

This is the mechanical part of the OS-II supplier: once each adjacent
transposition has a real-open Jost patch with left/right extended-tube
membership and a direct `AdjacentOSEOWDifferenceEnvelope`, the selected
distributional Jost anchor data follows by the checked Hall-Wightman
Gram-environment supplier and the checked real-edge compact-equality
consumer. -/
noncomputable def bvt_F_selectedAdjacentDistributionalJostAnchorData_of_os45Envelopes
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hOS45 :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        ∃ V : Set (NPointDomain d n),
          IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
          (∀ x, x ∈ V → x ∈ BHW.JostSet d n) ∧
          (∀ x, x ∈ V → BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
          (∀ x, x ∈ V →
            BHW.realEmbed
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
              BHW.ExtendedTube d n) ∧
          Nonempty
            (BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
              (Equiv.swap i ⟨i.val + 1, hi⟩) V)) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n := by
  classical
  choose V hV using hOS45
  have hGram :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        ∃ E : Set (Fin n → Fin n → ℝ),
          BHW.sourceDistributionalUniquenessSetOnVariety d n E ∧
          (∀ x, x ∈ V i hi →
            BHW.sourceRealMinkowskiGram d n x ∈ E) ∧
          (∀ G, G ∈ E → ∃ x ∈ V i hi,
            BHW.sourceRealMinkowskiGram d n x = G) := by
    intro i hi
    exact
      BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch
        (d := d) n
        (hV i hi).1
        (hV i hi).2.2.1
        (hV i hi).2.2.2.1
  choose E hE using hGram
  refine
    { basePatch := V
      basePatch_open := ?basePatch_open
      basePatch_nonempty := ?basePatch_nonempty
      basePatch_jost := ?basePatch_jost
      basePatch_left_ET := ?basePatch_left_ET
      basePatch_right_ET := ?basePatch_right_ET
      baseGramEnvironment := E
      baseGramEnvironment_unique := ?baseGramEnvironment_unique
      baseGram_left_mem := ?baseGram_left_mem
      baseGram_realized := ?baseGram_realized
      baseCompactEq := ?baseCompactEq }
  · intro i hi
    exact (hV i hi).1
  · intro i hi
    exact (hV i hi).2.2.1
  · intro i hi x hx
    exact (hV i hi).2.2.2.1 x hx
  · intro i hi x hx
    exact (hV i hi).2.2.2.2.1 x hx
  · intro i hi x hx
    exact (hV i hi).2.2.2.2.2.1 x hx
  · intro i hi
    exact (hE i hi).1
  · intro i hi x hx
    exact (hE i hi).2.1 x hx
  · intro i hi G hG
    exact (hE i hi).2.2 G hG
  · intro i hi φ hφ_comp hφ_supp
    have hswap_first :=
      BHW.bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope
        (d := d) OS lgc n i hi (V i hi)
        (hV i hi).1
        (hV i hi).2.2.1
        (Classical.choice (hV i hi).2.2.2.2.2.2)
        φ hφ_comp hφ_supp
    exact hswap_first.symm

/-- Conditional selected Jost data constructor from common-chart OS45
envelopes.

This is one step upstream of
`bvt_F_selectedAdjacentDistributionalJostAnchorData_of_os45Envelopes`: it
performs the checked pullback from a common-chart holomorphic envelope to the
direct-coordinate `AdjacentOSEOWDifferenceEnvelope`, then reuses the selected
Jost-data constructor above. -/
noncomputable def bvt_F_selectedAdjacentDistributionalJostAnchorData_of_commonChartEnvelopes
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hOS45 :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        ∃ (V : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n))
          (Uc : Set (Fin n → Fin (d + 1) → ℂ))
          (Hc : (Fin n → Fin (d + 1) → ℂ) → ℂ),
          IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
          (∀ x, x ∈ V → x ∈ BHW.JostSet d n) ∧
          (∀ x, x ∈ V → BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
          (∀ x, x ∈ V →
            BHW.realEmbed
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
              BHW.ExtendedTube d n) ∧
          IsOpen Uc ∧ IsConnected Uc ∧
          DifferentiableOn ℂ Hc Uc ∧
          (∀ x, x ∈ V →
            BHW.os45CommonChartCLE (d := d) (n := n) ρ
              (fun k => wickRotatePoint (x k)) ∈ Uc) ∧
          (∀ x, x ∈ V →
            BHW.os45CommonChartCLE (d := d) (n := n) ρ
              (BHW.realEmbed x) ∈ Uc) ∧
          (∀ x, x ∈ V →
            Hc (BHW.os45CommonChartCLE (d := d) (n := n) ρ
                (fun k => wickRotatePoint (x k))) =
              bvt_F OS lgc n
                (fun k => wickRotatePoint
                  (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
              bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
          (∀ x, x ∈ V →
            Hc (BHW.os45CommonChartCLE (d := d) (n := n) ρ
                (BHW.realEmbed x)) =
              BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x))) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n :=
  BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_os45Envelopes
    (d := d) OS lgc n
    (by
      intro i hi
      rcases hOS45 i hi with
        ⟨V, ρ, Uc, Hc, hV_open, hV_conn, hV_ne, hV_jost,
          hV_ET, hV_swapET, hUc_open, hUc_conn, hHc_holo,
          hwick_mem, hreal_mem, hwick_trace, hreal_trace⟩
      refine
        ⟨V, hV_open, hV_conn, hV_ne, hV_jost, hV_ET, hV_swapET, ?_⟩
      exact ⟨
        BHW.adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope
          (d := d) OS lgc n i hi V ρ Uc Hc
          hUc_open hUc_conn hHc_holo
          hwick_mem hreal_mem hwick_trace hreal_trace⟩)

/-- The compact Figure-2-4 Wick-pairing family supplies the source
distributional adjacent-tube anchor consumed by the source-side BHW theorem,
under the OS-selected-witness naming convention. -/
def bvt_F_distributionalJostAnchor_of_compactWickPairingEq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hCompact :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45CompactFigure24WickPairingEq
          (d := d) n i hi OS lgc) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_compactWickPairingEq
    (d := d) OS lgc n hCompact

end BHW
