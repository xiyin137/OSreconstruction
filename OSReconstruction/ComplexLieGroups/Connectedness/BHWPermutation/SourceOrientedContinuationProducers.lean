import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation

/-!
# Source-oriented BHW/Jost continuation producers

This file contains small producer-level assemblies built from the checked
source-oriented continuation carriers.  The hard Hall-Wightman/Jost analytic
inputs remain explicit parameters.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- A family of source-normal-form geometry patches plus a uniform oriented
descent theorem on each patch gives branch-free transfer neighborhoods at all
points of the ambient continuation set. -/
def bhw_jost_orientedBranchFreeTransferNeighborhood_at_of_sourceNormalFormProducer
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (patchAt :
      ∀ {center : Fin n → Fin (d + 1) → ℂ}, center ∈ U →
        BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center)
    (uniformDescent :
      ∀ {center : Fin n → Fin (d + 1) → ℂ}
        (hcenter : center ∈ U),
        ∀ p q,
          p ∈ (patchAt hcenter).carrier → p ∈ U →
          q ∈ (patchAt hcenter).carrier → q ∈ U →
          ∀ Cprev : BHWJostLocalOrientedContinuationChart hd n τ U,
            p ∈ Cprev.carrier →
              Σ Cnext : BHWJostLocalOrientedContinuationChart hd n τ U,
                BHWJostOrientedTransitionData hd n τ U Cprev Cnext p q)
    {center : Fin n → Fin (d + 1) → ℂ}
    (hcenter : center ∈ U) :
    BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center :=
  BHWJostOrientedBranchFreeTransferNeighborhood.ofSourceNormalFormPatch
    (patchAt hcenter)
    (fun p q hpG hpU hqG hqU Cprev hpC =>
      uniformDescent hcenter p q hpG hpU hqG hqU Cprev hpC)

/-- Top-level spelling of the compact transfer-cover chain constructor.  This
is the mechanical continuation-chain assembly after the initial chart and the
branch-free transfer neighborhoods have been supplied. -/
noncomputable def bhw_jost_orientedContinuationChain_of_transferCover
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
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
    BHWJostOrientedSourcePatchContinuationChain
      hd n τ Ω0 U B0 p0 (γ 1) :=
  BHWJostOrientedSourcePatchContinuationChain.ofTransferCover
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    (p0 := p0) γ hγ hγ_zero hγU T C0 hbase hp0C start_patch
    hstart_open hstart_preconnected hstart_nonempty hstart_mem
    hstart_sub hstart_agree

/-- Chain-level data sufficient to assemble a source-patch continuation atlas.
The hard content is selecting one continuation chain through each point of
`U`, proving terminal overlap equality for the selected chains, and proving
agreement with the initial branch on `Ω0 ∩ U`. -/
structure BHWOrientedContinuationChainAtlasData
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  p0 : Fin n → Fin (d + 1) → ℂ
  base_mem : p0 ∈ Ω0 ∩ U
  chainAt :
    ∀ z, z ∈ U →
      BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z
  terminal_overlap_eq :
    ∀ a b : {z // z ∈ U},
      Set.EqOn
        ((chainAt a.1 a.2).branch (Fin.last (chainAt a.1 a.2).m))
        ((chainAt b.1 b.2).branch (Fin.last (chainAt b.1 b.2).m))
        ((chainAt a.1 a.2).chart (Fin.last (chainAt a.1 a.2).m) ∩
          (chainAt b.1 b.2).chart (Fin.last (chainAt b.1 b.2).m))
  terminal_base_agree :
    ∀ z (hz : z ∈ Ω0 ∩ U),
      (chainAt z hz.2).branch (Fin.last (chainAt z hz.2).m) z = B0 z

namespace BHWOrientedContinuationChainAtlasData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}

/-- Assemble a continuation atlas from selected terminal chains plus their
terminal overlap and base-agreement proofs. -/
noncomputable def to_sourcePatchContinuationAtlas
    (D : BHWOrientedContinuationChainAtlasData hd n τ Ω0 U B0) :
    BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0 where
  chart := {z // z ∈ U}
  carrier := fun a =>
    (D.chainAt a.1 a.2).chart (Fin.last (D.chainAt a.1 a.2).m)
  branch := fun a =>
    (D.chainAt a.1 a.2).branch (Fin.last (D.chainAt a.1 a.2).m)
  cover := by
    intro z hz
    exact ⟨⟨z, hz⟩, (D.chainAt z hz).final_mem⟩
  carrier_open := by
    intro a
    exact (D.chainAt a.1 a.2).chart_open
      (Fin.last (D.chainAt a.1 a.2).m)
  carrier_sub_U := by
    intro a
    exact (D.chainAt a.1 a.2).chart_sub_U
      (Fin.last (D.chainAt a.1 a.2).m)
  branch_holo := by
    intro a
    exact (D.chainAt a.1 a.2).branch_holo
      (Fin.last (D.chainAt a.1 a.2).m)
  overlap_eq := by
    intro a b
    exact D.terminal_overlap_eq a b
  base_agree := by
    intro z hz
    exact ⟨⟨z, hz.2⟩, (D.chainAt z hz.2).final_mem,
      D.terminal_base_agree z hz⟩

/-- Chain-atlas data immediately gives a glued holomorphic branch on `U`. -/
theorem exists_glued_branch
    (D : BHWOrientedContinuationChainAtlasData hd n τ Ω0 U B0) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) :=
  bhw_glue_sourcePatchContinuationAtlas hd n τ Ω0 U B0
    D.to_sourcePatchContinuationAtlas

end BHWOrientedContinuationChainAtlasData

/-- Terminal comparison data for two oriented continuation chains with the
same base point and endpoint.  The hard BHW/Jost closed-loop comparison should
produce this object; its consumer is just evaluation at the endpoint. -/
structure BHWOrientedTerminalChainComparisonData
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 z : Fin n → Fin (d + 1) → ℂ}
    (C₁ C₂ :
      BHWJostOrientedSourcePatchContinuationChain
        hd n τ Ω0 U B0 p0 z) where
  terminalPatch : Set (Fin n → Fin (d + 1) → ℂ)
  endpoint_mem : z ∈ terminalPatch
  terminalPatch_open : IsOpen terminalPatch
  terminalPatch_preconnected : IsPreconnected terminalPatch
  terminalPatch_sub_left :
    terminalPatch ⊆ C₁.chart (Fin.last C₁.m)
  terminalPatch_sub_right :
    terminalPatch ⊆ C₂.chart (Fin.last C₂.m)
  terminal_branches_eq :
    Set.EqOn
      (C₁.branch (Fin.last C₁.m))
      (C₂.branch (Fin.last C₂.m))
      terminalPatch

namespace BHWOrientedTerminalChainComparisonData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 z : Fin n → Fin (d + 1) → ℂ}
variable {C₁ C₂ :
  BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z}

/-- Terminal comparison data immediately gives equality of the two continued
values. -/
theorem continuedValue_eq
    (P : BHWOrientedTerminalChainComparisonData C₁ C₂) :
    bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 C₁ =
      bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 C₂ :=
  P.terminal_branches_eq P.endpoint_mem

end BHWOrientedTerminalChainComparisonData

namespace BHWOrientedContinuationChainAtlasData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}

/-- Same-endpoint terminal comparison data for all retargeted chains supplies
the terminal overlap field required by the source-patch continuation atlas.

The point of this constructor is that atlas overlap is stronger than equality
of two continued endpoint values: for a point `y` in the intersection of two
terminal charts, retarget both terminal chains to end at `y` using the
tautological same-chart transition, then compare those two same-endpoint
chains with the selected chain ending at `y`. -/
noncomputable def ofSameEndpointComparisons
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (chainAt :
      ∀ z, z ∈ U →
        BHWJostOrientedSourcePatchContinuationChain
          hd n τ Ω0 U B0 p0 z)
    (sameEndpointComparison :
      ∀ {z : Fin n → Fin (d + 1) → ℂ}
        (C₁ C₂ :
          BHWJostOrientedSourcePatchContinuationChain
            hd n τ Ω0 U B0 p0 z),
          BHWOrientedTerminalChainComparisonData C₁ C₂)
    (terminal_base_agree :
      ∀ z (hz : z ∈ Ω0 ∩ U),
        (chainAt z hz.2).branch
          (Fin.last (chainAt z hz.2).m) z = B0 z) :
    BHWOrientedContinuationChainAtlasData hd n τ Ω0 U B0 where
  p0 := p0
  base_mem := base_mem
  chainAt := chainAt
  terminal_overlap_eq := by
    intro a b y hy
    rcases hy with ⟨hya, hyb⟩
    let Ca := chainAt a.1 a.2
    let Cb := chainAt b.1 b.2
    have hyU : y ∈ U := Ca.chart_sub_U (Fin.last Ca.m) hya
    let Cy := chainAt y hyU
    let Cay := Ca.retargetTerminal hya
    let Cby := Cb.retargetTerminal hyb
    have haCy :
        bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 Cay =
          bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 Cy :=
      (sameEndpointComparison Cay Cy).continuedValue_eq
    have hbCy :
        bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 Cby =
          bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 Cy :=
      (sameEndpointComparison Cby Cy).continuedValue_eq
    calc
      Ca.branch (Fin.last Ca.m) y =
          bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 Cay :=
        (BHWJostOrientedSourcePatchContinuationChain.retargetTerminal_continuedValue_eq_branch
          Ca hya).symm
      _ = bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 Cy :=
        haCy
      _ = bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 Cby :=
        hbCy.symm
      _ = Cb.branch (Fin.last Cb.m) y :=
        BHWJostOrientedSourcePatchContinuationChain.retargetTerminal_continuedValue_eq_branch
          Cb hyb
  terminal_base_agree := terminal_base_agree

end BHWOrientedContinuationChainAtlasData

end BHW
