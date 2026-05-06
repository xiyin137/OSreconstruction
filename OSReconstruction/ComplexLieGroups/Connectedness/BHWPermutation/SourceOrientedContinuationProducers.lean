import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuationTrace

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

/-- A path-connected continuation set, together with branch-free transfer
neighborhoods at every point, gives a selected continuation chain from the
fixed base point to every point of `U`. -/
noncomputable def bhw_jost_orientedContinuationChainAt_of_pathConnected_transferCover
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (hU_path : IsPathConnected U)
    (T :
      ∀ z, z ∈ U →
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U z)
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
    ∀ z, z ∈ U →
      BHWJostOrientedSourcePatchContinuationChain
        hd n τ Ω0 U B0 p0 z := by
  intro z hz
  let hjoin : JoinedIn U p0 z := hU_path.joinedIn p0 hbase.2 z hz
  have hchain :=
    bhw_jost_orientedContinuationChain_of_transferCover
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) (γ := fun t : unitInterval => hjoin.somePath t)
      hjoin.somePath.continuous
      (by simp)
      (fun t => hjoin.somePath_mem t)
      (fun t => T (hjoin.somePath t) (hjoin.somePath_mem t))
      C0 hbase hp0C start_patch hstart_open hstart_preconnected
      hstart_nonempty hstart_mem hstart_sub hstart_agree
  simpa using hchain

/-- Top-level spelling of the compact transfer-cover trace constructor.  This
is the provenance-retaining analogue of
`bhw_jost_orientedContinuationChain_of_transferCover`. -/
noncomputable def bhw_jost_orientedTransferContinuationTrace_of_transferCover
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
    BHWJostOrientedTransferContinuationTrace
      hd n τ Ω0 U B0 p0 (γ 1) :=
  BHWJostOrientedTransferContinuationTrace.ofTransferCover
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    (p0 := p0) γ hγ hγ_zero hγU T C0 hbase hp0C
    start_patch hstart_open hstart_preconnected hstart_nonempty
    hstart_mem hstart_sub hstart_agree

/-- A path-connected continuation set, together with branch-free transfer
neighborhoods at every point, gives selected provenance-retaining transfer
traces from the fixed base point to every point of `U`. -/
noncomputable def bhw_jost_orientedTransferContinuationTraceAt_of_pathConnected_transferCover
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (hU_path : IsPathConnected U)
    (T :
      ∀ z, z ∈ U →
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U z)
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
    ∀ z, z ∈ U →
      BHWJostOrientedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 z := by
  intro z hz
  let hjoin : JoinedIn U p0 z := hU_path.joinedIn p0 hbase.2 z hz
  have htrace :=
    bhw_jost_orientedTransferContinuationTrace_of_transferCover
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) (γ := fun t : unitInterval => hjoin.somePath t)
      hjoin.somePath.continuous
      (by simp)
      (fun t => hjoin.somePath_mem t)
      (fun t => T (hjoin.somePath t) (hjoin.somePath_mem t))
      C0 hbase hp0C start_patch hstart_open hstart_preconnected
      hstart_nonempty hstart_mem hstart_sub hstart_agree
  simpa using htrace

/-- Top-level spelling of the compact transfer-cover certified trace
constructor.  This is the provenance-retaining trace constructor plus the
one-step uniqueness certificates for the selected transfer controls. -/
noncomputable def bhw_jost_orientedCertifiedTransferContinuationTrace_of_transferCover
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
  BHWJostOrientedCertifiedTransferContinuationTrace.ofTransferCover
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    (p0 := p0) γ hγ hγ_zero hγU T T_unique C0 hbase hp0C
    start_patch hstart_open hstart_preconnected hstart_nonempty
    hstart_mem hstart_sub hstart_agree

/-- A path-connected continuation set, together with branch-free transfer
neighborhoods whose center-forgotten controls are uniqueness-certified, gives
selected certified transfer traces from the fixed base point to every point of
`U`. -/
noncomputable def bhw_jost_orientedCertifiedTransferContinuationTraceAt_of_pathConnected_transferCover
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (hU_path : IsPathConnected U)
    (T :
      ∀ z, z ∈ U →
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U z)
    (T_unique :
      ∀ z (hz : z ∈ U),
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (T z hz)))
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
    ∀ z, z ∈ U →
      BHWJostOrientedCertifiedTransferContinuationTrace
        hd n τ Ω0 U B0 p0 z := by
  intro z hz
  let hjoin : JoinedIn U p0 z := hU_path.joinedIn p0 hbase.2 z hz
  have htrace :=
    bhw_jost_orientedCertifiedTransferContinuationTrace_of_transferCover
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) (γ := fun t : unitInterval => hjoin.somePath t)
      hjoin.somePath.continuous
      (by simp)
      (fun t => hjoin.somePath_mem t)
      (fun t => T (hjoin.somePath t) (hjoin.somePath_mem t))
      (fun t => T_unique (hjoin.somePath t) (hjoin.somePath_mem t))
      C0 hbase hp0C start_patch hstart_open hstart_preconnected
      hstart_nonempty hstart_mem hstart_sub hstart_agree
  simpa using htrace

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

/-- Trace-level data sufficient to assemble a source-patch continuation
atlas.  Unlike an arbitrary chain-atlas producer, this records the actual
branch-free transfer trace selected for each terminal point and asks for the
local terminal-point comparison theorem only for such traced continuations. -/
structure BHWOrientedContinuationTraceAtlasData
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  p0 : Fin n → Fin (d + 1) → ℂ
  base_mem : p0 ∈ Ω0 ∩ U
  traceAt :
    ∀ z, z ∈ U →
      BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 z
  terminal_overlap_comparison :
    ∀ (a b : {z // z ∈ U}) {y : Fin n → Fin (d + 1) → ℂ},
      y ∈ (traceAt a.1 a.2).chain.chart
        (Fin.last (traceAt a.1 a.2).chain.m) →
      y ∈ (traceAt b.1 b.2).chain.chart
        (Fin.last (traceAt b.1 b.2).chain.m) →
      BHWLocalChartTerminalComparisonData
        ((traceAt a.1 a.2).chain.localChart
          (Fin.last (traceAt a.1 a.2).chain.m))
        ((traceAt b.1 b.2).chain.localChart
          (Fin.last (traceAt b.1 b.2).chain.m)) y
  terminal_base_agree :
    ∀ z (hz : z ∈ Ω0 ∩ U),
      ((traceAt z hz.2).chain.branch
        (Fin.last (traceAt z hz.2).chain.m)) z = B0 z

namespace BHWOrientedContinuationTraceAtlasData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}

/-- Forget trace provenance and retain only the terminal continuation chain
selected for each point of `U`. -/
def chainAt
    (D : BHWOrientedContinuationTraceAtlasData hd n τ Ω0 U B0) :
    ∀ z, z ∈ U →
      BHWJostOrientedSourcePatchContinuationChain
        hd n τ Ω0 U B0 D.p0 z :=
  fun z hz => (D.traceAt z hz).chain

/-- Trace-level terminal-point comparison gives the terminal overlap field
of the ordinary chain-atlas data. -/
noncomputable def to_chainAtlasData
    (D : BHWOrientedContinuationTraceAtlasData hd n τ Ω0 U B0) :
    BHWOrientedContinuationChainAtlasData hd n τ Ω0 U B0 where
  p0 := D.p0
  base_mem := D.base_mem
  chainAt := D.chainAt
  terminal_overlap_eq := by
    intro a b y hy
    rcases hy with ⟨hya, hyb⟩
    let P := D.terminal_overlap_comparison a b hya hyb
    have hlocal :
        ((D.traceAt a.1 a.2).chain.localChart
            (Fin.last (D.traceAt a.1 a.2).chain.m)).branch y =
          ((D.traceAt b.1 b.2).chain.localChart
            (Fin.last (D.traceAt b.1 b.2).chain.m)).branch y := by
      exact BHWLocalChartTerminalComparisonData.branch_eq_at_endpoint P
    calc
      ((D.traceAt a.1 a.2).chain.branch
          (Fin.last (D.traceAt a.1 a.2).chain.m)) y =
          ((D.traceAt a.1 a.2).chain.localChart
            (Fin.last (D.traceAt a.1 a.2).chain.m)).branch y :=
        (D.traceAt a.1 a.2).chain.branch_eq_local
          (Fin.last (D.traceAt a.1 a.2).chain.m) y hya
      _ =
          ((D.traceAt b.1 b.2).chain.localChart
            (Fin.last (D.traceAt b.1 b.2).chain.m)).branch y :=
        hlocal
      _ =
          ((D.traceAt b.1 b.2).chain.branch
            (Fin.last (D.traceAt b.1 b.2).chain.m)) y :=
        ((D.traceAt b.1 b.2).chain.branch_eq_local
          (Fin.last (D.traceAt b.1 b.2).chain.m) y hyb).symm
  terminal_base_agree := D.terminal_base_agree

/-- Trace-atlas data immediately gives a source-patch continuation atlas. -/
noncomputable def to_sourcePatchContinuationAtlas
    (D : BHWOrientedContinuationTraceAtlasData hd n τ Ω0 U B0) :
    BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0 :=
  D.to_chainAtlasData.to_sourcePatchContinuationAtlas

/-- Trace-atlas data immediately gives a glued holomorphic branch on `U`. -/
theorem exists_glued_branch
    (D : BHWOrientedContinuationTraceAtlasData hd n τ Ω0 U B0) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) :=
  D.to_chainAtlasData.exists_glued_branch

/-- Selected trace comparisons plus selected base-chart comparisons supply
trace-atlas data.  This is the minimal atlas constructor: comparison is
required only for the selected traces that actually define the atlas. -/
noncomputable def ofSelectedComparisonsAndInitialChart
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (traceAt :
      ∀ z, z ∈ U →
        BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 z)
    (terminal_overlap_comparison :
      ∀ (a b : {z // z ∈ U}) {y : Fin n → Fin (d + 1) → ℂ},
        y ∈ (traceAt a.1 a.2).chain.chart
          (Fin.last (traceAt a.1 a.2).chain.m) →
        y ∈ (traceAt b.1 b.2).chain.chart
          (Fin.last (traceAt b.1 b.2).chain.m) →
        BHWLocalChartTerminalComparisonData
          ((traceAt a.1 a.2).chain.localChart
            (Fin.last (traceAt a.1 a.2).chain.m))
          ((traceAt b.1 b.2).chain.localChart
            (Fin.last (traceAt b.1 b.2).chain.m)) y)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (terminal_base_comparison :
      ∀ z (hz : z ∈ Ω0 ∩ U),
        BHWLocalChartTerminalComparisonData
          ((traceAt z hz.2).chain.localChart
            (Fin.last (traceAt z hz.2).chain.m)) C0 z)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    BHWOrientedContinuationTraceAtlasData hd n τ Ω0 U B0 where
  p0 := p0
  base_mem := base_mem
  traceAt := traceAt
  terminal_overlap_comparison := terminal_overlap_comparison
  terminal_base_agree := by
    intro z hz
    let P := terminal_base_comparison z hz
    have hlocal :
        ((traceAt z hz.2).chain.localChart
            (Fin.last (traceAt z hz.2).chain.m)).branch z =
          C0.branch z :=
      BHWLocalChartTerminalComparisonData.branch_eq_at_endpoint P
    calc
      ((traceAt z hz.2).chain.branch
          (Fin.last (traceAt z hz.2).chain.m)) z =
          ((traceAt z hz.2).chain.localChart
            (Fin.last (traceAt z hz.2).chain.m)).branch z :=
        (traceAt z hz.2).chain.branch_eq_local
          (Fin.last (traceAt z hz.2).chain.m) z
          (traceAt z hz.2).chain.final_mem
      _ = C0.branch z := hlocal
      _ = B0 z := initial_branch_agree z hz

/-- Terminal-point comparison plus an initial chart normalized by `B0`
supplies all trace-atlas data.  Base agreement is proved by comparing the
selected trace ending at `z` with the zero-step base trace observed at `z`. -/
noncomputable def ofTerminalPointComparisonsAndInitialChart
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (traceAt :
      ∀ z, z ∈ U →
        BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 z)
    (terminalPointComparison :
      ∀ {y : Fin n → Fin (d + 1) → ℂ}
        (T₁ T₂ :
          BHWJostOrientedTransferTerminalPointTrace
            hd n τ Ω0 U B0 p0 y),
        BHWLocalChartTerminalComparisonData
          (T₁.trace.chain.localChart (Fin.last T₁.trace.chain.m))
          (T₂.trace.chain.localChart (Fin.last T₂.trace.chain.m)) y)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    BHWOrientedContinuationTraceAtlasData hd n τ Ω0 U B0 where
  p0 := p0
  base_mem := base_mem
  traceAt := traceAt
  terminal_overlap_comparison := by
    intro a b y hya hyb
    exact terminalPointComparison
      (BHWJostOrientedTransferTerminalPointTrace.ofTracePoint
        (y := y) (traceAt a.1 a.2) hya)
      (BHWJostOrientedTransferTerminalPointTrace.ofTracePoint
        (y := y) (traceAt b.1 b.2) hyb)
  terminal_base_agree := by
    intro z hz
    let Tz :=
      BHWJostOrientedTransferTerminalPointTrace.atEndpoint
        (traceAt z hz.2)
    let TbaseTrace :=
      BHWJostOrientedTransferContinuationTrace.base
        (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
        (p0 := p0) C0 base_mem hp0C start_patch hstart_open
        hstart_preconnected hstart_nonempty hstart_mem hstart_sub
        hstart_agree
    have hzBase :
        z ∈ TbaseTrace.chain.chart (Fin.last TbaseTrace.chain.m) := by
      simpa [TbaseTrace, BHWJostOrientedTransferContinuationTrace.base,
        BHWJostOrientedSourcePatchContinuationChain.base] using
        initial_chart_mem z hz
    let Tbase :=
      BHWJostOrientedTransferTerminalPointTrace.ofTracePoint
        (y := z) TbaseTrace hzBase
    let P := terminalPointComparison Tz Tbase
    have hlocal :
        ((traceAt z hz.2).chain.localChart
            (Fin.last (traceAt z hz.2).chain.m)).branch z =
          C0.branch z := by
      have hcmp :=
        BHWLocalChartTerminalComparisonData.branch_eq_at_endpoint P
      simpa [Tz, Tbase, TbaseTrace,
        BHWJostOrientedTransferContinuationTrace.base,
        BHWJostOrientedSourcePatchContinuationChain.base] using hcmp
    calc
      ((traceAt z hz.2).chain.branch
          (Fin.last (traceAt z hz.2).chain.m)) z =
          ((traceAt z hz.2).chain.localChart
            (Fin.last (traceAt z hz.2).chain.m)).branch z :=
        (traceAt z hz.2).chain.branch_eq_local
          (Fin.last (traceAt z hz.2).chain.m) z
          (traceAt z hz.2).chain.final_mem
      _ = C0.branch z := hlocal
      _ = B0 z := initial_branch_agree z hz

/-- Certified terminal-point comparison plus an initial chart normalized by
`B0` supplies all trace-atlas data.  This is the future strict-route
constructor: terminal comparison consumes only traces carrying certified
one-step uniqueness for every stored transfer control. -/
noncomputable def ofCertifiedTerminalPointComparisonsAndInitialChart
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (traceAt :
      ∀ z, z ∈ U →
        BHWJostOrientedCertifiedTransferContinuationTrace
          hd n τ Ω0 U B0 p0 z)
    (terminalPointComparison :
      ∀ {y : Fin n → Fin (d + 1) → ℂ}
        (T₁ T₂ :
          BHWJostOrientedCertifiedTransferTerminalPointTrace
            hd n τ Ω0 U B0 p0 y),
        BHWLocalChartTerminalComparisonData
          (T₁.trace.trace.chain.localChart
            (Fin.last T₁.trace.trace.chain.m))
          (T₂.trace.trace.chain.localChart
            (Fin.last T₂.trace.trace.chain.m)) y)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    BHWOrientedContinuationTraceAtlasData hd n τ Ω0 U B0 where
  p0 := p0
  base_mem := base_mem
  traceAt := fun z hz => (traceAt z hz).trace
  terminal_overlap_comparison := by
    intro a b y hya hyb
    exact terminalPointComparison
      (BHWJostOrientedCertifiedTransferTerminalPointTrace.ofTracePoint
        (y := y) (traceAt a.1 a.2) hya)
      (BHWJostOrientedCertifiedTransferTerminalPointTrace.ofTracePoint
        (y := y) (traceAt b.1 b.2) hyb)
  terminal_base_agree := by
    intro z hz
    let Tz :=
      BHWJostOrientedCertifiedTransferTerminalPointTrace.atEndpoint
        (traceAt z hz.2)
    let TbaseTrace :=
      BHWJostOrientedCertifiedTransferContinuationTrace.base
        (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
        (p0 := p0) C0 base_mem hp0C start_patch hstart_open
        hstart_preconnected hstart_nonempty hstart_mem hstart_sub
        hstart_agree
    have hzBase :
        z ∈ TbaseTrace.trace.chain.chart
          (Fin.last TbaseTrace.trace.chain.m) := by
      simpa [TbaseTrace, BHWJostOrientedCertifiedTransferContinuationTrace.base,
        BHWJostOrientedTransferContinuationTrace.base,
        BHWJostOrientedSourcePatchContinuationChain.base] using
        initial_chart_mem z hz
    let Tbase :=
      BHWJostOrientedCertifiedTransferTerminalPointTrace.ofTracePoint
        (y := z) TbaseTrace hzBase
    let P := terminalPointComparison Tz Tbase
    have hlocal :
        ((traceAt z hz.2).trace.chain.localChart
            (Fin.last (traceAt z hz.2).trace.chain.m)).branch z =
          C0.branch z := by
      have hcmp :=
        BHWLocalChartTerminalComparisonData.branch_eq_at_endpoint P
      simpa [Tz, Tbase, TbaseTrace,
        BHWJostOrientedCertifiedTransferContinuationTrace.base,
        BHWJostOrientedTransferContinuationTrace.base,
        BHWJostOrientedSourcePatchContinuationChain.base] using hcmp
    calc
      ((traceAt z hz.2).trace.chain.branch
          (Fin.last (traceAt z hz.2).trace.chain.m)) z =
          ((traceAt z hz.2).trace.chain.localChart
            (Fin.last (traceAt z hz.2).trace.chain.m)).branch z :=
        (traceAt z hz.2).trace.chain.branch_eq_local
          (Fin.last (traceAt z hz.2).trace.chain.m) z
          (traceAt z hz.2).trace.chain.final_mem
      _ = C0.branch z := hlocal
      _ = B0 z := initial_branch_agree z hz

/-- A path-connected continuation set with branch-free transfer
neighborhoods at every point, together with terminal-point comparison for
transfer traces and an initial chart normalized by `B0`, supplies all
trace-atlas data. -/
noncomputable def ofPathConnectedTransferCoverAndInitialChart
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (hU_path : IsPathConnected U)
    (T :
      ∀ z, z ∈ U →
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U z)
    (terminalPointComparison :
      ∀ {y : Fin n → Fin (d + 1) → ℂ}
        (T₁ T₂ :
          BHWJostOrientedTransferTerminalPointTrace
            hd n τ Ω0 U B0 p0 y),
        BHWLocalChartTerminalComparisonData
          (T₁.trace.chain.localChart (Fin.last T₁.trace.chain.m))
          (T₂.trace.chain.localChart (Fin.last T₂.trace.chain.m)) y)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    BHWOrientedContinuationTraceAtlasData hd n τ Ω0 U B0 :=
  ofTerminalPointComparisonsAndInitialChart
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    p0 base_mem
    (bhw_jost_orientedTransferContinuationTraceAt_of_pathConnected_transferCover
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) hU_path T C0 base_mem hp0C start_patch
      hstart_open hstart_preconnected hstart_nonempty hstart_mem
      hstart_sub hstart_agree)
    terminalPointComparison C0 hp0C start_patch hstart_open
    hstart_preconnected hstart_nonempty hstart_mem hstart_sub
    hstart_agree initial_chart_mem initial_branch_agree

end BHWOrientedContinuationTraceAtlasData

/-- A path-connected branch-free transfer cover plus terminal-point trace
comparison gives the glued holomorphic source-patch branch on `U`. -/
theorem bhw_jost_orientedGluedBranch_of_pathConnected_transferCover
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (hU_path : IsPathConnected U)
    (T :
      ∀ z, z ∈ U →
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U z)
    (terminalPointComparison :
      ∀ {y : Fin n → Fin (d + 1) → ℂ}
        (T₁ T₂ :
          BHWJostOrientedTransferTerminalPointTrace
            hd n τ Ω0 U B0 p0 y),
        BHWLocalChartTerminalComparisonData
          (T₁.trace.chain.localChart (Fin.last T₁.trace.chain.m))
          (T₂.trace.chain.localChart (Fin.last T₂.trace.chain.m)) y)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) :=
  (BHWOrientedContinuationTraceAtlasData.ofPathConnectedTransferCoverAndInitialChart
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    p0 base_mem hU_path T terminalPointComparison C0 hp0C
    start_patch hstart_open hstart_preconnected hstart_nonempty
    hstart_mem hstart_sub hstart_agree initial_chart_mem
    initial_branch_agree).exists_glued_branch

/-- Certified selected traces plus certified terminal-point comparison give
the glued holomorphic source-patch branch on `U`.  This is the checked final
assembly surface for the strict route after the certified trace producer and
the certified terminal comparison theorem are proved. -/
theorem bhw_jost_orientedGluedBranch_of_certifiedTraces
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (traceAt :
      ∀ z, z ∈ U →
        BHWJostOrientedCertifiedTransferContinuationTrace
          hd n τ Ω0 U B0 p0 z)
    (terminalPointComparison :
      ∀ {y : Fin n → Fin (d + 1) → ℂ}
        (T₁ T₂ :
          BHWJostOrientedCertifiedTransferTerminalPointTrace
            hd n τ Ω0 U B0 p0 y),
        BHWLocalChartTerminalComparisonData
          (T₁.trace.trace.chain.localChart
            (Fin.last T₁.trace.trace.chain.m))
          (T₂.trace.trace.chain.localChart
            (Fin.last T₂.trace.trace.chain.m)) y)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) :=
  (BHWOrientedContinuationTraceAtlasData.ofCertifiedTerminalPointComparisonsAndInitialChart
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    p0 base_mem traceAt terminalPointComparison C0 hp0C start_patch
    hstart_open hstart_preconnected hstart_nonempty hstart_mem hstart_sub
    hstart_agree initial_chart_mem initial_branch_agree).exists_glued_branch

/-- A path-connected branch-free transfer cover whose center-forgotten controls
are uniqueness-certified, plus certified terminal-point trace comparison, gives
the glued holomorphic source-patch branch on `U`. -/
theorem bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (hU_path : IsPathConnected U)
    (T :
      ∀ z, z ∈ U →
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U z)
    (T_unique :
      ∀ z (hz : z ∈ U),
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (T z hz)))
    (terminalPointComparison :
      ∀ {y : Fin n → Fin (d + 1) → ℂ}
        (T₁ T₂ :
          BHWJostOrientedCertifiedTransferTerminalPointTrace
            hd n τ Ω0 U B0 p0 y),
        BHWLocalChartTerminalComparisonData
          (T₁.trace.trace.chain.localChart
            (Fin.last T₁.trace.trace.chain.m))
          (T₂.trace.trace.chain.localChart
            (Fin.last T₂.trace.trace.chain.m)) y)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) :=
  bhw_jost_orientedGluedBranch_of_certifiedTraces
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    p0 base_mem
    (bhw_jost_orientedCertifiedTransferContinuationTraceAt_of_pathConnected_transferCover
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) hU_path T T_unique C0 base_mem hp0C start_patch
      hstart_open hstart_preconnected hstart_nonempty hstart_mem
      hstart_sub hstart_agree)
    terminalPointComparison C0 hp0C start_patch hstart_open
    hstart_preconnected hstart_nonempty hstart_mem hstart_sub hstart_agree
    initial_chart_mem initial_branch_agree

/-- Source-normal-form producer form of the certified path-connected gluing
theorem.  The remaining analytic inputs are the uniform local descent theorem,
one-step uniqueness for the center-forgotten controls produced by that descent,
and certified terminal-point trace comparison. -/
theorem bhw_jost_orientedGluedBranch_of_pathConnected_sourceNormalFormProducer
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (hU_path : IsPathConnected U)
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
    (uniformDescent_unique :
      ∀ z (hz : z ∈ U),
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (bhw_jost_orientedBranchFreeTransferNeighborhood_at_of_sourceNormalFormProducer
              (hd := hd) (τ := τ) (U := U)
              patchAt uniformDescent hz)))
    (terminalPointComparison :
      ∀ {y : Fin n → Fin (d + 1) → ℂ}
        (T₁ T₂ :
          BHWJostOrientedCertifiedTransferTerminalPointTrace
            hd n τ Ω0 U B0 p0 y),
        BHWLocalChartTerminalComparisonData
          (T₁.trace.trace.chain.localChart
            (Fin.last T₁.trace.trace.chain.m))
          (T₂.trace.trace.chain.localChart
            (Fin.last T₂.trace.trace.chain.m)) y)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) :=
  bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    p0 base_mem hU_path
    (fun _ hz =>
      bhw_jost_orientedBranchFreeTransferNeighborhood_at_of_sourceNormalFormProducer
        (hd := hd) (τ := τ) (U := U)
        patchAt uniformDescent hz)
    uniformDescent_unique terminalPointComparison C0 hp0C start_patch
    hstart_open hstart_preconnected hstart_nonempty hstart_mem hstart_sub
    hstart_agree initial_chart_mem initial_branch_agree

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

/-- A chart-level comparison between the terminal local charts packages into
the chain-level terminal comparison data. -/
def ofLocalChartComparison
    (P :
      BHWLocalChartTerminalComparisonData
        (C₁.localChart (Fin.last C₁.m))
        (C₂.localChart (Fin.last C₂.m)) z) :
    BHWOrientedTerminalChainComparisonData C₁ C₂ where
  terminalPatch := P.terminalPatch
  endpoint_mem := P.endpoint_mem
  terminalPatch_open := P.terminalPatch_open
  terminalPatch_preconnected := P.terminalPatch_preconnected
  terminalPatch_sub_left := by
    intro y hy
    simpa [C₁.chart_eq_local (Fin.last C₁.m)]
      using P.terminalPatch_sub_left hy
  terminalPatch_sub_right := by
    intro y hy
    simpa [C₂.chart_eq_local (Fin.last C₂.m)]
      using P.terminalPatch_sub_right hy
  terminal_branches_eq := by
    intro y hy
    have hy₁ : y ∈ C₁.chart (Fin.last C₁.m) := by
      simpa [C₁.chart_eq_local (Fin.last C₁.m)]
        using P.terminalPatch_sub_left hy
    have hy₂ : y ∈ C₂.chart (Fin.last C₂.m) := by
      simpa [C₂.chart_eq_local (Fin.last C₂.m)]
        using P.terminalPatch_sub_right hy
    rw [C₁.branch_eq_local (Fin.last C₁.m) y hy₁,
      C₂.branch_eq_local (Fin.last C₂.m) y hy₂]
    exact P.terminal_branches_eq hy

/-- Terminal comparison data immediately gives equality of the two continued
values. -/
theorem continuedValue_eq
    (P : BHWOrientedTerminalChainComparisonData C₁ C₂) :
    bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 C₁ =
      bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 C₂ :=
  P.terminal_branches_eq P.endpoint_mem

/-- Same-endpoint comparison of two terminal-retargeted transfer traces gives
the local chart comparison required by the trace-atlas overlap field.  This is
the mechanical endpoint conversion after the closed-path theorem has compared
the retargeted chains. -/
noncomputable def ofRetargetedTerminalPointTraceComparison
    {y : Fin n → Fin (d + 1) → ℂ}
    (T₁ T₂ :
      BHWJostOrientedTransferTerminalPointTrace
        hd n τ Ω0 U B0 p0 y)
    (P :
      BHWOrientedTerminalChainComparisonData
        (T₁.trace.chain.retargetTerminal T₁.point_mem)
        (T₂.trace.chain.retargetTerminal T₂.point_mem)) :
    BHWLocalChartTerminalComparisonData
      (T₁.trace.chain.localChart (Fin.last T₁.trace.chain.m))
      (T₂.trace.chain.localChart (Fin.last T₂.trace.chain.m)) y where
  terminalPatch := P.terminalPatch
  endpoint_mem := P.endpoint_mem
  terminalPatch_open := P.terminalPatch_open
  terminalPatch_preconnected := P.terminalPatch_preconnected
  terminalPatch_sub_left := by
    intro x hx
    simpa [BHWJostOrientedSourcePatchContinuationChain.retargetTerminal,
      BHWJostOrientedSourcePatchContinuationChain.snoc] using
      P.terminalPatch_sub_left hx
  terminalPatch_sub_right := by
    intro x hx
    simpa [BHWJostOrientedSourcePatchContinuationChain.retargetTerminal,
      BHWJostOrientedSourcePatchContinuationChain.snoc] using
      P.terminalPatch_sub_right hx
  terminal_branches_eq := by
    intro x hx
    simpa [BHWJostOrientedSourcePatchContinuationChain.retargetTerminal,
      BHWJostOrientedSourcePatchContinuationChain.snoc] using
      P.terminal_branches_eq hx

/-- Certified variant of
`ofRetargetedTerminalPointTraceComparison`.  The proof only forgets the
certificates after the two certified traces have been retargeted to the common
terminal point; the one-step uniqueness content remains available to the
closed-path theorem that supplies `P`. -/
noncomputable def ofCertifiedRetargetedTerminalPointTraceComparison
    {y : Fin n → Fin (d + 1) → ℂ}
    (T₁ T₂ :
      BHWJostOrientedCertifiedTransferTerminalPointTrace
        hd n τ Ω0 U B0 p0 y)
    (P :
      BHWOrientedTerminalChainComparisonData
        (T₁.trace.trace.chain.retargetTerminal T₁.point_mem)
        (T₂.trace.trace.chain.retargetTerminal T₂.point_mem)) :
    BHWLocalChartTerminalComparisonData
      (T₁.trace.trace.chain.localChart
        (Fin.last T₁.trace.trace.chain.m))
      (T₂.trace.trace.chain.localChart
        (Fin.last T₂.trace.trace.chain.m)) y where
  terminalPatch := P.terminalPatch
  endpoint_mem := P.endpoint_mem
  terminalPatch_open := P.terminalPatch_open
  terminalPatch_preconnected := P.terminalPatch_preconnected
  terminalPatch_sub_left := by
    intro x hx
    simpa [BHWJostOrientedSourcePatchContinuationChain.retargetTerminal,
      BHWJostOrientedSourcePatchContinuationChain.snoc] using
      P.terminalPatch_sub_left hx
  terminalPatch_sub_right := by
    intro x hx
    simpa [BHWJostOrientedSourcePatchContinuationChain.retargetTerminal,
      BHWJostOrientedSourcePatchContinuationChain.snoc] using
      P.terminalPatch_sub_right hx
  terminal_branches_eq := by
    intro x hx
    simpa [BHWJostOrientedSourcePatchContinuationChain.retargetTerminal,
      BHWJostOrientedSourcePatchContinuationChain.snoc] using
      P.terminal_branches_eq hx

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

/-- Base agreement follows from same-endpoint comparison with a base chain
whose terminal chart covers the initial source patch and whose terminal branch
is already normalized by `B0` there. -/
theorem terminal_base_agree_of_sameEndpointComparison
    {p0 : Fin n → Fin (d + 1) → ℂ}
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
    (Cbase :
      BHWJostOrientedSourcePatchContinuationChain
        hd n τ Ω0 U B0 p0 p0)
    (base_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ Cbase.chart (Fin.last Cbase.m))
    (base_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U →
        Cbase.branch (Fin.last Cbase.m) z = B0 z) :
    ∀ z (hz : z ∈ Ω0 ∩ U),
      (chainAt z hz.2).branch
        (Fin.last (chainAt z hz.2).m) z = B0 z := by
  intro z hz
  let Ctarget := chainAt z hz.2
  let CbaseAtZ := Cbase.retargetTerminal (base_chart_mem z hz)
  have hcmp :
      bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 Ctarget =
        bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 CbaseAtZ :=
    (sameEndpointComparison Ctarget CbaseAtZ).continuedValue_eq
  calc
    (chainAt z hz.2).branch (Fin.last (chainAt z hz.2).m) z =
        bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 Ctarget := rfl
    _ = bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 CbaseAtZ :=
        hcmp
    _ = Cbase.branch (Fin.last Cbase.m) z :=
        BHWJostOrientedSourcePatchContinuationChain.retargetTerminal_continuedValue_eq_branch
          Cbase (base_chart_mem z hz)
    _ = B0 z := base_branch_agree z hz

/-- Same-endpoint comparison plus a normalized base chain supplies all
chain-atlas fields, including both terminal overlap and base agreement. -/
noncomputable def ofSameEndpointComparisonsAndBaseChain
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
    (Cbase :
      BHWJostOrientedSourcePatchContinuationChain
        hd n τ Ω0 U B0 p0 p0)
    (base_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ Cbase.chart (Fin.last Cbase.m))
    (base_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U →
        Cbase.branch (Fin.last Cbase.m) z = B0 z) :
    BHWOrientedContinuationChainAtlasData hd n τ Ω0 U B0 :=
  ofSameEndpointComparisons
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    p0 base_mem chainAt sameEndpointComparison
    (terminal_base_agree_of_sameEndpointComparison chainAt
      sameEndpointComparison Cbase base_chart_mem base_branch_agree)

/-- Same-endpoint comparison plus an initial chart covering `Ω0 ∩ U`
supplies the chain-atlas data.  The normalized base chain is the zero-step
chain built from the initial chart. -/
noncomputable def ofSameEndpointComparisonsAndInitialChart
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
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    BHWOrientedContinuationChainAtlasData hd n τ Ω0 U B0 :=
  let Cbase :=
    BHWJostOrientedSourcePatchContinuationChain.base
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) C0 base_mem hp0C start_patch hstart_open
      hstart_preconnected hstart_nonempty hstart_mem hstart_sub
      hstart_agree
  ofSameEndpointComparisonsAndBaseChain
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    p0 base_mem chainAt sameEndpointComparison Cbase
    (fun z hz => initial_chart_mem z hz)
    (fun z hz => initial_branch_agree z hz)

end BHWOrientedContinuationChainAtlasData

/-- A path-connected branch-free transfer cover whose center-forgotten
controls are uniqueness-certified, plus same-endpoint comparison for the two
terminal-retargeted certified traces, gives the glued holomorphic source-patch
branch on `U`.

This is the monodromy-facing variant of
`bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover`: the
closed-path theorem may compare retargeted chains, and the local terminal
chart comparison required by the atlas is then obtained mechanically. -/
theorem bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover_retargetedComparisons
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (hU_path : IsPathConnected U)
    (T :
      ∀ z, z ∈ U →
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U z)
    (T_unique :
      ∀ z (hz : z ∈ U),
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (T z hz)))
    (retargetedComparison :
      ∀ {y : Fin n → Fin (d + 1) → ℂ}
        (T₁ T₂ :
          BHWJostOrientedCertifiedTransferTerminalPointTrace
            hd n τ Ω0 U B0 p0 y),
        BHWOrientedTerminalChainComparisonData
          (T₁.trace.trace.chain.retargetTerminal T₁.point_mem)
          (T₂.trace.trace.chain.retargetTerminal T₂.point_mem))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) :=
  bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    p0 base_mem hU_path T T_unique
    (fun T₁ T₂ =>
      BHWOrientedTerminalChainComparisonData.ofCertifiedRetargetedTerminalPointTraceComparison
        T₁ T₂ (retargetedComparison T₁ T₂))
    C0 hp0C start_patch hstart_open hstart_preconnected hstart_nonempty
    hstart_mem hstart_sub hstart_agree initial_chart_mem
    initial_branch_agree

/-- Source-normal-form producer form with the monodromy-facing retargeted
comparison input.  After the source-normal-form patch producer and one-step
uniqueness theorem are available, the only remaining comparison theorem has to
compare the two terminal-retargeted certified chains. -/
theorem bhw_jost_orientedGluedBranch_of_pathConnected_sourceNormalFormProducer_retargetedComparisons
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
    {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (p0 : Fin n → Fin (d + 1) → ℂ)
    (base_mem : p0 ∈ Ω0 ∩ U)
    (hU_path : IsPathConnected U)
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
    (uniformDescent_unique :
      ∀ z (hz : z ∈ U),
        BHWJostOrientedTransferControlHasUniqueNext
          (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
            (bhw_jost_orientedBranchFreeTransferNeighborhood_at_of_sourceNormalFormProducer
              (hd := hd) (τ := τ) (U := U)
              patchAt uniformDescent hz)))
    (retargetedComparison :
      ∀ {y : Fin n → Fin (d + 1) → ℂ}
        (T₁ T₂ :
          BHWJostOrientedCertifiedTransferTerminalPointTrace
            hd n τ Ω0 U B0 p0 y),
        BHWOrientedTerminalChainComparisonData
          (T₁.trace.trace.chain.retargetTerminal T₁.point_mem)
          (T₂.trace.trace.chain.retargetTerminal T₂.point_mem))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (initial_chart_mem :
      ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier)
    (initial_branch_agree :
      ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) :=
  bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover_retargetedComparisons
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    p0 base_mem hU_path
    (fun _ hz =>
      bhw_jost_orientedBranchFreeTransferNeighborhood_at_of_sourceNormalFormProducer
        (hd := hd) (τ := τ) (U := U)
        patchAt uniformDescent hz)
    uniformDescent_unique retargetedComparison C0 hp0C start_patch
    hstart_open hstart_preconnected hstart_nonempty hstart_mem hstart_sub
    hstart_agree initial_chart_mem initial_branch_agree

end BHW
