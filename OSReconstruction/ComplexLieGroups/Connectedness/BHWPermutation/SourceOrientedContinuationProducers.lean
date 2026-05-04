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

end BHW
