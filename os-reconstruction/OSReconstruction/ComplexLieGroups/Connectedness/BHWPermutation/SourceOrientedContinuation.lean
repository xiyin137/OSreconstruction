/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Topology.UnitInterval
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented
import Init
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Implicit
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension











noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- The source-patch ambient used in the OS I §4.5 adjacent transposition
route: the ordinary extended tube together with the selected adjacent
permuted extended-tube sector. -/
def os45SourcePatchBHWJostAmbient
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  ExtendedTube d n ∪ {z | permAct (d := d) τ z ∈ ExtendedTube d n}

namespace UnitIntervalOrderedSubdivision

variable {ι : Type*} {c : ι → Set unitInterval}

end UnitIntervalOrderedSubdivision

/-- Permuting source labels is continuous in the finite product topology. -/
theorem continuous_permAct (σ : Equiv.Perm (Fin n)) :
    Continuous (permAct (d := d) σ) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (σ k))

/-- A local source chart whose branch descends through the oriented source
invariant.  The `oriented_realizes` field is essential: the stored oriented
domain is a local image of the source carrier, not an arbitrary larger
relative-open set. -/
structure BHWJostLocalOrientedContinuationChart
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (U : Set (Fin n → Fin (d + 1) → ℂ)) where
  carrier : Set (Fin n → Fin (d + 1) → ℂ)
  carrier_open : IsOpen carrier
  carrier_preconnected : IsPreconnected carrier
  carrier_sub_U : carrier ⊆ U
  carrier_is_lorentz_step :
    ∃ Ωbase : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ωbase ∧
      Ωbase ⊆ os45SourcePatchBHWJostAmbient d n τ ∧
      ∃ Λ : ComplexLorentzGroup d,
        carrier = (fun u => complexLorentzAction Λ u) '' Ωbase
  orientedDomain : Set (SourceOrientedGramData d n)
  oriented_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n orientedDomain
  oriented_preconnected : IsPreconnected orientedDomain
  oriented_sub_variety :
    orientedDomain ⊆ sourceOrientedGramVariety d n
  oriented_mem :
    ∀ z, z ∈ carrier →
      sourceOrientedMinkowskiInvariant d n z ∈ orientedDomain
  oriented_realizes :
    ∀ G, G ∈ orientedDomain →
      ∃ z, z ∈ carrier ∧ sourceOrientedMinkowskiInvariant d n z = G
  Psi : SourceOrientedGramData d n → ℂ
  Psi_holo :
    SourceOrientedVarietyGermHolomorphicOn d n Psi orientedDomain
  branch : (Fin n → Fin (d + 1) → ℂ) → ℂ
  branch_eq_orientedPullback :
    ∀ z, z ∈ carrier →
      branch z = Psi (sourceOrientedMinkowskiInvariant d n z)
  branch_holo : DifferentiableOn ℂ branch carrier
  branch_same_sourceOrientedInvariant :
    ∀ z w, z ∈ carrier → w ∈ carrier →
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w →
      branch z = branch w
  branch_complexLorentzInvariant :
    ∀ Λ z, z ∈ carrier →
      complexLorentzAction Λ z ∈ carrier →
        branch (complexLorentzAction Λ z) = branch z

namespace BHWJostLocalOrientedContinuationChart

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}

end BHWJostLocalOrientedContinuationChart

/-- Transition data between consecutive oriented BHW/Jost charts.  The
oriented transition patch is again required to be locally realized by the
source overlap. -/
structure BHWJostOrientedTransitionData
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (Cleft Cright :
      BHWJostLocalOrientedContinuationChart hd n τ U)
    (p q : Fin n → Fin (d + 1) → ℂ) where
  sourcePatch : Set (Fin n → Fin (d + 1) → ℂ)
  sourcePatch_open : IsOpen sourcePatch
  sourcePatch_preconnected : IsPreconnected sourcePatch
  sourcePatch_nonempty : sourcePatch.Nonempty
  source_mem : p ∈ sourcePatch
  target_mem_sourcePatch : q ∈ sourcePatch
  target_mem : q ∈ Cright.carrier
  sourcePatch_sub :
    sourcePatch ⊆ Cleft.carrier ∩ Cright.carrier
  source_branch_agree :
    Set.EqOn Cleft.branch Cright.branch sourcePatch
  orientedPatch : Set (SourceOrientedGramData d n)
  orientedPatch_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n orientedPatch
  orientedPatch_preconnected : IsPreconnected orientedPatch
  orientedPatch_nonempty : orientedPatch.Nonempty
  orientedPatch_sub :
    orientedPatch ⊆ Cleft.orientedDomain ∩ Cright.orientedDomain
  sourcePatch_oriented_mem :
    ∀ y, y ∈ sourcePatch →
      sourceOrientedMinkowskiInvariant d n y ∈ orientedPatch
  orientedPatch_source_realizes :
    ∀ G, G ∈ orientedPatch →
      ∃ y, y ∈ sourcePatch ∧ sourceOrientedMinkowskiInvariant d n y = G
  oriented_psi_agree :
    Set.EqOn Cleft.Psi Cright.Psi orientedPatch

namespace BHWJostOrientedTransitionData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {Cleft Cright : BHWJostLocalOrientedContinuationChart hd n τ U}
variable {p q : Fin n → Fin (d + 1) → ℂ}

end BHWJostOrientedTransitionData

namespace BHWLocalChartTerminalComparisonData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {Cleft Cright : BHWJostLocalOrientedContinuationChart hd n τ U}
variable {q : Fin n → Fin (d + 1) → ℂ}

end BHWLocalChartTerminalComparisonData

namespace BHWJostOrientedSourceNormalFormGeometryPatch

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {center : Fin n → Fin (d + 1) → ℂ}

end BHWJostOrientedSourceNormalFormGeometryPatch

namespace BHWJostOrientedBranchFreeTransferNeighborhood

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {center : Fin n → Fin (d + 1) → ℂ}

end BHWJostOrientedBranchFreeTransferNeighborhood

namespace BHWJostOrientedBranchFreeTransferNeighborhood

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {center : Fin n → Fin (d + 1) → ℂ}

end BHWJostOrientedBranchFreeTransferNeighborhood

/-- A finite oriented source-patch continuation chain from the fixed base
point `p0` to the endpoint `z`. -/
structure BHWJostOrientedSourcePatchContinuationChain
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (p0 z : Fin n → Fin (d + 1) → ℂ) where
  base_mem : p0 ∈ Ω0 ∩ U
  m : ℕ
  node : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ
  node_zero : node 0 = p0
  node_last : node (Fin.last m) = z
  chart : Fin (m + 1) → Set (Fin n → Fin (d + 1) → ℂ)
  node_mem : ∀ j, node j ∈ chart j
  localChart :
    Fin (m + 1) → BHWJostLocalOrientedContinuationChart hd n τ U
  branch : Fin (m + 1) → (Fin n → Fin (d + 1) → ℂ) → ℂ
  chart_open : ∀ j, IsOpen (chart j)
  chart_preconnected : ∀ j, IsPreconnected (chart j)
  chart_sub_U : ∀ j, chart j ⊆ U
  chart_eq_local : ∀ j, chart j = (localChart j).carrier
  branch_eq_local :
    ∀ j y, y ∈ chart j → branch j y = (localChart j).branch y
  branch_holo : ∀ j, DifferentiableOn ℂ (branch j) (chart j)
  start_patch : Set (Fin n → Fin (d + 1) → ℂ)
  start_patch_open : IsOpen start_patch
  start_patch_preconnected : IsPreconnected start_patch
  start_patch_nonempty : start_patch.Nonempty
  start_mem : p0 ∈ start_patch
  start_patch_sub : start_patch ⊆ Ω0 ∩ chart 0
  start_agree :
    ∀ y, y ∈ start_patch → branch 0 y = B0 y
  transition_patch :
    ∀ _ : Fin m, Set (Fin n → Fin (d + 1) → ℂ)
  transition_patch_open : ∀ j, IsOpen (transition_patch j)
  transition_patch_nonempty : ∀ j, (transition_patch j).Nonempty
  transition_patch_preconnected :
    ∀ j, IsPreconnected (transition_patch j)
  transition_patch_sub_left :
    ∀ j, transition_patch j ⊆ chart (Fin.castSucc j)
  transition_patch_sub_right :
    ∀ j, transition_patch j ⊆ chart j.succ
  consecutive_agree :
    ∀ j : Fin m, ∀ y,
      y ∈ transition_patch j →
        branch (Fin.castSucc j) y = branch j.succ y
  oriented_transition :
    ∀ j : Fin m,
      BHWJostOrientedTransitionData hd n τ U
        (localChart (Fin.castSucc j)) (localChart j.succ)
        (node (Fin.castSucc j)) (node j.succ)
  final_mem : z ∈ chart (Fin.last m)
  chart_is_lorentz_step :
    ∀ j, ∃ Ωbase : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ωbase ∧
      Ωbase ⊆ os45SourcePatchBHWJostAmbient d n τ ∧
      ∃ Λ : ComplexLorentzGroup d,
        chart j = (fun u => complexLorentzAction Λ u) '' Ωbase

namespace BHWJostOrientedSourcePatchContinuationChain

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 z : Fin n → Fin (d + 1) → ℂ}

end BHWJostOrientedSourcePatchContinuationChain

namespace BHWJostOrientedSourcePatchContinuationChain

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 z : Fin n → Fin (d + 1) → ℂ}

end BHWJostOrientedSourcePatchContinuationChain

namespace BHWJostOrientedTransferContinuationTrace

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}

end BHWJostOrientedTransferContinuationTrace

namespace BHWJostOrientedTransferTerminalPointTrace

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 y : Fin n → Fin (d + 1) → ℂ}

end BHWJostOrientedTransferTerminalPointTrace

/-- A closed oriented continuation loop at the fixed base point. -/
structure BHWJostOrientedClosedContinuationLoop
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (p0 : Fin n → Fin (d + 1) → ℂ) where
  chain :
    BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 p0
  final_base_mem : p0 ∈ chain.chart (Fin.last chain.m)
  closing_patch : Set (Fin n → Fin (d + 1) → ℂ)
  closing_patch_open : IsOpen closing_patch
  closing_patch_preconnected : IsPreconnected closing_patch
  closing_patch_nonempty : closing_patch.Nonempty
  closing_patch_mem : p0 ∈ closing_patch
  closing_patch_sub_start : closing_patch ⊆ chain.start_patch
  closing_patch_sub_final : closing_patch ⊆ chain.chart (Fin.last chain.m)
  closing_orientedPatch : Set (SourceOrientedGramData d n)
  closing_orientedPatch_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n closing_orientedPatch
  closing_orientedPatch_preconnected : IsPreconnected closing_orientedPatch
  closing_orientedPatch_nonempty : closing_orientedPatch.Nonempty
  closing_orientedPatch_sub_start :
    closing_orientedPatch ⊆ (chain.localChart 0).orientedDomain
  closing_orientedPatch_sub_final :
    closing_orientedPatch ⊆
      (chain.localChart (Fin.last chain.m)).orientedDomain
  closing_patch_oriented_mem :
    ∀ y, y ∈ closing_patch →
      sourceOrientedMinkowskiInvariant d n y ∈ closing_orientedPatch

namespace BHWJostOrientedClosedContinuationLoop

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}

end BHWJostOrientedClosedContinuationLoop

namespace BHWJostOrientedMaxRankClosedLoopSeed

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}
variable {L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}

end BHWJostOrientedMaxRankClosedLoopSeed

namespace BHWSourcePatchContinuationAtlas

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}

end BHWSourcePatchContinuationAtlas

end BHW
