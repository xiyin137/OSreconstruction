import Mathlib.Topology.UnitInterval
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented

/-!
# Connected-component support for the oriented source variety

This file contains the purely topological part of the oriented source-variety
connected-component construction.  The local connected relatively open basis
is kept as an explicit parameter, so the remaining max-rank/rank-deficient
geometry is not hidden inside a global theorem.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- If the oriented source variety has local connected relatively open
neighborhoods, then connected components of relatively open oriented domains
are relatively open in the oriented source variety. -/
theorem sourceOrientedGramVariety_connectedComponentIn_relOpen_of_local_connectedRelOpen_basis
    (localBasis :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          ∃ V : Set (SourceOrientedGramData d n),
            G0 ∈ V ∧
            IsRelOpenInSourceOrientedGramVariety d n V ∧
            IsConnected V ∧
            V ⊆ N0 ∩ sourceOrientedGramVariety d n)
    {D : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    {G0 : SourceOrientedGramData d n}
    (_hG0D : G0 ∈ D) :
    IsRelOpenInSourceOrientedGramVariety d n (connectedComponentIn D G0) := by
  classical
  rcases hD_rel with ⟨D0, hD0_open, hD_eq⟩
  let C : Set (SourceOrientedGramData d n) := connectedComponentIn D G0
  let Index : Type := {G : SourceOrientedGramData d n // G ∈ C}
  have hloc : ∀ G : Index,
      ∃ V : Set (SourceOrientedGramData d n),
        G.1 ∈ V ∧
        IsRelOpenInSourceOrientedGramVariety d n V ∧
        IsConnected V ∧
        V ⊆ D ∧
        V ⊆ C := by
    intro G
    have hGD : G.1 ∈ D := connectedComponentIn_subset D G0 G.2
    have hGD0 : G.1 ∈ D0 := by
      rw [hD_eq] at hGD
      exact hGD.1
    have hGvar : G.1 ∈ sourceOrientedGramVariety d n := by
      rw [hD_eq] at hGD
      exact hGD.2
    rcases localBasis hGvar hD0_open hGD0 with
      ⟨V, hGV, hV_rel, hV_conn, hV_sub⟩
    have hV_D : V ⊆ D := by
      intro H hH
      rw [hD_eq]
      exact hV_sub hH
    have hV_C : V ⊆ C := by
      have hV_compG : V ⊆ connectedComponentIn D G.1 :=
        hV_conn.isPreconnected.subset_connectedComponentIn hGV hV_D
      have hCeq : C = connectedComponentIn D G.1 := connectedComponentIn_eq G.2
      intro H hH
      rw [hCeq]
      exact hV_compG hH
    exact ⟨V, hGV, hV_rel, hV_conn, hV_D, hV_C⟩
  choose V hV_mem hV_rel _hV_conn _hV_D hV_C using hloc
  have hC_eq : C = ⋃ G : Index, V G := by
    ext H
    constructor
    · intro hHC
      exact Set.mem_iUnion.2 ⟨⟨H, hHC⟩, hV_mem ⟨H, hHC⟩⟩
    · intro hHUnion
      rcases Set.mem_iUnion.1 hHUnion with ⟨G, hHG⟩
      exact hV_C G hHG
  rw [show connectedComponentIn D G0 = C by rfl, hC_eq]
  exact IsRelOpenInSourceOrientedGramVariety.iUnion hV_rel

/-- A connected relatively open oriented-source tube follows a continuous
path inside a relatively open oriented source-variety domain.  The only
geometric input is the local connected relatively open basis. -/
theorem sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath_of_local_connectedRelOpen_basis
    (localBasis :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          ∃ V : Set (SourceOrientedGramData d n),
            G0 ∈ V ∧
            IsRelOpenInSourceOrientedGramVariety d n V ∧
            IsConnected V ∧
            V ⊆ N0 ∩ sourceOrientedGramVariety d n)
    {D : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    {γ : unitInterval → SourceOrientedGramData d n}
    (hγ_cont : Continuous γ)
    (hγD : ∀ t, γ t ∈ D)
    {W0 : Set (SourceOrientedGramData d n)}
    (_hW0_rel : IsRelOpenInSourceOrientedGramVariety d n W0)
    (hW0_conn : IsConnected W0)
    (_hW0_nonempty : W0.Nonempty)
    (hW0D : W0 ⊆ D)
    (hstart : γ (0 : unitInterval) ∈ W0) :
    ∃ Wtube : Set (SourceOrientedGramData d n),
      IsRelOpenInSourceOrientedGramVariety d n Wtube ∧
      IsConnected Wtube ∧
      W0 ⊆ Wtube ∧
      Wtube ⊆ D ∧
      (∀ t, γ t ∈ Wtube) := by
  classical
  let Gstart : SourceOrientedGramData d n := γ (0 : unitInterval)
  let Wtube : Set (SourceOrientedGramData d n) := connectedComponentIn D Gstart
  have hGstartD : Gstart ∈ D := hγD 0
  refine ⟨Wtube, ?_, ?_, ?_, ?_, ?_⟩
  · exact sourceOrientedGramVariety_connectedComponentIn_relOpen_of_local_connectedRelOpen_basis
      (d := d) (n := n) localBasis hD_rel hGstartD
  · simpa [Wtube, Gstart] using
      (isConnected_connectedComponentIn_iff.mpr hGstartD)
  · simpa [Wtube, Gstart] using
      hW0_conn.isPreconnected.subset_connectedComponentIn hstart hW0D
  · intro G hG
    simpa [Wtube, Gstart] using connectedComponentIn_subset D Gstart hG
  · intro t
    have hγ_pre : IsPreconnected (Set.range γ) := isPreconnected_range hγ_cont
    have hγ_base : Gstart ∈ Set.range γ := ⟨0, rfl⟩
    have hγ_range_D : Set.range γ ⊆ D := by
      intro G hG
      rcases hG with ⟨s, rfl⟩
      exact hγD s
    have hγ_sub : Set.range γ ⊆ connectedComponentIn D Gstart :=
      hγ_pre.subset_connectedComponentIn hγ_base hγ_range_D
    simpa [Wtube, Gstart] using hγ_sub ⟨t, rfl⟩

end BHW
