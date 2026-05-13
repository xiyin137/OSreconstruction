import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Separation.Regular

/-!
# Connected Open Neighborhoods

Small neutral topology helpers used by local edge-of-the-wedge charts.
-/

noncomputable section

open Topology

namespace SCV

/-- A compact connected set inside an open set has an open connected
neighborhood still inside that open set, in locally compact regular locally
connected spaces.

The proof first chooses an open shrink with closure inside the target open set,
then takes the connected component of that shrink containing a point of the
compact connected set.  Local connectedness makes that component open. -/
theorem exists_open_connected_neighborhood_of_compact_connected_subset_open
    {E : Type*} [TopologicalSpace E] [LocallyCompactSpace E] [RegularSpace E]
    [LocallyConnectedSpace E]
    {K Ω : Set E}
    (hK_compact : IsCompact K)
    (hK_connected : IsConnected K)
    (hΩ_open : IsOpen Ω)
    (hKΩ : K ⊆ Ω) :
    ∃ U : Set E, IsOpen U ∧ IsConnected U ∧ K ⊆ U ∧ U ⊆ Ω := by
  rcases hK_connected.nonempty with ⟨x0, hx0K⟩
  obtain ⟨V, hV_open, hKV, hclVΩ, _hclV_compact⟩ :=
    exists_open_between_and_isCompact_closure hK_compact hΩ_open hKΩ
  let U : Set E := connectedComponentIn V x0
  have hx0V : x0 ∈ V := hKV hx0K
  have hU_open : IsOpen U :=
    (locallyConnectedSpace_iff_connectedComponentIn_open.mp inferInstance)
      V hV_open x0 hx0V
  have hU_connected : IsConnected U := by
    exact
      ⟨⟨x0, mem_connectedComponentIn hx0V⟩,
        isPreconnected_connectedComponentIn⟩
  have hK_U : K ⊆ U :=
    hK_connected.isPreconnected.subset_connectedComponentIn hx0K hKV
  have hVΩ : V ⊆ Ω := by
    intro y hy
    exact hclVΩ (subset_closure hy)
  have hUΩ : U ⊆ Ω :=
    (connectedComponentIn_subset V x0).trans hVΩ
  exact ⟨U, hU_open, hU_connected, hK_U, hUΩ⟩

end SCV

