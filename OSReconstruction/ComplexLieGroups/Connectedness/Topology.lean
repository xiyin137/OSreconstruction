import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Algebra.Group.Quotient

open Topology Filter

namespace BHW

/-- Quotient map + connected fibers + preconnected codomain implies preconnected domain. -/
theorem IsQuotientMap.preconnectedSpace_of_connectedFibers
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hf : Topology.IsQuotientMap f)
    (hFib : ∀ y : β, IsConnected (f ⁻¹' ({y} : Set β)))
    [Nonempty α] [PreconnectedSpace β] :
    PreconnectedSpace α := by
  classical
  let a : α := Classical.choice inferInstance
  have hpre := hf.preimage_connectedComponent hFib a
  have hβ : connectedComponent (f a) = (Set.univ : Set β) :=
    PreconnectedSpace.connectedComponent_eq_univ (f a)
  have hα : connectedComponent a = (Set.univ : Set α) := by
    calc
      connectedComponent a = f ⁻¹' connectedComponent (f a) := hpre.symm
      _ = f ⁻¹' (Set.univ : Set β) := by rw [hβ]
      _ = Set.univ := by simp
  have hconn : ConnectedSpace α :=
    connectedSpace_iff_connectedComponent.mpr ⟨a, hα⟩
  exact hconn.toPreconnectedSpace

/-- If every point in `S` is joined to a basepoint `x0` inside `S`, then `S` is preconnected. -/
theorem isPreconnected_of_joinedIn_base
    {X : Type*} [TopologicalSpace X]
    {S : Set X} {x0 : X}
    (hx0 : x0 ∈ S)
    (hjoined : ∀ y ∈ S, JoinedIn S x0 y) :
    IsPreconnected S := by
  let x0S : S := ⟨x0, hx0⟩
  have h_joined_subtype : ∀ y : S, Joined x0S y := by
    intro y
    exact (joinedIn_iff_joined (x_in := hx0) (y_in := y.2)).mp (hjoined y y.2)
  haveI : PathConnectedSpace S := by
    refine PathConnectedSpace.mk ?_ ?_
    · exact ⟨x0S⟩
    · intro x y
      exact (h_joined_subtype x).symm.trans (h_joined_subtype y)
  exact (isPreconnected_iff_preconnectedSpace).2 (inferInstance : PreconnectedSpace S)

/-- A local eventual path-joining hypothesis makes each path component open. -/
theorem isOpen_pathComponentIn_of_eventually_joined
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (hlocal : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, ∃ γ : Path x y, ∀ t, γ t ∈ S) :
    ∀ x ∈ S, IsOpen (pathComponentIn S x) := by
  intro x hxS
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyS : y ∈ S := hy.target_mem
  refine Filter.mem_of_superset (hlocal y hyS) ?_
  intro z hz
  rcases hz with ⟨γ, hγS⟩
  exact hy.trans ⟨γ, hγS⟩

end BHW
