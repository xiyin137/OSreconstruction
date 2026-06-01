import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Separation.Regular
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Normed.Module.Convex

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

/-- A path inside an open set has an open connected neighborhood, still inside
that open set, containing both endpoints. -/
theorem exists_open_connected_neighborhood_of_joinedIn_subset_open
    {E : Type*} [TopologicalSpace E] [LocallyCompactSpace E] [RegularSpace E]
    [LocallyConnectedSpace E]
    {Ω : Set E} {a b : E}
    (hΩ_open : IsOpen Ω) (hjoin : JoinedIn Ω a b) :
    ∃ U : Set E, IsOpen U ∧ IsConnected U ∧ a ∈ U ∧ b ∈ U ∧ U ⊆ Ω := by
  let γ := hjoin.somePath
  let K : Set E := Set.range γ
  have hK_compact : IsCompact K := by
    simpa [K] using (isCompact_univ.image γ.continuous_toFun)
  have hK_connected : IsConnected K := by
    simpa [K] using (isConnected_univ.image γ γ.continuous_toFun.continuousOn)
  have hKΩ : K ⊆ Ω := by
    rintro z ⟨t, rfl⟩
    exact hjoin.somePath_mem t
  rcases SCV.exists_open_connected_neighborhood_of_compact_connected_subset_open
      hK_compact hK_connected hΩ_open hKΩ with ⟨U, hU_open, hU_connected, hKU, hUΩ⟩
  refine ⟨U, hU_open, hU_connected, ?_, ?_, hUΩ⟩
  · exact hKU ⟨0, hjoin.somePath.source⟩
  · exact hKU ⟨1, hjoin.somePath.target⟩

/-- If membership in a set can be propagated between any two points in a
small open neighborhood of each point, then a nonempty reachable set in a
preconnected space is all of the space.

This is the neutral topology core used by the OS45 one-branch chain assembly:
the hard OS/BHW content is the local propagation hypothesis. -/
theorem reachable_eq_univ_of_local_symmetric_extension
    {E : Type*} [TopologicalSpace E] [PreconnectedSpace E]
    {Reach : Set E}
    (hReach_nonempty : Reach.Nonempty)
    (hlocal :
      ∀ x : E, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        ∀ ⦃y z : E⦄, y ∈ U → z ∈ U → y ∈ Reach → z ∈ Reach) :
    Reach = Set.univ := by
  have hReach_open : IsOpen Reach := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rcases hlocal x with ⟨U, hU_open, hxU, hprop⟩
    exact Filter.mem_of_superset (hU_open.mem_nhds hxU)
      (fun y hyU => hprop hxU hyU hx)
  have hReach_compl_open : IsOpen Reachᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rcases hlocal x with ⟨U, hU_open, hxU, hprop⟩
    exact Filter.mem_of_superset (hU_open.mem_nhds hxU)
      (fun y hyU hyReach => hx (hprop hyU hxU hyReach))
  have hReach_closed : IsClosed Reach := by
    simpa using (isClosed_compl_iff.mpr hReach_compl_open)
  exact IsClopen.eq_univ ⟨hReach_closed, hReach_open⟩ hReach_nonempty

/-- A connected core with connected attached sets has connected union, provided
the core is covered by the union and every attached set meets the core. -/
theorem isConnected_iUnion_of_connected_core
    {E ι : Type*} [TopologicalSpace E]
    {K : Set E} {N : ι → Set E}
    (hK : IsConnected K)
    (hN : ∀ i, IsConnected (N i))
    (hattach : ∀ i, (K ∩ N i).Nonempty)
    (hK_subset : K ⊆ ⋃ i, N i) :
    IsConnected (⋃ i, N i) := by
  classical
  let S : Option ι → Set E := fun o =>
    match o with
    | none => K
    | some i => N i
  let R : Option ι → Option ι → Prop := fun a b => (S a ∩ S b).Nonempty
  have hS_conn : ∀ o : Option ι, IsConnected (S o) := by
    intro o
    cases o with
    | none => simpa [S] using hK
    | some i => simpa [S] using hN i
  have h_none_some : ∀ j : ι, R none (some j) := by
    intro j
    simpa [R, S] using hattach j
  have h_some_none : ∀ i : ι, R (some i) none := by
    intro i
    simpa [R, S, Set.inter_comm] using hattach i
  have hreach : ∀ o p : Option ι, Relation.ReflTransGen R o p := by
    intro o p
    cases o with
    | none =>
        cases p with
        | none => exact Relation.ReflTransGen.refl
        | some j => exact Relation.ReflTransGen.single (h_none_some j)
    | some i =>
        cases p with
        | none => exact Relation.ReflTransGen.single (h_some_none i)
        | some j =>
            have step1 : Relation.ReflTransGen R (some i) none :=
              Relation.ReflTransGen.single (h_some_none i)
            have step2 : Relation.ReflTransGen R none (some j) :=
              Relation.ReflTransGen.single (h_none_some j)
            exact step1.trans step2
  have hUnion_conn : IsConnected (⋃ o : Option ι, S o) := by
    exact IsConnected.iUnion_of_reflTransGen hS_conn hreach
  have hEq : (⋃ o : Option ι, S o) = (⋃ i, N i) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨o, hxo⟩
      cases o with
      | none => exact hK_subset hxo
      | some i => exact Set.mem_iUnion.mpr ⟨i, hxo⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.mpr ⟨some i, hxi⟩
  simpa [hEq] using hUnion_conn

/-- A nonempty intersection of two metric balls in a real normed vector space
is connected. -/
theorem isConnected_inter_metric_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} {r s : ℝ}
    (hne : Set.Nonempty (Metric.ball x r ∩ Metric.ball y s)) :
    IsConnected (Metric.ball x r ∩ Metric.ball y s) :=
  ⟨hne, (convex_ball x r).inter (convex_ball y s) |>.isPreconnected⟩

/-- Two open neighborhoods of the same point contain a metric ball around that
point inside their intersection. -/
theorem exists_metric_ball_subset_of_mem_open
    {E : Type*} [PseudoMetricSpace E]
    {U : Set E} {z : E}
    (hU : IsOpen U) (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U := by
  exact Metric.mem_nhds_iff.mp (hU.mem_nhds hz)

/-- A holomorphic chart on an open carrier can be restricted to an
endpoint-centered metric ball inside that carrier. -/
theorem exists_metric_ball_differentiableOn_subset_of_mem_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set E} {z : E} {f : E → F}
    (hU : IsOpen U) (hz : z ∈ U) (hf : DifferentiableOn ℂ f U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      DifferentiableOn ℂ f (Metric.ball z r) := by
  rcases SCV.exists_metric_ball_subset_of_mem_open hU hz with ⟨r, hr_pos, hball_sub⟩
  exact ⟨r, hr_pos, hball_sub, hf.mono hball_sub⟩

/-- Two open neighborhoods of the same point contain a metric ball around that
point inside their intersection. -/
theorem exists_metric_ball_subset_inter_of_mem_open
    {E : Type*} [PseudoMetricSpace E]
    {U V : Set E} {z : E}
    (hU : IsOpen U) (hzU : z ∈ U)
    (hV : IsOpen V) (hzV : z ∈ V) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∩ V := by
  have hUV : U ∩ V ∈ nhds z :=
    Filter.inter_mem (hU.mem_nhds hzU) (hV.mem_nhds hzV)
  rcases Metric.mem_nhds_iff.mp hUV with ⟨r, hr_pos, hball⟩
  exact ⟨r, hr_pos, hball⟩

/-- Local holomorphic representatives glue to a holomorphic function on the
covered set.  The representatives are proof-local data; no atlas structure is
needed. -/
theorem differentiableOn_of_locally_eq_differentiableOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set E} {f : E → F}
    (hlocal :
      ∀ z, z ∈ U →
        ∃ V : Set E, IsOpen V ∧ z ∈ V ∧
          ∃ g : E → F,
            DifferentiableOn ℂ g V ∧ Set.EqOn f g (U ∩ V)) :
    DifferentiableOn ℂ f U := by
  intro z hzU
  rcases hlocal z hzU with ⟨V, hV_open, hzV, g, hg, hfg⟩
  have hgd : DifferentiableAt ℂ g z :=
    (hg z hzV).differentiableAt (hV_open.mem_nhds hzV)
  have hlocal_eq : f =ᶠ[𝓝[U] z] g := by
    filter_upwards
      [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hV_open.mem_nhds hzV)]
      with y hyU hyV
    exact hfg ⟨hyU, hyV⟩
  exact
    hgd.differentiableWithinAt.congr_of_eventuallyEq
      hlocal_eq (hfg ⟨hzU, hzV⟩)

/-- Glue a family of local representatives by choosing any representative
whose carrier contains the point, and using `0` off the union.  Pairwise
agreement on overlaps makes the choice immaterial on the covered region. -/
noncomputable def glued_iUnion
    {E F ι : Type*} [Zero F]
    (N : ι → Set E) (D : ι → E → F) : E → F :=
  by
    classical
    exact fun z =>
      if h : ∃ i, z ∈ N i then
        D (Classical.choose h) z
      else
        0

/-- On each carrier, the indexed glued function agrees with that carrier's
representative, provided the representatives agree pairwise on overlaps. -/
theorem glued_iUnion_eqOn
    {E F ι : Type*} [Zero F]
    {N : ι → Set E} {D : ι → E → F}
    (hEq : ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j))
    (i : ι) :
    Set.EqOn (SCV.glued_iUnion N D) (D i) (N i) := by
  classical
  intro z hz
  have hmem : ∃ j, z ∈ N j := ⟨i, hz⟩
  have hchosen : z ∈ N (Classical.choose hmem) :=
    Classical.choose_spec hmem
  rw [SCV.glued_iUnion]
  simp [hmem, hEq (Classical.choose hmem) i ⟨hchosen, hz⟩]

/-- Pairwise-equal holomorphic representatives glue to a holomorphic function
on any set covered by their carriers. -/
theorem differentiableOn_glued_iUnion
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set E} {N : ι → Set E} {D : ι → E → F}
    (hcover : U ⊆ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hD : ∀ i, DifferentiableOn ℂ (D i) (N i))
    (hEq : ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) :
    DifferentiableOn ℂ (SCV.glued_iUnion N D) U := by
  classical
  refine
    SCV.differentiableOn_of_locally_eq_differentiableOn
      (U := U) (f := SCV.glued_iUnion N D) ?_
  intro z hzU
  rcases Set.mem_iUnion.mp (hcover hzU) with ⟨i, hzi⟩
  refine ⟨N i, hN_open i, hzi, D i, hD i, ?_⟩
  intro y hy
  exact SCV.glued_iUnion_eqOn (N := N) (D := D) hEq i hy.2

end SCV
