/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Separation.Regular
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Normed.Module.Convex







noncomputable section

open Topology

namespace SCV

/-- Two open neighborhoods of the same point contain a metric ball around that
point inside their intersection. -/
theorem exists_metric_ball_subset_of_mem_open
    {E : Type*} [PseudoMetricSpace E]
    {U : Set E} {z : E}
    (hU : IsOpen U) (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U := by
  exact Metric.mem_nhds_iff.mp (hU.mem_nhds hz)

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
