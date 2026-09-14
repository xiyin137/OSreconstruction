/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialConvexAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialStageExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageExtensionConvexCoreAtlas

















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace GeneratorSpatialApproximationFamily

variable {d k : ℕ} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}

/-- A radial branch restricted to a convex core agrees with a predecessor
carrying only pointed convex-atlas provenance.

The selected seed chart contains the radial origin and the complete local
real edge.  The distinguished atlas point lies in the core and in every
predecessor chart, so it propagates the seed equality across the atlas cover.
-/
theorem agreesOnCore_of_radialPointedAtlas
    (B : GeneratorSpatialApproximationFamily d k)
    (E : B.CommonPositiveRealEdgeData)
    (F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (domain_eq :
      ∀ i, B.domain i = F.radialChronologicalDomain i)
    (A : OSIITimeContinuationStage d k)
    (hold : A.HasPositiveRealEdge E.orbit E.realRegion)
    {hub : OSIITimeGapSpace k}
    {ι : Type*}
    (atlas : GeneratorStagePointedConvexAtlas A hub ι)
    (seedChart : ι)
    (zero_mem_seed :
      (0 : OSIITimeGapSpace k) ∈ atlas.domain seedChart)
    (edge_mem_seed :
      ∀ τ ∈ E.realRegion,
        osiiPositiveRealTimeEmbed τ ∈ atlas.domain seedChart)
    (i : GeneratorIndex k)
    (core : Set (OSIITimeGapSpace k))
    (core_open : IsOpen core)
    (core_convex : Convex ℝ core)
    (core_subset : core ⊆ B.domain i)
    (hub_mem_core : hub ∈ core) :
    Set.EqOn (B.distribution i) A.distribution
      (core ∩ A.carrier) := by
  let seedDomain : Set (OSIITimeGapSpace k) :=
    B.domain i ∩ atlas.domain seedChart
  have hseedDomain_open : IsOpen seedDomain :=
    (B.domain_open i).inter (atlas.domain_open seedChart)
  have hseedDomain_connected : IsConnected seedDomain := by
    obtain ⟨τ, hτ⟩ := E.realRegion_nonempty
    have hcF :
        osiiPositiveRealTimeEmbed τ ∈
          F.radialChronologicalDomain i := by
      rw [← domain_eq i]
      exact (B.distribution_commonPositiveRealEdge E i τ hτ).1
    have hcAtlas :
        osiiPositiveRealTimeEmbed τ ∈
          atlas.domain seedChart :=
      edge_mem_seed τ hτ
    have hpath :
        IsPathConnected
          (F.radialChronologicalDomain i ∩
            atlas.domain seedChart) := by
      apply
        F.radialChronologicalDomain_inter_convex_isPathConnected
          i (atlas.domain_convex seedChart) hcF hcAtlas
      intro t ht0 ht1
      exact
        ((atlas.domain_convex seedChart).starConvex
          zero_mem_seed).smul_mem hcAtlas ht0.le ht1
    simpa [seedDomain, domain_eq i] using hpath.isConnected
  have hseed_eq :
      Set.EqOn (B.distribution i) A.distribution seedDomain := by
    intro z hz
    apply ContinuousLinearMap.ext
    intro χ
    let G : OSIITimeGapSpace k → ℂ :=
      fun w => B.distribution i w χ - A.distribution w χ
    have hG : DifferentiableOn ℂ G seedDomain :=
      ((B.distribution_weaklyHolomorphic i χ).mono
        Set.inter_subset_left).sub
        ((A.weaklyHolomorphic χ).mono
          (Set.inter_subset_right.trans
            (atlas.domain_subset_carrier seedChart)))
    have hreal_sub :
        ∀ τ ∈ E.realRegion,
          SCV.realToComplex τ ∈ seedDomain := by
      intro τ hτ
      simpa [seedDomain, SCV.realToComplex,
        osiiPositiveRealTimeEmbed] using
        (show osiiPositiveRealTimeEmbed τ ∈
            B.domain i ∩ atlas.domain seedChart from
          ⟨(B.distribution_commonPositiveRealEdge E i τ hτ).1,
            edge_mem_seed τ hτ⟩)
    have hG_zero :
        ∀ τ ∈ E.realRegion,
          G (SCV.realToComplex τ) = 0 := by
      intro τ hτ
      have hnew :=
        (B.distribution_commonPositiveRealEdge E i τ hτ).2
      have hold_eq := (hold τ hτ).2
      simp only [G]
      rw [show SCV.realToComplex τ =
          osiiPositiveRealTimeEmbed τ by rfl,
        hnew, hold_eq, sub_self]
    exact
      sub_eq_zero.mp
        (SCV.identity_theorem_totally_real
          hseedDomain_open hseedDomain_connected hG
          E.realRegion_open E.realRegion_nonempty
          hreal_sub hG_zero z hz)
  intro z hz
  obtain ⟨chart, hchart⟩ :=
    Set.mem_iUnion.mp (atlas.carrier_subset_iUnion hz.2)
  let chartDomain : Set (OSIITimeGapSpace k) :=
    core ∩ atlas.domain chart
  have hchartDomain_open : IsOpen chartDomain :=
    core_open.inter (atlas.domain_open chart)
  have hchartDomain_connected : IsConnected chartDomain := by
    apply
      (core_convex.inter
        (atlas.domain_convex chart)).isConnected
    exact
      ⟨hub, hub_mem_core, atlas.point_mem chart⟩
  let overlap : Set (OSIITimeGapSpace k) :=
    chartDomain ∩ atlas.domain seedChart
  have hoverlap_open : IsOpen overlap :=
    hchartDomain_open.inter (atlas.domain_open seedChart)
  have hoverlap_nonempty : overlap.Nonempty :=
    ⟨hub,
      ⟨hub_mem_core, atlas.point_mem chart⟩,
      atlas.point_mem seedChart⟩
  have hoverlap_subset : overlap ⊆ chartDomain :=
    Set.inter_subset_left
  have hoverlap_eq :
      Set.EqOn (B.distribution i) A.distribution overlap := by
    intro w hw
    exact hseed_eq ⟨core_subset hw.1.1, hw.2⟩
  exact
    (weaklyHolomorphic_eqOn_of_eqOn_open
      hchartDomain_open hchartDomain_connected
      hoverlap_open hoverlap_nonempty hoverlap_subset
      (fun χ =>
        (B.distribution_weaklyHolomorphic i χ).mono
          (Set.inter_subset_left.trans core_subset))
      (fun χ =>
        (A.weaklyHolomorphic χ).mono
          (Set.inter_subset_right.trans
            (atlas.domain_subset_carrier chart)))
      hoverlap_eq) ⟨hz.1, hchart⟩

/-- Restrict one radial split to a convex hub-containing core and package it
as a genuine predecessor extension.  All other generator domains are empty.
-/
noncomputable def toSingleGeneratorStageExtensionDataOfRadialPointedAtlas
    (B : GeneratorSpatialApproximationFamily d k)
    (E : B.CommonPositiveRealEdgeData)
    (F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (domain_eq :
      ∀ i, B.domain i = F.radialChronologicalDomain i)
    (A : OSIITimeContinuationStage d k)
    (hold : A.HasPositiveRealEdge E.orbit E.realRegion)
    {hub : OSIITimeGapSpace k}
    {ι : Type*}
    (atlas : GeneratorStagePointedConvexAtlas A hub ι)
    (seedChart : ι)
    (zero_mem_seed :
      (0 : OSIITimeGapSpace k) ∈ atlas.domain seedChart)
    (edge_mem_seed :
      ∀ τ ∈ E.realRegion,
        osiiPositiveRealTimeEmbed τ ∈ atlas.domain seedChart)
    (i : GeneratorIndex k)
    (core : Set (OSIITimeGapSpace k))
    (core_open : IsOpen core)
    (core_convex : Convex ℝ core)
    (core_subset : core ⊆ B.domain i)
    (hub_mem_core : hub ∈ core) :
    GeneratorStageExtensionData A where
  domain := singleGeneratorChartDomain i core
  domain_open := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using core_open
    · rw [singleGeneratorChartDomain_eq_empty i core j hj]
      exact isOpen_empty
  distribution := fun _ => B.distribution i
  weaklyHolomorphic := by
    intro j χ
    by_cases hj : j = i
    · subst j
      simpa using
        (B.distribution_weaklyHolomorphic i χ).mono core_subset
    · rw [singleGeneratorChartDomain_eq_empty i core j hj]
      exact differentiableOn_empty
  compatible := by
    intro _j _l _z _hz
    rfl
  agreesOnOld := by
    intro j z hz
    by_cases hj : j = i
    · subst j
      apply
        B.agreesOnCore_of_radialPointedAtlas
          E F domain_eq A hold atlas seedChart
          zero_mem_seed edge_mem_seed i
          core core_open core_convex core_subset hub_mem_core
      simpa using hz
    · have hzempty :
          z ∈ (∅ : Set (OSIITimeGapSpace k)) := by
        simpa [singleGeneratorChartDomain_eq_empty
          i core j hj] using hz.1
      exact hzempty.elim

end GeneratorSpatialApproximationFamily
end OSIIChapterV
end OSReconstruction
