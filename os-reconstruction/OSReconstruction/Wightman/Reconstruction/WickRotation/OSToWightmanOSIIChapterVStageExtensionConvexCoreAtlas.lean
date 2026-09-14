/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageExtensionAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVanishingAnchorStageExtension
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain

















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- An open convex chart cover of a continuation stage whose charts share one
complex point.

Unlike `GeneratorStageConvexAtlas`, this structure does not assert a common
positive-real neighborhood.  It records the exact geometric provenance
preserved by direct convex-core gluing through one predecessor hub. -/
structure GeneratorStagePointedConvexAtlas
    {d k : ℕ}
    (stage : OSIITimeContinuationStage d k)
    (point : OSIITimeGapSpace k)
    (ι : Type*) where
  domain : ι → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  domain_convex : ∀ i, Convex ℝ (domain i)
  domain_subset_carrier : ∀ i, domain i ⊆ stage.carrier
  carrier_subset_iUnion : stage.carrier ⊆ ⋃ i, domain i
  point_mem : ∀ i, point ∈ domain i

namespace GeneratorStagePointedConvexAtlas

/-- Recenter every pointed chart and the distinguished common point. -/
def recenter
    {d k : ℕ}
    {stage : OSIITimeContinuationStage d k}
    {point : OSIITimeGapSpace k}
    {ι : Type*}
    (atlas : GeneratorStagePointedConvexAtlas stage point ι)
    (center : Fin k → ℝ) :
    GeneratorStagePointedConvexAtlas
      (stage.recenter center)
      (point - osiiPositiveRealTimeEmbed center)
      ι where
  domain := fun i =>
    {z | z + osiiPositiveRealTimeEmbed center ∈ atlas.domain i}
  domain_open := fun i =>
    (atlas.domain_open i).preimage
      (continuous_id.add continuous_const)
  domain_convex := fun i =>
    (atlas.domain_convex i).translate_preimage_left
      (osiiPositiveRealTimeEmbed center)
  domain_subset_carrier := by
    intro i z hz
    exact atlas.domain_subset_carrier i hz
  carrier_subset_iUnion := by
    intro z hz
    obtain ⟨i, hi⟩ :=
      Set.mem_iUnion.mp (atlas.carrier_subset_iUnion hz)
    exact Set.mem_iUnion_of_mem i hi
  point_mem := by
    intro i
    change
      point - osiiPositiveRealTimeEmbed center +
          osiiPositiveRealTimeEmbed center ∈ atlas.domain i
    simpa using atlas.point_mem i

end GeneratorStagePointedConvexAtlas

namespace GeneratorStageConvexAtlas

/-- Forget a common real region after selecting one of its points, retaining
the resulting shared complex point in every chart. -/
def toPointedAtReal
    {d k : ℕ}
    {stage : OSIITimeContinuationStage d k}
    {realRegion : Set (Fin k → ℝ)}
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas stage realRegion ι)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ realRegion) :
    GeneratorStagePointedConvexAtlas
      stage (osiiPositiveRealTimeEmbed τ) ι where
  domain := atlas.domain
  domain_open := atlas.domain_open
  domain_convex := atlas.domain_convex
  domain_subset_carrier := atlas.domain_subset_carrier
  carrier_subset_iUnion := atlas.carrier_subset_iUnion
  point_mem := fun i => atlas.realEdge_mem i τ hτ

end GeneratorStageConvexAtlas

/-- Convex analytic cores, each carried by one genuine extension of a fixed
predecessor. The chart assignment records which generator branch contains
the core. A single common point in the predecessor carrier supplies every
cross-chart identity-theorem seed. -/
structure GeneratorStageExtensionConvexCoreAtlasData
    {d k : ℕ}
    (predecessor : OSIITimeContinuationStage d k) where
  chart : Type
  chartGenerator : chart → GeneratorIndex k
  carrier : chart → Set (OSIITimeGapSpace k)
  carrier_open : ∀ a, IsOpen (carrier a)
  carrier_convex : ∀ a, Convex ℝ (carrier a)
  extension : chart → GeneratorStageExtensionData predecessor
  carrier_subset_extensionDomain :
    ∀ a, carrier a ⊆ (extension a).domain (chartGenerator a)
  commonPoint : OSIITimeGapSpace k
  commonPoint_mem_predecessor : commonPoint ∈ predecessor.carrier
  commonPoint_mem_carrier : ∀ a, commonPoint ∈ carrier a

namespace GeneratorStageExtensionConvexCoreAtlasData

variable {d k : ℕ}
  {predecessor : OSIITimeContinuationStage d k}

/-- Retain only the core assigned to this chart's generator split. -/
def localDomain
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (a : P.chart)
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  {z | i = P.chartGenerator a ∧ z ∈ P.carrier a}

theorem localDomain_open
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (a : P.chart)
    (i : GeneratorIndex k) :
    IsOpen (P.localDomain a i) := by
  by_cases h : i = P.chartGenerator a
  · subst i
    simpa [localDomain] using P.carrier_open a
  · simp [localDomain, h]

theorem localDomain_subset_extensionDomain
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (a : P.chart)
    (i : GeneratorIndex k) :
    P.localDomain a i ⊆ (P.extension a).domain i := by
  rintro z ⟨rfl, hz⟩
  exact P.carrier_subset_extensionDomain a hz

/-- The selected extension restricted to its assigned convex core. -/
noncomputable def localExtension
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (a : P.chart) :
    GeneratorStageExtensionData predecessor :=
  (P.extension a).restrictDomains
    (P.localDomain a)
    (P.localDomain_open a)
    (P.localDomain_subset_extensionDomain a)

@[simp]
theorem localExtension_domain
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (a : P.chart)
    (i : GeneratorIndex k) :
    (P.localExtension a).domain i = P.localDomain a i :=
  rfl

@[simp]
theorem mem_localExtension_domain
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (a : P.chart)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    z ∈ (P.localExtension a).domain i ↔
      i = P.chartGenerator a ∧ z ∈ P.carrier a :=
  Iff.rfl

/-- The selected convex cores form a coherent atlas without any
anchor-uniform compact bound. -/
noncomputable def toGeneratorStageExtensionAtlas
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor) :
    GeneratorStageExtensionAtlas predecessor where
  chart := P.chart
  extension := P.localExtension
  compatible := by
    intro a b i j z hz
    change
      (i = P.chartGenerator a ∧ z ∈ P.carrier a) ∧
        (j = P.chartGenerator b ∧ z ∈ P.carrier b) at hz
    rcases hz with ⟨⟨rfl, hza⟩, ⟨rfl, hzb⟩⟩
    have hoverlap_connected :
        IsConnected
          ((P.localExtension a).domain (P.chartGenerator a) ∩
            (P.localExtension b).domain (P.chartGenerator b)) := by
      simpa [localDomain] using
        ((P.carrier_convex a).inter (P.carrier_convex b)).isConnected
          ⟨P.commonPoint,
            P.commonPoint_mem_carrier a,
            P.commonPoint_mem_carrier b⟩
    have hoverlap_old_nonempty :
        (((P.localExtension a).domain (P.chartGenerator a) ∩
            (P.localExtension b).domain (P.chartGenerator b)) ∩
          predecessor.carrier).Nonempty := by
      refine ⟨P.commonPoint, ?_⟩
      exact
        ⟨⟨by
            exact
              (P.mem_localExtension_domain
                a (P.chartGenerator a) P.commonPoint).2
                ⟨rfl, P.commonPoint_mem_carrier a⟩,
            by
              exact
                (P.mem_localExtension_domain
                  b (P.chartGenerator b) P.commonPoint).2
                  ⟨rfl, P.commonPoint_mem_carrier b⟩⟩,
          P.commonPoint_mem_predecessor⟩
    exact
      (P.localExtension a).eqOn_of_connectedOverlap
        (P.localExtension b)
        (P.chartGenerator a) (P.chartGenerator b)
        hoverlap_connected hoverlap_old_nonempty
        ⟨(P.mem_localExtension_domain
            a (P.chartGenerator a) z).2 ⟨rfl, hza⟩,
          (P.mem_localExtension_domain
            b (P.chartGenerator b) z).2 ⟨rfl, hzb⟩⟩

/-- Merge the coherent core atlas split by split. -/
noncomputable def stageExtensionData
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor) :
    GeneratorStageExtensionData predecessor :=
  P.toGeneratorStageExtensionAtlas.toStageExtensionData

/-- The fixed-coordinate successor obtained by gluing the selected cores. -/
noncomputable def successorStage
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor) :
    OSIITimeContinuationStage d k :=
  P.stageExtensionData.toTimeContinuationStage

/-- Every core is retained in the merged branch assigned to its generator. -/
theorem carrier_subset_stageExtensionDomain
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (a : P.chart) :
    P.carrier a ⊆
      P.stageExtensionData.domain (P.chartGenerator a) := by
  intro z hz
  apply
    P.toGeneratorStageExtensionAtlas.chartDomain_subset_domain
      a (P.chartGenerator a)
  exact
    (P.mem_localExtension_domain
      a (P.chartGenerator a) z).2 ⟨rfl, hz⟩

/-- Every selected convex core lies in the glued successor carrier. -/
theorem carrier_subset_successorCarrier
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (a : P.chart) :
    P.carrier a ⊆ P.successorStage.carrier :=
  (P.carrier_subset_stageExtensionDomain a).trans
    (P.stageExtensionData.generatorDomain_subset_stageCarrier
      (P.chartGenerator a))

/-- On every selected convex core, the final glued successor is exactly the
distribution branch of the genuine local extension which supplied that
core.  This is the quantitative handoff needed to transport chartwise bounds
through the two gluing layers. -/
theorem successorStage_eqOn_extensionCarrier
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (a : P.chart) :
    Set.EqOn
      P.successorStage.distribution
      ((P.extension a).distribution (P.chartGenerator a))
      (P.carrier a) := by
  intro z hz
  have hmerged :
      z ∈ P.stageExtensionData.domain (P.chartGenerator a) :=
    P.carrier_subset_stageExtensionDomain a hz
  have hlocal :
      z ∈ (P.localExtension a).domain (P.chartGenerator a) :=
    (P.mem_localExtension_domain
      a (P.chartGenerator a) z).2 ⟨rfl, hz⟩
  calc
    P.successorStage.distribution z =
        P.stageExtensionData.distribution (P.chartGenerator a) z :=
      P.stageExtensionData.newStage_eqOn_generatorDomain
        (P.chartGenerator a) hmerged
    _ = (P.localExtension a).distribution
          (P.chartGenerator a) z :=
      P.toGeneratorStageExtensionAtlas.splitDistribution_eqOn
        a (P.chartGenerator a) hlocal
    _ = (P.extension a).distribution
          (P.chartGenerator a) z := rfl

/-- The selected successor retains the complete predecessor carrier. -/
theorem oldCarrier_subset_successorCarrier
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor) :
    predecessor.carrier ⊆ P.successorStage.carrier :=
  P.stageExtensionData.oldCarrier_subset_newCarrier

/-- Any target covered by the selected cores lies in the glued successor. -/
theorem subset_successorCarrier_of_subset_iUnion_carrier
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (U : Set (OSIITimeGapSpace k))
    (hU : U ⊆ ⋃ a, P.carrier a) :
    U ⊆ P.successorStage.carrier := by
  intro z hz
  obtain ⟨a, hza⟩ := Set.mem_iUnion.mp (hU hz)
  exact P.carrier_subset_successorCarrier a hza

/-- Exact handoff for one raw logarithmic generator fiber. Coverage by the
selected convex cores inserts the complete fiber into the successor. -/
theorem argumentGeneratorCarrier_subset_successorCarrier
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (i : GeneratorIndex k)
    (left : Fin i.n → ℝ)
    (θ : ℝ)
    (right : Fin i.m → ℝ)
    (hcover :
      osiiTimeArgumentCarrier
          ({osiiArgumentGeneratorPoint i left θ right} :
            Set (Fin k → ℝ)) ⊆
        ⋃ a, P.carrier a) :
    osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left θ right} :
          Set (Fin k → ℝ)) ⊆
      P.successorStage.carrier :=
  P.subset_successorCarrier_of_subset_iUnion_carrier _ hcover

/-- The glued stage contains and agrees with the complete predecessor. -/
theorem successorStage_extends_predecessor
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor) :
    Set.EqOn P.successorStage.distribution
      predecessor.distribution predecessor.carrier :=
  P.stageExtensionData.newStage_extends_old

/-- A pointed convex predecessor atlas together with the selected convex
cores gives a pointed convex atlas of the direct successor through the same
common point. -/
noncomputable def successorPointedConvexAtlas
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    {ι : Type*}
    (atlas :
      GeneratorStagePointedConvexAtlas
        predecessor P.commonPoint ι) :
    GeneratorStagePointedConvexAtlas
      P.successorStage P.commonPoint (Sum ι P.chart) where
  domain
    | Sum.inl i => atlas.domain i
    | Sum.inr a => P.carrier a
  domain_open
    | Sum.inl i => atlas.domain_open i
    | Sum.inr a => P.carrier_open a
  domain_convex
    | Sum.inl i => atlas.domain_convex i
    | Sum.inr a => P.carrier_convex a
  domain_subset_carrier := by
    intro a z hz
    cases a with
    | inl i =>
        exact
          P.oldCarrier_subset_successorCarrier
            (atlas.domain_subset_carrier i hz)
    | inr a =>
        exact P.carrier_subset_successorCarrier a hz
  carrier_subset_iUnion := by
    intro z hz
    change z ∈ P.stageExtensionData.stageCarrier at hz
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
    cases a with
    | none =>
        obtain ⟨i, hi⟩ :=
          Set.mem_iUnion.mp (atlas.carrier_subset_iUnion ha)
        exact Set.mem_iUnion_of_mem (Sum.inl i) hi
    | some i =>
        change
          z ∈
            P.toGeneratorStageExtensionAtlas.splitDomain i at ha
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp ha
        exact
          Set.mem_iUnion_of_mem (Sum.inr a)
            ((P.mem_localExtension_domain a i z).mp ha).2
  point_mem := by
    intro a
    cases a with
    | inl i => exact atlas.point_mem i
    | inr a => exact P.commonPoint_mem_carrier a

end GeneratorStageExtensionConvexCoreAtlasData

end OSIIChapterV
end OSReconstruction
