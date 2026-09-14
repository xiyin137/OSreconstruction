/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedStageMatchedRepresentedGenerator
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageExtension











noncomputable section

open Complex Filter Set Topology
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV

/-- A fixed-coordinate continuation stage equipped with the two invariants
needed by the next rooted Chapter V successor:

* every compact strict-positive real carrier has a canonical reduced edge;
* one nonempty open positive-real patch lies in every retained convex chart.
-/
structure CanonicalGeneratorConvexAtlasStageData
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ) where
  stage : OSIITimeContinuationStage d k
  chart : Type
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  realRegion_nonempty : realRegion.Nonempty
  realRegion_subset_strictPositive :
    realRegion ⊆ section43TimeStrictPositiveRegion k
  atlas : GeneratorStageConvexAtlas stage realRegion chart
  canonicalEdges : HasCanonicalReducedCompactStageEdges OS stage

namespace CanonicalGeneratorConvexAtlasStageData

variable {d k : ℕ} [NeZero d]
  {OS : OsterwalderSchraderAxioms d}

/-- A convex stage carrying one canonical compact edge is the base case of the
iterated atlas invariant. -/
noncomputable def ofConvexCompactEdge
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k → ℝ)}
    (Hstage : HasCanonicalReducedCompactStageEdges OS stage)
    (D : CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (compactCarrier_nonempty : compactCarrier.Nonempty)
    (carrier_convex : Convex ℝ stage.carrier) :
    CanonicalGeneratorConvexAtlasStageData OS k where
  stage := stage
  chart := PUnit
  realRegion := D.realRegion
  realRegion_open := D.realRegion_open
  realRegion_nonempty := by
    obtain ⟨τ, hτ⟩ := compactCarrier_nonempty
    exact ⟨τ, D.compactCarrier_subset hτ⟩
  realRegion_subset_strictPositive :=
    D.realRegion_subset_strictPositive
  atlas :=
    GeneratorStageConvexAtlas.ofConvex
      D.edge.stageEdge carrier_convex
  canonicalEdges := Hstage

end CanonicalGeneratorConvexAtlasStageData

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {H : RootedA0BlockHolomorphicTranslationData OS A R}
  {lgc : OSLinearGrowthCondition d OS}
  {S : CanonicalGeneratorConvexAtlasStageData OS k}

/-- The proof-relevant data for one iterated rooted successor.  The new
centered edge is explicitly confined so that its absolute translate remains
inside the predecessor atlas patch. -/
structure RootedGeneratorConvexAtlasSuccessorDataOfOS
    (S : CanonicalGeneratorConvexAtlasStageData OS k)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) where
  current :
    StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS S.stage
  matched :
    StageMatchedRootedRepresentedGeneratorDataOfOS current H
  edge_subset_atlas :
    ∀ u ∈ matched.edge.realRegion,
      u + anchor ∈ S.realRegion

/-- Compatibility presentation of the rooted convex-atlas successor. -/
structure RootedGeneratorConvexAtlasSuccessorData
    (S : CanonicalGeneratorConvexAtlasStageData OS k)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS) where
  current :
    StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS S.stage
  matched :
    StageMatchedRootedRepresentedGeneratorData current H lgc
  edge_subset_atlas :
    ∀ u ∈ matched.edge.realRegion,
      u + anchor ∈ S.realRegion

namespace RootedGeneratorConvexAtlasSuccessorData

/-- The genuine fixed-coordinate generator extension carried by one successor
package. -/
noncomputable def extension
    (X : RootedGeneratorConvexAtlasSuccessorData S A H lgc) :
    GeneratorStageExtensionData S.stage :=
  X.matched.toAbsoluteStageExtensionDataOfConvexAtlas
    S.atlas X.edge_subset_atlas

/-- The successor again carries the complete canonical-edge and convex-atlas
invariant, so the construction can be repeated. -/
noncomputable def next
    (X : RootedGeneratorConvexAtlasSuccessorData S A H lgc) :
    CanonicalGeneratorConvexAtlasStageData OS k where
  stage := X.extension.toTimeContinuationStage
  chart := Sum S.chart (GeneratorIndex k)
  realRegion := X.matched.absoluteEdge.realRegion
  realRegion_open := X.matched.absoluteEdge.realRegion_open
  realRegion_nonempty := X.matched.absoluteEdge.realRegion_nonempty
  realRegion_subset_strictPositive := by
    intro τ hτ
    apply S.realRegion_subset_strictPositive
    simpa [add_assoc] using
      X.edge_subset_atlas (τ + -anchor) hτ
  atlas :=
    X.matched.toAbsoluteSuccessorConvexAtlas
      S.atlas X.edge_subset_atlas
  canonicalEdges :=
    X.extension.preservesCanonicalReducedCompactStageEdges
      OS S.canonicalEdges

end RootedGeneratorConvexAtlasSuccessorData

namespace RootedGeneratorConvexAtlasSuccessorDataOfOS

/-- The fixed-coordinate original-OS generator extension. -/
noncomputable def extension
    (X : RootedGeneratorConvexAtlasSuccessorDataOfOS S A H) :
    GeneratorStageExtensionData S.stage :=
  X.matched.toAbsoluteStageExtensionDataOfConvexAtlas
    S.atlas X.edge_subset_atlas

/-- The original-OS successor preserves the complete compact-edge and
convex-atlas invariant. -/
noncomputable def next
    (X : RootedGeneratorConvexAtlasSuccessorDataOfOS S A H) :
    CanonicalGeneratorConvexAtlasStageData OS k where
  stage := X.extension.toTimeContinuationStage
  chart := Sum S.chart (GeneratorIndex k)
  realRegion := X.matched.absoluteEdge.realRegion
  realRegion_open := X.matched.absoluteEdge.realRegion_open
  realRegion_nonempty := X.matched.absoluteEdge.realRegion_nonempty
  realRegion_subset_strictPositive := by
    intro τ hτ
    apply S.realRegion_subset_strictPositive
    simpa [add_assoc] using
      X.edge_subset_atlas (τ + -anchor) hτ
  atlas :=
    X.matched.toAbsoluteSuccessorConvexAtlas
      S.atlas X.edge_subset_atlas
  canonicalEdges :=
    X.extension.preservesCanonicalReducedCompactStageEdges
      OS S.canonicalEdges

end RootedGeneratorConvexAtlasSuccessorDataOfOS

/-- Every anchor in the current common atlas patch admits a fixed-coordinate
rooted successor which preserves the complete induction invariant. -/
theorem nonempty_rootedGeneratorConvexAtlasSuccessorDataOfOS
    (S : CanonicalGeneratorConvexAtlasStageData OS k)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (anchor_mem : anchor ∈ S.realRegion) :
    Nonempty
      (RootedGeneratorConvexAtlasSuccessorDataOfOS S A H) := by
  obtain ⟨D⟩ :=
    nonempty_stageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      (A := A) S.canonicalEdges
  let atlasRegionCentered : Set (Fin k → ℝ) :=
    {u | u + anchor ∈ S.realRegion}
  have hatlas_nhds : atlasRegionCentered ∈ 𝓝 0 := by
    exact
      (S.realRegion_open.preimage
        (continuous_id.add continuous_const)).mem_nhds
          (by simpa [atlasRegionCentered] using anchor_mem)
  let Q : Set (Fin k → ℝ) :=
    (D.currentData.realRegion ∩ D.recenteredRealRegion) ∩
      atlasRegionCentered
  have hQ : Q ∈ 𝓝 0 := by
    exact
      Filter.inter_mem
        (Filter.inter_mem
          D.currentData.realRegion_mem_nhds
          (D.recenteredRealRegion_open.mem_nhds
            D.zero_mem_recenteredRealRegion))
        hatlas_nhds
  obtain ⟨P, hPQ⟩ :=
    exists_stageMatchedRootedRepresentedGeneratorDataOfOS_on
      D H Q hQ
      (fun _ hu => hu.1.1)
      (fun _ hu => hu.1.2)
  exact ⟨{
    current := D
    matched := P
    edge_subset_atlas := fun u hu => (hPQ hu).2 }⟩

/-- Compatibility constructor for the legacy rooted successor record. -/
theorem nonempty_rootedGeneratorConvexAtlasSuccessorData
    (S : CanonicalGeneratorConvexAtlasStageData OS k)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (anchor_mem : anchor ∈ S.realRegion) :
    Nonempty
      (RootedGeneratorConvexAtlasSuccessorData S A H lgc) := by
  obtain ⟨D⟩ :=
    nonempty_stageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      (A := A) S.canonicalEdges
  let atlasRegionCentered : Set (Fin k → ℝ) :=
    {u | u + anchor ∈ S.realRegion}
  have hatlas_nhds : atlasRegionCentered ∈ 𝓝 0 := by
    exact
      (S.realRegion_open.preimage
        (continuous_id.add continuous_const)).mem_nhds
          (by simpa [atlasRegionCentered] using anchor_mem)
  let Q : Set (Fin k → ℝ) :=
    (D.currentData.realRegion ∩ D.recenteredRealRegion) ∩
      atlasRegionCentered
  have hQ : Q ∈ 𝓝 0 := by
    exact
      Filter.inter_mem
        (Filter.inter_mem
          D.currentData.realRegion_mem_nhds
          (D.recenteredRealRegion_open.mem_nhds
            D.zero_mem_recenteredRealRegion))
        hatlas_nhds
  obtain ⟨P, hPQ⟩ :=
    exists_stageMatchedRootedRepresentedGeneratorData_on
      D H lgc Q hQ
      (fun _ hu => hu.1.1)
      (fun _ hu => hu.1.2)
  exact ⟨{
    current := D
    matched := P
    edge_subset_atlas := fun u hu => (hPQ hu).2 }⟩

/-- Choose one anchor from the common strict-positive real patch. -/
noncomputable def selectedSuccessorAnchor
    (S : CanonicalGeneratorConvexAtlasStageData OS k) :
    Fin k → ℝ :=
  S.realRegion_nonempty.some

omit [NeZero k] in
theorem selectedSuccessorAnchor_mem
    (S : CanonicalGeneratorConvexAtlasStageData OS k) :
    selectedSuccessorAnchor S ∈ S.realRegion :=
  S.realRegion_nonempty.some_mem

/-- Select the rooted packet package for the canonical successor anchor. -/
noncomputable def selectedSuccessorPacket
    (S : CanonicalGeneratorConvexAtlasStageData OS k) :
    RootedAnchoredPacketTimeShellFamilyData
      (d := d) (selectedSuccessorAnchor S) :=
  selectedRootedAnchoredPacketTimeShellFamilyData
    (d := d) (selectedSuccessorAnchor S)
      (S.realRegion_subset_strictPositive
        (selectedSuccessorAnchor_mem S))

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
