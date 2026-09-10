/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalStageEdgeInvariant
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredOrderedTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPositiveProductBasepointFamily

















noncomputable section

open Complex Filter Set Topology
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {stage : OSIITimeContinuationStage d k}

/-- The data shared by a predecessor Chapter V stage and the rooted packet
construction at one anchor.

The named package keeps the central successor invariant explicit: the packet
recovery theorem and the predecessor real edge use the same canonical reduced
current. -/
structure StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (stage : OSIITimeContinuationStage d k) where
  currentData :
    CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  anchor_mem : anchor ∈ realRegion
  realRegion_subset_strictPositive :
    realRegion ⊆ section43TimeStrictPositiveRegion k
  edge :
    stage.PositiveRealEdgeData
      (orderedTransportDistribution currentData.current)
      realRegion

namespace StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData

variable
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {OS : OsterwalderSchraderAxioms d}
  {stage : OSIITimeContinuationStage d k}

/-- The predecessor real-edge region in coordinates centered at the packet
anchor. -/
def recenteredRealRegion
    (D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    Set (Fin k → ℝ) :=
  {u | u + anchor ∈ D.realRegion}

theorem recenteredRealRegion_open
    (D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    IsOpen D.recenteredRealRegion := by
  exact
    D.realRegion_open.preimage
      (continuous_id.add continuous_const)

theorem zero_mem_recenteredRealRegion
    (D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    (0 : Fin k → ℝ) ∈ D.recenteredRealRegion := by
  simpa [recenteredRealRegion] using D.anchor_mem

/-- After recentering at the packet anchor, the predecessor stage represents
the anchored ordered transport of the same canonical reduced current used by
the rooted packet construction. -/
noncomputable def recenteredEdge
    (D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    (stage.recenter anchor).PositiveRealEdgeData
      (anchoredOrderedTransportDistribution D.currentData.current anchor)
      D.recenteredRealRegion where
  orbit := fun u => D.edge.orbit (u + anchor)
  stageEdge := by
    simpa [recenteredRealRegion] using
      stage.recenter_hasPositiveRealEdge
        D.edge.orbit D.realRegion anchor D.edge.stageEdge
  represents := by
    intro chi phi hphi
    let psi : SchwartzMap (Fin k → ℝ) ℂ :=
      SCV.translateSchwartz (-anchor) phi
    have hpsi :
        SCV.SupportsInOpen
          (psi : (Fin k → ℝ) → ℂ) D.realRegion := by
      constructor
      · exact
          hasCompactSupport_translateSchwartz
            phi hphi.1 (-anchor)
      · intro u hu
        have hu' :
            u ∈ tsupport
              ((SCV.translateSchwartz (-anchor) phi :
                SchwartzMap (Fin k → ℝ) ℂ) :
                (Fin k → ℝ) → ℂ) := by
          simpa [psi] using hu
        rw [tsupport_translateSchwartz_eq_preimage] at hu'
        have hcentered : u + -anchor ∈ D.recenteredRealRegion :=
          hphi.2 hu'
        simpa [recenteredRealRegion, add_assoc] using hcentered
    have hold := D.edge.represents chi psi hpsi
    calc
      (anchoredOrderedTransportDistribution
          D.currentData.current anchor).comp
            (section43OrderedPullbackTimeSpatialTensorCLM d k chi) phi =
          (orderedTransportDistribution D.currentData.current).comp
            (section43OrderedPullbackTimeSpatialTensorCLM d k chi) psi := by
        simp only [ContinuousLinearMap.comp_apply]
        rw [
          anchoredOrderedTransportDistribution_orderedPullbackTimeSpatialTensor,
          orderedTransportDistribution_orderedPullbackTimeSpatialTensor]
        rfl
      _ = ∫ u : Fin k → ℝ, D.edge.orbit u chi * psi u := hold
      _ = ∫ u : Fin k → ℝ,
          D.edge.orbit (u + anchor) chi * phi u := by
        let g : (Fin k → ℝ) → ℂ :=
          fun u => D.edge.orbit u chi * psi u
        have hshift :
            (fun u : Fin k → ℝ =>
              D.edge.orbit (u + anchor) chi * phi u) =
              fun u => g (u + anchor) := by
          funext u
          simp [g, psi, SCV.translateSchwartz_apply, add_assoc]
        rw [show
          (fun u : Fin k → ℝ => D.edge.orbit u chi * psi u) = g by
            rfl]
        rw [hshift]
        exact
          (MeasureTheory.integral_add_right_eq_self g anchor).symm
  pointwiseBounded := by
    intro chi
    obtain ⟨C, hC⟩ := D.edge.pointwiseBounded chi
    exact ⟨C, fun u hu => hC (u + anchor) hu⟩

end StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData

/-- A predecessor stage carrying all canonical compact reduced edges admits a
rooted packet current which it represents on an open strict-positive real
region.

The packet recovery neighborhood and the represented real-edge region need
not coincide.  What matters for the successor comparison is that they use the
same reduced current. -/
theorem nonempty_stageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
    (H : HasCanonicalReducedCompactStageEdges OS stage) :
    Nonempty
      (StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
        A OS stage) := by
  obtain ⟨C₀⟩ :=
    A.nonempty_commonTranslatedPositiveHeadSpatialSourceCurrentData OS
  let compactCarrier : Set (Fin k → ℝ) :=
    tsupport (C₀.cutoff : (Fin k → ℝ) → ℂ) ∪ {anchor}
  have hcompactCarrier : IsCompact compactCarrier := by
    exact C₀.cutoff_compact.isCompact.union isCompact_singleton
  have hcompactCarrier_positive :
      compactCarrier ⊆ section43TimeStrictPositiveRegion k := by
    exact Set.union_subset C₀.cutoff_support
      (Set.singleton_subset_iff.mpr A.anchor_positive)
  obtain ⟨D⟩ :=
    H compactCarrier hcompactCarrier hcompactCarrier_positive
  let C :
      CommonTranslatedPositiveHeadSpatialSourceCurrentData
        (d := d) (k := k) A OS :=
    { cutoff := D.cutoff
      cutoff_support := D.cutoff_support
      cutoff_compact := D.cutoff_compact
      realRegion := C₀.realRegion
      realRegion_open := C₀.realRegion_open
      realRegion_mem_nhds := C₀.realRegion_mem_nhds
      cutoff_one_on_translatedSource := by
        intro u hu N χ x hx
        exact
          D.reducedTimeCutoffWeight_eq_one_of_auxiliary
            C₀.cutoff Set.subset_union_left x
            (C₀.cutoff_one_on_translatedSource u hu N χ x hx)
      recover := by
        intro u hu N χ
        let f : SchwartzNPoint d (k + 1) :=
          translateSchwartzConfiguration
            (sourceParameterDisplacementCLM
              (fun i : Fin k =>
                chronologicalTimeSourceDirection (d := d) i) u)
            (A.positiveHeadSpatialSource N χ).1
        have hf : VanishesToInfiniteOrderOnCoincidence f := by
          exact C₀.translatedSource_vanishes u hu N χ
        have hone :
            SchwartzMap.smulLeftCLM ℂ
                (reducedTimeCutoffWeight (d := d) D.cutoff) f =
              f := by
          exact
            reducedTimeCutoff_smul_eq_of_one_on_tsupport
              D.cutoff f
              (fun x hx =>
                D.reducedTimeCutoffWeight_eq_one_of_auxiliary
                  C₀.cutoff Set.subset_union_left x
                  (C₀.cutoff_one_on_translatedSource
                    u hu N χ x (by simpa [f] using hx)))
        have hrecover :
            canonicalReducedTimeCutoffSchwingerCLM
                OS D.cutoff D.cutoff_support
                (diffVarReduction d k f) =
              OS.S (k + 1) ⟨f, hf⟩ :=
          canonicalReducedTimeCutoffSchwingerCLM_apply_diffVarReduction_eq_of_cutoff
            OS D.cutoff D.cutoff_support f hf hone
        rw [← ZeroDiagonalSchwartz.ofClassical_of_vanishes f hf] at hrecover
        change
          canonicalReducedTimeCutoffSchwingerCLM
              OS D.cutoff D.cutoff_support
              (section43NPointTimeSpatialTensor d k
                (SCV.translateSchwartz (-u) (A.timeTest N))
                (section43SpatialHeadMarginal χ)) =
            OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical f)
        rw [← hrecover]
        apply congrArg
          (canonicalReducedTimeCutoffSchwingerCLM
            OS D.cutoff D.cutoff_support)
        simp only [f]
        rw [diffVarReduction_translateSchwartzConfiguration,
          A.diffVarReduction_positiveHeadSpatialSource,
          translate_reducedTimeSpatialTensor_chronological] }
  refine ⟨{
    currentData := C
    realRegion := D.realRegion
    realRegion_open := D.realRegion_open
    anchor_mem :=
      D.compactCarrier_subset
        (Set.mem_union_right _ (Set.mem_singleton anchor))
    realRegion_subset_strictPositive :=
      D.realRegion_subset_strictPositive
    edge := ?_ }⟩
  simpa [C, CommonTranslatedPositiveHeadSpatialSourceCurrentData.current] using
    D.edge

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
