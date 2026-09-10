import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalMovingSliceCutoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltGlobalPhysicalAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIFlatPairing

/-!
# Global equation-(6.6) density as a moving-slice representative

The all-edge equation-(6.6) density and the Chapter V moving-slice
distribution are two presentations of the same reduced real-edge
distribution.  On a compact positive-time carrier, the adapted moving-slice
cutoff is one on every supported reduced test.  Its zero slice therefore
reduces to the canonical reduced cutoff distribution, which is already
represented by the global equation-(6.6) density in flattened coordinates.

This file records that comparison at the full distributional level.  It does
not assert any complex MZ continuation to the literal flat-Wick slice; that
remains the separate producer-side obligation.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable {stage : OSIITimeContinuationStage d k}
variable {compactCarrier : Set (Fin k -> Real)}

omit [NeZero k] in
/-- On reduced tests supported over the named compact time carrier, the zero
moving slice is exactly the canonical reduced cutoff distribution. -/
theorem osiiStageMovingSliceDistribution_zero_eq_canonicalReducedTimeCutoff_of_tsupport
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (C : OSIIChapterV.CanonicalReducedCompactMovingSliceCutoffData D)
    (F : SchwartzNPoint d k)
    (hF :
      tsupport (F : NPointDomain d k -> Complex) ⊆
        {q | section43QTime (d := d) (n := k) q ∈ compactCarrier}) :
    osiiStageMovingSliceDistribution stage C.cutoff C.cutoff_compact 0 F =
      OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS D.cutoff D.cutoff_support F := by
  have hzero : 0 ∈ osiiStageMovingSliceCarrier stage C.cutoff := by
    intro tau htau
    simpa using
      (D.edge.stageEdge tau (C.cutoff_support htau)).1
  rw [osiiStageMovingSliceDistribution_apply_of_mem
    stage C.cutoff C.cutoff_compact 0 hzero F]
  rw [osiiStageMovingSliceScalar_zero_eq_orderedPullbackFullCutoff
    stage
    (OSIIChapterV.orderedTransportDistribution
      (OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS D.cutoff D.cutoff_support))
    C.cutoff D.realRegion C.cutoff_compact C.cutoff_support
    D.edge.stage_continuousOn D.edge.stage_pointwiseBounded
    D.edge.stage_represents F]
  rw [OSIIChapterV.orderedTransportDistribution_cutoff]
  congr 1
  ext q
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (section43NPointTimeCutoffWeight_hasTemperateGrowth d k C.cutoff)]
  by_cases hq : q ∈ tsupport (F : NPointDomain d k -> Complex)
  · have htime := hF hq
    simp [section43NPointTimeCutoffWeight, C.cutoff_one_on _ htime]
  · have hzeroF : F q = 0 := image_eq_zero_of_notMem_tsupport hq
    simp [hzeroF]

/-- The OS-built global positive-real equation-(6.6) density, pulled back
from flattened blocks to native reduced configurations, represents the
canonical zero moving slice on every compact positive-time carrier. -/
theorem osiiEquation66OSBuiltGlobalPhysicalDensity_represents_movingSlice
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (C : OSIIChapterV.CanonicalReducedCompactMovingSliceCutoffData D) :
    SCV.RepresentsDistributionOn
      (osiiStageMovingSliceDistribution stage C.cutoff C.cutoff_compact 0)
      (fun q : NPointDomain d k =>
        osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage
          (flattenCLEquivReal k (d + 1) q))
      {q | section43QTime (d := d) (n := k) q ∈ compactCarrier} := by
  intro F hF
  have hflat_support :
      SCV.SupportsInOpen
        ((flattenSchwartzNPoint (d := d) F :
          SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
          (Fin (k * (d + 1)) -> Real) -> Complex)
        {y | osiiEquation66FlatTime (d := d) y ∈ D.realRegion} := by
    constructor
    · exact hF.1.comp_homeomorph
        ((flattenCLEquivReal k (d + 1)).symm.toHomeomorph)
    · intro y hy
      have hpre :
          (flattenCLEquivReal k (d + 1)).symm y ∈
            tsupport (F : NPointDomain d k -> Complex) := by
        have h :=
          tsupport_comp_subset_preimage
            (F : NPointDomain d k -> Complex)
            (flattenCLEquivReal k (d + 1)).symm.continuous hy
        simpa [flattenSchwartzNPoint_apply] using h
      have htime := hF.2 hpre
      apply D.compactCarrier_subset
      simpa [osiiEquation66FlatTime, section43QTime,
        nPointTimeSpatialCLE, flattenCLEquivReal_apply] using htime
  calc
    osiiStageMovingSliceDistribution stage C.cutoff C.cutoff_compact 0 F =
        OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS D.cutoff D.cutoff_support F :=
      osiiStageMovingSliceDistribution_zero_eq_canonicalReducedTimeCutoff_of_tsupport
        D C F hF.2
    _ = ∫ q : NPointDomain d k,
        osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage
            (flattenCLEquivReal k (d + 1) q) * F q :=
      flatPairing_of_represents
        (OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS D.cutoff D.cutoff_support)
        (osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage)
        {y | osiiEquation66FlatTime (d := d) y ∈ D.realRegion}
        (osiiEquation66OSBuiltGlobalPhysicalDensity_represents
          (lgc := lgc) (stage := stage) D)
        F hflat_support

end OSReconstruction
