import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFlatWickMovingSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIGlobalPhysicalDensityMovingSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPhysicalTestDistribution
import OSReconstruction.SCV.DistributionalRepresentationUniqueness

/-!
# Pointwise Euclidean identification of the physical tube

The physical Wick slice and the OS-built equation-(6.6) density represent
the same canonical moving-slice distribution. Continuity and local test
uniqueness identify them at every strict-positive Euclidean configuration.
-/

noncomputable section

open Complex MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction.OSIIReducedForwardTubeBoundaryData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d} {lgc : OSLinearGrowthCondition d OS}
variable {stage : OSIITimeContinuationStage d k}
variable {W : SchwartzNPoint d k →L[Complex] Complex}

theorem flatWick_eq_globalPhysicalDensity
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (R : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (q : NPointDomain d k)
    (hq : section43QTime (d := d) (n := k) q ∈ section43TimeStrictPositiveRegion k) :
    H.kernel (fun j => wickRotatePoint (q j)) =
      osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage
        (flattenCLEquivReal k (d + 1) q) := by
  let tau := section43QTime (d := d) (n := k) q
  obtain ⟨r, hr, hrsub⟩ := SCV.exists_pos_closedBall_subset_of_isOpen
    (isOpen_section43TimeStrictPositiveRegion k) hq
  let K := Metric.closedBall tau r
  have hK : IsCompact K := isCompact_closedBall tau r
  have hKpos : K ⊆ section43TimeStrictPositiveRegion k := hrsub
  obtain ⟨D⟩ := Hstage K hK hKpos
  obtain ⟨C⟩ := OSIIChapterV.CanonicalReducedCompactMovingSliceCutoffData.nonempty D hK
  let U : Set (NPointDomain d k) :=
    {p | section43QTime (d := d) (n := k) p ∈ Metric.ball tau r}
  have hU : IsOpen U := Metric.isOpen_ball.preimage (section43QTimeCLM d k).continuous
  have hUK : U ⊆ {p | section43QTime (d := d) (n := k) p ∈ K} :=
    fun _ hp => Metric.ball_subset_closedBall hp
  have hUpos (p : NPointDomain d k) (hp : p ∈ U) :
      section43QTime (d := d) (n := k) p ∈ section43TimeStrictPositiveRegion k :=
    hKpos (hUK hp)
  have hHcont : ContinuousOn (fun p : NPointDomain d k =>
      H.kernel (fun j => wickRotatePoint (p j))) U :=
    H.holomorphic.continuousOn.comp continuous_osiiReducedWickRotateConfig.continuousOn
      (fun p hp => osiiReducedWickRotateConfig_mem_productForwardTube_of_strictPositive p
        (hUpos p hp))
  have hGcont : ContinuousOn (fun p : NPointDomain d k =>
      osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage (flattenCLEquivReal k (d + 1) p)) U := by
    apply (continuousOn_osiiEquation66OSBuiltGlobalPhysicalDensity Hstage).comp
      (flattenCLEquivReal k (d + 1)).continuous.continuousOn
    intro p hp
    have htime : osiiEquation66FlatTime (d := d) (flattenCLEquivReal k (d + 1) p) =
        section43QTime (d := d) (n := k) p := by
      ext j
      simp [osiiEquation66FlatTime, section43QTime, nPointTimeSpatialCLE,
        flattenCLEquivReal_apply]
    change osiiEquation66FlatTime (d := d) (flattenCLEquivReal k (d + 1) p) ∈
      section43TimeStrictPositiveRegion k
    rw [htime]
    exact hUpos p hp
  have hGrep : SCV.RepresentsDistributionOn
      (osiiStageMovingSliceDistribution stage C.cutoff C.cutoff_compact 0)
      (fun p : NPointDomain d k =>
        osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage (flattenCLEquivReal k (d + 1) p)) U := by
    intro F hF
    exact osiiEquation66OSBuiltGlobalPhysicalDensity_represents_movingSlice
      D C F ⟨hF.1, hF.2.trans hUK⟩
  have heq := SCV.eqOn_inter_of_representsDistributionOn
    (osiiStageMovingSliceDistribution stage C.cutoff C.cutoff_compact 0) U U _ _
    hU hU hHcont hGcont (forwardTubeFlatWick_represents_movingSlice D C H R U hUK) hGrep
  have hqU : q ∈ U := by simpa [U, tau] using hr
  exact heq ⟨hqU, hqU⟩

omit [NeZero k] in
/-- The literal Wick slice represents the original positive-chamber LF
current on every compact source. This includes zero gap arity and is
independent of a choice of scalar-density representative. -/
theorem wickIntegral_eq_positiveChamberCurrent
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (R : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (chi : BHW.NormalizedBasepointCutoff d)
    (phi : TestFunction (OSIIChapterV.initialReducedStrictPositiveGapOpen d k) Complex ⊤) :
    (∫ q : NPointDomain d k, H.kernel (fun j => wickRotatePoint (q j)) * phi q) =
      OSIIChapterV.initialPhysicalPositiveChamberCurrent OS chi phi := by
  let F := OSIIChapterV.initialPhysicalTestToSchwartzCLM
    (OSIIChapterV.initialReducedStrictPositiveGapOpen d k) phi
  have hFfun : (F : NPointDomain d k -> Complex) = phi := rfl
  let K := section43QTimeCLM d k '' tsupport (F : NPointDomain d k -> Complex)
  have hK : IsCompact K :=
    (show HasCompactSupport (F : NPointDomain d k -> Complex) from
      hFfun ▸ phi.hasCompactSupport).image (section43QTimeCLM d k).continuous
  have hKpos : K ⊆ section43TimeStrictPositiveRegion k := by
    rintro _ ⟨q, hq, rfl⟩
    have h := phi.tsupport_subset (hFfun ▸ hq)
    exact h
  obtain ⟨D⟩ := Hstage K hK hKpos
  obtain ⟨C⟩ := OSIIChapterV.CanonicalReducedCompactMovingSliceCutoffData.nonempty D hK
  have hsupp : tsupport (F : NPointDomain d k -> Complex) ⊆
      {q | section43QTime (d := d) (n := k) q ∈ K} := fun q hq => ⟨q, hq, rfl⟩
  have hpair := osiiStageMovingSliceDistribution_zero_eq_forwardTubeFlatWickIntegral D C H R F
    ⟨hFfun ▸ phi.hasCompactSupport, hsupp⟩
  rw [osiiStageMovingSliceDistribution_zero_eq_canonicalReducedTimeCutoff_of_tsupport
    D C F hsupp] at hpair
  have hcurrent := OSIIChapterV.initialPhysicalPositiveChamberCurrent_eq_canonical_of_cutoff
    OS chi D.toCutoffData phi (fun q hq => ⟨q, hq, rfl⟩)
  exact hpair.symm.trans hcurrent.symm

end OSReconstruction.OSIIReducedForwardTubeBoundaryData
