/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.LocallyUniformDistributionRepresentation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVApproxIdentityConvolution
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDoubleDeltaSmearing
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPacketTimeTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialTimeSmearingStageFamily

















noncomputable section

open Complex Filter Set Topology
open scoped Classical BigOperators

namespace OSReconstruction
namespace OSIIChapterV
namespace InitialTimeSmearingStageFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity k}
  {compactCarrier : Set (Fin k → ℝ)}
  {C : CanonicalReducedCompactCutoffData compactCarrier}
  {realRegion : Set (Fin k → ℝ)}
  {tailStart : ℕ}
  {η : ℝ}

/-- The locally uniform scalar limit selected by the normal-family argument
for a scale-uniformly bounded shrinking-smearing stage family. -/
structure NormalFamilyLimitData
    (F : InitialTimeSmearingStageFamilyData
      OS I C realRegion tailStart η) where
  value :
    OSIITimeGapSpace k →
      SchwartzMap (Section43SpatialSpace d k) ℂ → ℂ
  locallyUniform :
    ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
      TendstoLocallyUniformlyOn
        (fun N z => (F.stage N).distribution z χ)
        (fun z => value z χ)
        atTop
        (osiiNarrowTimeCarrier (k := k) η)

/-- A normal-family limit selected directly from convergence of the shrinking
real edges as distributions. The representation field records the output
needed to make the limit itself the unsmeared real-edge orbit. -/
structure DistributionalNormalFamilyLimitData
    (F : InitialTimeSmearingStageFamilyData
      OS I C realRegion tailStart η) where
  toNormalFamilyLimitData : NormalFamilyLimitData F
  representsValue :
    ∀ (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
      (φ : SchwartzMap (Fin k → ℝ) ℂ),
      SCV.SupportsInOpen
          (φ : (Fin k → ℝ) → ℂ) realRegion →
        ∫ τ : Fin k → ℝ,
            toNormalFamilyLimitData.value
                (osiiPositiveRealTimeEmbed τ) χ * φ τ =
          (orderedTransportDistribution
              (canonicalReducedTimeCutoffSchwingerCLM
                OS C.cutoff C.cutoff_support)).comp
              (section43OrderedPullbackTimeSpatialTensorCLM d k χ) φ

namespace NormalFamilyLimitData

variable
  {F : InitialTimeSmearingStageFamilyData
    OS I C realRegion tailStart η}

/-- Scale-uniform compact bounds plus the intrinsic distributional convergence
of the translated shrinking edges select an unsmeared holomorphic limit,
without assuming a pointwise real-edge representative in advance. -/
theorem nonempty_distributional_of_scaleUniform
    (hη : 0 < η)
    (hrealRegion_open : IsOpen realRegion)
    (hrealRegion_nonempty : realRegion.Nonempty)
    (huniform : F.ScaleUniformLocallyPointwiseBounded) :
    Nonempty (DistributionalNormalFamilyLimitData F) := by
  let W : SchwartzNPoint d k →L[ℂ] ℂ :=
    orderedTransportDistribution
      (canonicalReducedTimeCutoffSchwingerCLM
        OS C.cutoff C.cutoff_support)
  have hreal_sub :
      ∀ τ ∈ realRegion,
        osiiPositiveRealTimeEmbed τ ∈
          osiiNarrowTimeCarrier (k := k) η := by
    intro τ hτ
    simpa [F.carrier 0] using (F.edge 0 τ hτ).1
  have hlimit :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ∃ limit : OSIITimeGapSpace k → ℂ,
          TendstoLocallyUniformlyOn
              (fun N z => (F.stage N).distribution z χ)
              limit atTop
              (osiiNarrowTimeCarrier (k := k) η) ∧
            ∀ φ : SchwartzMap (Fin k → ℝ) ℂ,
              SCV.SupportsInOpen
                  (φ : (Fin k → ℝ) → ℂ) realRegion →
                ∫ τ : Fin k → ℝ,
                    limit (osiiPositiveRealTimeEmbed τ) * φ τ =
                  W.comp
                    (section43OrderedPullbackTimeSpatialTensorCLM
                      d k χ) φ := by
    intro χ
    obtain ⟨limit, hlocal, _hhol, hrep⟩ :=
      SCV.exists_tendstoLocallyUniformlyOn_of_locally_bounded_holomorphic_of_distributional_real_limit
        (U := osiiNarrowTimeCarrier (k := k) η)
        (V := realRegion)
        (T := W.comp
          (section43OrderedPullbackTimeSpatialTensorCLM d k χ))
        (F := fun N z => (F.stage N).distribution z χ)
        (isOpen_osiiNarrowTimeCarrier η)
        (isConnected_osiiNarrowTimeCarrier η hη)
        hrealRegion_open hrealRegion_nonempty hreal_sub
        (fun N => by
          simpa [F.carrier N] using
            (F.stage N).weaklyHolomorphic χ)
        (by
          intro K hK_compact hK_subset
          obtain ⟨M, hM⟩ :=
            huniform K hK_compact hK_subset χ
          refine ⟨max M 1, lt_of_lt_of_le zero_lt_one
            (le_max_right M 1), ?_⟩
          intro N z hz
          exact (hM N z hz).trans (le_max_left M 1))
        (by
          intro φ hφ
          let J : SchwartzTimeApproximateIdentity k :=
            I.toSchwartzTimeApproximateIdentity.tail tailStart
          have hpair :
              Tendsto
                (fun N =>
                  ∫ τ : Fin k → ℝ,
                    W.comp
                        (section43OrderedPullbackTimeSpatialTensorCLM
                          d k χ)
                        (SCV.translateSchwartz (-τ) (J.test N)) *
                      φ τ)
                atTop
                (𝓝 (W.comp
                  (section43OrderedPullbackTimeSpatialTensorCLM
                    d k χ) φ)) :=
            J.tendsto_integral_apply_translate_test_mul
              φ hφ.1
              (W.comp
                (section43OrderedPullbackTimeSpatialTensorCLM
                  d k χ))
          apply (tendsto_congr' ?_).2 hpair
          exact Filter.Eventually.of_forall fun N => by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with τ
            by_cases hτ : τ ∈ realRegion
            · have hedge := (F.edge N τ hτ).2
              have happ :=
                congrArg
                  (fun R : OSIISpatialDistribution d k => R χ)
                  hedge
              have happ_mul :=
                congrArg (fun w : ℂ => w * φ τ) happ
              change
                (F.stage N).distribution
                    (osiiPositiveRealTimeEmbed τ) χ * φ τ = _
              simpa [W, J,
                SchwartzTimeApproximateIdentity.tail,
                Section43ProductTimeApproximateIdentity.toSchwartzTimeApproximateIdentity,
                osiiTranslatedTimeSmearedSpatialDistribution_apply]
                using happ_mul
            · have hφτ : φ τ = 0 := by
                apply image_eq_zero_of_notMem_tsupport
                intro hτ_support
                exact hτ (hφ.2 hτ_support)
              simp [hφτ])
    exact ⟨limit, hlocal, hrep⟩
  choose value hlocal hrep using hlimit
  let D : NormalFamilyLimitData F := {
    value := fun z χ => value χ z
    locallyUniform := hlocal }
  exact ⟨{
    toNormalFamilyLimitData := D
    representsValue := by
      intro χ φ hφ
      exact hrep χ φ hφ }⟩

/-- The selected locally uniform scalar limit gives pointwise convergence at
every point of the common complex carrier. -/
theorem pointwise_tendsto
    (D : NormalFamilyLimitData F)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ osiiNarrowTimeCarrier (k := k) η)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    Tendsto
      (fun N => (F.stage N).distribution z χ)
      atTop
      (𝓝 (D.value z χ)) :=
  (D.locallyUniform χ).tendsto_at hz

/-- The spatial distribution reconstructed from the normal-family scalar
limit, set to zero off the common carrier. -/
noncomputable def distribution
    (D : NormalFamilyLimitData F)
    (z : OSIITimeGapSpace k) :
    OSIISpatialDistribution d k :=
  if hz : z ∈ osiiNarrowTimeCarrier (k := k) η then
    osiiSpatialDistributionOfPointwiseLimit
      (fun N => (F.stage N).distribution z)
      (D.value z)
      (D.pointwise_tendsto z hz)
  else
    0

/-- On the common carrier, the reconstructed distribution is the selected
scalar normal-family limit. -/
theorem distribution_apply_of_mem
    (D : NormalFamilyLimitData F)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ osiiNarrowTimeCarrier (k := k) η)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    D.distribution z χ = D.value z χ := by
  rw [distribution, dif_pos hz]
  exact
    osiiSpatialDistributionOfPointwiseLimit_apply
      (fun N => (F.stage N).distribution z)
      (D.value z)
      (D.pointwise_tendsto z hz)
      χ

/-- The reconstructed distribution family is weakly holomorphic. -/
theorem distribution_weaklyHolomorphic
    (D : NormalFamilyLimitData F) :
    OSIIWeaklyHolomorphicOn
      D.distribution
      (osiiNarrowTimeCarrier (k := k) η) := by
  intro χ
  have hlimit :
      DifferentiableOn ℂ
        (fun z => D.value z χ)
        (osiiNarrowTimeCarrier (k := k) η) :=
    (D.locallyUniform χ).differentiableOn_fin
      (Eventually.of_forall fun N => by
        simpa [F.carrier N] using
          (F.stage N).weaklyHolomorphic χ)
      (isOpen_osiiNarrowTimeCarrier η)
  exact hlimit.congr fun z hz =>
    D.distribution_apply_of_mem z hz χ

/-- The unsmeared initial continuation stage selected by the scale-uniform
normal family. -/
noncomputable def limitStage
    (D : NormalFamilyLimitData F) :
    OSIITimeContinuationStage d k where
  carrier := osiiNarrowTimeCarrier (k := k) η
  carrier_open := isOpen_osiiNarrowTimeCarrier η
  distribution := D.distribution
  weaklyHolomorphic := D.distribution_weaklyHolomorphic

end NormalFamilyLimitData

/- Consequences of selecting the normal-family limit by its intrinsic
distributional real-edge convergence. -/
namespace DistributionalNormalFamilyLimitData

variable
  {F : InitialTimeSmearingStageFamilyData
    OS I C realRegion tailStart η}

/-- Every point of the retained compact positive-time enclosure embeds into
the common narrow complex carrier. -/
theorem realCompact_mem_narrowCarrier
    (D : DistributionalNormalFamilyLimitData F)
    (hη : 0 < η)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ F.realCompact) :
    osiiPositiveRealTimeEmbed τ ∈
      osiiNarrowTimeCarrier (k := k) η :=
  osiiPositiveRealTimeEmbed_mem_osiiNarrowTimeCarrier
    η hη τ (F.realCompact_positive hτ)

/-- The actual real restriction of the distributionally selected limit stage
is a positive real edge on the common open patch. -/
theorem limitStage_hasPositiveRealEdge
    (D : DistributionalNormalFamilyLimitData F)
    (hη : 0 < η) :
    D.toNormalFamilyLimitData.limitStage.HasPositiveRealEdge
      (fun τ =>
        D.toNormalFamilyLimitData.distribution
          (osiiPositiveRealTimeEmbed τ))
      realRegion := by
  intro τ hτ
  have hmem :=
    D.realCompact_mem_narrowCarrier hη τ
      (F.realRegion_subset_realCompact hτ)
  exact ⟨hmem, rfl⟩

/-- The real restriction of the distributionally selected limit stage
represents the canonical reduced cutoff distribution. -/
theorem limitStage_represents
    (D : DistributionalNormalFamilyLimitData F)
    (hη : 0 < η) :
    OSIITimeSpatialRepresentsDistributionOn
      (orderedTransportDistribution
        (canonicalReducedTimeCutoffSchwingerCLM
          OS C.cutoff C.cutoff_support))
      (fun τ =>
        D.toNormalFamilyLimitData.distribution
          (osiiPositiveRealTimeEmbed τ))
      realRegion := by
  intro χ φ hφ
  rw [← D.representsValue χ φ hφ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with τ
  by_cases hτ : τ ∈ realRegion
  · rw [D.toNormalFamilyLimitData.distribution_apply_of_mem
      (osiiPositiveRealTimeEmbed τ)
      (D.realCompact_mem_narrowCarrier hη τ
        (F.realRegion_subset_realCompact hτ)) χ]
  · have hφτ : φ τ = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hτ_support
      exact hτ (hφ.2 hτ_support)
    simp [hφτ]

/-- Compactness of the retained real enclosure bounds every scalar stage
restriction uniformly on the open real patch. -/
theorem limitStage_pointwiseBounded
    (D : DistributionalNormalFamilyLimitData F)
    (hη : 0 < η) :
    OSIITimeSpatialPointwiseBoundedOn
      (fun τ =>
        D.toNormalFamilyLimitData.distribution
          (osiiPositiveRealTimeEmbed τ))
      realRegion := by
  intro χ
  have hcontinuous :
      ContinuousOn
        (fun τ =>
          D.toNormalFamilyLimitData.distribution
            (osiiPositiveRealTimeEmbed τ) χ)
        F.realCompact :=
    (D.toNormalFamilyLimitData.distribution_weaklyHolomorphic χ).continuousOn.comp
      continuous_osiiPositiveRealTimeEmbed.continuousOn
      (fun τ hτ => D.realCompact_mem_narrowCarrier hη τ hτ)
  obtain ⟨B, hB⟩ :=
    F.realCompact_compact.exists_bound_of_continuousOn hcontinuous
  exact ⟨B, fun τ hτ =>
    hB τ (F.realRegion_subset_realCompact hτ)⟩

/-- The distributionally selected normal-family limit supplies the complete
canonical positive-real-edge package with no external representative. -/
noncomputable def limitPositiveRealEdgeData
    (D : DistributionalNormalFamilyLimitData F)
    (hη : 0 < η) :
    D.toNormalFamilyLimitData.limitStage.PositiveRealEdgeData
      (orderedTransportDistribution
        (canonicalReducedTimeCutoffSchwingerCLM
          OS C.cutoff C.cutoff_support))
      realRegion where
  orbit := fun τ =>
    D.toNormalFamilyLimitData.distribution
      (osiiPositiveRealTimeEmbed τ)
  stageEdge := D.limitStage_hasPositiveRealEdge hη
  represents := D.limitStage_represents hη
  pointwiseBounded := D.limitStage_pointwiseBounded hη

/-- The distributionally selected limit is exactly one local canonical stage
edge around the compact carrier used to construct the shrinking family. -/
noncomputable def limitCanonicalReducedCompactStageEdgeData
    (D : DistributionalNormalFamilyLimitData F)
    (hη : 0 < η) :
    CanonicalReducedCompactStageEdgeData
      OS D.toNormalFamilyLimitData.limitStage compactCarrier where
  cutoff := C.cutoff
  cutoff_support := C.cutoff_support
  cutoff_compact := C.cutoff_compact
  realRegion := realRegion
  realRegion_open := F.realRegion_open
  compactCarrier_subset := F.compactCarrier_subset_realRegion
  cutoff_one_on := fun τ hτ =>
    C.cutoff_one_on τ (F.realRegion_subset_cutoffRegion hτ)
  edge := D.limitPositiveRealEdgeData hη

end DistributionalNormalFamilyLimitData

namespace CanonicalPacketApproximationData

variable
  {lgc : OSLinearGrowthCondition d OS}
  {hηsum :
    (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
        Real.arctan η < Real.pi / 2}
  {F : InitialTimeSmearingStageFamilyData
    OS I C realRegion tailStart η}

namespace ScaleUniformKernelRepresentationData

end ScaleUniformKernelRepresentationData

end CanonicalPacketApproximationData

namespace LocallyCompactTimeKernelData

variable
  {F : InitialTimeSmearingStageFamilyData
    OS I C realRegion tailStart η}

end LocallyCompactTimeKernelData
end InitialTimeSmearingStageFamilyData
end OSIIChapterV
end OSReconstruction
