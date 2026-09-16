import OSReconstruction.SCV.LocallyUniformDistributionRepresentation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredGeneratorPacketScaleLimits
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredOrderedTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPositiveProductBasepointFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumSource

/-!
# Vacuum-tail fields for the Chapter V anchored atlas

The mixed Hilbert field in OS II Chapter V must recover the scalar
continuation one particle lower after pairing with the vacuum.  This file
constructs that projection without adding a scalar-stage hypothesis.

There are three ingredients.

* The degree-zero constant-one positive-time source defines the OS vacuum
  vector, and vacuum-left pairing with a homogeneous positive-time source is
  exactly its Schwinger functional.
* Packet-scale anchored Hilbert fields are continuous and linear in the full
  spatial Schwartz test.  Their pointwise Hilbert limits therefore remain
  continuous linear by Banach--Steinhaus.
* Pairing the resulting source-linear limit with the vacuum gives an honest
  spatial-distribution-valued holomorphic field on the source-linear anchored
  atlas domain.

The final real-edge theorem identifies this limiting field, distributionally,
with the anchored reduced current retained by
`CommonTranslatedPositiveHeadSpatialSourceCurrentData`.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d n : ℕ} [NeZero d]

/-- The OS vacuum vector in the Hilbert completion. -/
noncomputable def osiiChapterVVacuumVector
    (OS : OsterwalderSchraderAxioms d) :
    OSHilbertSpace OS :=
  osiiPositiveTimeSingleVectorCLM OS 0 osiiChapterVVacuumSource

/-- Vacuum-left OS pairing is the Schwinger functional of the right source. -/
theorem osiiChapterVVacuumVector_inner_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (g : euclideanPositiveTimeSubmodule (d := d) n) :
    @inner ℂ (OSHilbertSpace OS) _
        (osiiChapterVVacuumVector OS)
        (osiiPositiveTimeSingleVectorCLM OS n g) =
      OS.S n (ZeroDiagonalSchwartz.ofClassical g.1) := by
  have hsource :
      reindexSchwartz (d := d) (finCongr (Nat.zero_add n))
          ((osiiChapterVVacuumSource (d := d)).1.osConjTensorProduct g.1) =
        g.1 := by
    simpa [osiiChapterVVacuumSource] using
      (reindex_osiiChapterVVacuumUnit_osConjTensorProduct
        (d := d) g.1)
  exact
    (osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger
      OS 0 n osiiChapterVVacuumSource g).trans
        (osiiSchwinger_ofClassical_eq_of_reindex_finCongr
          OS (Nat.zero_add n) _ _ hsource)

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

section AnchoredApproximateIdentity

variable {k : ℕ} [NeZero k]
variable
  {I₀ : Section43ProductTimeApproximateIdentity k}
  {anchor₀ : Fin k → ℝ}

/-- Distributional convergence of the translated anchored kernels.  The
anchor remains in the limiting test because translating `A.timeTest N` by
`-u` centers the underlying zero-centered approximate identity at
`u + anchor`. -/
theorem tendsto_integral_apply_translate_timeTest_mul
    (A₀ : AnchoredPacketTimeShellFamilyData (d := d) I₀ anchor₀)
    (h : SchwartzMap (Fin k → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin k → ℝ) → ℂ))
    (T : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ) :
    Tendsto
      (fun N =>
        ∫ u : Fin k → ℝ,
          T (SCV.translateSchwartz (-u) (A₀.timeTest N)) * h u)
      atTop
      (𝓝 (T (SCV.translateSchwartz (-anchor₀) h))) := by
  let h' : SchwartzMap (Fin k → ℝ) ℂ :=
    SCV.translateSchwartz (-anchor₀) h
  have h'compact : HasCompactSupport (h' : (Fin k → ℝ) → ℂ) :=
    hasCompactSupport_translateSchwartz h hcompact (-anchor₀)
  have hbase :=
    (I₀.toSchwartzTimeApproximateIdentity
      |>.tendsto_integral_apply_translate_test_mul h' h'compact T).comp
        (tendsto_add_atTop_nat A₀.carrierData.tailStart)
  apply (tendsto_congr' ?_).2 hbase
  exact Filter.Eventually.of_forall fun N => by
    let g : (Fin k → ℝ) → ℂ :=
      fun x =>
        T (SCV.translateSchwartz (-x)
          (I₀.test (N + A₀.carrierData.tailStart))) * h' x
    calc
      (∫ u : Fin k → ℝ,
          T (SCV.translateSchwartz (-u) (A₀.timeTest N)) * h u) =
          ∫ u : Fin k → ℝ, g (u + anchor₀) := by
        apply integral_congr_ae
        filter_upwards with u
        rw [A₀.translate_timeTest N u]
        simp [g, h', SCV.translateSchwartz_apply]
      _ = ∫ x : Fin k → ℝ, g x := by
        simpa using MeasureTheory.integral_add_right_eq_self g anchor₀

end AnchoredApproximateIdentity

namespace PositiveHeadUniversalAnchoredAtlasData

variable {q : ℕ}
variable
  {I : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) → ℝ}
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {A :
    AnchoredPacketTimeShellFamilyData
      (d := d) I anchor}

/-- The real parameter germ on which every local positive-time source in the
packet family is the genuine chronological configuration translate. -/
def vacuumTailSourceRealTraceRegion :
    Set (Fin (q + 1) → ℝ) :=
  {u |
    ∀ (scale : ℕ)
      (χ : SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ),
      (localPositiveTimeParameterTranslate
        (A.positiveHeadSpatialSource scale χ)
        (fun i : Fin (q + 1) =>
          chronologicalTimeSourceDirection (d := d) i) u).1 =
        translateSchwartzConfiguration
          (sourceParameterDisplacementCLM
            (fun i : Fin (q + 1) =>
              chronologicalTimeSourceDirection (d := d) i) u)
          (A.positiveHeadSpatialSource scale χ).1}

theorem vacuumTailSourceRealTraceRegion_mem_nhds :
    vacuumTailSourceRealTraceRegion (d := d) (A := A) ∈
      𝓝 (0 : Fin (q + 1) → ℝ) := by
  have hsource :=
    eventually_localPositiveTimeParameterTranslate_family_chronological_coe_eq
      (f := fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        A.positiveHeadSpatialSource p.1 p.2)
      A.positiveHeadSpatialSource_uniformCompactSupport
  filter_upwards [hsource] with u hu
  exact fun scale χ => hu (scale, χ)

/-- Insert the normalized absolute spatial basepoint before applying the
source-linear anchored Hilbert field. -/
noncomputable def vacuumTailSpatialLiftCLM :
    SchwartzMap (Section43SpatialSpace d (q + 1)) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) ℂ :=
  section43SpatialBasepointLiftCLM d (q + 1)
    (normalizedSpatialBasepointCutoff d).toSchwartz

@[simp]
theorem spatialHeadMarginal_vacuumTailSpatialLiftCLM
    (χ : SchwartzMap (Section43SpatialSpace d (q + 1)) ℂ) :
    section43SpatialHeadMarginal (vacuumTailSpatialLiftCLM χ) = χ := by
  exact
    section43SpatialHeadMarginal_basepointLift_eq
      (normalizedSpatialBasepointCutoff d) χ

/-- At a fixed complex time point, the packet-scale Hilbert limit remains a
continuous linear function of the full spatial Schwartz test.

Pointwise convergence of the finite-scale CLMs is enough: the Schwartz space
is barrelled, so `continuousLinearMapOfTendstoComplex` supplies continuity of
the limit while preserving complex linearity. -/
noncomputable def fixedHeadAnchoredSpatialHilbertFieldLimitCLM
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain) :
    SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  SchwartzMap.continuousLinearMapOfTendstoComplex
    (fun scale => D.spatialFieldCLM scale z hz)
    (fun χ => fixedHeadAnchoredSpatialHilbertFieldLimit D χ z)
    (by
      rw [tendsto_pi_nhds]
      intro χ
      simpa only [spatialFieldCLM_apply] using
        (fixedHeadAnchoredSpatialHilbertFieldLimit_locallyUniform
          D χ).tendsto_at hz)

@[simp]
theorem fixedHeadAnchoredSpatialHilbertFieldLimitCLM_apply
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    D.fixedHeadAnchoredSpatialHilbertFieldLimitCLM z hz χ =
      fixedHeadAnchoredSpatialHilbertFieldLimit D χ z :=
  rfl

/-- The finite packet-scale vacuum-tail spatial distribution.  It is
totalized by zero off the source-linear anchored domain. -/
noncomputable def vacuumTailPacketSpatialDistribution
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ) :
    OSIISpatialDistribution d (q + 1) :=
  if hz : z ∈ D.spatialLinearDomain then
    (innerSL ℂ (osiiChapterVVacuumVector OS)).comp
      ((D.spatialFieldCLM scale z hz).comp
        vacuumTailSpatialLiftCLM)
  else
    0

@[simp]
theorem vacuumTailPacketSpatialDistribution_apply_of_mem
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain)
    (χ : SchwartzMap (Section43SpatialSpace d (q + 1)) ℂ) :
    D.vacuumTailPacketSpatialDistribution scale z χ =
      (innerSL ℂ (osiiChapterVVacuumVector OS))
        (D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (A.positiveHeadSpatialAnchoredSourceCLM scale
            (vacuumTailSpatialLiftCLM χ)) z) := by
  simp [vacuumTailPacketSpatialDistribution, hz,
    ContinuousLinearMap.comp_apply, spatialFieldCLM_apply]

/-- The common open real germ on which the anchored Hilbert edge, the
retained reduced current, and the genuine translated source formula all
hold simultaneously. -/
def vacuumTailRealRegion
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    Set (Fin (q + 1) → ℝ) :=
  D.gram.anchoredAtlasRealRegion
      D.sourceStage.stage D.sourceStage.germ ∩
    C.realRegion ∩
      interior (vacuumTailSourceRealTraceRegion (d := d) (A := A))

theorem vacuumTailRealRegion_open
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    IsOpen (D.vacuumTailRealRegion C) :=
  ((D.gram.anchoredAtlasRealRegion_open
      D.sourceStage.stage D.sourceStage.germ).inter
    C.realRegion_open).inter isOpen_interior

theorem vacuumTailRealRegion_mem_nhds
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    D.vacuumTailRealRegion C ∈
      𝓝 (0 : Fin (q + 1) → ℝ) := by
  exact
    Filter.inter_mem
      (Filter.inter_mem
        (D.gram.anchoredAtlasRealRegion_mem_nhds
          D.sourceStage.stage D.sourceStage.germ)
        C.realRegion_mem_nhds)
      (interior_mem_nhds.2
        (vacuumTailSourceRealTraceRegion_mem_nhds
          (d := d) (A := A)))

@[simp]
theorem zero_mem_vacuumTailRealRegion
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    (0 : Fin (q + 1) → ℝ) ∈ D.vacuumTailRealRegion C :=
  mem_of_mem_nhds (D.vacuumTailRealRegion_mem_nhds C)

/-- On the common real germ, vacuum pairing of a finite anchored Hilbert
packet is exactly the retained reduced Schwinger current with the translated
anchored time test. -/
theorem vacuumTailPacketSpatialDistribution_realEdge
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS)
    (scale : ℕ)
    (u : Fin (q + 1) → ℝ)
    (hu : u ∈ D.vacuumTailRealRegion C)
    (χ : SchwartzMap (Section43SpatialSpace d (q + 1)) ℂ) :
    D.vacuumTailPacketSpatialDistribution scale
        (SCV.realToComplex u) χ =
      C.current
        (section43NPointTimeSpatialTensor d (q + 1)
          (SCV.translateSchwartz (-u) (A.timeTest scale)) χ) := by
  have hz : SCV.realToComplex u ∈ D.spatialLinearDomain :=
    D.initialGramPolydisc_subset_spatialLinearDomain hu.1.1.2
  rw [D.vacuumTailPacketSpatialDistribution_apply_of_mem
    scale (SCV.realToComplex u) hz χ]
  have hedge :=
    D.generatedSpatialField_realEdge
      scale (vacuumTailSpatialLiftCLM χ) u hu.1.1
  rw [show
    D.gram.anchoredAtlasField
        D.sourceStage.stage D.sourceStage.germ
        (A.positiveHeadSpatialAnchoredSourceCLM scale
          (vacuumTailSpatialLiftCLM χ))
        (SCV.realToComplex u) =
      osiiPositiveTimeSingleVectorCLM OS ((q + 1) + 1)
        (localPositiveTimeParameterTranslate
          (A.positiveHeadSpatialSource scale
            (vacuumTailSpatialLiftCLM χ))
          (fun i : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) i) u) by
    simpa [SCV.realToComplex] using! hedge]
  rw [show
    (innerSL ℂ (osiiChapterVVacuumVector OS))
        (osiiPositiveTimeSingleVectorCLM OS ((q + 1) + 1)
          (localPositiveTimeParameterTranslate
            (A.positiveHeadSpatialSource scale
              (vacuumTailSpatialLiftCLM χ))
            (fun i : Fin (q + 1) =>
              chronologicalTimeSourceDirection (d := d) i) u)) =
      OS.S ((q + 1) + 1)
        (ZeroDiagonalSchwartz.ofClassical
          (localPositiveTimeParameterTranslate
            (A.positiveHeadSpatialSource scale
              (vacuumTailSpatialLiftCLM χ))
            (fun i : Fin (q + 1) =>
              chronologicalTimeSourceDirection (d := d) i) u).1) by
    simpa using
      osiiChapterVVacuumVector_inner_eq_schwinger OS
        (localPositiveTimeParameterTranslate
          (A.positiveHeadSpatialSource scale
            (vacuumTailSpatialLiftCLM χ))
          (fun i : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) i) u)]
  rw [(interior_subset hu.2) scale (vacuumTailSpatialLiftCLM χ)]
  rw [← C.recover u hu.1.2 scale (vacuumTailSpatialLiftCLM χ)]
  rw [spatialHeadMarginal_vacuumTailSpatialLiftCLM]
  rfl

/-- The packet-scale vacuum-tail distributions are weakly holomorphic on the
complete source-linear anchored domain. -/
theorem vacuumTailPacketSpatialDistribution_weaklyHolomorphic
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (scale : ℕ) :
    OSIIWeaklyHolomorphicOn
      (D.vacuumTailPacketSpatialDistribution scale)
      D.spatialLinearDomain := by
  intro χ
  have hfield :
      DifferentiableOn ℂ
        (fun z =>
          D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ
            (A.positiveHeadSpatialAnchoredSourceCLM scale
              (vacuumTailSpatialLiftCLM χ)) z)
        D.spatialLinearDomain :=
    (D.generatedSpatialField_holomorphic
      scale (vacuumTailSpatialLiftCLM χ)).mono
        (fun _ hz => hz.1)
  exact
    ((differentiableOn_const
      (c := innerSL ℂ (osiiChapterVVacuumVector OS))).clm_apply
        hfield).congr fun z hz => by
          exact
            (D.vacuumTailPacketSpatialDistribution_apply_of_mem
              scale z hz χ)

/-- The packet-scale limit paired with the vacuum, as a genuine spatial
Schwartz distribution.  It is totalized by zero off the source-linear
anchored domain. -/
noncomputable def vacuumTailLimitSpatialDistribution
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (z : Fin (q + 1) → ℂ) :
    OSIISpatialDistribution d (q + 1) :=
  if hz : z ∈ D.spatialLinearDomain then
    (innerSL ℂ (osiiChapterVVacuumVector OS)).comp
      ((D.fixedHeadAnchoredSpatialHilbertFieldLimitCLM z hz).comp
        vacuumTailSpatialLiftCLM)
  else
    0

@[simp]
theorem vacuumTailLimitSpatialDistribution_apply_of_mem
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain)
    (χ : SchwartzMap (Section43SpatialSpace d (q + 1)) ℂ) :
    D.vacuumTailLimitSpatialDistribution z χ =
      (innerSL ℂ (osiiChapterVVacuumVector OS))
        (fixedHeadAnchoredSpatialHilbertFieldLimit D
          (vacuumTailSpatialLiftCLM χ) z) := by
  simp [vacuumTailLimitSpatialDistribution, hz,
    ContinuousLinearMap.comp_apply]

/-- The vacuum-tail packet distributions converge locally uniformly, after
evaluation on every fixed reduced spatial Schwartz test. -/
theorem vacuumTailSpatialDistribution_locallyUniform
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (χ : SchwartzMap (Section43SpatialSpace d (q + 1)) ℂ) :
    TendstoLocallyUniformlyOn
      (fun scale z =>
        D.vacuumTailPacketSpatialDistribution scale z χ)
      (fun z => D.vacuumTailLimitSpatialDistribution z χ)
      atTop D.spatialLinearDomain := by
  have hfield :=
    fixedHeadAnchoredSpatialHilbertFieldLimit_locallyUniform
      D (vacuumTailSpatialLiftCLM χ)
  have hpair :=
    (innerSL ℂ (osiiChapterVVacuumVector OS)).uniformContinuous
      |>.comp_tendstoLocallyUniformlyOn hfield
  exact
    (hpair.congr fun scale z hz => by
      simpa [Function.comp_def] using
        (D.vacuumTailPacketSpatialDistribution_apply_of_mem
          scale z hz χ).symm).congr_right fun z hz => by
            simpa [Function.comp_def] using
              (D.vacuumTailLimitSpatialDistribution_apply_of_mem
                z hz χ).symm

/-- The limiting vacuum-tail orbit represents the anchored reduced current
on the common real germ.  This is the distributional passage from the finite
packet real-edge identity: local uniform convergence controls the left-hand
integrals, while the translated anchored approximate identity recovers the
current on the right. -/
theorem vacuumTailLimitSpatialDistribution_represents
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    OSIITimeSpatialRepresentsDistributionOn
      (anchoredOrderedTransportDistribution C.current anchor)
      (fun u =>
        D.vacuumTailLimitSpatialDistribution (SCV.realToComplex u))
      (D.vacuumTailRealRegion C) := by
  intro χ φ hφ
  have hrealToComplex :
      Continuous
        (SCV.realToComplex :
          (Fin (q + 1) → ℝ) → Fin (q + 1) → ℂ) :=
    continuous_pi fun i =>
      Complex.continuous_ofReal.comp (continuous_apply i)
  have hmem :
      ∀ u ∈ D.vacuumTailRealRegion C,
        SCV.realToComplex u ∈ D.spatialLinearDomain := by
    intro u hu
    exact D.initialGramPolydisc_subset_spatialLinearDomain hu.1.1.2
  have hlocal :
      TendstoLocallyUniformlyOn
        (fun scale u =>
          D.vacuumTailPacketSpatialDistribution scale
            (SCV.realToComplex u) χ)
        (fun u =>
          D.vacuumTailLimitSpatialDistribution
            (SCV.realToComplex u) χ)
        atTop (D.vacuumTailRealRegion C) := by
    exact
      (D.vacuumTailSpatialDistribution_locallyUniform χ).comp
        SCV.realToComplex hmem hrealToComplex.continuousOn
  have hcontinuous :
      ∀ scale,
        ContinuousOn
          (fun u =>
            D.vacuumTailPacketSpatialDistribution scale
              (SCV.realToComplex u) χ)
          (D.vacuumTailRealRegion C) := by
    intro scale
    exact
      ((D.vacuumTailPacketSpatialDistribution_weaklyHolomorphic
          scale χ).continuousOn.comp
        hrealToComplex.continuousOn hmem)
  have hlimit :=
    SCV.tendsto_integral_mul_schwartz_of_tendstoLocallyUniformlyOn
      (D.vacuumTailRealRegion_open C)
      hcontinuous hlocal φ hφ
  let T : SchwartzMap (Fin (q + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    C.current.comp (section43TimeSpatialTensorCLM d (q + 1) χ)
  have hcurrentBase :=
    A.tendsto_integral_apply_translate_timeTest_mul φ hφ.1 T
  have hcurrent :
      Tendsto
        (fun scale =>
          ∫ u : Fin (q + 1) → ℝ,
            D.vacuumTailPacketSpatialDistribution scale
                (SCV.realToComplex u) χ *
              φ u)
        atTop
        (𝓝 (T (SCV.translateSchwartz (-anchor) φ))) := by
    apply (tendsto_congr' ?_).2 hcurrentBase
    exact Filter.Eventually.of_forall fun scale => by
      apply integral_congr_ae
      filter_upwards with u
      by_cases hu :
          u ∈ tsupport (φ : (Fin (q + 1) → ℝ) → ℂ)
      · rw [D.vacuumTailPacketSpatialDistribution_realEdge
          C scale u (hφ.2 hu) χ]
        rfl
      · have hφ_zero : φ u = 0 :=
          image_eq_zero_of_notMem_tsupport hu
        simp [hφ_zero]
  have heq := tendsto_nhds_unique hcurrent hlimit
  calc
    ((anchoredOrderedTransportDistribution C.current anchor).comp
        (section43OrderedPullbackTimeSpatialTensorCLM
          d (q + 1) χ)) φ =
        C.current
          (section43NPointTimeSpatialTensor d (q + 1)
            (SCV.translateSchwartz (-anchor) φ) χ) := by
      simpa only [ContinuousLinearMap.comp_apply] using
        anchoredOrderedTransportDistribution_orderedPullbackTimeSpatialTensor
          C.current anchor χ φ
    _ = ∫ u : Fin (q + 1) → ℝ,
          D.vacuumTailLimitSpatialDistribution
              (SCV.realToComplex u) χ *
            φ u := by
      simpa [T, ContinuousLinearMap.comp_apply] using heq

/-- Vacuum pairing of the source-linear packet limit is weakly holomorphic. -/
theorem vacuumTailLimitSpatialDistribution_weaklyHolomorphic
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A) :
    OSIIWeaklyHolomorphicOn
      D.vacuumTailLimitSpatialDistribution
      D.spatialLinearDomain := by
  intro χ
  have hfield :=
    fixedHeadAnchoredSpatialHilbertFieldLimit_holomorphic
      D (vacuumTailSpatialLiftCLM χ)
  exact
    ((differentiableOn_const
      (c := innerSL ℂ (osiiChapterVVacuumVector OS))).clm_apply
        hfield).congr fun z hz => by
          exact
            (D.vacuumTailLimitSpatialDistribution_apply_of_mem
              z hz χ)

/-- The limiting vacuum-tail field as a scalar continuation-stage candidate
on the complete source-linear anchored domain. -/
noncomputable def vacuumTailLimitStage
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A) :
    OSIITimeContinuationStage d (q + 1) where
  carrier := D.spatialLinearDomain
  carrier_open := D.spatialLinearDomain_open
  distribution := D.vacuumTailLimitSpatialDistribution
  weaklyHolomorphic :=
    D.vacuumTailLimitSpatialDistribution_weaklyHolomorphic

end PositiveHeadUniversalAnchoredAtlasData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
