/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapFullSourceRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalReducedSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIINarrowTimeStageChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedFiberMarginalSchwartz




















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- The canonical full source, viewed as a continuous linear map in the
reduced-time Schwartz factor for one fixed reduced spatial test.  This is the
time-shell presentation dual to `initialReducedSpatialFullSourceCLM`; keeping
the full reduced-time tuple as one input is essential because its coordinates
are coupled after the lift to absolute spacetime variables. -/
noncomputable def initialReducedTimeFullSourceCLM
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1) :=
  (BHW.reducedTestLift k d
      (BHW.normalizedCutoffOfBump d).toSchwartz).comp
    (section43TimeSpatialTensorCLM d k χ)

@[simp] theorem initialReducedTimeFullSourceCLM_apply
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ) :
    initialReducedTimeFullSourceCLM (d := d) χ φ =
      BHW.reducedTestLift k d
        (BHW.normalizedCutoffOfBump d).toSchwartz
        (section43NPointTimeSpatialTensor d k φ χ) :=
  rfl

/-- The canonical full source associated with a fixed reduced-time factor and
an arbitrary reduced spatial Schwartz test. -/
noncomputable def initialReducedSpatialFullSourceCLM
    (φ : SchwartzMap (Fin k → ℝ) ℂ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1) :=
  (BHW.reducedTestLift k d
      (BHW.normalizedCutoffOfBump d).toSchwartz).comp
    (section43TimeSpatialTensorSpatialCLM d k φ)

@[simp] theorem initialReducedSpatialFullSourceCLM_apply
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    initialReducedSpatialFullSourceCLM (d := d) φ χ =
      BHW.reducedTestLift k d
        (BHW.normalizedCutoffOfBump d).toSchwartz
        (section43NPointTimeSpatialTensor d k φ χ) :=
  rfl

@[simp] theorem initialReducedTimeFullSourceCLM_apply_eq_spatial
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ) :
    initialReducedTimeFullSourceCLM (d := d) χ φ =
      initialReducedSpatialFullSourceCLM (d := d) φ χ :=
  rfl

@[simp] theorem initialReducedSpatialFullSourceCLM_apply_point
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (y : NPointDomain d (k + 1)) :
    initialReducedSpatialFullSourceCLM (d := d) φ χ y =
      (BHW.normalizedCutoffOfBump d).toSchwartz (y 0) *
        (φ (reducedTimeProjectionCLM d k y) *
          χ (section43QSpatial (d := d) (n := k)
            (BHW.reducedDiffMapReal (k + 1) d y))) := by
  simp [initialReducedSpatialFullSourceCLM,
    BHW.reducedTestLift_apply,
    section43NPointTimeSpatialTensor_apply,
    reducedTimeProjectionCLM_apply, mul_assoc]

/-- Every point in the support of the canonical full source has reduced-time
coordinate in the support of its fixed reduced-time factor. -/
theorem reducedTimeProjection_mem_tsupport_of_mem_initialReducedSpatialFullSource
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (x : NPointDomain d (k + 1))
    (hx :
      x ∈ tsupport
        ((initialReducedSpatialFullSourceCLM (d := d) φ χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ)) :
    reducedTimeProjectionCLM d k x ∈
      tsupport (φ : (Fin k → ℝ) → ℂ) := by
  have hdiff :
      BHW.reducedDiffMapRealCLM (k + 1) d x ∈
        tsupport
          ((section43NPointTimeSpatialTensor d k φ χ :
              SchwartzNPoint d k) :
            NPointDomain d k → ℂ) :=
    reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      (BHW.normalizedCutoffOfBump d).toSchwartz
      (section43NPointTimeSpatialTensor d k φ χ) hx
  have htime :=
    tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
      d k φ χ hdiff
  simpa [reducedTimeProjectionCLM_apply,
    BHW.reducedDiffMapRealCLM] using htime

/-- Strict-positive support of the reduced-time factor forces strict ordering
of all absolute Euclidean times on the canonical source support, hence the
source vanishes to infinite order on every coincidence locus. -/
theorem initialReducedSpatialFullSource_vanishes_of_tsupport_strictPositive
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k) :
    VanishesToInfiniteOrderOnCoincidence
      (initialReducedSpatialFullSourceCLM (d := d) φ χ) := by
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  refine Set.disjoint_left.2 ?_
  intro y hy hcoin
  have hdiff :
      BHW.reducedDiffMapRealCLM (k + 1) d y ∈
        tsupport
          ((section43NPointTimeSpatialTensor d k φ χ :
              SchwartzNPoint d k) :
            NPointDomain d k → ℂ) :=
    reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      (BHW.normalizedCutoffOfBump d).toSchwartz
      (section43NPointTimeSpatialTensor d k φ χ) hy
  have htime_support :
      reducedTimeProjectionCLM d k y ∈
        tsupport (φ : (Fin k → ℝ) → ℂ) := by
    have htime :=
      tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
        d k φ χ hdiff
    simpa [reducedTimeProjectionCLM_apply,
      BHW.reducedDiffMapRealCLM] using htime
  have hgap : ∀ i : Fin k, 0 < y i.succ 0 - y i.castSucc 0 := by
    intro i
    have hi := hφ_positive htime_support i
    have hi' :
        0 <
          BHW.reducedDiffMapReal (k + 1) d y
            ⟨i.val, by omega⟩ 0 := by
      simpa [reducedTimeProjectionCLM_apply, section43QTime,
        nPointTimeSpatialCLE] using hi
    change 0 < y i.succ 0 - y i.castSucc 0 at hi'
    exact hi'
  have htime : StrictMono (fun i : Fin (k + 1) => y i 0) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact sub_pos.mp (hgap i)
  rcases hcoin with ⟨i, j, hij, hyeq⟩
  have htEq : y i 0 = y j 0 :=
    congrArg (fun z : SpacetimeDim d => z 0) hyeq
  exact hij (htime.injective htEq)

/-- The point at which an unlocalized source is evaluated after the packet's
independent chronological translations. -/
noncomputable def chronologicalSourceEvaluationConfiguration
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (y : NPointDomain d (k + 1)) :
    NPointDomain d (k + 1) :=
  y + fun i => -osiiAxisPairChronologicalPointTranslation T x i

/-- Consecutive differences underneath the translated source are the original
differences minus the independently prescribed chronological gaps. -/
theorem reducedDiffMapReal_chronologicalSourceEvaluationConfiguration
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (y : NPointDomain d (k + 1)) :
    BHW.reducedDiffMapReal (k + 1) d
        (chronologicalSourceEvaluationConfiguration T x y) =
      BHW.reducedDiffMapReal (k + 1) d y -
        fun i =>
          osiiAxisPairChronologicalGapTranslation T x
            ⟨i.val, by omega⟩ := by
  ext i μ
  let j : Fin k := ⟨i.val, by omega⟩
  rw [BHW.reducedDiffMapReal_apply]
  simp only [Pi.sub_apply]
  rw [BHW.reducedDiffMapReal_apply]
  change
    (y i.succ μ -
          osiiAxisPairChronologicalPointTranslation T x i.succ μ) -
        (y i.castSucc μ -
          osiiAxisPairChronologicalPointTranslation T x i.castSucc μ) =
      (y i.succ μ - y i.castSucc μ) -
        osiiAxisPairChronologicalGapTranslation T x j μ
  have hgap :=
    congrFun
      (osiiAxisPairChronologicalPointTranslation_sub_castSucc
        (d := d) T x j) μ
  simp only [Pi.sub_apply] at hgap
  have hsucc : i.succ = j.succ := by
    apply Fin.ext
    rfl
  have hcastSucc : i.castSucc = j.castSucc := by
    apply Fin.ext
    rfl
  rw [hsucc, hcastSucc]
  linarith

/-- On the narrow pure-time real slice, chronological source translation
subtracts the prescribed gap-time vector from the reduced-time coordinates. -/
theorem reducedTimeProjectionCLM_chronologicalSourceEvaluationConfiguration_narrow
    (T : ℝ) (hT : 0 < T)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k)
    (y : NPointDomain d (k + 1)) :
    reducedTimeProjectionCLM d k
        (chronologicalSourceEvaluationConfiguration T
          (osiiNarrowTimeRealCoordinate (d := d) T τ) y) =
      reducedTimeProjectionCLM d k y - τ := by
  rw [reducedTimeProjectionCLM_apply,
    reducedTimeProjectionCLM_apply,
    reducedDiffMapReal_chronologicalSourceEvaluationConfiguration]
  have hgap :
      (fun i : Fin (k + 1 - 1) =>
        osiiAxisPairChronologicalGapTranslation T
          (osiiNarrowTimeRealCoordinate (d := d) T τ)
          ⟨i.val, by omega⟩) =
        fun i =>
          osiiPureTimeReal (d := d) (τ ⟨i.val, by omega⟩) := by
    funext i
    exact osiiNarrowTimeRealCoordinate_gapTranslation
      T hT τ hτ ⟨i.val, by omega⟩
  rw [hgap]
  ext i
  change
    BHW.reducedDiffMapReal (k + 1) d y i 0 -
        osiiPureTimeReal (d := d) (τ i) 0 =
      BHW.reducedDiffMapReal (k + 1) d y i 0 - τ i
  simp [osiiPureTimeReal]

/-- On the narrow pure-time real slice, chronological source translation
does not change any reduced spatial coordinate. -/
theorem section43QSpatial_reducedDiffMapReal_chronologicalSourceEvaluationConfiguration_narrow
    (T : ℝ) (hT : 0 < T)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k)
    (y : NPointDomain d (k + 1)) :
    section43QSpatial (d := d) (n := k)
        (BHW.reducedDiffMapReal (k + 1) d
          (chronologicalSourceEvaluationConfiguration T
            (osiiNarrowTimeRealCoordinate (d := d) T τ) y)) =
      section43QSpatial (d := d) (n := k)
        (BHW.reducedDiffMapReal (k + 1) d y) := by
  rw [reducedDiffMapReal_chronologicalSourceEvaluationConfiguration]
  have hgap :
      (fun i : Fin (k + 1 - 1) =>
        osiiAxisPairChronologicalGapTranslation T
          (osiiNarrowTimeRealCoordinate (d := d) T τ)
          ⟨i.val, by omega⟩) =
        fun i =>
          osiiPureTimeReal (d := d) (τ ⟨i.val, by omega⟩) := by
    funext i
    exact osiiNarrowTimeRealCoordinate_gapTranslation
      T hT τ hτ ⟨i.val, by omega⟩
  rw [hgap]
  apply (EuclideanSpace.equiv
    (ι := Fin k × Fin d) (𝕜 := ℝ)).injective
  funext p
  rw [section43QSpatial_apply, section43QSpatial_apply]
  change
    BHW.reducedDiffMapReal (k + 1) d y p.1 p.2.succ -
        osiiPureTimeReal (d := d) (τ p.1) p.2.succ =
      BHW.reducedDiffMapReal (k + 1) d y p.1 p.2.succ
  simp [osiiPureTimeReal]

/-- On the narrow pure-time real slice, translating the canonical absolute
source is exactly translation of its reduced-time Schwartz factor by `-τ`.
The normalized basepoint factor and reduced spatial factor are unchanged. -/
theorem translate_initialReducedSpatialFullSource_narrow
    (T : ℝ) (hT : 0 < T)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    translateSchwartzConfiguration
        (fun i =>
          -osiiAxisPairChronologicalPointTranslation T
            (osiiNarrowTimeRealCoordinate (d := d) T τ) i)
        (initialReducedSpatialFullSourceCLM (d := d) φ χ) =
      initialReducedSpatialFullSourceCLM (d := d)
        (SCV.translateSchwartz (-τ) φ) χ := by
  ext y
  rw [translateSchwartzConfiguration_apply,
    initialReducedSpatialFullSourceCLM_apply_point,
    initialReducedSpatialFullSourceCLM_apply_point]
  change
    (BHW.normalizedCutoffOfBump d).toSchwartz
          (chronologicalSourceEvaluationConfiguration T
            (osiiNarrowTimeRealCoordinate (d := d) T τ) y 0) *
        (φ (reducedTimeProjectionCLM d k
              (chronologicalSourceEvaluationConfiguration T
                (osiiNarrowTimeRealCoordinate (d := d) T τ) y)) *
          χ (section43QSpatial (d := d) (n := k)
            (BHW.reducedDiffMapReal (k + 1) d
              (chronologicalSourceEvaluationConfiguration T
                (osiiNarrowTimeRealCoordinate (d := d) T τ) y)))) =
      (BHW.normalizedCutoffOfBump d).toSchwartz (y 0) *
        ((SCV.translateSchwartz (-τ) φ)
            (reducedTimeProjectionCLM d k y) *
          χ (section43QSpatial (d := d) (n := k)
            (BHW.reducedDiffMapReal (k + 1) d y)))
  have hbase :
      chronologicalSourceEvaluationConfiguration T
          (osiiNarrowTimeRealCoordinate (d := d) T τ) y 0 =
        y 0 := by
    simp [chronologicalSourceEvaluationConfiguration]
  rw [hbase,
    reducedTimeProjectionCLM_chronologicalSourceEvaluationConfiguration_narrow
      T hT τ hτ y,
    section43QSpatial_reducedDiffMapReal_chronologicalSourceEvaluationConfiguration_narrow
      T hT τ hτ y,
    SCV.translateSchwartz_apply, sub_eq_add_neg]

/-- The translated carrier is the configuration translation of the fixed
untranslated product carrier by the same displacement used on full sources. -/
theorem chronologicalTranslatedCarrier_eq_translate_base
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    F.chronologicalTranslatedCarrier T x =
      translateSchwartzConfiguration
        (fun i => -osiiAxisPairChronologicalPointTranslation T x i)
        (SchwartzMap.productTensor F.factors) := by
  symm
  rw [OSIIChronologicalCompactFactors.chronologicalTranslatedCarrier]
  change
    translateSchwartzConfiguration
        (fun i => -osiiAxisPairChronologicalPointTranslation T x i)
        (SchwartzMap.productTensor F.factors) =
      SchwartzMap.productTensor
        (fun j => SCV.translateSchwartz
          (-osiiAxisPairChronologicalPointTranslation T x j)
          (F.factors j))
  exact
    translateSchwartzConfiguration_productTensor
      (d := d)
      (fun i => -osiiAxisPairChronologicalPointTranslation T x i)
      F.factors

/-- If multiplication by the untranslated product carrier fixes a full
source, then translating carrier and source together makes packet
localization exactly the translated source.  This is the source-map form used
for partition-of-unity pieces. -/
theorem sourcewiseLocalizedTranslatedFullCLM_eq_translate_of_fixed
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (f : SchwartzNPoint d (k + 1))
    (hfixed :
      SchwartzMap.smulLeftCLM ℂ
          (SchwartzMap.productTensor F.factors) f =
        f) :
    F.sourcewiseLocalizedTranslatedFullCLM T x f =
      translateSchwartzConfiguration
        (fun i => -osiiAxisPairChronologicalPointTranslation T x i) f := by
  ext y
  rw [OSIIChronologicalCompactFactors.sourcewiseLocalizedTranslatedFullCLM,
    ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (F.chronologicalTranslatedCarrier T x).hasTemperateGrowth,
    translateSchwartzConfigurationCLM_apply]
  let z := chronologicalSourceEvaluationConfiguration T x y
  have htranslated :
      translateSchwartzConfiguration
          (fun i => -osiiAxisPairChronologicalPointTranslation T x i) f y =
        f z := by
    rfl
  have hcarrier_eval :
      F.chronologicalTranslatedCarrier T x y =
        SchwartzMap.productTensor F.factors z := by
    rw [chronologicalTranslatedCarrier_eq_translate_base,
      translateSchwartzConfiguration_apply]
    rfl
  have hfixed_eval :=
    congrArg
      (fun g : SchwartzNPoint d (k + 1) => g z)
      hfixed
  change
    (SchwartzMap.smulLeftCLM ℂ
        (SchwartzMap.productTensor F.factors) f) z =
      f z at hfixed_eval
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (SchwartzMap.productTensor F.factors).hasTemperateGrowth]
    at hfixed_eval
  rw [htranslated, hcarrier_eval]
  simpa only [smul_eq_mul] using hfixed_eval

end OSIIChapterV
end OSReconstruction
