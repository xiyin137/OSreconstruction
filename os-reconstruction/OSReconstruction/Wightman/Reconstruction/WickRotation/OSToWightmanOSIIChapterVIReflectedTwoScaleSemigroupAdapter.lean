/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedTwoScaleSourceIntegralBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCompactCenterTimeCarrier
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetRankField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicGeneratorDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBranchGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedRootedSuccessor
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitRankGenerator
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedTarget
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceAdapter
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDifferenceReducedSupport
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetCutoffHullRankField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceDistribution
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialCoherentTarget
import OSReconstruction.SCV.SchwartzFiniteSeminormBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairCompactSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerFunctional
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIWeightedReflectedRankFieldIdentification















noncomputable section

open Complex Set
open scoped Classical Pointwise

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

variable {d q : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- Internal chronological displacement from one packet center to another.
The missing zeroth coordinate is the common Euclidean time shift. -/
def chronologicalPacketInternalRecentering
    {k : Nat}
    (anchor center : Fin (k + 1) -> Real) : Fin k -> Real :=
  fun i => center i.succ - anchor i.succ

/-- Common Euclidean time displacement from one packet center to another. -/
def chronologicalPacketFirstTimeRecentering
    {k : Nat}
    (anchor center : Fin (k + 1) -> Real) : Real :=
  center 0 - anchor 0

/-- The packet center obtained after only the internal chronological
recentering. Its first difference-time coordinate remains at the canonical
anchor, while every later coordinate is already at the new center. -/
def chronologicalPacketInternalCenter
    {k : Nat}
    (anchor center : Fin (k + 1) -> Real) : Fin (k + 1) -> Real :=
  Fin.cons (anchor 0) (fun i => center i.succ)

@[simp]
theorem chronologicalPacketInternalCenter_zero
    {k : Nat}
    (anchor center : Fin (k + 1) -> Real) :
    chronologicalPacketInternalCenter anchor center 0 = anchor 0 := by
  rfl

@[simp]
theorem chronologicalPacketInternalCenter_succ
    {k : Nat}
    (anchor center : Fin (k + 1) -> Real)
    (i : Fin k) :
    chronologicalPacketInternalCenter anchor center i.succ = center i.succ := by
  rfl

theorem chronologicalPacketInternalCenter_mem_strictPositive
    {k : Nat}
    {anchor center : Fin (k + 1) -> Real}
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion (k + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion (k + 1)) :
    chronologicalPacketInternalCenter anchor center ∈
      section43TimeStrictPositiveRegion (k + 1) := by
  intro j
  refine Fin.cases ?_ ?_ j
  · simpa using hanchor 0
  · intro i
    simpa using hcenter i.succ

/-- Chronological source translation changes exactly the noninitial time
coordinates of an ordered time/spatial tensor. -/
theorem translateSchwartzConfiguration_orderedPullback_chronological
    {k : Nat}
    (u : Fin k -> Real)
    (chi : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (phi : SchwartzMap (Fin (k + 1) -> Real) Complex) :
    translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i) u)
        (section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) chi phi) =
      section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) chi
        (SCV.translateSchwartz (fun j => -Fin.cases 0 u j) phi) := by
  ext x
  rw [translateSchwartzConfiguration_apply,
    section43OrderedPullbackTimeSpatialTensorCLM_apply,
    section43OrderedPullbackTimeSpatialTensorCLM_apply]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, section43NPointTimeSpatialTensor_apply,
    SCV.translateSchwartz_apply]
  rw [chronologicalSourceParameterDisplacement_diff_time,
    chronologicalSourceParameterDisplacement_diff_spatial]
  congr 2

/-- A translated packet at `center` is exactly the packet at `anchor`,
translated in its internal chronological coordinates and then by the common
forward time displacement. -/
theorem timeShift_chronologicalTranslate_translatedPositiveTimeSpatialSource
    {k : Nat}
    (I : Section43ProductTimeApproximateIdentity (k + 1))
    (anchor center : Fin (k + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion (k + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion (k + 1))
    (chi : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (N : Nat) :
    timeShiftSchwartzNPoint (d := d)
        (chronologicalPacketFirstTimeRecentering anchor center)
        (translateSchwartzConfiguration
          (sourceParameterDisplacementCLM
            (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
            (chronologicalPacketInternalRecentering anchor center))
          (I.translatedPositiveTimeSpatialSource anchor hanchor chi N).1) =
      (I.translatedPositiveTimeSpatialSource center hcenter chi N).1 := by
  rw [translatedPositiveTimeSpatialSource_coe,
    translateSchwartzConfiguration_orderedPullback_chronological,
    timeShift_orderedPullbackTimeSpatialTensorCLM_eq_translate_firstTime
      (d := d) (Nat.succ_pos k),
    translatedPositiveTimeSpatialSource_coe]
  congr 1
  simp only [SCV.translateSchwartz_translateSchwartz]
  congr 1
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [section43FirstTimeShift,
      chronologicalPacketFirstTimeRecentering]
    ring
  · intro i
    simp [section43FirstTimeShift,
      chronologicalPacketInternalRecentering]
    ring

/-- The internal chronological recenter is itself the exact translated packet
at the hybrid center. In particular, its positive-time certificate is not an
extra analytic hypothesis. -/
theorem chronologicalTranslate_translatedPositiveTimeSpatialSource_eq_internalCenter
    {k : Nat}
    (I : Section43ProductTimeApproximateIdentity (k + 1))
    (anchor center : Fin (k + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion (k + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion (k + 1))
    (chi : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (N : Nat) :
    translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
          (chronologicalPacketInternalRecentering anchor center))
        (I.translatedPositiveTimeSpatialSource anchor hanchor chi N).1 =
      (I.translatedPositiveTimeSpatialSource
        (chronologicalPacketInternalCenter anchor center)
        (chronologicalPacketInternalCenter_mem_strictPositive hanchor hcenter)
        chi N).1 := by
  have h :=
    timeShift_chronologicalTranslate_translatedPositiveTimeSpatialSource
      I anchor (chronologicalPacketInternalCenter anchor center)
      hanchor
      (chronologicalPacketInternalCenter_mem_strictPositive hanchor hcenter)
      chi N
  have hzeroShift (f : SchwartzNPoint d (k + 1)) :
      timeShiftSchwartzNPoint (d := d) 0 f = f := by
    ext y
    apply congrArg f
    funext i mu
    simp [timeShiftVec]
  simpa [chronologicalPacketFirstTimeRecentering,
    chronologicalPacketInternalRecentering,
    chronologicalPacketInternalCenter, hzeroShift] using h

/-- Configuration translations commute with a common Euclidean time shift. -/
theorem translateSchwartzConfiguration_timeShiftSchwartzNPoint
    {n : Nat}
    (a : NPointDomain d n)
    (t : Real)
    (f : SchwartzNPoint d n) :
    translateSchwartzConfiguration a (timeShiftSchwartzNPoint (d := d) t f) =
      timeShiftSchwartzNPoint (d := d) t
        (translateSchwartzConfiguration a f) := by
  ext x
  simp only [translateSchwartzConfiguration_apply,
    timeShiftSchwartzNPoint_apply]
  apply congrArg f
  funext j mu
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Recentered source identity after an additional chronological parameter.
This is the real-edge formula used by the holomorphic field transport. -/
theorem timeShift_chronologicalTranslate_add_translatedPositiveTimeSpatialSource
    {k : Nat}
    (I : Section43ProductTimeApproximateIdentity (k + 1))
    (anchor center : Fin (k + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion (k + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion (k + 1))
    (chi : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (N : Nat)
    (x : Fin k -> Real) :
    timeShiftSchwartzNPoint (d := d)
        (chronologicalPacketFirstTimeRecentering anchor center)
        (translateSchwartzConfiguration
          (sourceParameterDisplacementCLM
            (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
            (chronologicalPacketInternalRecentering anchor center + x))
          (I.translatedPositiveTimeSpatialSource anchor hanchor chi N).1) =
      translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i) x)
        (I.translatedPositiveTimeSpatialSource center hcenter chi N).1 := by
  let directions : Fin k -> NPointDomain d (k + 1) :=
    fun i => chronologicalTimeSourceDirection (d := d) i
  have hsum :
      sourceParameterDisplacementCLM directions
          (chronologicalPacketInternalRecentering anchor center + x) =
        sourceParameterDisplacementCLM directions x +
          sourceParameterDisplacementCLM directions
            (chronologicalPacketInternalRecentering anchor center) := by
    rw [map_add]
    exact add_comm _ _
  rw [hsum,
    <- translateSchwartzConfiguration_translateSchwartzConfiguration,
    <- translateSchwartzConfiguration_timeShiftSchwartzNPoint]
  rw [timeShift_chronologicalTranslate_translatedPositiveTimeSpatialSource
    I anchor center hanchor hcenter chi N]

/-- The real OS time-shift operator extended to a nonnegative parameter by
the identity at zero. -/
noncomputable def osNonnegativeTimeShiftHilbert
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (t : Real)
    (ht : 0 <= t) : OSHilbertSpace OS →L[Complex] OSHilbertSpace OS :=
  if hzero : t = 0 then
    ContinuousLinearMap.id Complex (OSHilbertSpace OS)
  else
    osTimeShiftHilbert (d := d) OS lgc t (lt_of_le_of_ne ht (Ne.symm hzero))

/-- At positive time the real source-shift operator is the original-OS
complex semigroup, on the entire Hilbert completion. -/
theorem osNonnegativeTimeShiftHilbert_eq_complex_of_pos
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {t : Real} (ht : 0 < t) :
    osNonnegativeTimeShiftHilbert OS lgc t ht.le =
      osiiOriginalOSHilbertComplex OS (t : Complex) := by
  rw [osNonnegativeTimeShiftHilbert, dif_neg ht.ne',
    osTimeShiftHilbert_eq_ofOS,
    osiiOriginalOSHilbertComplex_ofReal_eq_shift OS t ht]

/-- The nonnegative real OS time-shift acts on every homogeneous
positive-time vector by translating its source. No compact spatial support is
required. -/
theorem osNonnegativeTimeShiftHilbert_single_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : Nat}
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n -> Complex) ⊆
      OrderedPositiveTimeRegion d n)
    (t : Real)
    (ht : 0 <= t) :
    osNonnegativeTimeShiftHilbert OS lgc t ht
        (osiiPositiveTimeSingleVectorCLM OS n ⟨f, hf⟩) =
      osiiPositiveTimeSingleVectorCLM OS n
        ⟨timeShiftSchwartzNPoint (d := d) t f,
          osiiEuclideanTranslation_preserves_orderedPositive
            (timeShiftVec d t) (by simpa [timeShiftVec] using ht) f hf⟩ := by
  by_cases hzero : t = 0
  · subst t
    simp only [osNonnegativeTimeShiftHilbert, dif_pos rfl,
      ContinuousLinearMap.id_apply]
    apply congrArg (osiiPositiveTimeSingleVectorCLM OS n)
    apply Subtype.ext
    ext x
    apply congrArg f
    funext i mu
    simp [timeShiftVec]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    let ft : euclideanPositiveTimeSubmodule (d := d) n :=
      ⟨timeShiftSchwartzNPoint (d := d) t f,
        osiiEuclideanTranslation_preserves_orderedPositive
          (timeShiftVec d t) (by simpa [timeShiftVec] using ht) f hf⟩
    have hft := ft.2
    change tsupport (ft.1 : NPointDomain d n → Complex) ⊆
      OrderedPositiveTimeRegion d n at hft
    simp only [osNonnegativeTimeShiftHilbert, dif_neg hzero]
    let x₀ : OSPreHilbertSpace OS :=
      ⟦PositiveTimeBorchersSequence.single n f hf⟧
    rw [osiiPositiveTimeSingleVectorCLM_apply]
    change osTimeShiftHilbert (d := d) OS lgc t htpos
      (x₀ : OSHilbertSpace OS) = osiiPositiveTimeSingleVectorCLM OS n ft
    rw [osTimeShiftHilbert_coe]
    rw [osiiPositiveTimeSingleVectorCLM_apply]
    apply congrArg (fun x : OSPreHilbertSpace OS => (x : OSHilbertSpace OS))
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro k
    change
      (timeShiftPositiveTimeBorchers t htpos
        (PositiveTimeBorchersSequence.single n f hf)).toBorchersSequence.funcs k =
      (PositiveTimeBorchersSequence.single n ft.1 hft).toBorchersSequence.funcs k
    by_cases hk : k = n
    · subst k
      rw [PositiveTimeBorchersSequence.single_toBorchersSequence]
      simp [BorchersSequence.single]
      rfl
    · rw [PositiveTimeBorchersSequence.single_toBorchersSequence]
      simp [BorchersSequence.single, hk]

/-- Near the real origin, the source vector centered at `center` is the
nonnegative OS time shift of the canonical-anchor source vector evaluated at
the internally recentered chronological parameter. -/
theorem eventually_centeredSourceVector_eq_nonnegativeTimeShift_recentered
    {k : Nat}
    (I : Section43ProductTimeApproximateIdentity (k + 1))
    (anchor center : Fin (k + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion (k + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion (k + 1))
    (chi : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (N : Nat)
    (lgc : OSLinearGrowthCondition d OS)
    (hfirst : anchor 0 <= center 0) :
    let directions : Fin k -> NPointDomain d (k + 1) :=
      fun i => chronologicalTimeSourceDirection (d := d) i
    let u := chronologicalPacketInternalRecentering anchor center
    let t := chronologicalPacketFirstTimeRecentering anchor center
    let anchorSource :=
      I.translatedPositiveTimeSpatialSource anchor hanchor chi N
    let centerSource :=
      I.translatedPositiveTimeSpatialSource center hcenter chi N
    ∀ᶠ x : Fin k -> Real in nhds 0,
      osNonnegativeTimeShiftHilbert OS lgc t
          (by simpa [t, chronologicalPacketFirstTimeRecentering] using
            sub_nonneg.mpr hfirst)
          (osiiPositiveTimeSingleVectorCLM OS (k + 1)
            (localPositiveTimeParameterTranslate anchorSource directions
              (u + x))) =
        osiiPositiveTimeSingleVectorCLM OS (k + 1)
          (localPositiveTimeParameterTranslate centerSource directions x) := by
  dsimp only
  let directions : Fin k -> NPointDomain d (k + 1) :=
    fun i => chronologicalTimeSourceDirection (d := d) i
  let u := chronologicalPacketInternalRecentering anchor center
  let t := chronologicalPacketFirstTimeRecentering anchor center
  let anchorSource :=
    I.translatedPositiveTimeSpatialSource anchor hanchor chi N
  let centerSource :=
    I.translatedPositiveTimeSpatialSource center hcenter chi N
  let internalCenter := chronologicalPacketInternalCenter anchor center
  let hinternalCenter :=
    chronologicalPacketInternalCenter_mem_strictPositive hanchor hcenter
  let internalSource :=
    I.translatedPositiveTimeSpatialSource internalCenter hinternalCenter chi N
  have hcenterCompact :
      HasCompactStrictPositiveDifferenceTimeSupport centerSource.1 := by
    simpa [centerSource, translatedPositiveTimeSpatialSource] using
      (section43PositiveTimeSpatialSource_hasCompactStrictPositiveDifferenceTimeSupport
        d (k + 1) (I.translatedSource center hcenter N) chi)
  have hinternalCompact :
      HasCompactStrictPositiveDifferenceTimeSupport internalSource.1 := by
    simpa [internalSource, internalCenter, hinternalCenter,
      translatedPositiveTimeSpatialSource] using
      (section43PositiveTimeSpatialSource_hasCompactStrictPositiveDifferenceTimeSupport
        d (k + 1)
        (I.translatedSource
          (chronologicalPacketInternalCenter anchor center)
          (chronologicalPacketInternalCenter_mem_strictPositive hanchor hcenter)
          N) chi)
  have hcenterEvent :=
    eventually_localPositiveTimeParameterTranslate_chronological_coe_eq
      centerSource hcenterCompact
  have hinternalEvent :=
    eventually_localPositiveTimeParameterTranslate_chronological_coe_eq
      internalSource hinternalCompact
  have ht : 0 <= t := by
    simpa [t, chronologicalPacketFirstTimeRecentering] using
      sub_nonneg.mpr hfirst
  filter_upwards [hcenterEvent, hinternalEvent] with x hxcenter hxinternal
  have hbaseInternal :
      translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions u) anchorSource.1 =
        internalSource.1 := by
    simpa [directions, u, anchorSource, internalSource, internalCenter,
      hinternalCenter] using
      chronologicalTranslate_translatedPositiveTimeSpatialSource_eq_internalCenter
        I anchor center hanchor hcenter chi N
  have hrawAnchorInternal :
      translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions (u + x)) anchorSource.1 =
        translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions x) internalSource.1 := by
    calc
      translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions (u + x)) anchorSource.1 =
        translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions u +
            sourceParameterDisplacementCLM directions x) anchorSource.1 := by
              rw [map_add]
      _ = translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions x +
            sourceParameterDisplacementCLM directions u) anchorSource.1 := by
              exact congrArg
                (fun a : NPointDomain d (k + 1) =>
                  translateSchwartzConfiguration a anchorSource.1)
                (add_comm
                  (sourceParameterDisplacementCLM directions u)
                  (sourceParameterDisplacementCLM directions x))
      _ = translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions x)
          (translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions u) anchorSource.1) := by
              rw [translateSchwartzConfiguration_translateSchwartzConfiguration]
      _ = translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions x) internalSource.1 := by
              rw [hbaseInternal]
  have hrawAnchorPositive :
      tsupport
          ((translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions (u + x))
            anchorSource.1 : SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) -> Complex) ⊆
        OrderedPositiveTimeRegion d (k + 1) := by
    rw [hrawAnchorInternal, <- hxinternal]
    exact (localPositiveTimeParameterTranslate internalSource directions x).2
  have hanchorLocal :
      localPositiveTimeParameterTranslate anchorSource directions (u + x) =
        localPositiveTimeParameterTranslate internalSource directions x := by
    apply Subtype.ext
    simp only [localPositiveTimeParameterTranslate]
    rw [dif_pos hrawAnchorPositive]
    exact hrawAnchorInternal.trans hxinternal.symm
  have hshiftRaw :=
    timeShift_chronologicalTranslate_add_translatedPositiveTimeSpatialSource
      I anchor center hanchor hcenter chi N x
  have hshiftSource :
      (⟨timeShiftSchwartzNPoint (d := d) t
          (localPositiveTimeParameterTranslate anchorSource directions
            (u + x)).1,
        osiiEuclideanTranslation_preserves_orderedPositive
          (timeShiftVec d t) (by simpa [timeShiftVec] using ht)
          (localPositiveTimeParameterTranslate anchorSource directions
            (u + x)).1
          (localPositiveTimeParameterTranslate anchorSource directions
            (u + x)).2⟩ :
          euclideanPositiveTimeSubmodule (d := d) (k + 1)) =
        localPositiveTimeParameterTranslate centerSource directions x := by
    apply Subtype.ext
    calc
      timeShiftSchwartzNPoint (d := d) t
          (localPositiveTimeParameterTranslate anchorSource directions
            (u + x)).1 =
        timeShiftSchwartzNPoint (d := d) t
          (localPositiveTimeParameterTranslate internalSource directions x).1 :=
            congrArg (timeShiftSchwartzNPoint (d := d) t)
              (congrArg Subtype.val hanchorLocal)
      _ = timeShiftSchwartzNPoint (d := d) t
          (translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions x) internalSource.1) :=
            congrArg (timeShiftSchwartzNPoint (d := d) t) hxinternal
      _ = timeShiftSchwartzNPoint (d := d) t
          (translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions (u + x))
            anchorSource.1) :=
            congrArg (timeShiftSchwartzNPoint (d := d) t)
              hrawAnchorInternal.symm
      _ = translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions x) centerSource.1 := by
            simpa [directions, u, t, anchorSource, centerSource] using hshiftRaw
      _ = (localPositiveTimeParameterTranslate centerSource directions x).1 :=
            hxcenter.symm
  have hop :=
    osNonnegativeTimeShiftHilbert_single_eq OS lgc
      (localPositiveTimeParameterTranslate anchorSource directions
        (u + x)).1
      (localPositiveTimeParameterTranslate anchorSource directions
        (u + x)).2 t ht
  rw [hshiftSource] at hop
  simpa [directions, u, t, anchorSource, centerSource] using hop

set_option maxHeartbeats 1000000 in
/-- Local source-atlas transport for a packet center whose first time moves
forward.  Internal chronological recentering is absorbed into the complex
coordinate, while the remaining first-time displacement is the nonnegative
OS semigroup operator. -/
theorem anchoredAtlasField_nonnegativeTimeShift_recenter_eq_of_small
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {k : Nat}
    (source : ReflectedGramSpatialSourceData (OS := OS) S k)
    (I : Section43ProductTimeApproximateIdentity ((k + 1) + 1))
    (anchor center : Fin ((k + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((k + 1) + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion ((k + 1) + 1))
    (hfirst : anchor 0 <= center 0)
    (anchorBase centerBase : UniformCompactTimeSource
      d ((k + 1) + 1) source.carrier)
    (scale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((k + 1) + 1)) Complex)
    (hanchorBase : UniformCompactTimeSource.source anchorBase =
      I.translatedPositiveTimeSpatialSource anchor hanchor chi scale)
    (hcenterBase : UniformCompactTimeSource.source centerBase =
      I.translatedPositiveTimeSpatialSource center hcenter chi scale)
    (lgc : OSLinearGrowthCondition d OS)
    (huReal : chronologicalPacketInternalRecentering anchor center ∈
      source.reflectedGram.atlas.gram.anchoredAtlasRealRegion
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ)
    (huKernel :
      (fun i =>
        (chronologicalPacketInternalRecentering anchor center i : Complex)) ∈
        openZeroConvexKernel
          source.reflectedGram.atlas.spatialLinearDomain)
    (z : Fin (k + 1) -> Complex)
    (hz : z ∈ connectedComponentIn
      (openZeroConvexKernel
          source.reflectedGram.atlas.spatialLinearDomain ∩
        {w | w + (fun i =>
          (chronologicalPacketInternalRecentering anchor center i : Complex)) ∈
            openZeroConvexKernel
              source.reflectedGram.atlas.spatialLinearDomain}) 0) :
    source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ centerBase z =
      osNonnegativeTimeShiftHilbert OS lgc
        (chronologicalPacketFirstTimeRecentering anchor center)
        (by
          simpa [chronologicalPacketFirstTimeRecentering] using
            sub_nonneg.mpr hfirst)
        (source.reflectedGram.atlas.gram.anchoredAtlasField
          source.reflectedGram.atlas.sourceStage.stage
          source.reflectedGram.atlas.sourceStage.germ anchorBase
          (z + (fun i =>
            (chronologicalPacketInternalRecentering anchor center i : Complex)))) := by
  let A := source.reflectedGram.atlas
  let u : Fin (k + 1) -> Real :=
    chronologicalPacketInternalRecentering anchor center
  let uC : Fin (k + 1) -> Complex := fun i => (u i : Complex)
  let t : Real := chronologicalPacketFirstTimeRecentering anchor center
  have ht : 0 <= t := by
    simpa [t, chronologicalPacketFirstTimeRecentering] using
      sub_nonneg.mpr hfirst
  let T := osNonnegativeTimeShiftHilbert OS lgc t ht
  let radial : Set (Fin (k + 1) -> Complex) :=
    openZeroConvexKernel A.spatialLinearDomain
  let shiftedRadial : Set (Fin (k + 1) -> Complex) :=
    {w | w + uC ∈ radial}
  let common : Set (Fin (k + 1) -> Complex) := radial ∩ shiftedRadial
  let U : Set (Fin (k + 1) -> Complex) := connectedComponentIn common 0
  have hradialOpen : IsOpen radial := openZeroConvexKernel_open _
  have hshiftedOpen : IsOpen shiftedRadial := by
    exact hradialOpen.preimage (by fun_prop)
  have hcommonOpen : IsOpen common := hradialOpen.inter hshiftedOpen
  have hzeroRadial : (0 : Fin (k + 1) -> Complex) ∈ radial :=
    zero_mem_openZeroConvexKernel A.spatialLinearDomain_open
      source.zero_mem_spatialLinearDomain
  have hzeroCommon : (0 : Fin (k + 1) -> Complex) ∈ common := by
    exact ⟨hzeroRadial, by simpa [shiftedRadial, uC, u] using huKernel⟩
  have hUOpen : IsOpen U :=
    _root_.OSReconstruction.FixedAxisSplitUniformRankFieldData.isOpen_connectedComponentIn_normedSpace
      hcommonOpen 0
  have hUConnected : IsConnected U :=
    isConnected_connectedComponentIn_iff.mpr hzeroCommon
  have hzeroU : (0 : Fin (k + 1) -> Complex) ∈ U :=
    mem_connectedComponentIn hzeroCommon
  have hUsub : U ⊆ common := connectedComponentIn_subset common 0
  have hcenterField : DifferentiableOn Complex
      (fun w => A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ centerBase w) U := by
    apply (A.gram.anchoredAtlasField_holomorphic
      A.sourceStage.stage A.sourceStage.germ centerBase).mono
    intro w hw
    exact (openZeroConvexKernel_subset _ (hUsub hw).1).1
  have hanchorField : DifferentiableOn Complex
      (fun w => A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ anchorBase (w + uC)) U := by
    apply (A.gram.anchoredAtlasField_holomorphic
      A.sourceStage.stage A.sourceStage.germ anchorBase).comp
        (by fun_prop : DifferentiableOn Complex
          (fun w : Fin (k + 1) -> Complex => w + uC) U)
    intro w hw
    exact (openZeroConvexKernel_subset _ (hUsub hw).2).1
  have hshiftedField : DifferentiableOn Complex
      (fun w => T (A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ anchorBase (w + uC))) U := by
    exact (differentiableOn_const (c := T)).clm_apply hanchorField
  have hvec :=
    eventually_centeredSourceVector_eq_nonnegativeTimeShift_recentered
      (OS := OS) I anchor center hanchor hcenter chi scale lgc hfirst
  change
    (fun x : Fin (k + 1) -> Real =>
      osNonnegativeTimeShiftHilbert OS lgc
          (chronologicalPacketFirstTimeRecentering anchor center)
          (by
            simpa [chronologicalPacketFirstTimeRecentering] using
              sub_nonneg.mpr hfirst)
          (osiiPositiveTimeSingleVectorCLM OS ((k + 1) + 1)
            (localPositiveTimeParameterTranslate
              (I.translatedPositiveTimeSpatialSource
                anchor hanchor chi scale)
              (fun i : Fin (k + 1) =>
                chronologicalTimeSourceDirection (d := d) i)
              (u + x)))) =ᶠ[nhds 0]
      (fun x =>
        osiiPositiveTimeSingleVectorCLM OS ((k + 1) + 1)
          (localPositiveTimeParameterTranslate
            (I.translatedPositiveTimeSpatialSource
              center hcenter chi scale)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) x)) at hvec
  obtain ⟨W, hWsub, hWOpen, hzeroW⟩ := mem_nhds_iff.mp hvec
  let realRegion : Set (Fin (k + 1) -> Real) :=
    A.gram.anchoredAtlasRealRegion A.sourceStage.stage A.sourceStage.germ
  let V : Set (Fin (k + 1) -> Real) :=
    W ∩
      {x | (fun i => (x i : Complex)) ∈ U} ∩
      realRegion ∩
      {x | x + u ∈ realRegion}
  have hrealRegionOpen : IsOpen realRegion :=
    A.gram.anchoredAtlasRealRegion_open
      A.sourceStage.stage A.sourceStage.germ
  have hVOpen : IsOpen V := by
    exact ((hWOpen.inter (hUOpen.preimage (by fun_prop))).inter
      hrealRegionOpen).inter (hrealRegionOpen.preimage (by fun_prop))
  have hzeroRealRegion : (0 : Fin (k + 1) -> Real) ∈ realRegion :=
    mem_of_mem_nhds
      (A.gram.anchoredAtlasRealRegion_mem_nhds
        A.sourceStage.stage A.sourceStage.germ)
  have hzeroV : (0 : Fin (k + 1) -> Real) ∈ V := by
    refine ⟨⟨⟨hzeroW, by change (0 : Fin (k + 1) → Complex) ∈ U; exact hzeroU⟩,
      hzeroRealRegion⟩, ?_⟩
    simpa [u, realRegion] using huReal
  have hVsub : forall x, x ∈ V ->
      (fun i => (x i : Complex)) ∈ U := fun _ hx => hx.1.1.2
  have hreal : forall x, x ∈ V ->
      A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
          centerBase (fun i => (x i : Complex)) =
        T (A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
          anchorBase ((fun i => (x i : Complex)) + uC)) := by
    intro x hx
    rw [A.gram.anchoredAtlasField_realEdge
        A.sourceStage.stage A.sourceStage.germ centerBase x hx.1.2]
    have hcomplexAdd :
        (fun i => ((x + u) i : Complex)) =
          (fun i => (x i : Complex)) + uC := by
      ext i
      simp [uC]
    rw [← hcomplexAdd,
      A.gram.anchoredAtlasField_realEdge
        A.sourceStage.stage A.sourceStage.germ anchorBase (x + u) hx.2]
    have hxvec := hWsub hx.1.1.1
    change
      osNonnegativeTimeShiftHilbert OS lgc
          (chronologicalPacketFirstTimeRecentering anchor center)
          (by
            simpa [chronologicalPacketFirstTimeRecentering] using
              sub_nonneg.mpr hfirst)
          (osiiPositiveTimeSingleVectorCLM OS ((k + 1) + 1)
            (localPositiveTimeParameterTranslate
              (I.translatedPositiveTimeSpatialSource
                anchor hanchor chi scale)
              (fun i : Fin (k + 1) =>
                chronologicalTimeSourceDirection (d := d) i)
              (u + x))) =
        osiiPositiveTimeSingleVectorCLM OS ((k + 1) + 1)
          (localPositiveTimeParameterTranslate
            (I.translatedPositiveTimeSpatialSource
              center hcenter chi scale)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) x) at hxvec
    have hcenterSource :
        localPositiveTimeParameterTranslate
            (UniformCompactTimeSource.source centerBase)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) x =
          localPositiveTimeParameterTranslate
            (I.translatedPositiveTimeSpatialSource
              center hcenter chi scale)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) x :=
      congrArg
        (fun f => localPositiveTimeParameterTranslate f
          (fun i : Fin (k + 1) =>
            chronologicalTimeSourceDirection (d := d) i) x)
        hcenterBase
    have hanchorSource :
        localPositiveTimeParameterTranslate
            (UniformCompactTimeSource.source anchorBase)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) (x + u) =
          localPositiveTimeParameterTranslate
            (I.translatedPositiveTimeSpatialSource
              anchor hanchor chi scale)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) (x + u) :=
      congrArg
        (fun f => localPositiveTimeParameterTranslate f
          (fun i : Fin (k + 1) =>
            chronologicalTimeSourceDirection (d := d) i) (x + u))
        hanchorBase
    rw [hcenterSource, hanchorSource]
    have hparameter : u + x = x + u := add_comm _ _
    rw [hparameter] at hxvec
    simpa [T, t, u] using hxvec.symm
  have heq :=
    _root_.OSReconstruction.FixedAxisSplitUniformRankFieldData.hilbert_holomorphic_eq_at_of_eq_on_open_real
      U hUOpen hUConnected
      (fun w => A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ centerBase w)
      (fun w => T (A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ anchorBase (w + uC)))
      hcenterField hshiftedField V hVOpen ⟨0, hzeroV⟩ hVsub hreal z
      (by simpa [U, common, shiftedRadial, radial, uC, u, A] using hz)
  simpa [A, T, t, u, uC] using heq

set_option maxHeartbeats 1000000 in
/-- Moving only the first packet time needs no smallness assumption. The
internal coordinate does not change, so the common zero-based domain is the
whole open convex kernel of the source atlas. -/
theorem anchoredAtlasField_headShift_eq
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    (source : ReflectedGramSpatialSourceData (OS := OS) S q)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (anchor center : Fin ((q + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hfirst : anchor 0 <= center 0)
    (hinternal : forall j : Fin (q + 1), center j.succ = anchor j.succ)
    (anchorBase centerBase : UniformCompactTimeSource
      d ((q + 1) + 1) source.carrier)
    (scale : Nat)
    (chi : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (hanchorBase : UniformCompactTimeSource.source anchorBase =
      I.translatedPositiveTimeSpatialSource anchor hanchor chi scale)
    (hcenterBase : UniformCompactTimeSource.source centerBase =
      I.translatedPositiveTimeSpatialSource center hcenter chi scale)
    (lgc : OSLinearGrowthCondition d OS)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ openZeroConvexKernel
      source.reflectedGram.atlas.spatialLinearDomain) :
    source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ centerBase z =
      osNonnegativeTimeShiftHilbert OS lgc
        (chronologicalPacketFirstTimeRecentering anchor center)
        (by simpa [chronologicalPacketFirstTimeRecentering] using
          sub_nonneg.mpr hfirst)
        (source.reflectedGram.atlas.gram.anchoredAtlasField
          source.reflectedGram.atlas.sourceStage.stage
          source.reflectedGram.atlas.sourceStage.germ anchorBase z) := by
  let A := source.reflectedGram.atlas
  have hu : chronologicalPacketInternalRecentering anchor center = 0 := by
    ext j
    simp [chronologicalPacketInternalRecentering, hinternal j]
  have huC : (fun j =>
      (chronologicalPacketInternalRecentering anchor center j : Complex)) =
        (0 : Fin (q + 1) -> Complex) := by
    ext j
    simp [hu]
  have hzero : (0 : Fin (q + 1) -> Complex) ∈
      openZeroConvexKernel A.spatialLinearDomain :=
    zero_mem_openZeroConvexKernel A.spatialLinearDomain_open
      source.zero_mem_spatialLinearDomain
  have hcomponent : z ∈ connectedComponentIn
      (openZeroConvexKernel A.spatialLinearDomain) 0 :=
    (((openZeroConvexKernel_starConvex _).isPathConnected hzero
      ).isConnected.isPreconnected.subset_connectedComponentIn
        hzero (Subset.refl _)) hz
  have hreal : (0 : Fin (q + 1) -> Real) ∈
      A.gram.anchoredAtlasRealRegion A.sourceStage.stage A.sourceStage.germ :=
    mem_of_mem_nhds
      (A.gram.anchoredAtlasRealRegion_mem_nhds
        A.sourceStage.stage A.sourceStage.germ)
  simpa only [huC, add_zero] using
    anchoredAtlasField_nonnegativeTimeShift_recenter_eq_of_small
      source I anchor center hanchor hcenter hfirst
      anchorBase centerBase scale chi hanchorBase hcenterBase lgc
      (by simpa [hu] using hreal)
      (by simpa only [huC] using hzero)
      z (by simpa only [huC, add_zero, Set.setOf_mem_eq, Set.inter_self]
        using hcomponent)

/-- The same genuine source identity with a prescribed positive head shift,
expressed in the spectral semigroup used by the generator. -/
theorem anchoredAtlasField_headShift_eq_complex
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    (source : ReflectedGramSpatialSourceData (OS := OS) S q)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (anchor center : Fin ((q + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hfirst : center 0 = anchor 0 + epsilon)
    (hinternal : forall j : Fin (q + 1), center j.succ = anchor j.succ)
    (anchorBase centerBase : UniformCompactTimeSource
      d ((q + 1) + 1) source.carrier)
    (scale : Nat)
    (chi : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (hanchorBase : UniformCompactTimeSource.source anchorBase =
      I.translatedPositiveTimeSpatialSource anchor hanchor chi scale)
    (hcenterBase : UniformCompactTimeSource.source centerBase =
      I.translatedPositiveTimeSpatialSource center hcenter chi scale)
    (lgc : OSLinearGrowthCondition d OS)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ openZeroConvexKernel
      source.reflectedGram.atlas.spatialLinearDomain) :
    source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ centerBase z =
      osiiOriginalOSHilbertComplex OS (epsilon : Complex)
        (source.reflectedGram.atlas.gram.anchoredAtlasField
          source.reflectedGram.atlas.sourceStage.stage
          source.reflectedGram.atlas.sourceStage.germ anchorBase z) := by
  have hle : anchor 0 <= center 0 := by linarith
  have htime : chronologicalPacketFirstTimeRecentering anchor center =
      epsilon := by simp [chronologicalPacketFirstTimeRecentering, hfirst]
  have h := anchoredAtlasField_headShift_eq source I anchor center
    hanchor hcenter hle hinternal anchorBase centerBase scale chi
    hanchorBase hcenterBase lgc z hz
  simpa only [htime, osNonnegativeTimeShiftHilbert_eq_complex_of_pos
    OS lgc hepsilon] using h

set_option maxHeartbeats 1000000 in
/-- Local internal-recentering covariance of one source-indexed anchored
atlas.  A sufficiently small real increment can be moved from the packet
center into the holomorphic chronological coordinate. -/
theorem anchoredAtlasField_internalRecenter_eq_of_small
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {k : Nat}
    (source : ReflectedGramSpatialSourceData (OS := OS) S k)
    (I : Section43ProductTimeApproximateIdentity ((k + 1) + 1))
    (anchor center : Fin ((k + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((k + 1) + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion ((k + 1) + 1))
    (hfirst : anchor 0 = center 0)
    (anchorBase centerBase : UniformCompactTimeSource
      d ((k + 1) + 1) source.carrier)
    (scale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((k + 1) + 1)) Complex)
    (hanchorBase : UniformCompactTimeSource.source anchorBase =
      I.translatedPositiveTimeSpatialSource anchor hanchor chi scale)
    (hcenterBase : UniformCompactTimeSource.source centerBase =
      I.translatedPositiveTimeSpatialSource center hcenter chi scale)
    (lgc : OSLinearGrowthCondition d OS)
    (huReal : chronologicalPacketInternalRecentering anchor center ∈
      source.reflectedGram.atlas.gram.anchoredAtlasRealRegion
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ)
    (huKernel :
      (fun i =>
        (chronologicalPacketInternalRecentering anchor center i : Complex)) ∈
        openZeroConvexKernel
          source.reflectedGram.atlas.spatialLinearDomain)
    (z : Fin (k + 1) -> Complex)
    (hz : z ∈ connectedComponentIn
      (openZeroConvexKernel
          source.reflectedGram.atlas.spatialLinearDomain ∩
        {w | w + (fun i =>
          (chronologicalPacketInternalRecentering anchor center i : Complex)) ∈
            openZeroConvexKernel
              source.reflectedGram.atlas.spatialLinearDomain}) 0) :
    source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ centerBase z =
      source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ anchorBase
        (z + (fun i =>
          (chronologicalPacketInternalRecentering anchor center i : Complex))) := by
  let A := source.reflectedGram.atlas
  let u : Fin (k + 1) -> Real :=
    chronologicalPacketInternalRecentering anchor center
  let uC : Fin (k + 1) -> Complex := fun i => (u i : Complex)
  let radial : Set (Fin (k + 1) -> Complex) :=
    openZeroConvexKernel A.spatialLinearDomain
  let shiftedRadial : Set (Fin (k + 1) -> Complex) :=
    {w | w + uC ∈ radial}
  let common : Set (Fin (k + 1) -> Complex) := radial ∩ shiftedRadial
  let U : Set (Fin (k + 1) -> Complex) := connectedComponentIn common 0
  have hradialOpen : IsOpen radial := openZeroConvexKernel_open _
  have hshiftedOpen : IsOpen shiftedRadial := by
    exact hradialOpen.preimage (by fun_prop)
  have hcommonOpen : IsOpen common := hradialOpen.inter hshiftedOpen
  have hzeroRadial : (0 : Fin (k + 1) -> Complex) ∈ radial :=
    zero_mem_openZeroConvexKernel A.spatialLinearDomain_open
      source.zero_mem_spatialLinearDomain
  have hzeroCommon : (0 : Fin (k + 1) -> Complex) ∈ common := by
    exact ⟨hzeroRadial, by simpa [shiftedRadial, uC, u] using huKernel⟩
  have hUOpen : IsOpen U :=
    _root_.OSReconstruction.FixedAxisSplitUniformRankFieldData.isOpen_connectedComponentIn_normedSpace
      hcommonOpen 0
  have hUConnected : IsConnected U :=
    isConnected_connectedComponentIn_iff.mpr hzeroCommon
  have hzeroU : (0 : Fin (k + 1) -> Complex) ∈ U :=
    mem_connectedComponentIn hzeroCommon
  have hUsub : U ⊆ common := connectedComponentIn_subset common 0
  have hcenterField : DifferentiableOn Complex
      (fun w => A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ centerBase w) U := by
    apply (A.gram.anchoredAtlasField_holomorphic
      A.sourceStage.stage A.sourceStage.germ centerBase).mono
    intro w hw
    exact (openZeroConvexKernel_subset _ (hUsub hw).1).1
  have hanchorField : DifferentiableOn Complex
      (fun w => A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ anchorBase (w + uC)) U := by
    apply (A.gram.anchoredAtlasField_holomorphic
      A.sourceStage.stage A.sourceStage.germ anchorBase).comp
        (by fun_prop : DifferentiableOn Complex
          (fun w : Fin (k + 1) -> Complex => w + uC) U)
    intro w hw
    exact (openZeroConvexKernel_subset _ (hUsub hw).2).1
  have hvec :=
    eventually_centeredSourceVector_eq_nonnegativeTimeShift_recentered
      (OS := OS) I anchor center hanchor hcenter chi scale lgc
      hfirst.le
  change
    (fun x : Fin (k + 1) -> Real =>
      osNonnegativeTimeShiftHilbert OS lgc
          (chronologicalPacketFirstTimeRecentering anchor center)
          (by simpa [chronologicalPacketFirstTimeRecentering, hfirst] using
            (show (0 : Real) <= 0 from le_rfl))
          (osiiPositiveTimeSingleVectorCLM OS ((k + 1) + 1)
            (localPositiveTimeParameterTranslate
              (I.translatedPositiveTimeSpatialSource
                anchor hanchor chi scale)
              (fun i : Fin (k + 1) =>
                chronologicalTimeSourceDirection (d := d) i)
              (u + x)))) =ᶠ[nhds 0]
      (fun x =>
        osiiPositiveTimeSingleVectorCLM OS ((k + 1) + 1)
          (localPositiveTimeParameterTranslate
            (I.translatedPositiveTimeSpatialSource
              center hcenter chi scale)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) x)) at hvec
  obtain ⟨W, hWsub, hWOpen, hzeroW⟩ := mem_nhds_iff.mp hvec
  let realRegion : Set (Fin (k + 1) -> Real) :=
    A.gram.anchoredAtlasRealRegion A.sourceStage.stage A.sourceStage.germ
  let V : Set (Fin (k + 1) -> Real) :=
    W ∩
      {x | (fun i => (x i : Complex)) ∈ U} ∩
      realRegion ∩
      {x | x + u ∈ realRegion}
  have hrealRegionOpen : IsOpen realRegion :=
    A.gram.anchoredAtlasRealRegion_open
      A.sourceStage.stage A.sourceStage.germ
  have hVOpen : IsOpen V := by
    exact ((hWOpen.inter (hUOpen.preimage (by fun_prop))).inter
      hrealRegionOpen).inter (hrealRegionOpen.preimage (by fun_prop))
  have hzeroRealRegion : (0 : Fin (k + 1) -> Real) ∈ realRegion :=
    mem_of_mem_nhds
      (A.gram.anchoredAtlasRealRegion_mem_nhds
        A.sourceStage.stage A.sourceStage.germ)
  have hzeroV : (0 : Fin (k + 1) -> Real) ∈ V := by
    refine ⟨⟨⟨hzeroW, by change (0 : Fin (k + 1) → Complex) ∈ U; exact hzeroU⟩,
      hzeroRealRegion⟩, ?_⟩
    simpa [u, realRegion] using huReal
  have hVsub : forall x, x ∈ V ->
      (fun i => (x i : Complex)) ∈ U := fun _ hx => hx.1.1.2
  have hreal : forall x, x ∈ V ->
      A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
          centerBase (fun i => (x i : Complex)) =
        A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
          anchorBase ((fun i => (x i : Complex)) + uC) := by
    intro x hx
    rw [A.gram.anchoredAtlasField_realEdge
        A.sourceStage.stage A.sourceStage.germ centerBase x hx.1.2]
    have hcomplexAdd :
        (fun i => ((x + u) i : Complex)) =
          (fun i => (x i : Complex)) + uC := by
      ext i
      simp [uC]
    rw [← hcomplexAdd,
      A.gram.anchoredAtlasField_realEdge
        A.sourceStage.stage A.sourceStage.germ anchorBase (x + u) hx.2]
    have hxvec := hWsub hx.1.1.1
    have hcenterSource :
        localPositiveTimeParameterTranslate
            (UniformCompactTimeSource.source centerBase)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) x =
          localPositiveTimeParameterTranslate
            (I.translatedPositiveTimeSpatialSource
              center hcenter chi scale)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) x :=
      congrArg
        (fun f => localPositiveTimeParameterTranslate f
          (fun i : Fin (k + 1) =>
            chronologicalTimeSourceDirection (d := d) i) x)
        hcenterBase
    have hanchorSource :
        localPositiveTimeParameterTranslate
            (UniformCompactTimeSource.source anchorBase)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) (x + u) =
          localPositiveTimeParameterTranslate
            (I.translatedPositiveTimeSpatialSource
              anchor hanchor chi scale)
            (fun i : Fin (k + 1) =>
              chronologicalTimeSourceDirection (d := d) i) (x + u) :=
      congrArg
        (fun f => localPositiveTimeParameterTranslate f
          (fun i : Fin (k + 1) =>
            chronologicalTimeSourceDirection (d := d) i) (x + u))
        hanchorBase
    rw [hcenterSource, hanchorSource]
    simp [chronologicalPacketFirstTimeRecentering, hfirst,
      osNonnegativeTimeShiftHilbert] at hxvec
    have hparameter : u + x = x + u := add_comm _ _
    rw [hparameter] at hxvec
    simpa [u] using hxvec.symm
  have heq :=
    _root_.OSReconstruction.FixedAxisSplitUniformRankFieldData.hilbert_holomorphic_eq_at_of_eq_on_open_real
      U hUOpen hUConnected
      (fun w => A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ centerBase w)
      (fun w => A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ anchorBase (w + uC))
      hcenterField hanchorField V hVOpen ⟨0, hzeroV⟩ hVsub hreal z
      (by simpa [U, common, shiftedRadial, radial, uC, u, A] using hz)
  simpa [A, u, uC] using heq

/-- A finite packet-recentering chain inside one source-indexed atlas.

The center at `j + 1` is evaluated at `coordinate (j + 1)`.  Moving its
internal center displacement into the holomorphic variable gives
`coordinate j`, where the packet based at center `j` is evaluated.  The
shifted radial-segment condition is a concrete sufficient condition for the
zero-connected common domain required by
`anchoredAtlasField_internalRecenter_eq_of_small`. -/
structure PacketInternalRecenteringChainData
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {k : Nat}
    (source : ReflectedGramSpatialSourceData (OS := OS) S k)
    (I : Section43ProductTimeApproximateIdentity ((k + 1) + 1))
    (scale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((k + 1) + 1)) Complex)
    (length : Nat) where
  center : Fin (length + 1) -> Fin ((k + 1) + 1) -> Real
  center_positive : forall j,
    center j ∈ section43TimeStrictPositiveRegion ((k + 1) + 1)
  base : Fin (length + 1) -> UniformCompactTimeSource
    d ((k + 1) + 1) source.carrier
  base_source : forall j,
    UniformCompactTimeSource.source (base j) =
      I.translatedPositiveTimeSpatialSource
        (center j) (center_positive j) chi scale
  coordinate : Fin (length + 1) -> Fin (k + 1) -> Complex
  step_first_eq : forall j : Fin length,
    center j.castSucc 0 = center j.succ 0
  step_real : forall j : Fin length,
    chronologicalPacketInternalRecentering
        (center j.castSucc) (center j.succ) ∈
      source.reflectedGram.atlas.gram.anchoredAtlasRealRegion
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ
  step_coordinate_radial : forall j : Fin length,
    coordinate j.succ ∈
      openZeroConvexKernel
        source.reflectedGram.atlas.spatialLinearDomain
  step_coordinate : forall j : Fin length,
    coordinate j.castSucc =
      coordinate j.succ + fun i =>
        (chronologicalPacketInternalRecentering
          (center j.castSucc) (center j.succ) i : Complex)
  step_shifted_radial_segment : forall j : Fin length,
    forall w, w ∈ segment Real 0 (coordinate j.succ) ->
      w + (fun i =>
        (chronologicalPacketInternalRecentering
          (center j.castSucc) (center j.succ) i : Complex)) ∈
        openZeroConvexKernel
          source.reflectedGram.atlas.spatialLinearDomain

set_option maxHeartbeats 1000000 in
/-- Local packet recentering telescopes along a finite admissible chain. -/
theorem anchoredAtlasField_internalRecenter_eq_of_chain
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {k length : Nat}
    {source : ReflectedGramSpatialSourceData (OS := OS) S k}
    {I : Section43ProductTimeApproximateIdentity ((k + 1) + 1)}
    {scale : Nat}
    {chi : SchwartzMap
      (Section43SpatialSpace d ((k + 1) + 1)) Complex}
    (chain : PacketInternalRecenteringChainData
      source I scale chi length)
    (lgc : OSLinearGrowthCondition d OS) :
    source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ
        (chain.base (Fin.last length))
        (chain.coordinate (Fin.last length)) =
      source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ
        (chain.base 0) (chain.coordinate 0) := by
  let fieldAt (j : Fin (length + 1)) : OSHilbertSpace OS :=
    source.reflectedGram.atlas.gram.anchoredAtlasField
      source.reflectedGram.atlas.sourceStage.stage
      source.reflectedGram.atlas.sourceStage.germ
      (chain.base j) (chain.coordinate j)
  have hstep : forall j : Fin length,
      fieldAt j.succ = fieldAt j.castSucc := by
    intro j
    let radial : Set (Fin (k + 1) -> Complex) :=
      openZeroConvexKernel
        source.reflectedGram.atlas.spatialLinearDomain
    let u : Fin (k + 1) -> Complex := fun i =>
      (chronologicalPacketInternalRecentering
        (chain.center j.castSucc) (chain.center j.succ) i : Complex)
    have hsegmentRadial : segment Real 0 (chain.coordinate j.succ) ⊆
        radial :=
      (openZeroConvexKernel_starConvex
        source.reflectedGram.atlas.spatialLinearDomain).segment_subset
          (chain.step_coordinate_radial j)
    have hsegmentCommon : segment Real 0 (chain.coordinate j.succ) ⊆
        radial ∩ {w | w + u ∈ radial} := by
      intro w hw
      exact ⟨hsegmentRadial hw,
        chain.step_shifted_radial_segment j w hw⟩
    have hcomponent : chain.coordinate j.succ ∈ connectedComponentIn
        (radial ∩ {w | w + u ∈ radial}) 0 := by
      exact (convex_segment (0 : Fin (k + 1) -> Complex)
        (chain.coordinate j.succ)).isPreconnected.subset_connectedComponentIn
          (left_mem_segment Real 0 (chain.coordinate j.succ))
          hsegmentCommon
          (right_mem_segment Real 0 (chain.coordinate j.succ))
    have huKernel : u ∈ radial := by
      have hzeroShift := chain.step_shifted_radial_segment j 0
        (left_mem_segment Real 0 (chain.coordinate j.succ))
      simpa [u, radial] using hzeroShift
    have h := anchoredAtlasField_internalRecenter_eq_of_small
      source I
      (chain.center j.castSucc) (chain.center j.succ)
      (chain.center_positive j.castSucc)
      (chain.center_positive j.succ)
      (chain.step_first_eq j)
      (chain.base j.castSucc) (chain.base j.succ)
      scale chi
      (chain.base_source j.castSucc)
      (chain.base_source j.succ)
      lgc (chain.step_real j) huKernel
      (chain.coordinate j.succ)
      (by simpa [radial, u] using hcomponent)
    rw [← chain.step_coordinate j] at h
    exact h
  have hprefix : forall m : Nat, forall hm : m <= length,
      fieldAt ⟨m, Nat.lt_succ_of_le hm⟩ = fieldAt 0 := by
    intro m
    induction m with
    | zero =>
        intro hm
        rfl
    | succ m ih =>
        intro hm
        have hm_lt : m < length := Nat.lt_of_succ_le hm
        let j : Fin length := ⟨m, hm_lt⟩
        calc
          fieldAt ⟨m + 1, Nat.lt_succ_of_le hm⟩ =
              fieldAt ⟨m, Nat.lt_succ_of_le (Nat.le_of_lt hm_lt)⟩ := by
                simpa [j] using hstep j
          _ = fieldAt 0 := ih (Nat.le_of_lt hm_lt)
  change fieldAt (Fin.last length) = fieldAt 0
  exact hprefix length le_rfl

/-- The affine parameter of one waypoint in a positive finite subdivision. -/
def packetRecenteringSubdivisionParameter
    (steps : Nat) (j : Fin (steps + 1)) : Real :=
  (j.val : Real) / (steps : Real)

/-- Equally spaced packet centers from the canonical anchor to the selected
source center. -/
def packetCenterSubdivision
    {k : Nat}
    (anchor center : Fin (k + 1) -> Real)
    (steps : Nat) (j : Fin (steps + 1)) : Fin (k + 1) -> Real :=
  AffineMap.lineMap (k := Real) anchor center
    (packetRecenteringSubdivisionParameter steps j)

/-- Reverse interpolation of the holomorphic coordinate.  At waypoint zero
the complete internal center displacement has been moved into the coordinate;
at the final waypoint the coordinate is the original `z`. -/
def packetCoordinateSubdivision
    {k : Nat}
    (z : Fin k -> Complex)
    (u : Fin k -> Real)
    (steps : Nat) (j : Fin (steps + 1)) : Fin k -> Complex :=
  AffineMap.lineMap (k := Real)
    (z + fun i => (u i : Complex)) z
    (packetRecenteringSubdivisionParameter steps j)

theorem packetRecenteringSubdivisionParameter_mem_Icc
    {steps : Nat} (hsteps : 0 < steps) (j : Fin (steps + 1)) :
    packetRecenteringSubdivisionParameter steps j ∈ Set.Icc (0 : Real) 1 := by
  have hstepsReal : (0 : Real) < (steps : Real) := by
    exact_mod_cast hsteps
  have hjle : (j.val : Real) <= (steps : Real) := by
    exact_mod_cast Nat.le_of_lt_succ j.isLt
  exact ⟨div_nonneg (Nat.cast_nonneg _) hstepsReal.le,
    (div_le_one hstepsReal).2 hjle⟩

@[simp]
theorem packetCenterSubdivision_zero
    {k steps : Nat}
    (anchor center : Fin (k + 1) -> Real) :
    packetCenterSubdivision anchor center steps 0 = anchor := by
  simp [packetCenterSubdivision, packetRecenteringSubdivisionParameter]

@[simp]
theorem packetCoordinateSubdivision_zero
    {k steps : Nat}
    (z : Fin k -> Complex) (u : Fin k -> Real) :
    packetCoordinateSubdivision z u steps 0 =
      z + fun i => (u i : Complex) := by
  simp [packetCoordinateSubdivision,
    packetRecenteringSubdivisionParameter]

@[simp]
theorem packetCenterSubdivision_last
    {k steps : Nat}
    (hsteps : 0 < steps)
    (anchor center : Fin (k + 1) -> Real) :
    packetCenterSubdivision anchor center steps (Fin.last steps) = center := by
  simp [packetCenterSubdivision, packetRecenteringSubdivisionParameter,
    hsteps.ne']

@[simp]
theorem packetCoordinateSubdivision_last
    {k steps : Nat}
    (hsteps : 0 < steps)
    (z : Fin k -> Complex) (u : Fin k -> Real) :
    packetCoordinateSubdivision z u steps (Fin.last steps) = z := by
  simp [packetCoordinateSubdivision,
    packetRecenteringSubdivisionParameter, hsteps.ne']

theorem packetCenterSubdivision_mem_segment
    {k steps : Nat}
    (hsteps : 0 < steps)
    (anchor center : Fin (k + 1) -> Real)
    (j : Fin (steps + 1)) :
    packetCenterSubdivision anchor center steps j ∈
      segment Real anchor center := by
  rw [segment_eq_image_lineMap]
  exact ⟨packetRecenteringSubdivisionParameter steps j,
    packetRecenteringSubdivisionParameter_mem_Icc hsteps j, rfl⟩

theorem packetCoordinateSubdivision_mem_segment
    {k steps : Nat}
    (hsteps : 0 < steps)
    (z : Fin k -> Complex) (u : Fin k -> Real)
    (j : Fin (steps + 1)) :
    packetCoordinateSubdivision z u steps j ∈
      segment Real (z + fun i => (u i : Complex)) z := by
  rw [segment_eq_image_lineMap]
  exact ⟨packetRecenteringSubdivisionParameter steps j,
    packetRecenteringSubdivisionParameter_mem_Icc hsteps j, rfl⟩

theorem packetCenterSubdivision_mem_strictPositive
    {k steps : Nat}
    (hsteps : 0 < steps)
    (anchor center : Fin (k + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion (k + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion (k + 1))
    (j : Fin (steps + 1)) :
    packetCenterSubdivision anchor center steps j ∈
      section43TimeStrictPositiveRegion (k + 1) := by
  intro i
  have ht := packetRecenteringSubdivisionParameter_mem_Icc hsteps j
  have ha := hanchor i
  have hc := hcenter i
  let s := packetRecenteringSubdivisionParameter steps j
  have hsleft : 0 <= (1 - s) * anchor i :=
    mul_nonneg (sub_nonneg.mpr ht.2) ha.le
  have hspos : 0 < (1 - s) * anchor i + s * center i := by
    by_cases hs : s = 0
    · simpa [hs] using ha
    · exact add_pos_of_nonneg_of_pos hsleft
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hs)) hc)
  simp only [packetCenterSubdivision, AffineMap.lineMap_apply,
    vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  change 0 < s * (center i - anchor i) + anchor i
  convert hspos using 1 <;> ring

/-- The strict-positive packet-center region contains the complete segment
between any two of its points. -/
theorem mem_strictPositive_of_mem_packetCenter_segment
    {k : Nat}
    {anchor center tau : Fin (k + 1) -> Real}
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion (k + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion (k + 1))
    (htau : tau ∈ segment Real anchor center) :
    tau ∈ section43TimeStrictPositiveRegion (k + 1) := by
  rw [segment_eq_image_lineMap] at htau
  obtain ⟨s, hs, rfl⟩ := htau
  intro i
  have ha := hanchor i
  have hc := hcenter i
  have hsleft : 0 <= (1 - s) * anchor i :=
    mul_nonneg (sub_nonneg.mpr hs.2) ha.le
  have hspos : 0 < (1 - s) * anchor i + s * center i := by
    by_cases hszero : s = 0
    · simpa [hszero] using ha
    · exact add_pos_of_nonneg_of_pos hsleft
        (mul_pos (lt_of_le_of_ne hs.1 (Ne.symm hszero)) hc)
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  convert hspos using 1 <;> ring

theorem packetCenterSubdivision_step_first_eq
    {k steps : Nat}
    (hsteps : 0 < steps)
    (anchor center : Fin (k + 1) -> Real)
    (hfirst : anchor 0 = center 0)
    (j : Fin steps) :
    packetCenterSubdivision anchor center steps j.castSucc 0 =
      packetCenterSubdivision anchor center steps j.succ 0 := by
  simp only [packetCenterSubdivision, AffineMap.lineMap_apply,
    vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  rw [← hfirst]
  ring

theorem chronologicalPacketInternalRecentering_packetCenterSubdivision_step
    {k steps : Nat}
    (hsteps : 0 < steps)
    (anchor center : Fin (k + 1) -> Real)
    (j : Fin steps) :
    chronologicalPacketInternalRecentering
        (packetCenterSubdivision anchor center steps j.castSucc)
        (packetCenterSubdivision anchor center steps j.succ) =
      (steps : Real)⁻¹ •
        chronologicalPacketInternalRecentering anchor center := by
  ext i
  simp only [chronologicalPacketInternalRecentering,
    packetCenterSubdivision, packetRecenteringSubdivisionParameter,
    AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Fin.val_succ,
    Fin.coe_castSucc]
  push_cast
  field_simp [hsteps.ne']
  ring

theorem packetCoordinateSubdivision_step
    {k steps : Nat}
    (hsteps : 0 < steps)
    (z : Fin k -> Complex) (u : Fin k -> Real)
    (j : Fin steps) :
    packetCoordinateSubdivision z u steps j.castSucc =
      packetCoordinateSubdivision z u steps j.succ +
        (fun i => (((steps : Real)⁻¹ • u) i : Complex)) := by
  ext i
  simp only [packetCoordinateSubdivision,
    packetRecenteringSubdivisionParameter, AffineMap.lineMap_apply,
    vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    Complex.real_smul, smul_eq_mul, Fin.val_succ, Fin.coe_castSucc]
  push_cast
  field_simp [hsteps.ne']
  ring

/-- One Archimedean subdivision makes two real-module increments
simultaneously smaller than any prescribed positive radius. -/
theorem exists_nat_inv_smul_norm_lt_pair
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (x : E) (y : F) {radius : Real} (hradius : 0 < radius) :
    exists steps : Nat, 0 < steps ∧
      ‖(steps : Real)⁻¹ • x‖ < radius ∧
      ‖(steps : Real)⁻¹ • y‖ < radius := by
  obtain ⟨steps, hsteps⟩ :=
    exists_nat_gt (max ‖x‖ ‖y‖ / radius)
  have hquotient : 0 <= max ‖x‖ ‖y‖ / radius :=
    div_nonneg ((norm_nonneg x).trans (le_max_left _ _)) hradius.le
  have hstepsReal : (0 : Real) < (steps : Real) :=
    lt_of_le_of_lt hquotient hsteps
  have hstepsNat : 0 < steps := by
    exact_mod_cast hstepsReal
  have hmaxMesh : max ‖x‖ ‖y‖ / (steps : Real) < radius := by
    rw [div_lt_iff₀ hstepsReal]
    rw [div_lt_iff₀ hradius] at hsteps
    simpa [mul_comm] using hsteps
  have hxMesh : ‖x‖ / (steps : Real) < radius :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hstepsReal.le).trans_lt
      hmaxMesh
  have hyMesh : ‖y‖ / (steps : Real) < radius :=
    (div_le_div_of_nonneg_right (le_max_right _ _) hstepsReal.le).trans_lt
      hmaxMesh
  refine ⟨steps, hstepsNat, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hstepsReal]
    simpa [div_eq_mul_inv, mul_comm] using hxMesh
  · rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hstepsReal]
    simpa [div_eq_mul_inv, mul_comm] using hyMesh

/-- The compact radial hull swept out by the zero-based segments through one
compact coordinate segment. -/
def packetCoordinateRadialHull
    {k : Nat}
    (start target : Fin k -> Complex) : Set (Fin k -> Complex) :=
  Set.Icc (0 : Real) 1 • segment Real start target

theorem packetCoordinateRadialHull_isCompact
    {k : Nat}
    (start target : Fin k -> Complex) :
    IsCompact (packetCoordinateRadialHull start target) := by
  apply isCompact_Icc.smul_set
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem packetCoordinateRadialHull_subset_of_starConvex
    {k : Nat}
    {U : Set (Fin k -> Complex)}
    (hU : StarConvex Real 0 U)
    {start target : Fin k -> Complex}
    (hsegment : segment Real start target ⊆ U) :
    packetCoordinateRadialHull start target ⊆ U := by
  rintro _ ⟨s, hs, p, hp, rfl⟩
  exact hU.smul_mem (hsegment hp) hs.1 hs.2

theorem segment_subset_packetCoordinateRadialHull
    {k : Nat}
    (start target p : Fin k -> Complex)
    (hp : p ∈ segment Real start target) :
    segment Real 0 p ⊆ packetCoordinateRadialHull start target := by
  intro w hw
  rw [segment_eq_image_lineMap] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  refine ⟨s, hs, p, hp, ?_⟩
  simp [AffineMap.lineMap_apply_module']

set_option maxHeartbeats 2000000 in
/-- Global internal packet recentering over a compact retained radial hull.

Compactness supplies one translation radius for every radial segment in the
coordinate interpolation.  A sufficiently fine affine subdivision then puts
every center increment in the atlas real-edge neighborhood and every shifted
radial segment in the source radial domain.  The resulting finite chain
telescopes the local holomorphic covariance. -/
theorem anchoredAtlasField_internalRecenter_eq_of_compact_radialHull
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {k : Nat}
    (source : ReflectedGramSpatialSourceData (OS := OS) S k)
    (I : Section43ProductTimeApproximateIdentity ((k + 1) + 1))
    (anchor center : Fin ((k + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((k + 1) + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion ((k + 1) + 1))
    (hfirst : anchor 0 = center 0)
    (scale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((k + 1) + 1)) Complex)
    (baseAt : forall tau, tau ∈ segment Real anchor center ->
      UniformCompactTimeSource d ((k + 1) + 1) source.carrier)
    (hbaseAt : forall tau (htau : tau ∈ segment Real anchor center)
      (hpositive : tau ∈
        section43TimeStrictPositiveRegion ((k + 1) + 1)),
      UniformCompactTimeSource.source (baseAt tau htau) =
        I.translatedPositiveTimeSpatialSource
          tau hpositive chi scale)
    (lgc : OSLinearGrowthCondition d OS)
    (z : Fin (k + 1) -> Complex)
    (K : Set (Fin (k + 1) -> Complex))
    (hKcompact : IsCompact K)
    (hKradial : K ⊆ openZeroConvexKernel
      source.reflectedGram.atlas.spatialLinearDomain)
    (hKcontainsRadialHull : forall p,
      p ∈ segment Real
        (z + fun i =>
          (chronologicalPacketInternalRecentering anchor center i : Complex))
        z ->
      segment Real 0 p ⊆ K) :
    source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ
        (baseAt center (right_mem_segment Real anchor center)) z =
      source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ
        (baseAt anchor (left_mem_segment Real anchor center))
        (z + fun i =>
          (chronologicalPacketInternalRecentering anchor center i : Complex)) := by
  let uR : Fin (k + 1) -> Real :=
    chronologicalPacketInternalRecentering anchor center
  let uC : Fin (k + 1) -> Complex := fun i => (uR i : Complex)
  let radial : Set (Fin (k + 1) -> Complex) :=
    openZeroConvexKernel source.reflectedGram.atlas.spatialLinearDomain
  let realRegion : Set (Fin (k + 1) -> Real) :=
    source.reflectedGram.atlas.gram.anchoredAtlasRealRegion
      source.reflectedGram.atlas.sourceStage.stage
      source.reflectedGram.atlas.sourceStage.germ
  have hrealOpen : IsOpen realRegion :=
    source.reflectedGram.atlas.gram.anchoredAtlasRealRegion_open
      source.reflectedGram.atlas.sourceStage.stage
      source.reflectedGram.atlas.sourceStage.germ
  have hzeroReal : (0 : Fin (k + 1) -> Real) ∈ realRegion :=
    mem_of_mem_nhds
      (source.reflectedGram.atlas.gram.anchoredAtlasRealRegion_mem_nhds
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ)
  obtain ⟨realRadius, hrealRadius, hrealBall⟩ :=
    Metric.isOpen_iff.mp hrealOpen 0 hzeroReal
  obtain ⟨radialRadius, hradialRadius, hradialThickening⟩ :=
    hKcompact.exists_thickening_subset_open
      (openZeroConvexKernel_open
        source.reflectedGram.atlas.spatialLinearDomain)
      hKradial
  have hminRadius : 0 < min realRadius radialRadius :=
    lt_min hrealRadius hradialRadius
  obtain ⟨steps, hsteps, hdeltaR, hdeltaC⟩ :=
    exists_nat_inv_smul_norm_lt_pair uR uC hminRadius
  let centerAt : Fin (steps + 1) -> Fin ((k + 1) + 1) -> Real :=
    packetCenterSubdivision anchor center steps
  have hcenterAtSegment : forall j, centerAt j ∈
      segment Real anchor center := by
    intro j
    exact packetCenterSubdivision_mem_segment hsteps anchor center j
  have hcenterAtPositive : forall j, centerAt j ∈
      section43TimeStrictPositiveRegion ((k + 1) + 1) := by
    intro j
    exact packetCenterSubdivision_mem_strictPositive
      hsteps anchor center hanchor hcenter j
  let chainBase (j : Fin (steps + 1)) : UniformCompactTimeSource
      d ((k + 1) + 1) source.carrier :=
    baseAt (centerAt j) (hcenterAtSegment j)
  let coordinateAt : Fin (steps + 1) -> Fin (k + 1) -> Complex :=
    packetCoordinateSubdivision z uR steps
  have hdeltaReal : (steps : Real)⁻¹ • uR ∈ realRegion := by
    apply hrealBall
    rw [Metric.mem_ball, dist_zero_right]
    exact hdeltaR.trans_le (min_le_left _ _)
  have hcastDelta :
      (fun i => (((steps : Real)⁻¹ • uR) i : Complex)) =
        (steps : Real)⁻¹ • uC := by
    ext i
    simp [uC, Complex.real_smul]
  let chain : PacketInternalRecenteringChainData
      source I scale chi steps :=
    { center := centerAt
      center_positive := hcenterAtPositive
      base := chainBase
      base_source := by
        intro j
        exact hbaseAt (centerAt j) (hcenterAtSegment j)
          (hcenterAtPositive j)
      coordinate := coordinateAt
      step_first_eq := by
        intro j
        exact packetCenterSubdivision_step_first_eq
          hsteps anchor center hfirst j
      step_real := by
        intro j
        rw [chronologicalPacketInternalRecentering_packetCenterSubdivision_step
          hsteps anchor center j]
        exact hdeltaReal
      step_coordinate_radial := by
        intro j
        apply hKradial
        apply hKcontainsRadialHull (coordinateAt j.succ)
        · simpa [coordinateAt, uR, uC] using
            packetCoordinateSubdivision_mem_segment
              hsteps z uR j.succ
        · exact right_mem_segment Real 0 (coordinateAt j.succ)
      step_coordinate := by
        intro j
        rw [chronologicalPacketInternalRecentering_packetCenterSubdivision_step
          hsteps anchor center j]
        simpa [coordinateAt, hcastDelta] using
          packetCoordinateSubdivision_step hsteps z uR j
      step_shifted_radial_segment := by
        intro j w hw
        have hcoordinateSegment : coordinateAt j.succ ∈
            segment Real (z + uC) z := by
          simpa [coordinateAt] using
            packetCoordinateSubdivision_mem_segment
              hsteps z uR j.succ
        have hwK : w ∈ K :=
          hKcontainsRadialHull (coordinateAt j.succ)
            (by simpa [uR, uC] using hcoordinateSegment) hw
        have htranslated :
            w + (steps : Real)⁻¹ • uC ∈
              Metric.thickening radialRadius K := by
          rw [Metric.mem_thickening_iff]
          refine ⟨w, hwK, ?_⟩
          rw [dist_eq_norm]
          simpa using hdeltaC.trans_le (min_le_right _ _)
        apply hradialThickening
        rw [chronologicalPacketInternalRecentering_packetCenterSubdivision_step
          hsteps anchor center j, hcastDelta]
        exact htranslated }
  have heq := anchoredAtlasField_internalRecenter_eq_of_chain chain lgc
  change source.reflectedGram.atlas.gram.anchoredAtlasField
      source.reflectedGram.atlas.sourceStage.stage
      source.reflectedGram.atlas.sourceStage.germ
      (chainBase (Fin.last steps)) (coordinateAt (Fin.last steps)) =
    source.reflectedGram.atlas.gram.anchoredAtlasField
      source.reflectedGram.atlas.sourceStage.stage
      source.reflectedGram.atlas.sourceStage.germ
      (chainBase 0) (coordinateAt 0) at heq
  have hlastCenter : centerAt (Fin.last steps) = center := by
    exact packetCenterSubdivision_last hsteps anchor center
  have hlastCoordinate : coordinateAt (Fin.last steps) = z := by
    exact packetCoordinateSubdivision_last hsteps z uR
  have hzeroCenter : centerAt 0 = anchor := by
    exact packetCenterSubdivision_zero anchor center
  have hzeroCoordinate : coordinateAt 0 = z + uC := by
    exact packetCoordinateSubdivision_zero z uR
  simp only [chainBase, hlastCenter, hlastCoordinate,
    hzeroCenter, hzeroCoordinate] at heq
  simpa [uR, uC] using heq

set_option maxHeartbeats 2000000 in
/-- Global packet recentering when the complete coordinate interpolation lies
in the source radial domain.  Its compact radial hull supplies the uniform
small-step neighborhood required by the finite chain. -/
theorem anchoredAtlasField_internalRecenter_eq_of_radial_segment
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {k : Nat}
    (source : ReflectedGramSpatialSourceData (OS := OS) S k)
    (I : Section43ProductTimeApproximateIdentity ((k + 1) + 1))
    (anchor center : Fin ((k + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((k + 1) + 1))
    (hcenter : center ∈ section43TimeStrictPositiveRegion ((k + 1) + 1))
    (hfirst : anchor 0 = center 0)
    (scale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((k + 1) + 1)) Complex)
    (baseAt : forall tau, tau ∈ segment Real anchor center ->
      UniformCompactTimeSource d ((k + 1) + 1) source.carrier)
    (hbaseAt : forall tau (htau : tau ∈ segment Real anchor center)
      (hpositive : tau ∈
        section43TimeStrictPositiveRegion ((k + 1) + 1)),
      UniformCompactTimeSource.source (baseAt tau htau) =
        I.translatedPositiveTimeSpatialSource
          tau hpositive chi scale)
    (lgc : OSLinearGrowthCondition d OS)
    (z : Fin (k + 1) -> Complex)
    (hcoordinateSegment : segment Real
        (z + fun i =>
          (chronologicalPacketInternalRecentering anchor center i : Complex))
        z ⊆
      openZeroConvexKernel
        source.reflectedGram.atlas.spatialLinearDomain) :
    source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ
        (baseAt center (right_mem_segment Real anchor center)) z =
      source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ
        (baseAt anchor (left_mem_segment Real anchor center))
        (z + fun i =>
          (chronologicalPacketInternalRecentering anchor center i : Complex)) := by
  let start : Fin (k + 1) -> Complex :=
    z + fun i =>
      (chronologicalPacketInternalRecentering anchor center i : Complex)
  let K : Set (Fin (k + 1) -> Complex) :=
    packetCoordinateRadialHull start z
  apply anchoredAtlasField_internalRecenter_eq_of_compact_radialHull
    source I anchor center hanchor hcenter hfirst scale chi
    baseAt hbaseAt lgc z K
  · exact packetCoordinateRadialHull_isCompact start z
  · exact packetCoordinateRadialHull_subset_of_starConvex
      (openZeroConvexKernel_starConvex
        source.reflectedGram.atlas.spatialLinearDomain)
      (by simpa [start] using hcoordinateSegment)
  · intro p hp
    exact segment_subset_packetCoordinateRadialHull start z p
      (by simpa [start] using hp)

variable {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
variable {S0 : C0}

end OSIIChapterV
end OSReconstruction
