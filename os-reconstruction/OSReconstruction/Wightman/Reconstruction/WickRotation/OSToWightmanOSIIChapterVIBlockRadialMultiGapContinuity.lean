/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketContinuity











noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

/-- Independent translation of a fixed configuration-space Schwartz source is
continuous in the full displacement tuple. -/
theorem continuous_translateSchwartzConfiguration_fixed
    {d n : Nat} (f : SchwartzNPoint d n) :
    Continuous
      (fun a : NPointDomain d n => translateSchwartzConfiguration a f) := by
  let e := flattenCLEquivReal n (d + 1)
  let fFlat : SchwartzMap (Fin (n * (d + 1)) -> Real) Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm f
  let unflatten :
      SchwartzMap (Fin (n * (d + 1)) -> Real) Complex →L[Complex]
        SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
  have hflat : Continuous
      (fun a : NPointDomain d n => SCV.translateSchwartz (e a) fFlat) :=
    (continuous_translateSchwartz_unrestricted fFlat).comp e.continuous
  refine (unflatten.continuous.comp hflat).congr ?_
  intro a
  ext x
  simp only [Function.comp_apply, SCV.translateSchwartz_apply, fFlat,
    unflatten, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    translateSchwartzConfiguration_apply]
  congr 1
  rw [map_add, e.symm_apply_apply, e.symm_apply_apply]

namespace OSIIStep4MultiGapSelectedCommonSlopeData

noncomputable def frozenLeftSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) : SchwartzNPoint d (i.val + 1) :=
  (osiiStep4MultiGapFrozenLeftPositiveSource
    d k hrho center y y' hcenter D.T x i).timeReflect

noncomputable def frozenRightSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    SchwartzNPoint d (osiiStep4MultiGapAfterCount i + 1) :=
  osiiStep4MultiGapFrozenRightPositiveSource
    d k hrho center y y' hcenter D.T x i

theorem frozenLeftSource_support
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport (D.frozenLeftSource x q.1 :
        NPointDomain d (q.1.val + 1) -> Complex) <=
      osiiEuclideanRotationOrderedNegativeTimeRegion
        (d := d) (n := q.1.val + 1)
        (osiiAxisPairRotationData D.T q.2).matrix := by
  apply SchwartzNPoint.timeReflect_tsupport_subset_all_orientedNegative
  intro a
  exact osiiStep4MultiGapFrozenLeftPositiveSource_support
    d k hrho center y y' hcenter D.T D.hT D.left_support x q.1 a

theorem frozenRightSource_support
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport (D.frozenRightSource x q.1 :
        NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) -> Complex) <=
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := osiiStep4MultiGapAfterCount q.1 + 1)
        (osiiAxisPairRotationData D.T q.2).matrix :=
  osiiStep4MultiGapFrozenRightPositiveSource_support
    d k hrho center y y' hcenter D.T D.hT D.right_support x q.1 q.2

theorem continuous_multiGapLeftSpectatorConfiguration
    {d k : Nat} [NeZero d] [NeZero k]
    (T : Real) (i : Fin k) :
    Continuous
      (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
        fun j => -osiiAxisPairChronologicalPointTranslation T
          (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j) := by
  apply continuous_pi
  intro j
  apply Continuous.neg
  unfold osiiAxisPairChronologicalPointTranslation
  apply continuous_finset_sum
  intro r _hr
  by_cases hrj : r.val < j.val
  · simp only [hrj, if_true]
    unfold osiiAxisPairChronologicalGapTranslation
    unfold osiiStep4MultiGapLeftSpectatorLogCoordinates
    unfold osiiAxisPairPositiveCoefficients
    fun_prop
  · simpa [hrj] using
      (continuous_const : Continuous
        (fun _x : Fin k -> osiiAxisPairIndex d -> Real =>
          (0 : SpacetimeDim d)))

theorem continuous_multiGapRightSpectatorConfiguration
    {d k : Nat} [NeZero d] [NeZero k]
    (T : Real) (i : Fin k) :
    Continuous
      (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
        fun j => -osiiAxisPairChronologicalPointTranslation T
          (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j) := by
  apply continuous_pi
  intro j
  apply Continuous.neg
  unfold osiiAxisPairChronologicalPointTranslation
  apply continuous_finset_sum
  intro r _hr
  by_cases hrj : r.val < j.val
  · simp only [hrj, if_true]
    unfold osiiAxisPairChronologicalGapTranslation
    unfold osiiStep4MultiGapRightSpectatorLogCoordinates
    unfold osiiAxisPairPositiveCoefficients
    fun_prop
  · simpa [hrj] using
      (continuous_const : Continuous
        (fun _x : Fin k -> osiiAxisPairIndex d -> Real =>
          (0 : SpacetimeDim d)))

theorem continuous_frozenLeftPositiveSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (i : Fin k) :
    Continuous
      (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
        osiiStep4MultiGapFrozenLeftPositiveSource
          d k hrho center y y' hcenter D.T x i) := by
  exact
    (continuous_translateSchwartzConfiguration_fixed
      (osiiStep4MultiGapSelectedLeftPositiveTimeSource
        d k hrho center y y' hcenter i).1).comp
      (continuous_multiGapLeftSpectatorConfiguration D.T i)

def frozenRightPacketConfiguration
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) :=
  fun j =>
    -osiiAxisPairChronologicalPointTranslation D.T
        (osiiStep4MultiGapRightSpectatorLogCoordinates d k x q.1) j -
      osiiAxisPairFrozenTranslation D.T
        (osiiAxisPairPositiveCoefficients (x q.1)) q.2

theorem translate_frozenRightSource_eq_configuration
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    translateSchwartzNPoint (d := d)
        (osiiAxisPairFrozenTranslation D.T
          (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
        (D.frozenRightSource x q.1) =
      translateSchwartzConfiguration
        (D.frozenRightPacketConfiguration x q)
        (osiiStep4MultiGapSelectedRightPositiveTimeSource
          d k hrho center y y' hcenter q.1).1 := by
  ext z
  simp only [frozenRightSource,
    osiiStep4MultiGapFrozenRightPositiveSource,
    translateSchwartzNPoint_apply,
    translateSchwartzConfiguration_apply]
  congr 1
  funext j mu
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
    frozenRightPacketConfiguration]
  ring

theorem continuous_frozenRightPacketConfiguration
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    Continuous
      (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
        D.frozenRightPacketConfiguration x q) := by
  apply continuous_pi
  intro j
  exact
    ((continuous_apply j).comp
      (continuous_multiGapRightSpectatorConfiguration D.T q.1)).sub
      (continuous_osiiAxisPairFrozenTranslation_logBase D.T q)

theorem continuous_frozenRightPacketSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    Continuous
      (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
        translateSchwartzNPoint (d := d)
          (osiiAxisPairFrozenTranslation D.T
            (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
          (D.frozenRightSource x q.1)) := by
  refine
    ((continuous_translateSchwartzConfiguration_fixed
      (osiiStep4MultiGapSelectedRightPositiveTimeSource
        d k hrho center y y' hcenter q.1).1).comp
      (D.continuous_frozenRightPacketConfiguration q)).congr ?_
  intro x
  exact (D.translate_frozenRightSource_eq_configuration x q).symm

/-- Rotate the frozen negative left source into ordinary Euclidean time and
reflect it back to a positive-time source. -/
noncomputable def rotatedFrozenLeftSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (q.1.val + 1) :=
  (osiiEuclideanRotateSchwartz
    (osiiAxisPairRotationData D.T q.2).matrix
    (osiiAxisPairRotationData D.T q.2).orthogonal
    (D.frozenLeftSource x q.1)).timeReflect

/-- Apply the active-gap compensation to the frozen right source before
rotating it into ordinary Euclidean time. -/
noncomputable def rotatedFrozenRightSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiStep4MultiGapAfterCount q.1 + 1) :=
  osiiEuclideanRotateSchwartz
    (osiiAxisPairRotationData D.T q.2).matrix
    (osiiAxisPairRotationData D.T q.2).orthogonal
    (translateSchwartzNPoint (d := d)
      (osiiAxisPairFrozenTranslation D.T
        (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
      (D.frozenRightSource x q.1))

theorem rotatedFrozenLeftSource_support
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport (D.rotatedFrozenLeftSource x q :
        NPointDomain d (q.1.val + 1) -> Complex) ⊆
      OrderedPositiveTimeRegion d (q.1.val + 1) := by
  apply SchwartzNPoint.timeReflect_tsupport_orderedPositive
  exact osiiEuclideanRotateSchwartz_tsupport_orderedNegative
    (osiiAxisPairRotationData D.T q.2).matrix
    (osiiAxisPairRotationData D.T q.2).orthogonal
    (D.frozenLeftSource x q.1) (D.frozenLeftSource_support x q)

theorem rotatedFrozenRightSource_support
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport (D.rotatedFrozenRightSource x q :
        NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) -> Complex) ⊆
      OrderedPositiveTimeRegion d
        (osiiStep4MultiGapAfterCount q.1 + 1) := by
  apply osiiEuclideanRotateSchwartz_tsupport_orderedPositive
  exact osiiEuclideanTranslation_preserves_orientedPositive
    (osiiAxisPairRotationData D.T q.2).matrix
    (osiiAxisPairFrozenTranslation D.T
      (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
    ((osiiAxisPairRotationData D.T q.2
      ).mulVec_frozenTranslation_time_nonneg D.hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b => le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (x q.1) b)))
    (D.frozenRightSource x q.1) (D.frozenRightSource_support x q)

/-- The rotated left source with its ordinary positive-time support proof. -/
noncomputable def rotatedFrozenLeftPositiveSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    euclideanPositiveTimeSubmodule (d := d) (q.1.val + 1) :=
  ⟨D.rotatedFrozenLeftSource x q, D.rotatedFrozenLeftSource_support x q⟩

/-- The rotated right source with its ordinary positive-time support proof. -/
noncomputable def rotatedFrozenRightPositiveSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    euclideanPositiveTimeSubmodule
      (d := d) (osiiStep4MultiGapAfterCount q.1 + 1) :=
  ⟨D.rotatedFrozenRightSource x q, D.rotatedFrozenRightSource_support x q⟩

theorem continuous_rotatedFrozenLeftSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    Continuous (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
      D.rotatedFrozenLeftSource x q) := by
  exact continuous_schwartzNPoint_timeReflect.comp
    ((continuous_osiiEuclideanRotateSchwartz
      (osiiAxisPairRotationData D.T q.2).matrix
      (osiiAxisPairRotationData D.T q.2).orthogonal).comp
      (continuous_schwartzNPoint_timeReflect.comp
        (D.continuous_frozenLeftPositiveSource q.1)))

theorem continuous_rotatedFrozenRightSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    Continuous (fun x : Fin k -> osiiAxisPairIndex d -> Real =>
      D.rotatedFrozenRightSource x q) := by
  exact (continuous_osiiEuclideanRotateSchwartz
    (osiiAxisPairRotationData D.T q.2).matrix
    (osiiAxisPairRotationData D.T q.2).orthogonal).comp
      (D.continuous_frozenRightPacketSource q)

theorem continuous_rotatedFrozenLeftPositiveSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    Continuous (D.rotatedFrozenLeftPositiveSource (q := q)) :=
  (D.continuous_rotatedFrozenLeftSource q).subtype_mk _

theorem continuous_rotatedFrozenRightPositiveSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    Continuous (D.rotatedFrozenRightPositiveSource (q := q)) :=
  (D.continuous_rotatedFrozenRightSource q).subtype_mk _

/-- On the logarithmic right-half-plane chart, the compensated frozen packet
is the Hilbert inner product of the two canonically rotated positive sources. -/
theorem compensatedFrozen_branch_eq_rotatedPositive_inner
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (w : Complex)
    (hw : 0 < ((osiiAxisPairRadius D.T : Complex) * Complex.exp w).re) :
    (OSIIAxisPairRotatedSourcePacket.compensatedFrozen
      D.T D.hT
      (osiiAxisPairPositiveCoefficients (x q.1))
      (fun b => le_of_lt
        (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
      q.2
      (D.frozenLeftSource x q.1)
      (D.frozenLeftSource_support x q)
      (D.frozenRightSource x q.1)
      (D.frozenRightSource_support x q)).branch OS lgc (Complex.exp w) =
      @inner Complex (OSHilbertSpace OS) _
        (osiiPositiveTimeSingleVectorCLM OS (q.1.val + 1)
          (D.rotatedFrozenLeftPositiveSource x q))
        (osTimeShiftHilbertComplex (d := d) OS lgc
          ((osiiAxisPairRadius D.T : Complex) * Complex.exp w)
          (osiiPositiveTimeSingleVectorCLM OS
            (osiiStep4MultiGapAfterCount q.1 + 1)
            (D.rotatedFrozenRightPositiveSource x q))) := by
  let P := OSIIAxisPairRotatedSourcePacket.compensatedFrozen
    D.T D.hT
    (osiiAxisPairPositiveCoefficients (x q.1))
    (fun b => le_of_lt
      (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
    q.2
    (D.frozenLeftSource x q.1)
    (D.frozenLeftSource_support x q)
    (D.frozenRightSource x q.1)
    (D.frozenRightSource_support x q)
  let Q := OSIIAxisPairRotatedSourcePacket.ofRotatedPositive
    D.T q.2
    (D.rotatedFrozenLeftSource x q)
    (D.rotatedFrozenLeftSource_support x q)
    (D.rotatedFrozenRightSource x q)
    (D.rotatedFrozenRightSource_support x q)
  have hPQleft : P.left = Q.left := by
    simp [P, Q, rotatedFrozenLeftSource,
      OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
      OSIIAxisPairRotatedSourcePacket.compensatedLeft,
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositive,
      osiiEuclideanCompensatedLeftSchwartz]
  have hPQright : P.right = Q.right := by
    dsimp [P, Q, rotatedFrozenRightSource,
      OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
      OSIIAxisPairRotatedSourcePacket.compensatedLeft,
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositive]
    rw [osiiEuclideanUnrotateSchwartz_rotate]
  change P.branch OS lgc (Complex.exp w) = _
  rw [show P.branch OS lgc (Complex.exp w) =
      Q.branch OS lgc (Complex.exp w) from
    congrFun
      (OSIIAxisPairRotatedSourcePacket.branch_eq_of_source_eq
        P Q hPQleft hPQright OS lgc)
      (Complex.exp w)]
  rw [OSIIAxisPairRotatedSourcePacket.ofRotatedPositive_branch_eq_holomorphicValue]
  rw [OSInnerProductTimeShiftHolomorphicValue_eq_inner_osTimeShiftHilbertComplex]
  · rfl
  · exact hw

theorem continuousOn_explicitFrozenPacket_branch
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    ContinuousOn
      (fun p : (Fin k -> osiiAxisPairIndex d -> Real) × Complex =>
        (OSIIAxisPairRotatedSourcePacket.compensatedFrozen
          D.T D.hT
          (osiiAxisPairPositiveCoefficients (p.1 q.1))
          (fun b => le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (p.1 q.1) b))
          q.2
          (D.frozenLeftSource p.1 q.1)
          (D.frozenLeftSource_support p.1 q)
          (D.frozenRightSource p.1 q.1)
          (D.frozenRightSource_support p.1 q)).branch
            OS lgc (Complex.exp p.2))
      (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2}) := by
  let Phi :
      ((Fin k -> osiiAxisPairIndex d -> Real) × Complex) ->
        Complex × OSHilbertSpace OS :=
    fun p =>
      ((osiiAxisPairRadius D.T : Complex) * Complex.exp p.2,
        osiiPositiveTimeSingleVectorCLM OS
          (osiiStep4MultiGapAfterCount q.1 + 1)
          (D.rotatedFrozenRightPositiveSource p.1 q))
  have hPhi : Continuous Phi := by
    refine Continuous.prodMk
      (continuous_const.mul (Complex.continuous_exp.comp continuous_snd)) ?_
    exact
      (osiiPositiveTimeSingleVectorCLM OS
        (osiiStep4MultiGapAfterCount q.1 + 1)).continuous.comp
          ((D.continuous_rotatedFrozenRightPositiveSource q).comp continuous_fst)
  have hPhi_maps : Set.MapsTo Phi
      (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2})
      ({z : Complex | 0 < z.re} ×ˢ Set.univ) := by
    intro p hp
    refine ⟨?_, trivial⟩
    change 0 < ((osiiAxisPairRadius D.T : Complex) * Complex.exp p.2).re
    rw [Complex.mul_re, Complex.exp_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (osiiAxisPairRadius_pos D.T)
      (mul_pos (Real.exp_pos _)
        (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.2)))
  have hshift : ContinuousOn
      (fun p : (Fin k -> osiiAxisPairIndex d -> Real) × Complex =>
        osTimeShiftHilbertComplex (d := d) OS lgc
          ((osiiAxisPairRadius D.T : Complex) * Complex.exp p.2)
          (osiiPositiveTimeSingleVectorCLM OS
            (osiiStep4MultiGapAfterCount q.1 + 1)
            (D.rotatedFrozenRightPositiveSource p.1 q)))
      (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2}) := by
    convert
      (continuousOn_osTimeShiftHilbertComplex_jointly
        (d := d) OS lgc).comp hPhi.continuousOn hPhi_maps using 1
    ext p
    rfl
  have hleftVector : Continuous
      (fun p : (Fin k -> osiiAxisPairIndex d -> Real) × Complex =>
        osiiPositiveTimeSingleVectorCLM OS (q.1.val + 1)
          (D.rotatedFrozenLeftPositiveSource p.1 q)) :=
    (osiiPositiveTimeSingleVectorCLM OS (q.1.val + 1)).continuous.comp
      ((D.continuous_rotatedFrozenLeftPositiveSource q).comp continuous_fst)
  have hinner : ContinuousOn
      (fun p : (Fin k -> osiiAxisPairIndex d -> Real) × Complex =>
        @inner Complex (OSHilbertSpace OS) _
          (osiiPositiveTimeSingleVectorCLM OS (q.1.val + 1)
            (D.rotatedFrozenLeftPositiveSource p.1 q))
          (osTimeShiftHilbertComplex (d := d) OS lgc
            ((osiiAxisPairRadius D.T : Complex) * Complex.exp p.2)
            (osiiPositiveTimeSingleVectorCLM OS
              (osiiStep4MultiGapAfterCount q.1 + 1)
              (D.rotatedFrozenRightPositiveSource p.1 q))))
      (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2}) :=
    hleftVector.continuousOn.inner hshift
  refine hinner.congr ?_
  intro p hp
  apply compensatedFrozen_branch_eq_rotatedPositive_inner OS lgc D p.1 q p.2
  rw [Complex.mul_re, Complex.exp_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (osiiAxisPairRadius_pos D.T)
    (mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.2)))

theorem spectatorPackage_data_left_eq_frozenLeftSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    (D.spectatorPackage x i).data.left = D.frozenLeftSource x i := by
  rw [(D.spectatorPackage x i).left_eq]
  exact congrArg SchwartzNPoint.timeReflect
    (osiiStep4MultiGapFrozenLeftPositiveSource_eq_selected_spectator
      d k hrho center y y' hcenter D.T D.hT x i).symm

theorem spectatorPackage_data_right_eq_frozenRightSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    (D.spectatorPackage x i).data.right = D.frozenRightSource x i := by
  rw [(D.spectatorPackage x i).right_eq]
  exact
    (osiiStep4MultiGapFrozenRightPositiveSource_eq_selected_spectator
      d k hrho center y y' hcenter D.T D.hT x i).symm

theorem packetFamily_packet_branch_eq_explicit
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (z : Complex) :
    ((D.packetFamily OS lgc).packet x q).branch OS lgc z =
      (OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        D.T D.hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b => le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (D.frozenLeftSource x q.1)
        (D.frozenLeftSource_support x q)
        (D.frozenRightSource x q.1)
        (D.frozenRightSource_support x q)).branch OS lgc z := by
  let A :=
    ((D.spectatorPackage x q.1).toSemigroupPacketFamily OS lgc
      ).packet (x q.1) q.2
  let E := OSIIAxisPairRotatedSourcePacket.compensatedFrozen
    D.T D.hT
    (osiiAxisPairPositiveCoefficients (x q.1))
    (fun b => le_of_lt
      (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
    q.2
    (D.frozenLeftSource x q.1)
    (D.frozenLeftSource_support x q)
    (D.frozenRightSource x q.1)
    (D.frozenRightSource_support x q)
  have hAEleft : A.left = E.left := by
    dsimp [A, E,
      OSIIAxisPairCompactCommonSourcePackage.toSemigroupPacketFamily,
      OSIIAxisPairCommonSourceData.toSemigroupPacketFamily,
      OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
      OSIIAxisPairRotatedSourcePacket.compensatedLeft]
    rw [D.spectatorPackage_data_left_eq_frozenLeftSource x q.1]
  have hAEright : A.right = E.right := by
    dsimp [A, E,
      OSIIAxisPairCompactCommonSourcePackage.toSemigroupPacketFamily,
      OSIIAxisPairCommonSourceData.toSemigroupPacketFamily,
      OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
      OSIIAxisPairRotatedSourcePacket.compensatedLeft]
    rw [D.spectatorPackage_data_right_eq_frozenRightSource x q.1]
  change A.branch OS lgc z = E.branch OS lgc z
  exact congrFun
    (OSIIAxisPairRotatedSourcePacket.branch_eq_of_source_eq
      A E hAEleft hAEright OS lgc) z

theorem continuousOn_packetFamily_branch
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    ContinuousOn
      (fun p : (Fin k -> osiiAxisPairIndex d -> Real) × Complex =>
        ((D.packetFamily OS lgc).packet p.1 q).branch
          OS lgc (Complex.exp p.2))
      (Set.univ ×ˢ {w : Complex | |w.im| < Real.pi / 2}) := by
  let explicit :
      ((Fin k -> osiiAxisPairIndex d -> Real) × Complex) -> Complex :=
    fun p =>
      (OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        D.T D.hT
        (osiiAxisPairPositiveCoefficients (p.1 q.1))
        (fun b => le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (p.1 q.1) b))
        q.2
        (D.frozenLeftSource p.1 q.1)
        (D.frozenLeftSource_support p.1 q)
        (D.frozenRightSource p.1 q.1)
        (D.frozenRightSource_support p.1 q)).branch
          OS lgc (Complex.exp p.2)
  have hfun :
      (fun p : (Fin k -> osiiAxisPairIndex d -> Real) × Complex =>
        ((D.packetFamily OS lgc).packet p.1 q).branch
          OS lgc (Complex.exp p.2)) = explicit := by
    funext p
    exact D.packetFamily_packet_branch_eq_explicit
      OS lgc p.1 q (Complex.exp p.2)
  rw [hfun]
  exact D.continuousOn_explicitFrozenPacket_branch OS lgc q

end OSIIStep4MultiGapSelectedCommonSlopeData
end OSReconstruction
