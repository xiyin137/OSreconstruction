/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicStageCompactBounds
import OSReconstruction.SCV.SchwartzFiniteSeminormBound






















noncomputable section

open Complex MeasureTheory Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]

namespace CompactRadialHullConstShiftWindowData

end CompactRadialHullConstShiftWindowData

omit [NeZero d] in
/-- A compact family of radial center segments whose translated cutoff
orbits lie in one open argument carrier has a common open zero-convex
moving-slice domain with logarithmic lifts in the matching tube.

This is the local-domain form needed by selected rooted charts: compactness
thickens the complete radial hull uniformly over the translated cutoff
support, while intersection with the raw moving-slice carrier keeps the
unnormalized continuation domain unchanged. -/
theorem exists_openZeroConvex_reflectedOrbitDomain_of_compact_radialHull
    {m : Nat}
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (eta : SchwartzMap (Fin (m + (m + 1)) -> Real) Complex)
    (heta_compact :
      HasCompactSupport
        (eta : (Fin (m + (m + 1)) -> Real) -> Complex))
    (epsilon : Real)
    (base : Set (Fin (m + (m + 1)) -> Real))
    (hbase_open : IsOpen base)
    (K : Set (Fin (m + m) -> Complex))
    (hK_compact : IsCompact K)
    (hK_nonempty : K.Nonempty)
    (hraw_segment : forall center, center ∈ K ->
      segment Real (0 : Fin (m + m) -> Complex) center ⊆
        reflectedMovingSliceCarrier A eta)
    (horbit_segment : forall center, center ∈ K ->
      forall w,
        w ∈ segment Real (0 : Fin (m + m) -> Complex) center ->
      forall sigma,
        sigma ∈ tsupport
          ((SCV.translateSchwartz
              (fun _ : Fin (m + (m + 1)) => epsilon) eta :
            SchwartzMap (Fin (m + (m + 1)) -> Real) Complex) :
            (Fin (m + (m + 1)) -> Real) -> Complex) ->
        -(reflectedReducedTimeDisplacementCLM m w) +
            osiiPositiveRealTimeEmbed sigma ∈
          osiiTimeArgumentCarrier base) :
    ∃ domain : Set (Fin (m + m) -> Complex),
      IsOpen domain ∧
      StarConvex Real 0 domain ∧
      (0 : Fin (m + m) -> Complex) ∈ domain ∧
      domain ⊆ reflectedMovingSliceCarrier A eta ∧
      K ⊆ domain ∧
      forall w, w ∈ domain ->
        forall sigma,
          sigma ∈ tsupport
            ((SCV.translateSchwartz
                (fun _ : Fin (m + (m + 1)) => epsilon) eta :
              SchwartzMap (Fin (m + (m + 1)) -> Real) Complex) :
              (Fin (m + (m + 1)) -> Real) -> Complex) ->
          ∃ z ∈ osiiLogarithmicTube base,
            osiiLogExp z =
              -(reflectedReducedTimeDisplacementCLM m w) +
                osiiPositiveRealTimeEmbed sigma := by
  let translatedEta : SchwartzMap
      (Fin (m + (m + 1)) -> Real) Complex :=
    SCV.translateSchwartz
      (fun _ : Fin (m + (m + 1)) => epsilon) eta
  let J : Set (Fin (m + (m + 1)) -> Real) :=
    tsupport
      (translatedEta :
        (Fin (m + (m + 1)) -> Real) -> Complex)
  let radialHull : Set (Fin (m + m) -> Complex) :=
    (fun p : Real × (Fin (m + m) -> Complex) => p.1 • p.2) ''
      (Set.Icc (0 : Real) 1 ×ˢ K)
  have hsmul_mem_segment :
      forall {center : Fin (m + m) -> Complex} {r : Real},
        r ∈ Set.Icc (0 : Real) 1 ->
          r • center ∈
            segment Real (0 : Fin (m + m) -> Complex) center := by
    intro center r hr
    rw [segment_eq_image_lineMap]
    refine ⟨r, hr, ?_⟩
    simp [AffineMap.lineMap_apply_module]
  have hsegment_subset_radialHull :
      forall center, center ∈ K ->
        segment Real (0 : Fin (m + m) -> Complex) center ⊆
          radialHull := by
    intro center hcenter w hw
    rw [segment_eq_image_lineMap] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    refine ⟨(r, center), ⟨hr, hcenter⟩, ?_⟩
    simp [AffineMap.lineMap_apply_module]
  have hradialHull_compact : IsCompact radialHull := by
    dsimp [radialHull]
    exact
      (isCompact_Icc.prod hK_compact).image
        (continuous_fst.smul continuous_snd)
  have htranslated_compact :
      HasCompactSupport
        (translatedEta :
          (Fin (m + (m + 1)) -> Real) -> Complex) := by
    dsimp [translatedEta]
    exact
      hasCompactSupport_translateSchwartz eta heta_compact
        (fun _ : Fin (m + (m + 1)) => epsilon)
  have hJ_compact : IsCompact J := by
    simpa [J, HasCompactSupport] using htranslated_compact
  let orbit :
      (Fin (m + m) -> Complex) ×
          (Fin (m + (m + 1)) -> Real) ->
        Fin (m + (m + 1)) -> Complex :=
    fun p =>
      -(reflectedReducedTimeDisplacementCLM m p.1) +
        osiiPositiveRealTimeEmbed p.2
  have horbit_continuous : Continuous orbit := by
    dsimp [orbit]
    exact
      (((reflectedReducedTimeDisplacementCLM m).continuous.comp
        continuous_fst).neg).add
        (continuous_osiiPositiveRealTimeEmbed.comp continuous_snd)
  let good :
      Set ((Fin (m + m) -> Complex) ×
        (Fin (m + (m + 1)) -> Real)) :=
    orbit ⁻¹' osiiTimeArgumentCarrier base
  have hgood_open : IsOpen good := by
    dsimp [good]
    exact
      (isOpen_timeArgumentCarrier_of_isOpen hbase_open).preimage
        horbit_continuous
  have hradialHull_good :
      radialHull ×ˢ J ⊆ good := by
    rintro ⟨w, sigma⟩ ⟨hw, hsigma⟩
    obtain ⟨⟨r, center⟩, ⟨hr, hcenter⟩, rfl⟩ := hw
    change orbit (r • center, sigma) ∈ osiiTimeArgumentCarrier base
    exact
      horbit_segment center hcenter (r • center)
        (hsmul_mem_segment hr) sigma (by simpa [J, translatedEta] using hsigma)
  obtain ⟨U, V, hU_open, _hV_open, hradialHull_U, hJ_V, hUV⟩ :=
    generalized_tube_lemma
      hradialHull_compact hJ_compact hgood_open hradialHull_good
  let raw : Set (Fin (m + m) -> Complex) :=
    reflectedMovingSliceCarrier A eta
  let Uraw : Set (Fin (m + m) -> Complex) := U ∩ raw
  have hUraw_open : IsOpen Uraw := by
    dsimp [Uraw, raw]
    exact hU_open.inter
      (isOpen_reflectedMovingSliceCarrier A eta heta_compact)
  have hsegment_subset_Uraw :
      forall center, center ∈ K ->
        segment Real (0 : Fin (m + m) -> Complex) center ⊆
          Uraw := by
    intro center hcenter w hw
    exact
      ⟨hradialHull_U (hsegment_subset_radialHull center hcenter hw),
        hraw_segment center hcenter hw⟩
  obtain ⟨center0, hcenter0⟩ := hK_nonempty
  have hzero_Uraw : (0 : Fin (m + m) -> Complex) ∈ Uraw :=
    hsegment_subset_Uraw center0 hcenter0
      (left_mem_segment Real (0 : Fin (m + m) -> Complex) center0)
  let domain : Set (Fin (m + m) -> Complex) :=
    openZeroConvexKernel Uraw
  refine
    ⟨domain,
      openZeroConvexKernel_open Uraw,
      openZeroConvexKernel_starConvex Uraw,
      zero_mem_openZeroConvexKernel hUraw_open hzero_Uraw,
      ?_,
      ?_,
      ?_⟩
  · exact
      (openZeroConvexKernel_subset Uraw).trans inter_subset_right
  · intro center hcenter
    exact
      mem_openZeroConvexKernel_of_segment_subset hUraw_open
        (hsegment_subset_Uraw center hcenter)
  · intro w hw sigma hsigma
    have hwU : w ∈ U :=
      (openZeroConvexKernel_subset Uraw hw).1
    have hsigmaV : sigma ∈ V := by
      apply hJ_V
      simpa [J, translatedEta] using hsigma
    have hgood : orbit (w, sigma) ∈ osiiTimeArgumentCarrier base := by
      exact hUV ⟨hwU, hsigmaV⟩
    refine
      ⟨osiiPrincipalLog (orbit (w, sigma)),
        osiiPrincipalLog_mem_logarithmicTube hgood,
        ?_⟩
    simpa [orbit] using osiiLogExp_principalLog hgood.1

/-- Compact logarithmic target data for one reflected moving source.

This is the geometric object produced before choosing a normalized envelope.
It remembers the compact target that will later be inserted into a finite
chart-local target family, together with the open local domain on which every
translated cutoff orbit has a lift in that target. -/
structure CompactLogTargetReflectedOrbitData
    {m : Nat}
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (eta : SchwartzMap (Fin (m + (m + 1)) -> Real) Complex)
    (epsilon : Real)
    (base : Set (Fin (m + (m + 1)) -> Real))
    (K : Set (Fin (m + m) -> Complex)) where
  domain : Set (Fin (m + m) -> Complex)
  orbitCarrier : Set (Fin (m + m) -> Complex)
  logTarget : Set (Fin (m + (m + 1)) -> Complex)
  domain_open : IsOpen domain
  domain_starConvex : StarConvex Real 0 domain
  zero_mem : (0 : Fin (m + m) -> Complex) ∈ domain
  domain_subset : domain ⊆ reflectedMovingSliceCarrier A eta
  orbitCarrier_compact : IsCompact orbitCarrier
  domain_subset_orbitCarrier : domain ⊆ orbitCarrier
  orbitCarrier_subset : orbitCarrier ⊆ reflectedMovingSliceCarrier A eta
  centers_mem : K ⊆ domain
  logTarget_compact : IsCompact logTarget
  logTarget_subset_tube : logTarget ⊆ osiiLogarithmicTube base
  logTarget_subset_normalizedPullback : forall t,
    logTarget ⊆
      (logarithmicPullbackStage
        (A.vi2NormalizedStage t epsilon)).carrier
  logTarget_exp_representation : forall z, z ∈ logTarget ->
    ∃ w : Fin (m + m) -> Complex,
      w ∈ orbitCarrier ∧
        ∃ sigma : Fin (m + (m + 1)) -> Real,
          sigma ∈ tsupport
            ((SCV.translateSchwartz
                (fun _ : Fin (m + (m + 1)) => epsilon) eta :
              SchwartzMap (Fin (m + (m + 1)) -> Real) Complex) :
              (Fin (m + (m + 1)) -> Real) -> Complex) ∧
          osiiLogExp z =
            -(reflectedReducedTimeDisplacementCLM m w) +
              osiiPositiveRealTimeEmbed sigma
  orbitLogLift : forall w, w ∈ orbitCarrier ->
    forall sigma,
      sigma ∈ tsupport
        ((SCV.translateSchwartz
            (fun _ : Fin (m + (m + 1)) => epsilon) eta :
          SchwartzMap (Fin (m + (m + 1)) -> Real) Complex) :
          (Fin (m + (m + 1)) -> Real) -> Complex) ->
      ∃ z ∈ logTarget,
        osiiLogExp z =
          -(reflectedReducedTimeDisplacementCLM m w) +
            osiiPositiveRealTimeEmbed sigma
  logLift : forall w, w ∈ domain ->
    forall sigma,
      sigma ∈ tsupport
        ((SCV.translateSchwartz
            (fun _ : Fin (m + (m + 1)) => epsilon) eta :
          SchwartzMap (Fin (m + (m + 1)) -> Real) Complex) :
          (Fin (m + (m + 1)) -> Real) -> Complex) ->
      ∃ z ∈ logTarget,
        osiiLogExp z =
          -(reflectedReducedTimeDisplacementCLM m w) +
            osiiPositiveRealTimeEmbed sigma

namespace CompactLogTargetReflectedOrbitData

end CompactLogTargetReflectedOrbitData

/-- One family-wide finite-seminorm majorant for a normalized VI.2 envelope.
The finite seminorm family and its coefficient may depend on arity, but not on
the spatial Schwartz test. -/
structure VI2NormalizedEnvelopeSeminormBoundData
    {S : SimultaneousTimeContinuationStageLevel d}
    {t : Nat} {epsilon : Real}
    {bound : forall k,
      SchwartzMap (Section43SpatialSpace d k) Complex -> Real}
    (D : VI2NormalizedEnvelopeFamilyData S t epsilon bound) where
  spatialSeminorms : Nat -> Finset (Nat × Nat)
  constant : Nat -> Real
  constant_nonneg : forall k, 0 <= constant k
  bound_le : forall k chi,
    bound k chi <=
      constant k *
        (spatialSeminorms k).sup
          (schwartzSeminormFamily Complex
            (Section43SpatialSpace d k) Complex) chi

namespace VI2NormalizedEnvelopeSeminormBoundData

variable
  {S : SimultaneousTimeContinuationStageLevel d}
  {t : Nat} {epsilon : Real}
  {bound : forall k,
    SchwartzMap (Section43SpatialSpace d k) Complex -> Real}
  {D : VI2NormalizedEnvelopeFamilyData S t epsilon bound}

end VI2NormalizedEnvelopeSeminormBoundData

/-- The common pointwise interface needed by moving-slice estimates on a
chosen logarithmic target.

This keeps target geometry separate from the source of the estimate.  A
star-convex envelope and a compact physical target both supply this same
small record, while downstream integration only uses the record itself. -/
structure VI2NormalizedTargetSeminormBoundData
    (S : SimultaneousTimeContinuationStageLevel d)
    (t : Nat) (epsilon : Real)
    (target : forall k, Set (Fin k -> Complex)) where
  spatialSeminorms : Nat -> Finset (Nat × Nat)
  constant : Nat -> Real
  constant_nonneg : forall k, 0 <= constant k
  norm_le : forall k z, z ∈ target k ->
    forall chi : SchwartzMap
      (Section43SpatialSpace d k) Complex,
      ‖((S.stage k).vi2NormalizedStage t epsilon).distribution
          (osiiLogExp z) chi‖ <=
        constant k *
          (spatialSeminorms k).sup
            (schwartzSeminormFamily Complex
              (Section43SpatialSpace d k) Complex) chi

namespace VI2NormalizedTargetSeminormProfileData

namespace BoundData

end BoundData
end VI2NormalizedTargetSeminormProfileData

namespace VI2NormalizedTargetSeminormBoundData

variable
  {S : SimultaneousTimeContinuationStageLevel d}
  {t : Nat} {epsilon : Real}
  {target : forall k, Set (Fin k -> Complex)}

end VI2NormalizedTargetSeminormBoundData

namespace VI2NormalizedCompactTargetSeminormBoundData

end VI2NormalizedCompactTargetSeminormBoundData

namespace VI2NormalizedEnvelopeCoverageData

end VI2NormalizedEnvelopeCoverageData

namespace VI2NormalizedEnvelopeCoverageData

variable
  {S : SimultaneousTimeContinuationStageLevel d}
  {t : Nat} {epsilon : Real}
  {bound : forall k,
    SchwartzMap (Section43SpatialSpace d k) Complex -> Real}
  {D : VI2NormalizedEnvelopeFamilyData S t epsilon bound}
  {target : forall k, Set (Fin k -> Complex)}

end VI2NormalizedEnvelopeCoverageData

end OSIIChapterV
end OSReconstruction
