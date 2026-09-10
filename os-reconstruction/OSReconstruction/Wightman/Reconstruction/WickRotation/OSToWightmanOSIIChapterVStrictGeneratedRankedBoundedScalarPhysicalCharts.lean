/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarGlobalSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientAmbientAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageExtensionConvexCoreAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialAssembly
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientBoundedChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVBoundedScalarTargetSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedBounds
















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A flat point with a generator active seed supplies contracted mixed
sources and bridge angle whose physical generator fiber contains the
exponentiated target. -/
theorem exists_generatorData_osiiLogExp_coefficientMap_mem
    {m n rank targetDepth : Nat}
    {rho : Real}
    (seed : Fin n -> Fin m -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (hgenerator : IsGeneratorRankSuccessorSeed
      rank m targetDepth (seed active)) :
    ∃ (i : GeneratorIndex m) (sourceDepth : Nat)
        (left : Fin i.n -> Real) (theta : Real)
        (right : Fin i.m -> Real),
      sourceDepth + 1 = targetDepth ∧
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n sourceDepth left ∧
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m sourceDepth right ∧
      |theta| < Real.pi / 2 ∧
      osiiLogExp (osiiStrictScalarSeedCoefficientMap seed r) ∈
        osiiTimeArgumentCarrier
          ({osiiArgumentGeneratorPoint i left theta right} :
            Set (Fin m -> Real)) := by
  obtain ⟨i, sourceDepth, left, theta, right,
      hdepth, hleft, hright, htheta, hpoint⟩ :=
    osiiStrictScalarSeedCoefficientMap_im_isGeneratorRankSuccessorSeed
      seed r active hactive hrho_lt_one hgenerator
  have hscalar :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m targetDepth
          (osiiArgumentGeneratorPoint i left theta right) := by
    rw [← hdepth]
    exact
      OSIIStrictGeneratedLogarithmicArgumentAtRank.generatorMemSucc
        i sourceDepth left theta right hleft hright htheta
  have hstrip :
      (fun j => (osiiStrictScalarSeedCoefficientMap seed r j).im) ∈
        osiiOpenArgumentStrip m := by
    intro j
    rw [← hpoint]
    exact hscalar.toStrictGenerated.coordinate_abs_lt_pi_div_two j
  refine ⟨i, sourceDepth, left, theta, right,
    hdepth, hleft, hright, htheta, ?_⟩
  apply osiiLogExp_mem_argumentCarrier
  exact
    ⟨Set.mem_singleton_iff.mpr hpoint.symm, hstrip⟩

/-- A flat point with a mixed-tail active seed exponentiates into the
physical tail carrier of a contracted mixed argument at the same source
rank. -/
theorem osiiLogExp_coefficientMap_mem_mixedTailArgumentCarrier
    {m n rank targetDepth : Nat}
    {rho : Real}
    (seed : Fin n -> Fin m -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (htail : IsMixedTailRankSuccessorSeed
      rank m targetDepth (seed active)) :
    osiiLogExp (osiiStrictScalarSeedCoefficientMap seed r) ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) targetDepth rank) := by
  obtain ⟨y, hy, htail_eq⟩ :=
    osiiStrictScalarSeedCoefficientMap_im_isMixedTailRankSuccessorSeed
      seed r active hactive hrho_lt_one htail
  have hstrip :
      (fun j => (osiiStrictScalarSeedCoefficientMap seed r j).im) ∈
        osiiOpenArgumentStrip m := by
    intro j
    rw [← htail_eq]
    simpa [Fin.tail] using
      hy.toStrictGenerated.coordinate_abs_lt_pi_div_two j.succ
  have hhead : y 0 = 0 :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
      (by omega) hy
  have hcons :
      Fin.cons 0
          (fun j =>
            (osiiStrictScalarSeedCoefficientMap seed r j).im) =
        y := by
    rw [← htail_eq, ← hhead]
    exact Fin.cons_self_tail y
  refine ⟨osiiLogExp_mem_rightHalfPlane hstrip, ?_⟩
  rw [osiiTimeArgumentVector_logExp hstrip, hcons]
  exact hy

/-- Scaling the coefficient vector is exactly the radial line in ambient
logarithmic coordinates. -/
theorem lineMap_zero_coefficientMap_eq_smul
    {m n : Nat}
    (seed : Fin n -> Fin m -> Real)
    (r : Fin n -> Complex)
    (t : Real) :
    AffineMap.lineMap
        (0 : Fin m -> Complex)
        (osiiStrictScalarSeedCoefficientMap seed r) t =
      osiiStrictScalarSeedCoefficientMap seed (t • r) := by
  funext j
  simp [AffineMap.lineMap_apply_module,
    osiiStrictScalarSeedCoefficientMap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Radial contraction preserves a chosen active imaginary coefficient and
its closed bound. -/
theorem coefficient_smul_preserves_activeImaginaryBound
    {n : Nat} {rho : Real}
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
    |((t • r) active).im| <= rho ∧
      forall j, j ≠ active -> ((t • r) j).im = 0 := by
  constructor
  · have hcontract : t * |(r active).im| <= |(r active).im| := by
      calc
        t * |(r active).im| <= 1 * |(r active).im| :=
          mul_le_mul_of_nonneg_right ht.2
            (abs_nonneg (r active).im)
        _ = |(r active).im| := one_mul _
    have hscaled := hcontract.trans hactive.1
    simpa [Pi.smul_apply, abs_mul, abs_of_nonneg ht.1] using hscaled
  · intro j hj
    simp [Pi.smul_apply, hactive.2 j hj]

/-- A bounded scalar continuation is the restriction of one fixed spatial
pairing of a physical continuation stage in logarithmic coordinates. -/
structure BoundedScalarLogarithmicRestrictionData
    {d m : Nat} [NeZero d] {B : Real}
    (A : BoundedScalarContinuationData m B)
    (physical : OSIITimeContinuationStage d m)
    (chi : SchwartzMap (Section43SpatialSpace d m) Complex) where
  carrier_subset_pullback :
    A.carrier ⊆ (logarithmicPullbackStage physical).carrier
  pullback_eq_toFun :
    Set.EqOn
      (fun z => physical.distribution (osiiLogExp z) chi)
      A.toFun A.carrier

namespace BoundedScalarLogarithmicRestrictionData

variable {d m : Nat} [NeZero d] {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {physical nextPhysical : OSIITimeContinuationStage d m}
variable {chi : SchwartzMap (Section43SpatialSpace d m) Complex}

/-- Carrier inclusion and one local zero germ determine the complete physical
realization of a bounded scalar continuation.  This is the identity-theorem
adapter used after scalar and physical successors have been built in
parallel: global agreement need not be carried through every intermediate
gluing operation. -/
def ofCarrierSubset_ofEventuallyEq
    (carrier_subset :
      A.carrier ⊆ (logarithmicPullbackStage physical).carrier)
    (germ :
      (fun z => physical.distribution (osiiLogExp z) chi) =ᶠ[
        nhds (0 : Fin m -> Complex)] A.toFun) :
    BoundedScalarLogarithmicRestrictionData A physical chi where
  carrier_subset_pullback := carrier_subset
  pullback_eq_toFun := by
    have hconnected : IsConnected A.carrier :=
      (A.carrier_starConvex.isPathConnected A.zero_mem).isConnected
    have hphysical : DifferentiableOn Complex
        (fun z => physical.distribution (osiiLogExp z) chi) A.carrier := by
      simpa using
        ((logarithmicPullbackStage physical).weaklyHolomorphic chi).mono
          carrier_subset
    exact identity_theorem_SCV A.carrier_open hconnected
      hphysical A.differentiableOn A.zero_mem germ

/-- Rebase a bounded logarithmic restriction along a genuine physical stage
extension.  No new scalar argument is needed: the new physical stage agrees
with the old one everywhere the bounded predecessor was defined. -/
def rebasePhysical
    (R : BoundedScalarLogarithmicRestrictionData A physical chi)
    (carrier_subset : physical.carrier ⊆ nextPhysical.carrier)
    (extendsOld : Set.EqOn nextPhysical.distribution
      physical.distribution physical.carrier) :
    BoundedScalarLogarithmicRestrictionData A nextPhysical chi where
  carrier_subset_pullback := by
    intro z hz
    exact carrier_subset (R.carrier_subset_pullback hz)
  pullback_eq_toFun := by
    intro z hz
    have hzphysical := R.carrier_subset_pullback hz
    exact
      congrArg
        (fun T : OSIISpatialDistribution d m => T chi)
        (extendsOld hzphysical) |>.trans
          (R.pullback_eq_toFun hz)

/-- Recover physical realization after a scalar extension and a physical
extension have independently retained the same predecessor.  Agreement on
the predecessor's open zero neighborhood is enough; the identity theorem
propagates it over the complete new bounded carrier. -/
def ofRetainedExtensions
    {A0 : BoundedScalarContinuationData m B}
    {physical0 : OSIITimeContinuationStage d m}
    (R0 : BoundedScalarLogarithmicRestrictionData A0 physical0 chi)
    (scalar_eq_old : Set.EqOn A.toFun A0.toFun A0.carrier)
    (physical_eq_old : Set.EqOn physical.distribution
      physical0.distribution physical0.carrier)
    (carrier_subset :
      A.carrier ⊆ (logarithmicPullbackStage physical).carrier) :
    BoundedScalarLogarithmicRestrictionData A physical chi := by
  apply ofCarrierSubset_ofEventuallyEq carrier_subset
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨A0.carrier, A0.carrier_open.mem_nhds A0.zero_mem, ?_⟩
  intro z hz
  have hz0 := R0.carrier_subset_pullback hz
  have hzphysical0 : osiiLogExp z ∈ physical0.carrier := hz0
  calc
    physical.distribution (osiiLogExp z) chi =
        physical0.distribution (osiiLogExp z) chi :=
      congrArg
        (fun T : OSIISpatialDistribution d m => T chi)
        (physical_eq_old hzphysical0)
    _ = A0.toFun z := R0.pullback_eq_toFun hz
    _ = A.toFun z := (scalar_eq_old hz).symm

/-- Rebase a bounded logarithmic restriction through the successor obtained
by gluing a convex-core extension atlas.  The atlas itself supplies both
physical extension obligations. -/
def rebaseConvexCoreAtlas
    {predecessor : OSIITimeContinuationStage d m}
    (R : BoundedScalarLogarithmicRestrictionData A predecessor chi)
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor) :
    BoundedScalarLogarithmicRestrictionData A P.successorStage chi :=
  R.rebasePhysical P.oldCarrier_subset_successorCarrier
    P.successorStage_extends_predecessor

end BoundedScalarLogarithmicRestrictionData

/-- A bounded scalar envelope bundled with its realization by one fixed
spatial pairing of a physical continuation stage.  Keeping these two objects
together prevents the quantitative rank/depth induction from losing the
physical function whose generator and vacuum-tail charts it must bound. -/
structure BoundedScalarPhysicalRealizationData
    {d m : Nat} [NeZero d]
    (physical : OSIITimeContinuationStage d m)
    (chi : SchwartzMap (Section43SpatialSpace d m) Complex)
    (B : Real) where
  continuation : BoundedScalarContinuationData m B
  restriction : BoundedScalarLogarithmicRestrictionData
    continuation physical chi

namespace BoundedScalarPhysicalRealizationData

variable {d m : Nat} [NeZero d] {B : Real}
variable {physical nextPhysical : OSIITimeContinuationStage d m}
variable {chi : SchwartzMap (Section43SpatialSpace d m) Complex}

end BoundedScalarPhysicalRealizationData

namespace ZeroPointedAmbientChartData

variable {d m : Nat} [NeZero d]
variable {physical : OSIITimeContinuationStage d m}
variable {target : Fin m -> Complex}

/-- Restrict the logarithmic pullback of a physical stage to an open convex
domain containing zero and one target.  The whole restricted domain is a
predecessor agreement seed by construction. -/
def ofLogarithmicRestriction
    (domain : Set (Fin m -> Complex))
    (domain_open : IsOpen domain)
    (domain_convex : Convex Real domain)
    (zero_mem : (0 : Fin m -> Complex) ∈ domain)
    (target_mem : target ∈ domain)
    (domain_subset :
      domain ⊆ (logarithmicPullbackStage physical).carrier) :
    ZeroPointedAmbientChartData physical target where
  stage :=
    { carrier := domain
      carrier_open := domain_open
      distribution :=
        (logarithmicPullbackStage physical).distribution
      weaklyHolomorphic := fun psi =>
        (logarithmicPullbackStage physical).weaklyHolomorphic psi
          |>.mono domain_subset }
  carrier_convex := domain_convex
  zero_mem := zero_mem
  target_mem := target_mem
  seedDomain := domain
  seed_open := domain_open
  zero_mem_seed := zero_mem
  seed_subset_overlap := fun _z hz => ⟨hz, domain_subset hz⟩
  seed_agreesPredecessor := Set.eqOn_refl _ domain

end ZeroPointedAmbientChartData

/-- A zero-pointed physical logarithmic chart with the exact scalar bound and
the predecessor seed needed by bounded gluing. -/
structure BoundedZeroPointedAmbientChartData
    {d m : Nat} [NeZero d] {B : Real}
    {A : BoundedScalarContinuationData m B}
    {physical : OSIITimeContinuationStage d m}
    {chi : SchwartzMap (Section43SpatialSpace d m) Complex}
    (R : BoundedScalarLogarithmicRestrictionData A physical chi)
    (target : Fin m -> Complex) where
  chart : ZeroPointedAmbientChartData physical target
  norm_pairing_le : forall z, z ∈ chart.stage.carrier ->
    ‖chart.stage.distribution z chi‖ <= B

namespace BoundedZeroPointedAmbientChartData

variable {d m : Nat} [NeZero d] {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {physical : OSIITimeContinuationStage d m}
variable {chi : SchwartzMap (Section43SpatialSpace d m) Complex}
variable {R : BoundedScalarLogarithmicRestrictionData A physical chi}
variable {target : Fin m -> Complex}

/-- Rebase a bounded physical chart across a genuine extension of its
physical predecessor.  The chart branch and its bound are unchanged; only
the overlap comparison is transported to the larger physical stage. -/
def rebasePhysical
    {nextPhysical : OSIITimeContinuationStage d m}
    (D : BoundedZeroPointedAmbientChartData R target)
    (carrier_subset : physical.carrier ⊆ nextPhysical.carrier)
    (extendsOld : Set.EqOn nextPhysical.distribution
      physical.distribution physical.carrier) :
    BoundedZeroPointedAmbientChartData
      (R.rebasePhysical carrier_subset extendsOld) target where
  chart :=
    { stage := D.chart.stage
      carrier_convex := D.chart.carrier_convex
      zero_mem := D.chart.zero_mem
      target_mem := D.chart.target_mem
      seedDomain := D.chart.seedDomain
      seed_open := D.chart.seed_open
      zero_mem_seed := D.chart.zero_mem_seed
      seed_subset_overlap := by
        intro z hz
        have hold := D.chart.seed_subset_overlap hz
        exact ⟨hold.1, carrier_subset hold.2⟩
      seed_agreesPredecessor := by
        intro z hz
        have hold := D.chart.seed_subset_overlap hz
        exact
          (D.chart.seed_agreesPredecessor hz).trans
            (extendsOld hold.2).symm }
  norm_pairing_le := D.norm_pairing_le

/-- Rebase a bounded physical chart to a specified logarithmic restriction
on the larger stage.  The restriction is proof-only provenance; the chart
branch and numerical estimate are transported exactly as in
`rebasePhysical`. -/
def rebasePhysicalTo
    {nextPhysical : OSIITimeContinuationStage d m}
    (D : BoundedZeroPointedAmbientChartData R target)
    (Rnext : BoundedScalarLogarithmicRestrictionData
      A nextPhysical chi)
    (carrier_subset : physical.carrier ⊆ nextPhysical.carrier)
    (extendsOld : Set.EqOn nextPhysical.distribution
      physical.distribution physical.carrier) :
    BoundedZeroPointedAmbientChartData Rnext target where
  chart :=
    { stage := D.chart.stage
      carrier_convex := D.chart.carrier_convex
      zero_mem := D.chart.zero_mem
      target_mem := D.chart.target_mem
      seedDomain := D.chart.seedDomain
      seed_open := D.chart.seed_open
      zero_mem_seed := D.chart.zero_mem_seed
      seed_subset_overlap := by
        intro z hz
        have hold := D.chart.seed_subset_overlap hz
        exact ⟨hold.1, carrier_subset hold.2⟩
      seed_agreesPredecessor := by
        intro z hz
        have hold := D.chart.seed_subset_overlap hz
        exact
          (D.chart.seed_agreesPredecessor hz).trans
            (extendsOld hold.2).symm }
  norm_pairing_le := D.norm_pairing_le

/-- Evaluate the physical chart on the fixed spatial test and retain its
zero-centered predecessor germ. -/
def toTargetChart
    (D : BoundedZeroPointedAmbientChartData R target) :
    BoundedScalarTargetChartData A target where
  domain := D.chart.stage.carrier
  domain_open := D.chart.stage.carrier_open
  domain_convex := D.chart.carrier_convex
  zero_mem_domain := D.chart.zero_mem
  target_mem_domain := D.chart.target_mem
  toFun := fun z => D.chart.stage.distribution z chi
  toFun_differentiableOn := D.chart.stage.weaklyHolomorphic chi
  norm_toFun_le := fun {z} hz => D.norm_pairing_le z hz
  exists_open_eq_predecessor := by
    let U := D.chart.seedDomain ∩ A.carrier
    refine
      ⟨U, D.chart.seed_open.inter A.carrier_open,
        ⟨D.chart.zero_mem_seed, A.zero_mem⟩, ?_, ?_⟩
    · intro z hz
      exact
        ⟨(D.chart.seed_subset_overlap hz.1).1, hz.2⟩
    · intro z hz
      have hphysical :=
        congrArg
          (fun T : OSIISpatialDistribution d m => T chi)
          (D.chart.seed_agreesPredecessor hz.1)
      have hchart_eq_pullback :
          D.chart.stage.distribution z chi =
            physical.distribution (osiiLogExp z) chi := by
        simpa using hphysical
      exact hchart_eq_pullback.trans
        (R.pullback_eq_toFun hz.2)

/-- A bounded open physical neighborhood of the complete zero-to-target
segment contains a bounded zero-pointed convex chart. -/
theorem nonempty_ofPhysicalSegmentNeighborhood
    (R : BoundedScalarLogarithmicRestrictionData A physical chi)
    (target : Fin m -> Complex)
    (neighborhood : Set (Fin m -> Complex))
    (neighborhood_open : IsOpen neighborhood)
    (segment_subset : segment Real 0 target ⊆ neighborhood)
    (neighborhood_subset :
      neighborhood ⊆ (logarithmicPullbackStage physical).carrier)
    (norm_pairing_le : forall z, z ∈ neighborhood ->
      ‖physical.distribution (osiiLogExp z) chi‖ <= B) :
    Nonempty (BoundedZeroPointedAmbientChartData R target) := by
  have hcompact : IsCompact (segment Real 0 target) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨eps, heps, hthick⟩ :=
    hcompact.exists_thickening_subset_open
      neighborhood_open segment_subset
  let domain := Metric.thickening eps (segment Real 0 target)
  let C : ZeroPointedAmbientChartData physical target :=
    ZeroPointedAmbientChartData.ofLogarithmicRestriction
      domain Metric.isOpen_thickening
      ((convex_segment (0 : Fin m -> Complex) target).thickening eps)
      (Metric.self_subset_thickening heps _
        (left_mem_segment Real 0 target))
      (Metric.self_subset_thickening heps _
        (right_mem_segment Real 0 target))
      (hthick.trans neighborhood_subset)
  refine ⟨{
    chart := C
    norm_pairing_le := ?_ }⟩
  intro z hz
  simpa [C, ZeroPointedAmbientChartData.ofLogarithmicRestriction] using
    norm_pairing_le z (hthick hz)

/-- If the whole radial segment is already in the bounded scalar
predecessor, its physical logarithmic restriction supplies the old-seed
chart with no additional estimate. -/
theorem nonempty_ofPredecessorSegment
    (R : BoundedScalarLogarithmicRestrictionData A physical chi)
    (target : Fin m -> Complex)
    (segment_subset : segment Real 0 target ⊆ A.carrier) :
    Nonempty (BoundedZeroPointedAmbientChartData R target) := by
  apply nonempty_ofPhysicalSegmentNeighborhood
    R target A.carrier A.carrier_open segment_subset
    R.carrier_subset_pullback
  intro z hz
  calc
    ‖physical.distribution (osiiLogExp z) chi‖ =
        ‖A.toFun z‖ := congrArg norm (R.pullback_eq_toFun hz)
    _ <= B := A.norm_le z hz

/-- Endpoint membership in the star-convex bounded predecessor is enough for
the old-seed chart; the complete radial segment is then automatic. -/
theorem nonempty_ofPredecessorTarget
    (R : BoundedScalarLogarithmicRestrictionData A physical chi)
    (target : Fin m -> Complex)
    (target_mem : target ∈ A.carrier) :
    Nonempty (BoundedZeroPointedAmbientChartData R target) :=
  nonempty_ofPredecessorSegment R target
    (A.carrier_starConvex.segment_subset target_mem)

end BoundedZeroPointedAmbientChartData

namespace BoundedScalarTargetChartData

variable {d m : Nat} [NeZero d] {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {physical : OSIITimeContinuationStage d m}
variable {chi : SchwartzMap (Section43SpatialSpace d m) Complex}
variable {R : BoundedScalarLogarithmicRestrictionData A physical chi}
variable {target : Fin m -> Complex}

end BoundedScalarTargetChartData

/-- Exact fixed-test bounds on every selected convex core of a genuine
extension atlas.  The local branches may come from different rooted packet
or vacuum-tail constructions; compatibility and physical gluing are already
carried by `GeneratorStageExtensionConvexCoreAtlasData`. -/
structure BoundedGeneratorStageExtensionConvexCoreAtlasData
    {d m : Nat} {B : Real}
    {predecessor : OSIITimeContinuationStage d m}
    (P : GeneratorStageExtensionConvexCoreAtlasData predecessor)
    (chi : SchwartzMap (Section43SpatialSpace d m) Complex) where
  norm_extension_le : forall (a : P.chart) z,
    z ∈ P.carrier a ->
      ‖(P.extension a).distribution (P.chartGenerator a) z chi‖ <= B

namespace BoundedGeneratorStageExtensionConvexCoreAtlasData

variable {d m : Nat} {B : Real}
variable {predecessor : OSIITimeContinuationStage d m}
variable {P : GeneratorStageExtensionConvexCoreAtlasData predecessor}
variable {chi : SchwartzMap (Section43SpatialSpace d m) Complex}

/-- The logarithmic preimage of the union of all bounded physical cores. -/
def physicalNeighborhood
    (_D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B) P chi) :
    Set (Fin m -> Complex) :=
  osiiLogExp ⁻¹' ⋃ a, P.carrier a

theorem physicalNeighborhood_open
    (D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B) P chi) :
    IsOpen D.physicalNeighborhood := by
  exact
    (isOpen_iUnion fun a => P.carrier_open a).preimage
      osiiLogExp_differentiable.continuous

theorem physicalNeighborhood_subset_pullback
    (D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B) P chi) :
    D.physicalNeighborhood ⊆
      (logarithmicPullbackStage P.successorStage).carrier := by
  intro z hz
  change osiiLogExp z ∈ ⋃ a, P.carrier a at hz
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
  exact P.carrier_subset_successorCarrier a ha

/-- The twice-glued successor retains the chartwise bound at every physical
point in the union of the selected convex cores. -/
theorem norm_successor_le_of_mem_iUnion_carrier
    (D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B) P chi)
    {z : OSIITimeGapSpace m}
    (hz : z ∈ ⋃ a, P.carrier a) :
    ‖P.successorStage.distribution z chi‖ <= B := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
  have heq := congrArg
    (fun T : OSIISpatialDistribution d m => T chi)
    (P.successorStage_eqOn_extensionCarrier a ha)
  calc
    ‖P.successorStage.distribution z chi‖ =
        ‖(P.extension a).distribution
          (P.chartGenerator a) z chi‖ :=
      congrArg norm heq
    _ <= B := D.norm_extension_le a z ha

/-- The final twice-glued physical successor retains the exact local bound
throughout the union of the selected cores. -/
theorem norm_successor_le
    (D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B) P chi)
    {z : Fin m -> Complex}
    (hz : z ∈ D.physicalNeighborhood) :
    ‖P.successorStage.distribution (osiiLogExp z) chi‖ <= B := by
  change osiiLogExp z ∈ ⋃ a, P.carrier a at hz
  exact D.norm_successor_le_of_mem_iUnion_carrier hz

/-- If the selected bounded cores cover the exponentiated zero-to-target
segment, their open union supplies the bounded physical chart required by
the scalar rank successor. -/
theorem nonempty_boundedZeroPointedChart
    [NeZero d]
    {A : BoundedScalarContinuationData m B}
    (D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B) P chi)
    (R : BoundedScalarLogarithmicRestrictionData
      A P.successorStage chi)
    (target : Fin m -> Complex)
    (segment_subset :
      segment Real 0 target ⊆ D.physicalNeighborhood) :
    Nonempty (BoundedZeroPointedAmbientChartData R target) :=
  BoundedZeroPointedAmbientChartData.nonempty_ofPhysicalSegmentNeighborhood
    R target D.physicalNeighborhood D.physicalNeighborhood_open
    segment_subset D.physicalNeighborhood_subset_pullback
    (fun _z hz => D.norm_successor_le hz)

end BoundedGeneratorStageExtensionConvexCoreAtlasData

namespace BoundedGeneratorStageExtensionFiniteSubatlasData

variable {d m : Nat} {B : Real}
variable {predecessor : OSIITimeContinuationStage d m}
variable {P : GeneratorStageExtensionConvexCoreAtlasData predecessor}
variable {chi : SchwartzMap (Section43SpatialSpace d m) Complex}

end BoundedGeneratorStageExtensionFiniteSubatlasData

namespace GeneratorOpenHilbertFieldScaleBlockData

variable {d m shell : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {B : Real}

end GeneratorOpenHilbertFieldScaleBlockData

namespace BoundedReflectedMovingSliceRankLadderData

end BoundedReflectedMovingSliceRankLadderData

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

namespace RootedTargetHubPointedDirectExtensionData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {i : GeneratorIndex k}
  {hub : Fin k -> Real}
  {z : OSIITimeGapSpace k}
  {iota : Type*}
  {atlas : GeneratorStagePointedConvexAtlas
    (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
    (osiiPositiveRealTimeEmbed hub) iota}

end RootedTargetHubPointedDirectExtensionData

namespace RootedGeneratorBoundedApproximationContinuationData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {i : GeneratorIndex k}
  {hub : Fin k -> Real}
  {z : OSIITimeGapSpace k}
  {iota : Type*}
  {atlas : GeneratorStagePointedConvexAtlas
    (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
    (osiiPositiveRealTimeEmbed hub) iota}
  {D : RootedTargetHubPointedDirectExtensionData
    S depth P lgc i hub z atlas}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}

end RootedGeneratorBoundedApproximationContinuationData

namespace RootedGeneratorWeightedFieldNormSqBoundData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {i : GeneratorIndex k}
  {hub : Fin k -> Real}
  {z : OSIITimeGapSpace k}
  {iota : Type*}
  {atlas : GeneratorStagePointedConvexAtlas
    (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
    (osiiPositiveRealTimeEmbed hub) iota}
  {D : RootedTargetHubPointedDirectExtensionData
    S depth P lgc i hub z atlas}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}

end RootedGeneratorWeightedFieldNormSqBoundData

namespace RootedGeneratorWeightedFieldNormSqBoundData

end RootedGeneratorWeightedFieldNormSqBoundData

namespace RootedGeneratorWeightedGramContinuationData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {i : GeneratorIndex k}
  {hub : Fin k -> Real}
  {z : OSIITimeGapSpace k}
  {iota : Type*}
  {atlas : GeneratorStagePointedConvexAtlas
    (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
    (osiiPositiveRealTimeEmbed hub) iota}
  {D : RootedTargetHubPointedDirectExtensionData
    S depth P lgc i hub z atlas}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}

end RootedGeneratorWeightedGramContinuationData

/-- The Hermite coefficient weight used by both sides of a rooted finite
shell.  Naming it once keeps the source-level continuation package aligned
definitionally with the Hilbert direct-sum estimate. -/
noncomputable def rootedGeneratorWeightedGramHermiteWeight
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k)
    (test : SchwartzMap (Section43SpatialSpace d k) Complex)
    (mode : Nat) : Real :=
  ‖complexSpatialHermiteCoefficientCLM
    d (k + 1) (Nat.succ_pos k) mode
    (rootedGeneratorSplitSpatialLiftCLM i test)‖

namespace RootedTargetHubPointedDirectExtensionData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {i : GeneratorIndex k}
  {hub : Fin k -> Real}
  {z : OSIITimeGapSpace k}
  {iota : Type*}
  {atlas : GeneratorStagePointedConvexAtlas
    (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
    (osiiPositiveRealTimeEmbed hub) iota}

end RootedTargetHubPointedDirectExtensionData

namespace RootedAllSplitWeightedDiagonalBoundData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {H : RootedA0BlockContinuousTranslationData OS A R}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}

end RootedAllSplitWeightedDiagonalBoundData

/-- Exact initial moving-source germs for every split of one rooted shell,
all with one common strict bound.  This is the analytic input prior to the
separate bounded scalar rank-successor construction. -/
structure RootedAllSplitWeightedSourceInitialRestrictionData
    {d k depth : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (test : SchwartzMap (Section43SpatialSpace d k) Complex)
    (B : Real) where
  leftEndpointBound : forall
      (m : Nat) (hn : 1 <= 1) (hm : 1 <= m)
      (hnm : k = 1 + m - 1) (scale : Nat),
    let i : GeneratorIndex k := ⟨1, m, hn, hm, hnm⟩
    ‖OS.S 2
      ((rootedAnchoredLeftOneParticleOpenFieldScaleBlockRealEdgeData
          A R H i rfl).oneParticleWeightedDiagonalSchwingerSource
        scale scale
        (fun mode =>
          rootedGeneratorWeightedGramHermiteWeight i test mode))‖ <= B
  rightEndpointBound : forall
      (n : Nat) (hn : 1 <= n) (hm : 1 <= 1)
      (hnm : k = n + 1 - 1) (scale : Nat),
    let i : GeneratorIndex k := ⟨n, 1, hn, hm, hnm⟩
    ‖OS.S 2
      ((rootedAnchoredRightOneParticleOpenFieldScaleBlockRealEdgeData
          A R H i rfl).oneParticleWeightedDiagonalSchwingerSource
        scale scale
        (fun mode =>
          rootedGeneratorWeightedGramHermiteWeight i test mode))‖ <= B
  leftNontrivial : forall
      (q m : Nat) (hn : 1 <= q + 2) (hm : 1 <= m)
      (hnm : k = q + 2 + m - 1) (scale : Nat),
    let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    let D := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
    BoundedReflectedMovingSliceInitialRestrictionData
      D.reflectedGram.atlas.sourceStage.stage
      D.reflectedGram.atlas.sourceStage.germ.η
      (D.weightedDiagonalMovingSliceSource
        (scale + H.commonTailStart i) scale
        (fun mode =>
          rootedGeneratorWeightedGramHermiteWeight i test mode)
        (leftSpatialHermiteBlock d i)) B
  rightNontrivial : forall
      (n q : Nat) (hn : 1 <= n) (hm : 1 <= q + 2)
      (hnm : k = n + (q + 2) - 1) (scale : Nat),
    let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
    let D := rootedRightNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
    BoundedReflectedMovingSliceInitialRestrictionData
      D.reflectedGram.atlas.sourceStage.stage
      D.reflectedGram.atlas.sourceStage.germ.η
      (D.weightedDiagonalMovingSliceSource
        (scale + H.commonTailStart i) scale
        (fun mode =>
          rootedGeneratorWeightedGramHermiteWeight i test mode)
        (rightSpatialHermiteBlock d i)) B

namespace RootedAllSplitWeightedSourceInitialRestrictionData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}

end RootedAllSplitWeightedSourceInitialRestrictionData

namespace RootedAllSplitWeightedSourceNaturalKernelBoundData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {H : RootedA0BlockContinuousTranslationData OS A R}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}
  {Q : RootedAllSplitWeightedSourceInitialRestrictionData
    P A R H test B}

end RootedAllSplitWeightedSourceNaturalKernelBoundData

namespace RootedAllSplitWeightedSourceInitialRestrictionData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {H : RootedA0BlockContinuousTranslationData OS A R}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}

end RootedAllSplitWeightedSourceInitialRestrictionData

namespace RootedAllSplitWeightedSourceRankLadderData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {H : RootedA0BlockContinuousTranslationData OS A R}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}

end RootedAllSplitWeightedSourceRankLadderData

namespace RootedAllSplitWeightedSourceContinuationData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {H : RootedA0BlockContinuousTranslationData OS A R}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}

end RootedAllSplitWeightedSourceContinuationData

namespace RootedAllSplitWeightedSourceNaturalKernelBoundData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {H : RootedA0BlockContinuousTranslationData OS A R}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}
  {Q : RootedAllSplitWeightedSourceInitialRestrictionData
    P A R H test B}

end RootedAllSplitWeightedSourceNaturalKernelBoundData

namespace RootedGeneratorRetainedSourceContinuationData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {i : GeneratorIndex k}
  {hub : Fin k -> Real}
  {z : OSIITimeGapSpace k}
  {iota : Type*}
  {atlas : GeneratorStagePointedConvexAtlas
    (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
    (osiiPositiveRealTimeEmbed hub) iota}
  {D : RootedTargetHubPointedDirectExtensionData
    S depth P lgc i hub z atlas}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}

end RootedGeneratorRetainedSourceContinuationData

namespace RootedGeneratorRetainedSourceRankLadderData

variable
  {d k depth : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {i : GeneratorIndex k}
  {hub : Fin k -> Real}
  {z : OSIITimeGapSpace k}
  {iota : Type*}
  {atlas : GeneratorStagePointedConvexAtlas
    (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
    (osiiPositiveRealTimeEmbed hub) iota}
  {D : RootedTargetHubPointedDirectExtensionData
    S depth P lgc i hub z atlas}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {B : Real}
  {sourceRank : Nat}

end RootedGeneratorRetainedSourceRankLadderData

namespace VacuumTailAtlasBoundedDiagonalContinuationData

variable
  {d q : Nat} [NeZero d]
  {OS : OsterwalderSchraderAxioms d}
  {L : SimultaneousTimeContinuationStageLevel d}
  {iota : Type*}
  {hub : Fin (q + 1) -> Real}
  {z : OSIITimeGapSpace (q + 1)}
  {atlas : GeneratorStagePointedConvexAtlas
    (L.stage (q + 1)) (osiiPositiveRealTimeEmbed hub) iota}
  {D : VacuumTailTargetHubPointedDirectExtensionData
    L OS hub z atlas}
  {test : SchwartzMap
    (Section43SpatialSpace d (q + 1)) Complex}
  {B : Real}

end VacuumTailAtlasBoundedDiagonalContinuationData

namespace VacuumTailBoundedDiagonalContinuationData

variable
  {d q : Nat} [NeZero d]
  {OS : OsterwalderSchraderAxioms d}
  {L : SimultaneousTimeContinuationStageLevel d}
  {iota : Type*}
  {hub : Fin (q + 1) -> Real}
  {z : OSIITimeGapSpace (q + 1)}
  {atlas : GeneratorStagePointedConvexAtlas
    (L.stage (q + 1)) (osiiPositiveRealTimeEmbed hub) iota}
  {D : VacuumTailTargetHubPointedDirectExtensionData
    L OS hub z atlas}
  {test : SchwartzMap
    (Section43SpatialSpace d (q + 1)) Complex}
  {B : Real}

end VacuumTailBoundedDiagonalContinuationData

/-- Generator coefficient segments are covered by the underlying qualitative
rooted atlas.  No bounded-atlas hypothesis is needed for this geometric
statement. -/
theorem segment_zero_coefficientMap_subset_rootedRankPhysicalAtlas
    {d k n : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C} {depth rank : Nat} {iota : Type*}
    (rankData : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota)
    {rho : Real}
    (seed : Fin n -> Fin k -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (hgenerator : IsGeneratorRankSuccessorSeed
      rank k (depth + 1) (seed active)) :
    segment Real 0 (osiiStrictScalarSeedCoefficientMap seed r) ⊆
      osiiLogExp ⁻¹' ⋃ a,
        (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
          S depth rank rankData lgc hub hhub atlas).carrier a := by
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  rw [lineMap_zero_coefficientMap_eq_smul]
  have hactive_t :=
    coefficient_smul_preserves_activeImaginaryBound
      r active hactive t ht
  obtain ⟨i, sourceDepth, left, theta, right,
      hsourceDepth, hleft, hright, htheta, htarget⟩ :=
    exists_generatorData_osiiLogExp_coefficientMap_mem
      seed (t • r) active hactive_t hrho_lt_one hgenerator
  have hdepth : sourceDepth = depth := by omega
  subst sourceDepth
  change
    osiiLogExp
        (osiiStrictScalarSeedCoefficientMap seed (t • r)) ∈
      ⋃ a,
        (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
          S depth rank rankData lgc hub hhub atlas).carrier a
  exact
    (RootedStrictGeneratedTargetHubPointedConvexCoreAtlasAtRank.argumentGeneratorCarrier_subset_iUnion_carrier
      S depth rank rankData lgc hub hhub atlas
      i left hleft theta htheta right hright) htarget

/-- The exponentiated radial coefficient segment of a generator seed is
covered by the complete bounded rooted convex-core atlas. -/
theorem segment_zero_coefficientMap_subset_rootedRankPhysicalNeighborhood
    {d k n : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C} {depth rank : Nat} {iota : Type*}
    (rankData : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota)
    {B rho : Real}
    {chi : SchwartzMap (Section43SpatialSpace d k) Complex}
    (D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B)
      (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
        S depth rank rankData lgc hub hhub atlas) chi)
    (seed : Fin n -> Fin k -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (hgenerator : IsGeneratorRankSuccessorSeed
      rank k (depth + 1) (seed active)) :
    segment Real 0 (osiiStrictScalarSeedCoefficientMap seed r) ⊆
      D.physicalNeighborhood := by
  simpa [BoundedGeneratorStageExtensionConvexCoreAtlasData.physicalNeighborhood]
    using
      segment_zero_coefficientMap_subset_rootedRankPhysicalAtlas
        rankData lgc hub hhub atlas seed r active hactive
        hrho_lt_one hgenerator

/-- A bounded complete rooted rank atlas supplies the zero-pointed physical
chart for every generator point appearing in a flat coefficient window. -/
theorem nonempty_boundedRootedRankZeroPointedChart
    {d k n : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C} {depth rank : Nat} {iota : Type*}
    (rankData : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota)
    {B rho : Real}
    {chi : SchwartzMap (Section43SpatialSpace d k) Complex}
    {A : BoundedScalarContinuationData k B}
    (D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B)
      (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
        S depth rank rankData lgc hub hhub atlas) chi)
    (R : BoundedScalarLogarithmicRestrictionData A
      (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
        S depth rank rankData lgc hub hhub atlas).successorStage chi)
    (seed : Fin n -> Fin k -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (hgenerator : IsGeneratorRankSuccessorSeed
      rank k (depth + 1) (seed active)) :
    Nonempty
      (BoundedZeroPointedAmbientChartData R
        (osiiStrictScalarSeedCoefficientMap seed r)) :=
  D.nonempty_boundedZeroPointedChart R _
    (segment_zero_coefficientMap_subset_rootedRankPhysicalNeighborhood
      rankData lgc hub hhub atlas D seed r active hactive
      hrho_lt_one hgenerator)

/-- Mixed-tail coefficient segments are covered by the underlying qualitative
vacuum-tail atlas, independently of any quantitative atlas package. -/
theorem segment_zero_coefficientMap_subset_vacuumTailRankPhysicalAtlas
    {d q n : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {iota : Type*}
    (L : SimultaneousTimeContinuationStageLevel d)
    (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
    (targetDepth rank : Nat)
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) targetDepth rank) ⊆
        (L.stage ((q + 1) + ((q + 1) + 1))).carrier)
    (hub : Fin (q + 1) -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion (q + 1))
    (atlas : GeneratorStagePointedConvexAtlas
      (L.stage (q + 1)) (osiiPositiveRealTimeEmbed hub) iota)
    {rho : Real}
    (seed : Fin n -> Fin (q + 1) -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (htail : IsMixedTailRankSuccessorSeed
      rank (q + 1) targetDepth (seed active)) :
    segment Real 0 (osiiStrictScalarSeedCoefficientMap seed r) ⊆
      osiiLogExp ⁻¹' ⋃ a,
        (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
          L Hcanonical targetDepth rank hscalar hub hhub atlas).carrier a := by
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  rw [lineMap_zero_coefficientMap_eq_smul]
  have hactive_t :=
    coefficient_smul_preserves_activeImaginaryBound
      r active hactive t ht
  have htarget :=
    osiiLogExp_coefficientMap_mem_mixedTailArgumentCarrier
      seed (t • r) active hactive_t hrho_lt_one htail
  change
    osiiLogExp
        (osiiStrictScalarSeedCoefficientMap seed (t • r)) ∈
      ⋃ a,
        (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
          L Hcanonical targetDepth rank hscalar hub hhub atlas).carrier a
  exact
    (VacuumTailStrictGeneratedTargetHubPointedProjectionAtRank.mixedTailArgumentCarrier_subset_iUnion_carrier
      L Hcanonical targetDepth rank hscalar hub hhub atlas) htarget

/-- The exponentiated radial coefficient segment of a mixed-tail seed is
covered by the complete bounded vacuum-tail convex-core atlas. -/
theorem segment_zero_coefficientMap_subset_vacuumTailRankPhysicalNeighborhood
    {d q n : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {iota : Type*}
    (L : SimultaneousTimeContinuationStageLevel d)
    (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
    (targetDepth rank : Nat)
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) targetDepth rank) ⊆
        (L.stage ((q + 1) + ((q + 1) + 1))).carrier)
    (hub : Fin (q + 1) -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion (q + 1))
    (atlas : GeneratorStagePointedConvexAtlas
      (L.stage (q + 1)) (osiiPositiveRealTimeEmbed hub) iota)
    {B rho : Real}
    {chi : SchwartzMap (Section43SpatialSpace d (q + 1)) Complex}
    (D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B)
      (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
        L Hcanonical targetDepth rank hscalar hub hhub atlas) chi)
    (seed : Fin n -> Fin (q + 1) -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (htail : IsMixedTailRankSuccessorSeed
      rank (q + 1) targetDepth (seed active)) :
    segment Real 0 (osiiStrictScalarSeedCoefficientMap seed r) ⊆
      D.physicalNeighborhood := by
  simpa [BoundedGeneratorStageExtensionConvexCoreAtlasData.physicalNeighborhood]
    using
      segment_zero_coefficientMap_subset_vacuumTailRankPhysicalAtlas
        L Hcanonical targetDepth rank hscalar hub hhub atlas
        seed r active hactive hrho_lt_one htail

/-- A bounded complete vacuum-tail rank atlas supplies the zero-pointed
physical chart for every tail point in a flat coefficient window. -/
theorem nonempty_boundedVacuumTailRankZeroPointedChart
    {d q n : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {iota : Type*}
    (L : SimultaneousTimeContinuationStageLevel d)
    (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
    (targetDepth rank : Nat)
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) targetDepth rank) ⊆
        (L.stage ((q + 1) + ((q + 1) + 1))).carrier)
    (hub : Fin (q + 1) -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion (q + 1))
    (atlas : GeneratorStagePointedConvexAtlas
      (L.stage (q + 1)) (osiiPositiveRealTimeEmbed hub) iota)
    {B rho : Real}
    {chi : SchwartzMap (Section43SpatialSpace d (q + 1)) Complex}
    {A : BoundedScalarContinuationData (q + 1) B}
    (D : BoundedGeneratorStageExtensionConvexCoreAtlasData
      (B := B)
      (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
        L Hcanonical targetDepth rank hscalar hub hhub atlas) chi)
    (R : BoundedScalarLogarithmicRestrictionData A
      (vacuumTailStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRank
        L Hcanonical targetDepth rank hscalar hub hhub atlas
        ).successorStage chi)
    (seed : Fin n -> Fin (q + 1) -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (htail : IsMixedTailRankSuccessorSeed
      rank (q + 1) targetDepth (seed active)) :
    Nonempty
      (BoundedZeroPointedAmbientChartData R
        (osiiStrictScalarSeedCoefficientMap seed r)) :=
  D.nonempty_boundedZeroPointedChart R _
    (segment_zero_coefficientMap_subset_vacuumTailRankPhysicalNeighborhood
      L Hcanonical targetDepth rank hscalar hub hhub atlas D
      seed r active hactive hrho_lt_one htail)

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

/-- Physical old/generator/tail chart obligations for one finite family of
rank-successor seeds.  Each chart is already zero-pointed and bounded after
evaluation on the fixed spatial test. -/
structure BoundedRankSuccessorSeedPhysicalChartProducerData
    {d m n : Nat} [NeZero d]
    {B S rho : Real}
    {A : BoundedScalarContinuationData m B}
    {physical : OSIITimeContinuationStage d m}
    {chi : SchwartzMap (Section43SpatialSpace d m) Complex}
    (R : BoundedScalarLogarithmicRestrictionData A physical chi)
    (P : SCV.StripCompactificationParameters S rho)
    (rank targetDepth : Nat)
    (seed : Fin n -> Fin m -> Real) where
  seed_rank : forall a,
    OSIIStrictGeneratedScalarRankSuccessorSeed
      rank m targetDepth (seed a)
  oldChart : forall
    (active : Fin n)
    (r : Fin n -> Complex),
    r ∈ osiiStrictScalarSeedCoefficientFlatWindow
      (Fin n) (P.radius + rho) rho ->
    (|(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0) ->
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar m targetDepth (seed active) ->
    BoundedZeroPointedAmbientChartData R
      (osiiStrictScalarSeedCoefficientMap seed r)
  generatorChart : forall
    (active : Fin n)
    (r : Fin n -> Complex),
    r ∈ osiiStrictScalarSeedCoefficientFlatWindow
      (Fin n) (P.radius + rho) rho ->
    (|(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0) ->
    IsGeneratorRankSuccessorSeed
      rank m targetDepth (seed active) ->
    BoundedZeroPointedAmbientChartData R
      (osiiStrictScalarSeedCoefficientMap seed r)
  mixedTailChart : forall
    (active : Fin n)
    (r : Fin n -> Complex),
    r ∈ osiiStrictScalarSeedCoefficientFlatWindow
      (Fin n) (P.radius + rho) rho ->
    (|(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0) ->
    IsMixedTailRankSuccessorSeed
      rank m targetDepth (seed active) ->
    BoundedZeroPointedAmbientChartData R
      (osiiStrictScalarSeedCoefficientMap seed r)

namespace BoundedRankSuccessorSeedPhysicalChartProducerData

variable {d m n : Nat} [NeZero d]
variable {B S rho : Real}
variable {A : BoundedScalarContinuationData m B}
variable {physical : OSIITimeContinuationStage d m}
variable {chi : SchwartzMap (Section43SpatialSpace d m) Complex}
variable {R : BoundedScalarLogarithmicRestrictionData A physical chi}
variable {P : SCV.StripCompactificationParameters S rho}
variable {rank targetDepth : Nat}
variable {seed : Fin n -> Fin m -> Real}

/-- Assemble the exact-bound physical constructor package when rooted and
vacuum-tail charts are first built on intermediate stages and then retained
by one composed physical successor. -/
noncomputable def ofRebasedBranches
    {rootPhysical tailPhysical : OSIITimeContinuationStage d m}
    (Rroot : BoundedScalarLogarithmicRestrictionData
      A rootPhysical chi)
    (Rtail : BoundedScalarLogarithmicRestrictionData
      A tailPhysical chi)
    (rootCarrierSubset : rootPhysical.carrier ⊆ physical.carrier)
    (rootExtends : Set.EqOn physical.distribution
      rootPhysical.distribution rootPhysical.carrier)
    (tailCarrierSubset : tailPhysical.carrier ⊆ physical.carrier)
    (tailExtends : Set.EqOn physical.distribution
      tailPhysical.distribution tailPhysical.carrier)
    (seed_rank : forall a,
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank m targetDepth (seed a))
    (oldChart : forall
      (active : Fin n)
      (r : Fin n -> Complex),
      r ∈ osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ->
      (|(r active).im| <= rho ∧
        forall j, j ≠ active -> (r j).im = 0) ->
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .scalar m targetDepth (seed active) ->
      Nonempty (BoundedZeroPointedAmbientChartData R
        (osiiStrictScalarSeedCoefficientMap seed r)))
    (generatorChart : forall
      (active : Fin n)
      (r : Fin n -> Complex),
      r ∈ osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ->
      (|(r active).im| <= rho ∧
        forall j, j ≠ active -> (r j).im = 0) ->
      IsGeneratorRankSuccessorSeed
        rank m targetDepth (seed active) ->
      Nonempty (BoundedZeroPointedAmbientChartData Rroot
        (osiiStrictScalarSeedCoefficientMap seed r)))
    (mixedTailChart : forall
      (active : Fin n)
      (r : Fin n -> Complex),
      r ∈ osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ->
      (|(r active).im| <= rho ∧
        forall j, j ≠ active -> (r j).im = 0) ->
      IsMixedTailRankSuccessorSeed
        rank m targetDepth (seed active) ->
      Nonempty (BoundedZeroPointedAmbientChartData Rtail
        (osiiStrictScalarSeedCoefficientMap seed r))) :
    BoundedRankSuccessorSeedPhysicalChartProducerData
      R P rank targetDepth seed where
  seed_rank := seed_rank
  oldChart := fun active r hr hactive hold =>
    Classical.choice (oldChart active r hr hactive hold)
  generatorChart := fun active r hr hactive hgenerator =>
    (Classical.choice
      (generatorChart active r hr hactive hgenerator)).rebasePhysicalTo
        R rootCarrierSubset rootExtends
  mixedTailChart := fun active r hr hactive htail =>
    (Classical.choice
      (mixedTailChart active r hr hactive htail)).rebasePhysicalTo
        R tailCarrierSubset tailExtends

/-- Assemble a physical constructor when rooted insertion is followed
sequentially by vacuum-tail projection.  The tail atlas successor is already
the common final physical stage, so all branch rebasing data are determined
by that atlas. -/
noncomputable def ofSequentialBranches
    {rootPhysical : OSIITimeContinuationStage d m}
    (tailAtlas : GeneratorStageExtensionConvexCoreAtlasData rootPhysical)
    (Rroot : BoundedScalarLogarithmicRestrictionData
      A rootPhysical chi)
    (seed_rank : forall a,
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank m targetDepth (seed a))
    (oldChart : forall
      (active : Fin n)
      (r : Fin n -> Complex),
      r ∈ osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ->
      (|(r active).im| <= rho ∧
        forall j, j ≠ active -> (r j).im = 0) ->
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .scalar m targetDepth (seed active) ->
      Nonempty (BoundedZeroPointedAmbientChartData
        (Rroot.rebaseConvexCoreAtlas tailAtlas)
        (osiiStrictScalarSeedCoefficientMap seed r)))
    (generatorChart : forall
      (active : Fin n)
      (r : Fin n -> Complex),
      r ∈ osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ->
      (|(r active).im| <= rho ∧
        forall j, j ≠ active -> (r j).im = 0) ->
      IsGeneratorRankSuccessorSeed
        rank m targetDepth (seed active) ->
      Nonempty (BoundedZeroPointedAmbientChartData Rroot
        (osiiStrictScalarSeedCoefficientMap seed r)))
    (mixedTailChart : forall
      (active : Fin n)
      (r : Fin n -> Complex),
      r ∈ osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ->
      (|(r active).im| <= rho ∧
        forall j, j ≠ active -> (r j).im = 0) ->
      IsMixedTailRankSuccessorSeed
        rank m targetDepth (seed active) ->
      Nonempty (BoundedZeroPointedAmbientChartData
        (Rroot.rebaseConvexCoreAtlas tailAtlas)
        (osiiStrictScalarSeedCoefficientMap seed r))) :
    BoundedRankSuccessorSeedPhysicalChartProducerData
      (Rroot.rebaseConvexCoreAtlas tailAtlas)
      P rank targetDepth seed :=
  ofRebasedBranches
    Rroot (Rroot.rebaseConvexCoreAtlas tailAtlas)
    tailAtlas.oldCarrier_subset_successorCarrier
    tailAtlas.successorStage_extends_predecessor
    Set.Subset.rfl (Set.eqOn_refl _ _)
    seed_rank oldChart generatorChart mixedTailChart

/-- Forget the physical provenance after evaluating each chart on the fixed
spatial test. -/
def toFlatChartProducer
    (D : BoundedRankSuccessorSeedPhysicalChartProducerData
      R P rank targetDepth seed) :
    BoundedRankSuccessorSeedFlatChartProducerData
      A P rank targetDepth seed where
  seed_rank := D.seed_rank
  oldChart := fun active r hr hactive hold =>
    (D.oldChart active r hr hactive hold).toTargetChart
  generatorChart := fun active r hr hactive hgenerator =>
    (D.generatorChart active r hr hactive hgenerator).toTargetChart
  mixedTailChart := fun active r hr hactive htail =>
    (D.mixedTailChart active r hr hactive htail).toTargetChart

end BoundedRankSuccessorSeedPhysicalChartProducerData

namespace BoundedGlobalRankSuccessorFlatChartData

variable {d m : Nat} [NeZero d] {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {physical : OSIITimeContinuationStage d m}
variable {chi : SchwartzMap (Section43SpatialSpace d m) Complex}
variable {R : BoundedScalarLogarithmicRestrictionData A physical chi}
variable {rank depth : Nat}

/-- Physical constructorwise charts, once bounded on one fixed spatial test,
supply the complete global bounded flat atlas at one analytic rank. -/
noncomputable def ofPhysicalConstructorwise
    (hB : 0 < B)
    (produce : forall
      (n : Nat)
      (seed : Fin n -> Fin m -> Real)
      (_hseed : forall a,
        OSIIStrictGeneratedScalarRankSuccessorSeed
          rank m (depth + 1) (seed a)),
      forall {S rho : Real}
        (P : SCV.StripCompactificationParameters S rho),
        0 < rho ->
        rho < 1 ->
        Nonempty
          (BoundedRankSuccessorSeedPhysicalChartProducerData
            R P rank (depth + 1) seed)) :
    BoundedGlobalRankSuccessorFlatChartData A rank depth :=
  ofConstructorwise hB fun n seed hseed {S rho} P
      hrho_pos hrho_lt_one => by
    obtain ⟨D⟩ :=
      produce n seed hseed P hrho_pos hrho_lt_one
    exact ⟨D.toFlatChartProducer⟩

end BoundedGlobalRankSuccessorFlatChartData

end OSIIChapterV
end OSReconstruction
