/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedSources
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniversalCompactCarrierAnchoredBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVBoundedScalarContinuation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdgeUniqueness











noncomputable section

open Complex Set Topology

namespace OSReconstruction

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

namespace OSIIChapterV

/-- A bounded continuation of one retained reflected moving-slice source.

Agreement is required along every radial segment which stays in the natural
moving-slice chart.  This is exactly the component used by the rooted
zero-convex block domains; no connectedness or convexity of the complete
post-successor stage carrier is asserted. -/
structure BoundedReflectedMovingSliceContinuationData
    {d q : Nat}
    (A : OSIITimeContinuationStage d ((q + 1) + ((q + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex)
    (F : SchwartzNPoint d ((q + 1) + ((q + 1) + 1)))
    (B : Real) where
  continuation :
    BoundedScalarContinuationData ((q + 1) + (q + 1)) B
  agrees_of_segment : forall z,
    z ∈ continuation.carrier ->
    segment Real 0 z ⊆ reflectedMovingSliceCarrier A eta ->
    continuation.toFun z = reflectedMovingSliceScalar A eta F z

namespace BoundedReflectedMovingSliceContinuationData

/-- Package a bound proved directly on an open star-convex moving-slice
subdomain.  This is the coordinate-native constructor: its variables are the
additive reflected Cauchy parameters, and no logarithmic rank interpretation
is imposed on them. -/
noncomputable def ofBoundedRestriction
    {d q : Nat}
    (A : OSIITimeContinuationStage d ((q + 1) + ((q + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex)
    (F : SchwartzNPoint d ((q + 1) + ((q + 1) + 1)))
    (B : Real)
    (domain : Set (Fin ((q + 1) + (q + 1)) -> Complex))
    (domain_open : IsOpen domain)
    (domain_starConvex : StarConvex Real 0 domain)
    (zero_mem : (0 : Fin ((q + 1) + (q + 1)) -> Complex) ∈ domain)
    (eta_compact : HasCompactSupport
      (eta : (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex))
    (domain_subset : domain ⊆ reflectedMovingSliceCarrier A eta)
    (norm_le : forall z, z ∈ domain ->
      ‖reflectedMovingSliceScalar A eta F z‖ <= B) :
    BoundedReflectedMovingSliceContinuationData A eta F B where
  continuation :=
    { carrier := domain
      carrier_open := domain_open
      carrier_starConvex := domain_starConvex
      zero_mem := zero_mem
      toFun := reflectedMovingSliceScalar A eta F
      differentiableOn :=
        (differentiableOn_reflectedMovingSliceScalar
          A eta F eta_compact).mono domain_subset
      norm_le := norm_le }
  agrees_of_segment := by
    intro _z _hz _hsegment
    rfl

/-- The open zero-convex kernel of the natural moving-slice carrier is the
canonical domain for a directly proved moving-source bound. -/
noncomputable def ofNaturalOpenZeroConvexKernel
    {d q : Nat}
    (A : OSIITimeContinuationStage d ((q + 1) + ((q + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex)
    (F : SchwartzNPoint d ((q + 1) + ((q + 1) + 1)))
    (B : Real)
    (eta_compact : HasCompactSupport
      (eta : (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex))
    (zero_mem : (0 : Fin ((q + 1) + (q + 1)) -> Complex) ∈
      reflectedMovingSliceCarrier A eta)
    (norm_le : forall z,
      z ∈ openZeroConvexKernel (reflectedMovingSliceCarrier A eta) ->
      ‖reflectedMovingSliceScalar A eta F z‖ <= B) :
    BoundedReflectedMovingSliceContinuationData A eta F B :=
  ofBoundedRestriction A eta F B
    (openZeroConvexKernel (reflectedMovingSliceCarrier A eta))
    (openZeroConvexKernel_open _)
    (openZeroConvexKernel_starConvex _)
    (zero_mem_openZeroConvexKernel
      (isOpen_reflectedMovingSliceCarrier A eta eta_compact) zero_mem)
    eta_compact
    (openZeroConvexKernel_subset _)
    norm_le

/-- A bounded holomorphic source branch with the represented positive-real
edge gives the canonical bounded reflected continuation.  This is the
non-circular handoff from an axis-pair semigroup estimate to the live rooted
moving-source package. -/
noncomputable def ofPositiveRealEdgeSourceComparison
    {d q : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d ((q + 1) + ((q + 1) + 1)))
    (W : SchwartzNPoint d ((q + 1) + ((q + 1) + 1)) →L[Complex] Complex)
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex)
    (edgeRegion : Set (Fin ((q + 1) + ((q + 1) + 1)) -> Real))
    (E : A.PositiveRealEdgeData W edgeRegion)
    (eta_compact : HasCompactSupport
      (eta : (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex))
    (F : SchwartzNPoint d ((q + 1) + ((q + 1) + 1)))
    (B : Real)
    (U : Set (Fin ((q + 1) + ((q + 1) + 1)) -> Complex))
    (hU_open : IsOpen U)
    (hU_connected : IsConnected U)
    (hU_moving : U ⊆ osiiStageMovingSliceCarrier A eta)
    (G : (Fin ((q + 1) + ((q + 1) + 1)) -> Complex) -> Complex)
    (hG : DifferentiableOn Complex G U)
    (hG_norm_le : forall z, z ∈ U -> ‖G z‖ <= B)
    (V : Set (Fin ((q + 1) + ((q + 1) + 1)) -> Real))
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_subset : forall x, x ∈ V ->
      (fun i => (x i : Complex)) ∈ U)
    (heta_shift_support : forall x, x ∈ V ->
      tsupport
          ((SCV.translateSchwartz (-x) eta :
            SchwartzMap
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex) :
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
        edgeRegion)
    (hG_real : forall x, x ∈ V ->
      G (fun i => (x i : Complex)) =
        W (section43OrderedPullbackFullCutoffCLM d
          ((q + 1) + ((q + 1) + 1))
          (SCV.translateSchwartz (-x) eta)
          (translateSchwartzConfiguration
            (osiiDifferenceTimeTranslation (d := d) (-x)) F)))
    (zero_mem :
      (0 : Fin ((q + 1) + (q + 1)) -> Complex) ∈
        reflectedMovingSliceCarrier A eta)
    (hkernel_image : forall z,
      z ∈ openZeroConvexKernel (reflectedMovingSliceCarrier A eta) ->
        -(reflectedReducedTimeDisplacementCLM (q + 1) z) ∈ U) :
    BoundedReflectedMovingSliceContinuationData A eta F B :=
  BoundedReflectedMovingSliceContinuationData.ofNaturalOpenZeroConvexKernel
    A eta F B eta_compact zero_mem (by
      intro z hz
      change
        ‖osiiStageMovingSliceScalar A eta F
          (-(reflectedReducedTimeDisplacementCLM (q + 1) z))‖ <= B
      exact
        norm_osiiStageMovingSliceScalar_le_of_positiveRealEdge_source_eq
          A W eta edgeRegion E eta_compact F U hU_open hU_connected
          hU_moving G hG B hG_norm_le V hV_open hV_nonempty hV_subset
          heta_shift_support hG_real _ (hkernel_image z hz))

end BoundedReflectedMovingSliceContinuationData

/-- The genuine initial datum from which the bounded scalar rank ladder can
continue one reflected moving-slice source.  Its bounded continuation is
required to be a restriction of that exact source, rather than merely to
share its value at the origin. -/
structure BoundedReflectedMovingSliceInitialRestrictionData
    {d q : Nat}
    (A : OSIITimeContinuationStage d ((q + 1) + ((q + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex)
    (F : SchwartzNPoint d ((q + 1) + ((q + 1) + 1)))
    (B : Real) where
  initial : BoundedScalarContinuationData ((q + 1) + (q + 1)) B
  eta_compact : HasCompactSupport
    (eta : (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex)
  carrier_subset :
    initial.carrier ⊆ reflectedMovingSliceCarrier A eta
  agrees : Set.EqOn initial.toFun
    (reflectedMovingSliceScalar A eta F) initial.carrier

namespace BoundedReflectedMovingSliceInitialRestrictionData

end BoundedReflectedMovingSliceInitialRestrictionData

namespace ReflectedGramSpatialSourceData

variable {d q : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}

/-- The initial reflected-Gram polydisc supplies the zero point of the
source-linear spatial chart. -/
theorem zero_mem_spatialLinearDomain
    (D : ReflectedGramSpatialSourceData (OS := OS) S q) :
    (0 : Fin (q + 1) -> Complex) ∈
      D.reflectedGram.atlas.spatialLinearDomain := by
  apply D.reflectedGram.atlas.initialGramPolydisc_subset_spatialLinearDomain
  exact SCV.center_mem_polydisc
    (fun _ => D.reflectedGram.atlas.gram.gramRadius_pos)

/-- A point in the radial source-linear block domain carries its complete
reflected-center segment inside the natural moving-slice carrier. -/
theorem
    reflectedCauchyCenter_segment_subset_movingSliceCarrier_of_mem_radialDomain
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    {z : Fin (q + 1) -> Complex}
    (hz : z ∈ openZeroConvexKernel
      D.reflectedGram.atlas.spatialLinearDomain) :
    segment Real 0 (reflectedCauchyCenter z) ⊆
      reflectedMovingSliceCarrier
        D.reflectedGram.atlas.sourceStage.stage
        D.reflectedGram.atlas.sourceStage.germ.η := by
  intro center hcenter
  rw [segment_eq_image_lineMap] at hcenter
  obtain ⟨t, ht, rfl⟩ := hcenter
  rw [← reflectedCauchyCenter_lineMap_zero z t]
  have hradial :
      AffineMap.lineMap (k := Real) 0 z t ∈
        openZeroConvexKernel
          D.reflectedGram.atlas.spatialLinearDomain :=
    by
      simpa [AffineMap.lineMap_apply_module] using
        real_smul_mem_openZeroConvexKernel hz ht.1 ht.2
  exact (openZeroConvexKernel_subset _ hradial).2.2

/-- The chronological source associated to two independently selected rooted
spatial tests.  This is the rank-one product source before difference
reduction; unlike the weighted shell below, its two factors need not agree. -/
noncomputable def sourceProductChronologicalSource
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    (leftScale rightScale : Nat)
    (left right : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) Complex) :
    SchwartzNPoint d (((q + 1) + ((q + 1) + 1)) + 1) :=
  mixedReflectedChronologicalSource
    (UniformCompactTimeSource.source (D.sourceCLM leftScale left)).1
    (UniformCompactTimeSource.source (D.sourceCLM rightScale right)).1

/-- Difference reduction of the two-factor chronological source, retained as
one moving-slice test for the represented predecessor stage. -/
noncomputable def sourceProductMovingSliceSource
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    (leftScale rightScale : Nat)
    (left right : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) Complex) :
    SchwartzNPoint d ((q + 1) + ((q + 1) + 1)) :=
  diffVarReduction d ((q + 1) + ((q + 1) + 1))
    (D.sourceProductChronologicalSource
      leftScale rightScale left right)

/-- The mixed reflected Gram scalar is exactly the represented-stage
moving-slice scalar of the corresponding two-factor source. -/
theorem cauchy_scalar_eq_sourceProductMovingSliceScalar
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    (leftScale rightScale : Nat)
    (left right : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (w : Fin ((q + 1) + (q + 1)) -> Complex) :
    (D.reflectedGram.atlas.gram.cauchy
      (D.sourceCLM leftScale left)
      (D.sourceCLM rightScale right)).scalar w =
      reflectedMovingSliceScalar
        D.reflectedGram.atlas.sourceStage.stage
        D.reflectedGram.atlas.sourceStage.germ.η
        (D.sourceProductMovingSliceSource
          leftScale rightScale left right) w := by
  rw [D.reflectedGram.atlas.gram.cauchy_scalar]
  rfl

/-- The whole coefficient-weighted diagonal shell as one Schwartz source for
the predecessor reflected moving slice.  Keeping the finite sum inside the
source is what lets the scalar rank induction continue the shell once,
rather than assigning and then adding separate modewise bounds. -/
noncomputable def weightedDiagonalMovingSliceSource
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    (scale shell : Nat)
    (weight : Fin shell -> Real)
    (modeTest :
      Nat ->
        SchwartzMap
          (Section43SpatialSpace d ((q + 1) + 1)) Complex) :
    SchwartzNPoint d ((q + 1) + ((q + 1) + 1)) :=
  ∑ mode : Fin shell,
    (weight mode : Complex) •
      diffVarReduction d ((q + 1) + ((q + 1) + 1))
        (mixedReflectedChronologicalSource
          (UniformCompactTimeSource.source
            (D.sourceCLM scale (modeTest mode))).1
        (UniformCompactTimeSource.source
          (D.sourceCLM scale (modeTest mode))).1)

end ReflectedGramSpatialSourceData

namespace GeneratorOpenHilbertFieldScaleBlockRealEdgeData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {B : Real}

/-- The complete weighted diagonal shell of a one-particle block as one
zero-diagonal two-point Schwartz source.  The empty chronological parameter
space is not an exceptional collection of modewise estimates: linearity of
the Schwinger functional still combines the whole shell before it is
bounded. -/
noncomputable def oneParticleWeightedDiagonalSchwingerSource
    (E : GeneratorOpenHilbertFieldScaleBlockRealEdgeData OS 1 0)
    (scale shell : Nat)
    (weight : Fin shell -> Real) :
    ZeroDiagonalSchwartz d 2 :=
  ∑ mode : Fin shell,
    (weight mode : Complex) •
      ZeroDiagonalSchwartz.ofClassical
        ((E.source scale mode 0).1.osConjTensorProduct
          (E.source scale mode 0).1)

end GeneratorOpenHilbertFieldScaleBlockRealEdgeData

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C} {depth : Nat}
variable {I : Section43ProductTimeApproximateIdentity k}
variable {anchor : Fin k -> Real}

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
