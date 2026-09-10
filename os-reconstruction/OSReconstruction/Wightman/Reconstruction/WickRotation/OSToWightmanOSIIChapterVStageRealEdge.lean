/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGluing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceRealEdge
import OSReconstruction.SCV.DistributionalRepresentationGluing













noncomputable section

open Complex Topology
open scoped Classical

namespace OSReconstruction

/-- A time-continuation stage has the real orbit `R` on `U`. -/
def OSIITimeContinuationStage.HasPositiveRealEdge
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (R : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (U : Set (Fin k -> Real)) : Prop :=
  forall tau, tau ∈ U ->
    osiiPositiveRealTimeEmbed tau ∈ A.carrier ∧
      A.distribution (osiiPositiveRealTimeEmbed tau) = R tau

namespace OSIITimeContinuationStage

variable {d k : Nat}

/-- Recenter a continuation stage at a positive-real basepoint.

The new complex parameter `z` denotes the old parameter
`z + osiiPositiveRealTimeEmbed center`.  This is the coordinate convention
used by the rooted Chapter V generators, whose small positive parameters are
increments from an absolute Euclidean-time anchor. -/
noncomputable def recenter
    (A : OSIITimeContinuationStage d k)
    (center : Fin k → Real) :
    OSIITimeContinuationStage d k where
  carrier :=
    {z | z + osiiPositiveRealTimeEmbed center ∈ A.carrier}
  carrier_open :=
    A.carrier_open.preimage
      (continuous_id.add continuous_const)
  distribution :=
    fun z => A.distribution
      (z + osiiPositiveRealTimeEmbed center)
  weaklyHolomorphic := by
    intro chi
    exact
      (A.weaklyHolomorphic chi).comp
        (differentiable_id.add_const
          (osiiPositiveRealTimeEmbed center)).differentiableOn
        (fun _ hz => hz)

@[simp] theorem recenter_carrier
    (A : OSIITimeContinuationStage d k)
    (center : Fin k → Real) :
    (A.recenter center).carrier =
      {z | z + osiiPositiveRealTimeEmbed center ∈ A.carrier} :=
  rfl

@[simp] theorem recenter_distribution
    (A : OSIITimeContinuationStage d k)
    (center : Fin k → Real)
    (z : OSIITimeGapSpace k) :
    (A.recenter center).distribution z =
      A.distribution (z + osiiPositiveRealTimeEmbed center) :=
  rfl

/-- Recenter an absolute positive-real edge at the same real basepoint. -/
theorem recenter_hasPositiveRealEdge
    (A : OSIITimeContinuationStage d k)
    (R : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (U : Set (Fin k -> Real))
    (center : Fin k → Real)
    (h : A.HasPositiveRealEdge R U) :
    (A.recenter center).HasPositiveRealEdge
      (fun tau => R (tau + center))
      {tau | tau + center ∈ U} := by
  intro tau htau
  have hold := h (tau + center) htau
  constructor
  · simpa [osiiPositiveRealTimeEmbed_add] using hold.1
  · simpa [osiiPositiveRealTimeEmbed_add] using hold.2

/-- Weak holomorphy supplies continuity of a declared positive real edge. -/
theorem continuousOn_positiveRealEdge
    (A : OSIITimeContinuationStage d k)
    (R : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (U : Set (Fin k -> Real))
    (h : A.HasPositiveRealEdge R U)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ContinuousOn (fun tau => R tau chi) U := by
  have hcont :
      ContinuousOn
        (fun tau => A.distribution (osiiPositiveRealTimeEmbed tau) chi) U :=
    (A.weaklyHolomorphic chi).continuousOn.comp
      continuous_osiiPositiveRealTimeEmbed.continuousOn
      (fun tau htau => (h tau htau).1)
  exact hcont.congr fun tau htau =>
    congrArg (fun T : OSIISpatialDistribution d k => T chi)
      (h tau htau).2.symm

/-- The exact positive-real-time data consumed by the moving-slice endpoint. -/
structure PositiveRealEdgeData
    [NeZero d]
    (A : OSIITimeContinuationStage d k)
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (U : Set (Fin k -> Real)) where
  orbit : (Fin k -> Real) -> OSIISpatialDistribution d k
  stageEdge : A.HasPositiveRealEdge orbit U
  represents :
    OSIITimeSpatialRepresentsDistributionOn W orbit U
  pointwiseBounded :
    OSIITimeSpatialPointwiseBoundedOn orbit U

namespace PositiveRealEdgeData

variable [NeZero d]
  {A : OSIITimeContinuationStage d k}
  {W : SchwartzNPoint d k →L[Complex] Complex}
  {U : Set (Fin k -> Real)}

/-- The actual stage restriction represents the same spacetime distribution
as the named real-edge orbit. -/
theorem stage_represents
    (E : PositiveRealEdgeData A W U) :
    OSIITimeSpatialRepresentsDistributionOn W
      (fun tau => A.distribution (osiiPositiveRealTimeEmbed tau)) U := by
  intro chi
  exact SCV.representsDistributionOn_congr_on_subset
    (W.comp (section43OrderedPullbackTimeSpatialTensorCLM d k chi))
    (E.represents chi)
    (fun tau htau =>
      congrArg (fun T : OSIISpatialDistribution d k => T chi)
        (E.stageEdge tau htau).2.symm)
    Set.Subset.rfl

/-- Pointwise boundedness transfers from the named orbit to the stage. -/
theorem stage_pointwiseBounded
    (E : PositiveRealEdgeData A W U) :
    OSIITimeSpatialPointwiseBoundedOn
      (fun tau => A.distribution (osiiPositiveRealTimeEmbed tau)) U := by
  intro chi
  obtain ⟨C, hC⟩ := E.pointwiseBounded chi
  exact ⟨C, fun tau htau => by
    change
      ‖A.distribution (osiiPositiveRealTimeEmbed tau) chi‖ ≤ C
    rw [(E.stageEdge tau htau).2]
    exact hC tau htau⟩

/-- The positive-real-time stage restriction is scalar-continuous. -/
theorem stage_continuousOn
    (E : PositiveRealEdgeData A W U)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ContinuousOn
      (fun tau => A.distribution (osiiPositiveRealTimeEmbed tau) chi) U :=
  (A.weaklyHolomorphic chi).continuousOn.comp
    continuous_osiiPositiveRealTimeEmbed.continuousOn
    (fun tau htau => (E.stageEdge tau htau).1)

end PositiveRealEdgeData
end OSIITimeContinuationStage

namespace OSIITimeContinuationLadder

variable {d k : Nat}

/-- A positive real edge carried by any finite ladder stage survives in the
full continuation on the exhausted right half-plane. -/
theorem toFullTimeContinuationStage_hasPositiveRealEdge
    (L : OSIITimeContinuationLadder d k)
    (N : Nat)
    (R : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (U : Set (Fin k -> Real))
    (hU_positive : U ⊆ section43TimeStrictPositiveRegion k)
    (h : (L.stage N).HasPositiveRealEdge R U) :
    L.toFullTimeContinuationStage.HasPositiveRealEdge R U := by
  intro tau htau
  have hstage := h tau htau
  refine
    ⟨(osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).mpr
      (hU_positive htau), ?_⟩
  exact
    (L.toFullTimeContinuationStage_extends_stage N hstage.1).trans
      hstage.2

/-- The complete represented positive-real edge package survives passage from
one finite stage to the full exhausted continuation. -/
noncomputable def toFullTimeContinuationStagePositiveRealEdgeData
    [NeZero d]
    (L : OSIITimeContinuationLadder d k)
    (N : Nat)
    {W : SchwartzNPoint d k →L[Complex] Complex}
    {U : Set (Fin k -> Real)}
    (hU_positive : U ⊆ section43TimeStrictPositiveRegion k)
    (E : (L.stage N).PositiveRealEdgeData W U) :
    L.toFullTimeContinuationStage.PositiveRealEdgeData W U where
  orbit := E.orbit
  stageEdge :=
    L.toFullTimeContinuationStage_hasPositiveRealEdge
      N E.orbit U hU_positive E.stageEdge
  represents := E.represents
  pointwiseBounded := E.pointwiseBounded

end OSIITimeContinuationLadder

namespace OSIIChapterV
namespace GeneratorFamily

variable {d k : Nat}

/-- Every generator branch has the same positive-real-time orbit. -/
def HasCommonPositiveRealEdge
    (G : GeneratorFamily d k)
    (R : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (U : Set (Fin k -> Real)) : Prop :=
  forall i tau, tau ∈ U ->
    osiiPositiveRealTimeEmbed tau ∈ G.domain i ∧
      G.distribution i (osiiPositiveRealTimeEmbed tau) = R tau

/-- Gluing preserves a common generator real edge. -/
theorem toTimeContinuationStage_hasPositiveRealEdge
    (G : GeneratorFamily d k)
    (R : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (U : Set (Fin k -> Real))
    (h : G.HasCommonPositiveRealEdge R U)
    (i : GeneratorIndex k) :
    G.toTimeContinuationStage.HasPositiveRealEdge R U := by
  intro tau htau
  have hi := h i tau htau
  refine ⟨Set.mem_iUnion_of_mem i hi.1, ?_⟩
  exact (G.gluedDistribution_eqOn_domain i hi.1).trans hi.2

/-- A common generator real edge together with its A0 representation data
produces the complete real-edge package for the glued stage. -/
def toTimeContinuationStagePositiveRealEdgeData
    [NeZero d]
    (G : GeneratorFamily d k)
    (R : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (U : Set (Fin k -> Real))
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (h : G.HasCommonPositiveRealEdge R U)
    (i : GeneratorIndex k)
    (hrep : OSIITimeSpatialRepresentsDistributionOn W R U)
    (hbounded : OSIITimeSpatialPointwiseBoundedOn R U) :
    G.toTimeContinuationStage.PositiveRealEdgeData W U where
  orbit := R
  stageEdge := G.toTimeContinuationStage_hasPositiveRealEdge R U h i
  represents := hrep
  pointwiseBounded := hbounded

end GeneratorFamily

namespace EnvelopeExtension

variable {d k : Nat}
  {G : GeneratorFamily d k}
  {V : Set (OSIITimeGapSpace k)}

end EnvelopeExtension
end OSIIChapterV

/-- The packaged positive real edge supplies every hypothesis of the
moving-slice real-edge theorem. -/
theorem osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_orderedPullbackFullCutoff_of_edgeData
    {d k : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d k)
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (U : Set (Fin k -> Real))
    (E : A.PositiveRealEdgeData W U)
    (hrho_compact : HasCompactSupport (rho : (Fin k -> Real) -> Complex))
    (F : SchwartzNPoint d k)
    (s : Fin k -> Real)
    (hrho_shift_support :
      tsupport
          ((SCV.translateSchwartz (-s) rho :
            SchwartzMap (Fin k -> Real) Complex) :
              (Fin k -> Real) -> Complex) ⊆ U) :
    osiiStageMovingSliceScalar A rho F
        (osiiPositiveRealTimeEmbed s) =
      W (section43OrderedPullbackFullCutoffCLM d k
        (SCV.translateSchwartz (-s) rho)
        (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) (-s)) F)) := by
  exact
    osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_orderedPullbackFullCutoff
      A W rho U hrho_compact E.stage_continuousOn
      E.stage_pointwiseBounded E.stage_represents F s hrho_shift_support

end OSReconstruction
