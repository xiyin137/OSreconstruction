/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVExhaustingCarrierNormalFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicStagePushforward
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPhysicalGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILocalTimeStageGluing
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Data needed to turn one ambient logarithmic continuation into an exact
physical target over a prescribed real logarithmic base. -/
structure LogarithmicTargetAmbientData
    {d k : Nat} [NeZero d]
    (predecessor : OSIITimeContinuationStage d k)
    (base : Set (Fin k -> Real)) where
  stage : OSIITimeContinuationStage d k
  base_open : IsOpen base
  zero_mem_base : (0 : Fin k -> Real) ∈ base
  base_solid : SCV.IsCoordinatewiseSolid base
  tube_subset_stage :
    osiiLogarithmicTube base ⊆ stage.carrier
  exists_open_seed :
    ∃ U : Set (Fin k -> Complex),
      IsOpen U ∧ (0 : Fin k -> Complex) ∈ U ∧
      U ⊆
        stage.carrier ∩
          (logarithmicPullbackStage predecessor).carrier ∧
      Set.EqOn
        stage.distribution
        (logarithmicPullbackStage predecessor).distribution
        U

namespace LogarithmicTargetAmbientData

variable
  {d k : Nat} [NeZero d]
  {predecessor : OSIITimeContinuationStage d k}
  {base : Set (Fin k -> Real)}

/-- The zero logarithmic point belongs to the exact tube. -/
theorem zero_mem_logarithmicTube
    (T : LogarithmicTargetAmbientData predecessor base) :
    (0 : Fin k -> Complex) ∈ osiiLogarithmicTube base := by
  rw [osiiLogarithmicTube, SCV.TubeDomain,
    osiiPhysicalLogarithmicBase]
  refine ⟨T.zero_mem_base, ?_⟩
  intro i
  simp
  positivity

/-- Restrict the ambient branch to the exact logarithmic tube. -/
noncomputable def exactLogarithmicTargetStage
    (T : LogarithmicTargetAmbientData predecessor base) :
    OSIITimeContinuationStage d k :=
  restrictTimeContinuationStageCarrier
    T.stage
    (osiiLogarithmicTube base)
    (isOpen_osiiLogarithmicTube T.base_open)
    T.tube_subset_stage

@[simp] theorem exactLogarithmicTargetStage_carrier
    (T : LogarithmicTargetAmbientData predecessor base) :
    T.exactLogarithmicTargetStage.carrier =
      osiiLogarithmicTube base :=
  rfl

@[simp] theorem exactLogarithmicTargetStage_distribution
    (T : LogarithmicTargetAmbientData predecessor base)
    (z : Fin k -> Complex) :
    T.exactLogarithmicTargetStage.distribution z =
      T.stage.distribution z :=
  rfl

/-- Transport the exact logarithmic target to physical time gaps. -/
noncomputable def exactPhysicalTargetStage
    (T : LogarithmicTargetAmbientData predecessor base) :
    OSIITimeContinuationStage d k :=
  principalLogPushforwardStage T.exactLogarithmicTargetStage

/-- Principal-log transport has exactly the physical argument carrier of the
chosen logarithmic base. -/
theorem exactPhysicalTargetStage_carrier
    (T : LogarithmicTargetAmbientData predecessor base) :
    T.exactPhysicalTargetStage.carrier =
      osiiTimeArgumentCarrier base := by
  ext z
  constructor
  · rintro ⟨hz_right, hz_log⟩
    refine ⟨hz_right, ?_⟩
    have hz_tube :
        osiiPrincipalLog z ∈ osiiLogarithmicTube base := by
      simpa using hz_log
    rw [osiiLogarithmicTube, SCV.TubeDomain,
      osiiPhysicalLogarithmicBase] at hz_tube
    simpa [osiiPrincipalLog_im] using hz_tube.1
  · intro hz
    exact
      ⟨hz.1, osiiPrincipalLog_mem_logarithmicTube hz⟩

/-- The zero-centered logarithmic germ pushes to a nonempty open physical
germ on which the exact target agrees with its predecessor. -/
theorem exists_open_seed_exactPhysicalTarget_eq_predecessor
    (T : LogarithmicTargetAmbientData predecessor base) :
    ∃ V : Set (OSIITimeGapSpace k),
      IsOpen V ∧ V.Nonempty ∧
      V ⊆
        T.exactPhysicalTargetStage.carrier ∩
          predecessor.carrier ∧
      Set.EqOn
        T.exactPhysicalTargetStage.distribution
        predecessor.distribution
        V := by
  obtain ⟨U, hU_open, hU_zero, hU_subset, hU_eq⟩ :=
    T.exists_open_seed
  let tube : Set (Fin k -> Complex) :=
    osiiLogarithmicTube base
  let W : Set (Fin k -> Complex) := U ∩ tube
  let V : Set (OSIITimeGapSpace k) :=
    osiiTimeRightHalfPlane k ∩
      osiiPrincipalLog ⁻¹' W
  have hW_open : IsOpen W := by
    exact
      hU_open.inter
        (isOpen_osiiLogarithmicTube T.base_open)
  have hV_open : IsOpen V := by
    exact
      (osiiPrincipalLog_differentiableOn_rightHalfPlane k).continuousOn
        |>.isOpen_inter_preimage
          (isOpen_osiiTimeRightHalfPlane k)
          hW_open
  let onePoint : OSIITimeGapSpace k :=
    osiiPositiveRealTimeEmbed (fun _ => (1 : Real))
  have hone_right :
      onePoint ∈ osiiTimeRightHalfPlane k := by
    apply
      (osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff
        (fun _ : Fin k => (1 : Real))).2
    intro i
    norm_num
  have hlog_one :
      osiiPrincipalLog onePoint =
        (0 : Fin k -> Complex) := by
    funext i
    simp [onePoint, osiiPrincipalLog,
      osiiPositiveRealTimeEmbed]
  have hone_V : onePoint ∈ V := by
    refine ⟨hone_right, ?_⟩
    change osiiPrincipalLog onePoint ∈ W
    rw [hlog_one]
    exact ⟨hU_zero, T.zero_mem_logarithmicTube⟩
  refine ⟨V, hV_open, ⟨onePoint, hone_V⟩, ?_, ?_⟩
  · intro z hz
    have hzlog : osiiPrincipalLog z ∈ W := hz.2
    refine ⟨?_, ?_⟩
    · exact ⟨hz.1, hzlog.2⟩
    · have hpull := (hU_subset hzlog.1).2
      change
        osiiLogExp (osiiPrincipalLog z) ∈
          predecessor.carrier at hpull
      simpa [osiiLogExp_principalLog hz.1] using hpull
  · intro z hz
    have hzlog : osiiPrincipalLog z ∈ W := hz.2
    calc
      T.exactPhysicalTargetStage.distribution z =
          T.stage.distribution (osiiPrincipalLog z) := rfl
      _ =
          (logarithmicPullbackStage predecessor).distribution
            (osiiPrincipalLog z) :=
        hU_eq hzlog.1
      _ =
          predecessor.distribution
            (osiiLogExp (osiiPrincipalLog z)) := rfl
      _ = predecessor.distribution z := by
        rw [osiiLogExp_principalLog hz.1]

/-- Pointed predecessor geometry sufficient for physical target gluing. The
hub membership is explicit because the atlas index type need not be known to
be inhabited. -/
structure PhysicalPointedPredecessorData
    (T : LogarithmicTargetAmbientData predecessor base) where
  chart : Type
  hub : Fin k -> Real
  hub_positive :
    hub ∈ section43TimeStrictPositiveRegion k
  hub_mem_predecessor :
    osiiPositiveRealTimeEmbed hub ∈ predecessor.carrier
  pointedAtlas :
    GeneratorStagePointedConvexAtlas
      predecessor
      (osiiPositiveRealTimeEmbed hub)
      chart

namespace PhysicalPointedPredecessorData

variable
  {T : LogarithmicTargetAmbientData predecessor base}

/-- Every positive-real hub belongs to an exact target whose logarithmic base
contains zero. -/
theorem hub_mem_exactPhysicalTargetStage
    (P : PhysicalPointedPredecessorData T) :
    osiiPositiveRealTimeEmbed P.hub ∈
      T.exactPhysicalTargetStage.carrier := by
  rw [T.exactPhysicalTargetStage_carrier]
  refine
    ⟨(osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff
        P.hub).2 P.hub_positive,
      ?_⟩
  have harg :
      osiiTimeArgumentVector
          (osiiPositiveRealTimeEmbed P.hub) =
        (0 : Fin k -> Real) := by
    funext i
    rw [osiiTimeArgumentVector, osiiPositiveRealTimeEmbed,
      Complex.arg_ofReal_of_nonneg (P.hub_positive i).le]
    rfl
  rw [harg]
  exact T.zero_mem_base

/-- The exact physical target and pointed predecessor have connected
overlap through their common positive-real hub. -/
theorem overlap_connected
    (P : PhysicalPointedPredecessorData T) :
    IsConnected
      (T.exactPhysicalTargetStage.carrier ∩
        predecessor.carrier) := by
  have htarget :
      StarConvex Real
        (osiiPositiveRealTimeEmbed P.hub)
        T.exactPhysicalTargetStage.carrier := by
    rw [T.exactPhysicalTargetStage_carrier]
    exact
      starConvex_osiiTimeArgumentCarrier_of_coordinatewiseSolid
        T.base_solid P.hub P.hub_positive
  have hpredecessor :
      StarConvex Real
        (osiiPositiveRealTimeEmbed P.hub)
        predecessor.carrier :=
    P.pointedAtlas.carrier_starConvex
  have hhub :
      osiiPositiveRealTimeEmbed P.hub ∈
        T.exactPhysicalTargetStage.carrier ∩
          predecessor.carrier :=
    ⟨P.hub_mem_exactPhysicalTargetStage,
      P.hub_mem_predecessor⟩
  exact
    ((htarget.inter hpredecessor).isPathConnected hhub).isConnected

/-- The physical identity theorem propagates the common germ to the complete
target/predecessor overlap. -/
theorem target_eqOn_predecessor
    (P : PhysicalPointedPredecessorData T) :
    Set.EqOn
      T.exactPhysicalTargetStage.distribution
      predecessor.distribution
      (T.exactPhysicalTargetStage.carrier ∩
        predecessor.carrier) := by
  obtain ⟨V, hV_open, hV_nonempty, hV_subset, hV_eq⟩ :=
    T.exists_open_seed_exactPhysicalTarget_eq_predecessor
  apply
    weaklyHolomorphic_eqOn_of_eqOn_open
      (T.exactPhysicalTargetStage.carrier_open.inter
        predecessor.carrier_open)
      P.overlap_connected
      hV_open hV_nonempty hV_subset
  · intro chi
    exact
      (T.exactPhysicalTargetStage.weaklyHolomorphic chi).mono
        Set.inter_subset_left
  · intro chi
    exact
      (predecessor.weaklyHolomorphic chi).mono
        Set.inter_subset_right
  · exact hV_eq

/-- Two-branch family consisting of the complete predecessor and the exact
physical target. -/
noncomputable def toLocalTimeStageFamily
    (P : PhysicalPointedPredecessorData T) :
    OSIILocalTimeStageFamily d k Bool where
  domain
    | false => predecessor.carrier
    | true => T.exactPhysicalTargetStage.carrier
  domain_open
    | false => predecessor.carrier_open
    | true => T.exactPhysicalTargetStage.carrier_open
  distribution
    | false => predecessor.distribution
    | true => T.exactPhysicalTargetStage.distribution
  weaklyHolomorphic
    | false => predecessor.weaklyHolomorphic
    | true => T.exactPhysicalTargetStage.weaklyHolomorphic
  compatible := by
    intro a b
    cases a <;> cases b
    · intro z hz
      rfl
    · intro z hz
      exact P.target_eqOn_predecessor ⟨hz.2, hz.1⟩ |>.symm
    · exact P.target_eqOn_predecessor
    · intro z hz
      rfl

/-- The physical successor obtained by adjoining the exact target to the
complete predecessor. -/
noncomputable def physicalSuccessorStage
    (P : PhysicalPointedPredecessorData T) :
    OSIITimeContinuationStage d k :=
  P.toLocalTimeStageFamily.toTimeContinuationStage

theorem predecessorCarrier_subset_physicalSuccessorStage
    (P : PhysicalPointedPredecessorData T) :
    predecessor.carrier ⊆ P.physicalSuccessorStage.carrier := by
  intro z hz
  exact Set.mem_iUnion_of_mem false hz

theorem targetCarrier_subset_physicalSuccessorStage
    (P : PhysicalPointedPredecessorData T) :
    T.exactPhysicalTargetStage.carrier ⊆
      P.physicalSuccessorStage.carrier := by
  intro z hz
  exact Set.mem_iUnion_of_mem true hz

theorem physicalSuccessorStage_extends_predecessor
    (P : PhysicalPointedPredecessorData T) :
    Set.EqOn
      P.physicalSuccessorStage.distribution
      predecessor.distribution
      predecessor.carrier :=
  P.toLocalTimeStageFamily.gluedDistribution_eqOn_domain false

theorem targetArgumentCarrier_subset_physicalSuccessorStage
    (P : PhysicalPointedPredecessorData T) :
    osiiTimeArgumentCarrier base ⊆
      P.physicalSuccessorStage.carrier := by
  rw [← T.exactPhysicalTargetStage_carrier]
  exact P.targetCarrier_subset_physicalSuccessorStage

/-- Both branches are star-convex about the same hub, so their union is
star-convex about that hub. -/
theorem physicalSuccessorStage_starConvex
    (P : PhysicalPointedPredecessorData T) :
    StarConvex Real
      (osiiPositiveRealTimeEmbed P.hub)
      P.physicalSuccessorStage.carrier := by
  change
    StarConvex Real
      (osiiPositiveRealTimeEmbed P.hub)
      (⋃ b : Bool, P.toLocalTimeStageFamily.domain b)
  apply starConvex_iUnion
  intro b
  cases b with
  | false =>
      exact P.pointedAtlas.carrier_starConvex
  | true =>
      change
        StarConvex Real
          (osiiPositiveRealTimeEmbed P.hub)
          T.exactPhysicalTargetStage.carrier
      rw [T.exactPhysicalTargetStage_carrier]
      exact
        starConvex_osiiTimeArgumentCarrier_of_coordinatewiseSolid
          T.base_solid P.hub P.hub_positive

end PhysicalPointedPredecessorData
end LogarithmicTargetAmbientData

end OSIIChapterV
end OSReconstruction
