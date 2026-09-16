/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRawGeneratedRecursiveAngleDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorNormalizedEnvelopeHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorAdaptiveShiftHandoff












noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open StrictGeneratedScalarDepthPointedData
open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

/-- The reflected-left block of an exact raw generator chart remains in the
corresponding raw mixed-tail carrier.

The singleton generator carrier fixes the target arguments exactly.  Removing
the mixed head therefore recovers the same raw left argument, including the
one-particle endpoint case handled separately below. -/
theorem rootedLeftBlockTarget_mem_rawMixedTailArgumentCarrier_of_raw_generator
    {k q m depth : Nat}
    (hn : 1 <= q + 2)
    (hm : 1 <= m)
    (hnm : k = q + 2 + m - 1)
    (z : OSIITimeGapSpace k)
    (left : Fin (q + 2) -> Real)
    (hleft :
      OSIIRawStrictGeneratedLogarithmicArgument
        .mixed (q + 2) depth left)
    (right : Fin m -> Real)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint
            (⟨q + 2, m, hn, hm, hnm⟩ : GeneratorIndex k)
            left theta right} :
          Set (Fin k -> Real))) :
    rootedLeftBlockTarget
        (⟨q + 2, m, hn, hm, hnm⟩ : GeneratorIndex k) z ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase
          ((q + 1) + 1) depth) := by
  let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let zleft := rootedLeftBlockTarget i z
  have hzleft_exact :
      zleft ∈
        osiiTimeArgumentCarrier
          ({osiiMixedArgumentTail left} :
            Set (Fin (q + 1) -> Real)) := by
    simpa [i, zleft, rootedLeftBlockTarget] using
      star_generatorChronological_split_left_mem_argumentCarrier
        i left theta right hz
  refine ⟨hzleft_exact.1, ?_⟩
  have harg :
      osiiTimeArgumentVector zleft =
        osiiMixedArgumentTail left :=
    Set.mem_singleton_iff.mp hzleft_exact.2
  have hhead : left 0 = 0 :=
    OSIIRawStrictGeneratedLogarithmicArgument.mixed_head_eq_zero
      (by omega) hleft
  have hcons :
      Fin.cons 0 (osiiMixedArgumentTail left) = left := by
    simpa [osiiMixedArgumentTail, hhead] using
      Fin.cons_self_tail left
  have hconsarg :
      @Fin.cons (q + 1) (fun _ => Real) 0
          (osiiTimeArgumentVector zleft) =
        @Fin.cons (q + 1) (fun _ => Real) 0
          (osiiMixedArgumentTail left) :=
    congrArg
      (fun v : Fin (q + 1) -> Real =>
        @Fin.cons (q + 1) (fun _ => Real) 0 v) harg
  rw [hconsarg, hcons]
  simpa [i, osiiRawStrictGeneratedMixedLogarithmicBase] using hleft

/-- The right block of an exact raw generator chart remains in the
corresponding raw mixed-tail carrier. -/
theorem rootedRightBlockTarget_mem_rawMixedTailArgumentCarrier_of_raw_generator
    {k n q depth : Nat}
    (hn : 1 <= n)
    (hm : 1 <= q + 2)
    (hnm : k = n + (q + 2) - 1)
    (z : OSIITimeGapSpace k)
    (left : Fin n -> Real)
    (right : Fin (q + 2) -> Real)
    (hright :
      OSIIRawStrictGeneratedLogarithmicArgument
        .mixed (q + 2) depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint
            (⟨n, q + 2, hn, hm, hnm⟩ : GeneratorIndex k)
            left theta right} :
          Set (Fin k -> Real))) :
    rootedRightBlockTarget
        (⟨n, q + 2, hn, hm, hnm⟩ : GeneratorIndex k) z ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase
          ((q + 1) + 1) depth) := by
  let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
  let zright := rootedRightBlockTarget i z
  have hzright_exact :
      zright ∈
        osiiTimeArgumentCarrier
          ({osiiMixedArgumentTail right} :
            Set (Fin (q + 1) -> Real)) := by
    simpa [i, zright, rootedRightBlockTarget] using
      generatorChronological_split_right_mem_argumentCarrier
        i left theta right hz
  refine ⟨hzright_exact.1, ?_⟩
  have harg :
      osiiTimeArgumentVector zright =
        osiiMixedArgumentTail right :=
    Set.mem_singleton_iff.mp hzright_exact.2
  have hhead : right 0 = 0 :=
    OSIIRawStrictGeneratedLogarithmicArgument.mixed_head_eq_zero
      (by omega) hright
  have hcons :
      Fin.cons 0 (osiiMixedArgumentTail right) = right := by
    simpa [osiiMixedArgumentTail, hhead] using
      Fin.cons_self_tail right
  have hconsarg :
      @Fin.cons (q + 1) (fun _ => Real) 0
          (osiiTimeArgumentVector zright) =
        @Fin.cons (q + 1) (fun _ => Real) 0
          (osiiMixedArgumentTail right) :=
    congrArg
      (fun v : Fin (q + 1) -> Real =>
        @Fin.cons (q + 1) (fun _ => Real) 0 v) harg
  rw [hconsarg, hcons]
  simpa [i, osiiRawStrictGeneratedMixedLogarithmicBase] using hright

/-- A one-particle left endpoint contributes the zero raw mixed source at
every depth. -/
theorem rootedLeftBlockTarget_mem_rawMixedTailArgumentCarrier_of_left_endpoint
    {k m depth : Nat}
    (hm : 1 <= m)
    (hnm : k = 1 + m - 1)
    (z : OSIITimeGapSpace k) :
    rootedLeftBlockTarget
        (⟨1, m, le_rfl, hm, hnm⟩ : GeneratorIndex k) z ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase 1 depth) := by
  constructor
  · intro j
    exact Fin.elim0 j
  · have hzero :=
      OSIIRawStrictGeneratedLogarithmicArgument.mixed_zero
        1 depth (by omega)
    change OSIIRawStrictGeneratedLogarithmicArgument .mixed 1 depth
      (Fin.cons 0 (osiiTimeArgumentVector
        (rootedLeftBlockTarget
          (⟨1, m, le_rfl, hm, hnm⟩ : GeneratorIndex k) z)))
    convert hzero using 1
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl

/-- A one-particle right endpoint contributes the zero raw mixed source at
every depth. -/
theorem rootedRightBlockTarget_mem_rawMixedTailArgumentCarrier_of_right_endpoint
    {k n depth : Nat}
    (hn : 1 <= n)
    (hnm : k = n + 1 - 1)
    (z : OSIITimeGapSpace k) :
    rootedRightBlockTarget
        (⟨n, 1, hn, le_rfl, hnm⟩ : GeneratorIndex k) z ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase 1 depth) := by
  constructor
  · intro j
    exact Fin.elim0 j
  · have hzero :=
      OSIIRawStrictGeneratedLogarithmicArgument.mixed_zero
        1 depth (by omega)
    change OSIIRawStrictGeneratedLogarithmicArgument .mixed 1 depth
      (Fin.cons 0 (osiiTimeArgumentVector
        (rootedRightBlockTarget
          (⟨n, 1, hn, le_rfl, hnm⟩ : GeneratorIndex k) z)))
    convert hzero using 1
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl

/-- A retained radial generator chart whose expanded lower inputs are known
to come from the raw mixed recurrence.

The legacy rank witness remains available for the existing continuation
backend.  These two extra fields record the stronger manuscript-faithful
provenance needed when raw equation (6.28') is applied to reflected lower
sources. -/
structure RawRecursiveAngleRadialGeneratorChartAtRank
    (k depth rank : Nat) where
  radial : RecursiveAngleRadialGeneratorChartAtRank k depth rank
  expanded_left_raw :
    OSIIRawStrictGeneratedLogarithmicArgument
      .mixed radial.chart.generator.n depth radial.expandedLeft
  expanded_right_raw :
    OSIIRawStrictGeneratedLogarithmicArgument
      .mixed radial.chart.generator.m depth radial.expandedRight

private theorem firstBridge_expandedLeft_raw
    {q depth rank : Nat}
    (R : RecursiveAngleFirstBridgeRadialGeneratorChartAtRank
      q depth rank) :
    OSIIRawStrictGeneratedLogarithmicArgument
      .mixed R.radial.chart.generator.n depth R.radial.expandedLeft := by
  cases R with
  | mk radial generator_eq expanded_right_tail_bound
      expanded_right_coordinate =>
    cases radial with
    | mk chart expandedLeft expanded_left_rank expandedTheta
        expanded_angle_bound expandedRight expanded_right_rank
        chart_left_eq chart_theta_eq chart_right_eq target_argument_eq =>
      cases chart with
      | mk generator left left_rank theta angle_bound right right_rank
          target target_mem =>
        cases generator with
        | mk n m hn hm hnm =>
          have hn_eq : n = 1 := by
            simpa using congrArg GeneratorIndex.n generator_eq
          subst n
          have hleft0 :
              expandedLeft ⟨0, hn⟩ = 0 :=
            OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
              hn expanded_left_rank
          apply rawStrict_recursiveAngle_mixedBox_subset 0 depth
          exact ⟨by simpa using hleft0, fun j => Fin.elim0 j⟩

private theorem firstBridge_expandedRight_raw
    {q depth rank : Nat}
    (R : RecursiveAngleFirstBridgeRadialGeneratorChartAtRank
      q depth rank) :
    OSIIRawStrictGeneratedLogarithmicArgument
      .mixed R.radial.chart.generator.m depth R.radial.expandedRight := by
  cases R with
  | mk radial generator_eq expanded_right_tail_bound
      expanded_right_coordinate =>
    cases radial with
    | mk chart expandedLeft expanded_left_rank expandedTheta
        expanded_angle_bound expandedRight expanded_right_rank
        chart_left_eq chart_theta_eq chart_right_eq target_argument_eq =>
      cases chart with
      | mk generator left left_rank theta angle_bound right right_rank
          target target_mem =>
        cases generator with
        | mk n m hn hm hnm =>
          have hm_eq : m = q + 1 := by
            simpa using congrArg GeneratorIndex.m generator_eq
          subst m
          have hright0 :
              expandedRight ⟨0, hm⟩ = 0 :=
            OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
              hm expanded_right_rank
          apply rawStrict_recursiveAngle_mixedBox_subset q depth
          refine ⟨by simpa using hright0, ?_⟩
          intro j
          exact expanded_right_tail_bound j

/-- A canonical first-bridge radial chart has raw provenance for both of its
expanded lower blocks.

The left block is the one-point zero mixed source.  The right block is the
retained predecessor tail, so its stored recursive-angle inequalities put it
in the raw mixed box directly.  No ranked-to-raw implication is used here. -/
def StrictGeneratedScalarDepthPointedData.RecursiveAngleFirstBridgeRadialGeneratorChartAtRank.toRawRadial
    {q depth rank : Nat}
    (R : RecursiveAngleFirstBridgeRadialGeneratorChartAtRank
      q depth rank) :
    RawRecursiveAngleRadialGeneratorChartAtRank (q + 1) depth rank where
  radial := R.radial
  expanded_left_raw := firstBridge_expandedLeft_raw R
  expanded_right_raw := firstBridge_expandedRight_raw R

/-- The recursive-angle sector has one common rank of canonical first-bridge
charts whose expanded lower sources are certified in the raw mixed
recurrence.

This is the source-side counterpart of the legacy radial exhaustion theorem:
the selected chart and its common rank are unchanged, but the two lower
blocks now carry the exact provenance needed by raw equation `(6.28')`. -/
theorem
    exists_rank_rawRecursiveAngleFirstBridgeRadialGeneratorChart_eq_on_recursiveAngleSector
    (q depth : Nat) :
    ∃ rank : Nat,
      ∀ z : OSIITimeGapSpace (q + 1),
        z ∈ osiiTimeArgumentSector
          (osiiRecursiveAngleAperture (q + 1) (depth + 1)) →
        ∃ radial : RawRecursiveAngleRadialGeneratorChartAtRank
            (q + 1) depth rank,
          radial.radial.chart.generator = firstBridgeGeneratorIndex q ∧
            radial.radial.chart.target = z := by
  obtain ⟨rank, hcharts⟩ :=
    exists_rank_recursiveAngleFirstBridgeRadialGeneratorChart_eq_on_recursiveAngleSector
      q depth
  refine ⟨rank, ?_⟩
  intro z hz
  obtain ⟨radial, htarget⟩ := hcharts z hz
  exact ⟨radial.toRawRadial, radial.generator_eq, htarget⟩

namespace RawRecursiveAngleRadialGeneratorChartAtRank

end RawRecursiveAngleRadialGeneratorChartAtRank

end OSIIChapterV
end OSReconstruction
