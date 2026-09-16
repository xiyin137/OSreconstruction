/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVOneParticleTranslatedMixedDeltaProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedRootedSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorGeneratorBounds
















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

namespace RootedGeneratorSelectedCompactEndpointTargetData

end RootedGeneratorSelectedCompactEndpointTargetData

namespace RootedGeneratorSelectedWeightedSourceContinuationData

variable
  {d k depth t : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {T : RootedA0BlockContinuousTranslationData OS A R}
  {i : GeneratorIndex k}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {epsilon : Real}
  {bound : forall arity,
    SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
  {Denv : VI2NormalizedEnvelopeFamilyData
    (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
      (OS := OS) S) t epsilon bound}
  {target : forall arity, Set (Fin arity -> Complex)}
  {Henv : VI2NormalizedEnvelopeSeminormBoundData Denv}
  {Bleft Bright : Real}

end RootedGeneratorSelectedWeightedSourceContinuationData

namespace RootedGeneratorAsymmetricWeightedGramContinuationData

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
  {B Bleft Bright : Real}

variable
  {t : Nat}
  {epsilon : Real}
  {bound : forall arity,
    SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
  {Denv : VI2NormalizedEnvelopeFamilyData
    (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
      (OS := OS) S) t epsilon bound}
  {target : forall arity, Set (Fin arity -> Complex)}
  {Henv : VI2NormalizedEnvelopeSeminormBoundData Denv}

end RootedGeneratorAsymmetricWeightedGramContinuationData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace StrictGeneratedScalarDepthPointedData

variable {depth : Nat}






/-- A radial rooted chart retaining the uncontracted generator pieces for
the very same split as its selected target chart.

The lighter radial wrapper above is enough for scalar target bookkeeping.
Safe normalization shifts need the stronger same-generator provenance:
left, bridge, and right block arguments must be compared with the matching
expanded mixed inputs, not with an unrelated generator presentation of the
same scalar argument vector. -/
structure RecursiveAngleRadialGeneratorChartAtRank
    (k depth rank : Nat) where
  chart : RootedStrictGeneratedTargetHubChartAtRank k depth rank
  expandedLeft : Fin chart.generator.n -> Real
  expanded_left_rank :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed chart.generator.n depth expandedLeft
  expandedTheta : Real
  expanded_angle_bound : |expandedTheta| < Real.pi / 2
  expandedRight : Fin chart.generator.m -> Real
  expanded_right_rank :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed chart.generator.m depth expandedRight
  chart_left_eq :
    chart.left =
      (1 - 1 / (2 : Real) ^ (depth + 1)) • expandedLeft
  chart_theta_eq :
    chart.theta =
      (1 - 1 / (2 : Real) ^ (depth + 1)) * expandedTheta
  chart_right_eq :
    chart.right =
      (1 - 1 / (2 : Real) ^ (depth + 1)) • expandedRight
  target_argument_eq :
    osiiTimeArgumentVector chart.target =
      (1 - 1 / (2 : Real) ^ (depth + 1)) •
        osiiArgumentGeneratorPoint chart.generator
          expandedLeft expandedTheta expandedRight

/-- The expanded right block of a canonical first-bridge radial chart,
transported to its explicit predecessor arity. -/
def RecursiveAngleRadialGeneratorChartAtRank.firstBridgeExpandedRight
    {q depth rank : Nat}
    (R : RecursiveAngleRadialGeneratorChartAtRank (q + 1) depth rank)
    (hgenerator : R.chart.generator = firstBridgeGeneratorIndex q) :
    Fin (q + 1) -> Real :=
  fun j =>
    R.expandedRight
      (Fin.cast
        (by
          simpa using
            (congrArg GeneratorIndex.m hgenerator).symm)
        j)

/-- Canonical first-bridge radial chart for the recursive sector.

Retaining the generator identity is mathematically significant: its left
source is the one-particle endpoint, while its right source is the explicit
mixed tail at the preceding outer depth. -/
structure RecursiveAngleFirstBridgeRadialGeneratorChartAtRank
    (q depth rank : Nat) where
  radial : RecursiveAngleRadialGeneratorChartAtRank (q + 1) depth rank
  generator_eq : radial.chart.generator = firstBridgeGeneratorIndex q
  expanded_right_tail_bound :
    forall j : Fin q,
      |osiiMixedArgumentTail
          (radial.firstBridgeExpandedRight generator_eq) j| <
        osiiRecursiveAngleAperture q depth j
  expanded_right_coordinate :
    forall j : Fin q,
      osiiArgumentGeneratorPoint radial.chart.generator
          radial.expandedLeft radial.expandedTheta radial.expandedRight j.succ =
        osiiMixedArgumentTail
          (radial.firstBridgeExpandedRight generator_eq) j

namespace RecursiveAngleRadialGeneratorChartAtRank

end RecursiveAngleRadialGeneratorChartAtRank

/-- The recursive-angle sector admits one common analytic rank of canonical
first-bridge radial charts.  Unlike the legacy exhaustion theorem, this form
retains the exact split used to expose the predecessor mixed tail. -/
theorem
    exists_rank_recursiveAngleFirstBridgeRadialGeneratorChart_eq_on_recursiveAngleSector
    (q depth : Nat) :
    ∃ rank : Nat,
      ∀ z : OSIITimeGapSpace (q + 1),
        z ∈ osiiTimeArgumentSector
          (osiiRecursiveAngleAperture (q + 1) (depth + 1)) ->
        ∃ radial : RecursiveAngleFirstBridgeRadialGeneratorChartAtRank
            q depth rank,
          radial.radial.chart.target = z := by
  by_cases hdepth : q <= depth
  · obtain ⟨rank, r, hr_eq, hr_pos, hr_lt, hcharts⟩ :=
      exists_rank_recursiveAngle_firstBridge_radialExpansion
        q depth hdepth
    refine ⟨rank, ?_⟩
    intro z hz
    have hexpansion :=
      hcharts (osiiTimeArgumentVector z) hz.2
    let theta := Classical.choose hexpansion
    have hrightExists := Classical.choose_spec hexpansion
    let right := Classical.choose hrightExists
    have hexpansionData := Classical.choose_spec hrightExists
    obtain ⟨hright, htail, htheta, htarget⟩ := hexpansionData
    let i := firstBridgeGeneratorIndex q
    have hleft :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .mixed 1 depth (0 : Fin 1 -> Real) :=
      OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_zero_mem
        rank 1 depth (by omega)
    have hr_abs : |r| <= 1 := by
      rw [abs_of_pos hr_pos]
      exact hr_lt.le
    have hcontracted :
        osiiArgumentGeneratorPoint i
            (r • (0 : Fin 1 -> Real)) (r * theta) (r • right) =
          r • osiiArgumentGeneratorPoint i
            (0 : Fin 1 -> Real) theta right := by
      dsimp [i]
      rw [osiiArgumentGeneratorPoint_firstBridge,
        osiiArgumentGeneratorPoint_firstBridge]
      funext j
      refine Fin.cases ?_ (fun a => ?_) j
      · rfl
      · change r * right a.succ = r * right a.succ
        rfl
    let chart : RootedStrictGeneratedTargetHubChartAtRank
        (q + 1) depth rank :=
      { generator := i
        left := r • (0 : Fin 1 -> Real)
        left_rank :=
          strictGeneratedAtRank_smul_of_abs_le_one hleft r hr_abs
        theta := r * theta
        angle_bound := by
          rw [abs_mul, abs_of_pos hr_pos]
          exact
            (mul_le_mul_of_nonneg_right hr_lt.le
              (abs_nonneg theta)).trans_lt (by simpa [theta] using htheta)
        right := r • right
        right_rank :=
          strictGeneratedAtRank_smul_of_abs_le_one hright r hr_abs
        target := z
        target_mem := by
          refine ⟨hz.1, Set.mem_singleton_iff.mpr ?_⟩
          calc
            osiiTimeArgumentVector z =
                r • osiiArgumentGeneratorPoint i
                  (0 : Fin 1 -> Real) theta right := by
              simpa [i, theta, right] using htarget
            _ = osiiArgumentGeneratorPoint i
                (r • (0 : Fin 1 -> Real)) (r * theta) (r • right) :=
              hcontracted.symm }
    let radial : RecursiveAngleRadialGeneratorChartAtRank
        (q + 1) depth rank :=
      { chart := chart
        expandedLeft := (0 : Fin 1 -> Real)
        expanded_left_rank := hleft
        expandedTheta := theta
        expanded_angle_bound := htheta
        expandedRight := right
        expanded_right_rank := hright
        chart_left_eq := by
          dsimp [chart]
          rw [← hr_eq]
          rfl
        chart_theta_eq := by
          dsimp [chart]
          rw [← hr_eq]
        chart_right_eq := by
          dsimp [chart]
          rw [← hr_eq]
          rfl
        target_argument_eq := by
          simpa [chart, i, theta, right, hr_eq] using htarget }
    refine ⟨⟨radial, rfl, ?_, ?_⟩, ?_⟩
    · have hfirst : radial.firstBridgeExpandedRight (by rfl) = right := by
        funext j
        simp only [RecursiveAngleRadialGeneratorChartAtRank.firstBridgeExpandedRight]
        dsimp [radial]
        congr 1
      rw [hfirst]
      simpa [right] using htail
    · intro j
      simp [RecursiveAngleRadialGeneratorChartAtRank.firstBridgeExpandedRight,
        radial, chart, i, theta, right,
        osiiArgumentGeneratorPoint_firstBridge, osiiMixedArgumentTail]
      rfl
    · rfl
  · refine ⟨0, ?_⟩
    intro z hz
    have hsector_depth : q + 1 <= depth + 1 :=
      arity_le_depth_of_mem_recursiveAngleTimeArgumentSector hz
    omega

namespace RecursiveSectorNormalizedOrbitEnvelopeRankFamilyData

end RecursiveSectorNormalizedOrbitEnvelopeRankFamilyData

namespace RecursiveSectorSelectedVI2RetainedSourceData

variable
  {D : StrictGeneratedScalarDepthPointedData OS depth}
  {lgc : OSLinearGrowthCondition d OS}
  {q : Nat}
  {epsilon : Real}
  {t : Nat}
  {alpha : Real}
  {beta M : Nat}
  {chi : SchwartzMap (Section43SpatialSpace d (q + 1)) Complex}
  {z : OSIITimeGapSpace (q + 1)}

end RecursiveSectorSelectedVI2RetainedSourceData

end StrictGeneratedScalarDepthPointedData

end OSIIChapterV
end OSReconstruction
