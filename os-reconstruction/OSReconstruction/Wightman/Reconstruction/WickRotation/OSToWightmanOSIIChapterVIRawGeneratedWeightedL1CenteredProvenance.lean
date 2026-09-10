/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRawGeneratedReflectedDiagonalCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRawGeneratedPointedDepthHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedEndpointRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621EndpointProbeRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedTwoPointRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedRootedSourceCarrier











noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

namespace RootedStrictGeneratedTargetHubChartAtRank

/-- A rooted generator chart with raw left provenance exposes its exact raw
mixed-tail source, including the one-particle endpoint. -/
theorem rootedLeftBlockTarget_mem_rawMixedTailArgumentCarrier
    {k depth rank : Nat}
    (a : RootedStrictGeneratedTargetHubChartAtRank k depth rank)
    (hleft_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed a.generator.n depth a.left) :
    rootedLeftBlockTarget a.generator a.target ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase
          ((a.generator.n - 1) + 1) depth) := by
  cases a with
  | mk generator left left_rank theta angle_bound right right_rank
      target target_mem =>
      cases generator with
      | mk nLeft m hn hm hnm =>
          by_cases hn_one : nLeft = 1
          · subst nLeft
            simpa using
              (rootedLeftBlockTarget_mem_rawMixedTailArgumentCarrier_of_left_endpoint
                (k := k) (m := m) (depth := depth) hm hnm target)
          · obtain ⟨q, hq⟩ : ∃ q, nLeft = q + 2 := by
              exact ⟨nLeft - 2, by omega⟩
            subst nLeft
            exact
              rootedLeftBlockTarget_mem_rawMixedTailArgumentCarrier_of_raw_generator
                hn hm hnm target left hleft_raw right theta target_mem

/-- Right-block form of the raw left source-carrier lemma. -/
theorem rootedRightBlockTarget_mem_rawMixedTailArgumentCarrier
    {k depth rank : Nat}
    (a : RootedStrictGeneratedTargetHubChartAtRank k depth rank)
    (hright_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed a.generator.m depth a.right) :
    rootedRightBlockTarget a.generator a.target ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase
          ((a.generator.m - 1) + 1) depth) := by
  cases a with
  | mk generator left left_rank theta angle_bound right right_rank
      target target_mem =>
      cases generator with
      | mk nLeft mRight hn hm hnm =>
          by_cases hm_one : mRight = 1
          · subst mRight
            simpa using
              (rootedRightBlockTarget_mem_rawMixedTailArgumentCarrier_of_right_endpoint
                (k := k) (n := nLeft) (depth := depth) hn hnm target)
          · obtain ⟨q, hq⟩ : ∃ q, mRight = q + 2 := by
              exact ⟨mRight - 2, by omega⟩
            subst mRight
            exact
              rootedRightBlockTarget_mem_rawMixedTailArgumentCarrier_of_raw_generator
                hn hm hnm target left right hright_raw theta target_mem

end RootedStrictGeneratedTargetHubChartAtRank

/-- A centered generator presentation retaining both the analytic-rank and
raw mixed provenance of its two lower blocks. -/
structure RawGeneratorCoordinatewiseShrinkData
    {k : Nat}
    (rank sourceDepth : Nat)
    (i : GeneratorIndex k)
    (y : Fin k -> Real) where
  centered : GeneratorCoordinatewiseShrinkData rank sourceDepth i y
  left_raw :
    OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.n sourceDepth centered.left
  right_raw :
    OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.m sourceDepth centered.right

/-- A coordinatewise shrink of a generator point preserves both ranked and
raw mixed provenance for the same split. -/
theorem nonempty_rawGeneratorCoordinatewiseShrinkData
    {k rank sourceDepth : Nat}
    (i : GeneratorIndex k)
    (left : Fin i.n -> Real)
    (hleft_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.n sourceDepth left)
    (hleft_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.n sourceDepth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.m sourceDepth right)
    (hright_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.m sourceDepth right)
    (y : Fin k -> Real)
    (hy : forall j,
      |y j| <= |osiiArgumentGeneratorPoint i left theta right j|) :
    Nonempty
      (RawGeneratorCoordinatewiseShrinkData
        rank sourceDepth i y) := by
  let left' : Fin i.n -> Real :=
    osiiMixedArgumentOfTail i.hn
      (fun a => -y (i.leftGlobalIndex a))
  let right' : Fin i.m -> Real :=
    osiiMixedArgumentOfTail i.hm
      (fun b => y (i.rightGlobalIndex b))
  have hleft'_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.n sourceDepth left' := by
    apply OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedHyperrectangle
      hleft_rank left'
    apply abs_osiiMixedArgumentOfTail_le i.hn
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
        i.hn hleft_rank)
    intro a
    simpa [left'] using hy (i.leftGlobalIndex a)
  have hleft'_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.n sourceDepth left' := by
    apply OSIIRawStrictGeneratedLogarithmicArgument.mixedHyperrectangle
      hleft_raw left'
    apply abs_osiiMixedArgumentOfTail_le i.hn
      (OSIIRawStrictGeneratedLogarithmicArgument.mixed_head_eq_zero
        i.hn hleft_raw)
    intro a
    simpa [left'] using hy (i.leftGlobalIndex a)
  have hright'_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.m sourceDepth right' := by
    apply OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedHyperrectangle
      hright_rank right'
    apply abs_osiiMixedArgumentOfTail_le i.hm
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
        i.hm hright_rank)
    intro b
    simpa [right'] using hy (i.rightGlobalIndex b)
  have hright'_raw : OSIIRawStrictGeneratedLogarithmicArgument
      .mixed i.m sourceDepth right' := by
    apply OSIIRawStrictGeneratedLogarithmicArgument.mixedHyperrectangle
      hright_raw right'
    apply abs_osiiMixedArgumentOfTail_le i.hm
      (OSIIRawStrictGeneratedLogarithmicArgument.mixed_head_eq_zero
        i.hm hright_raw)
    intro b
    simpa [right'] using hy (i.rightGlobalIndex b)
  have htheta' : |y i.bridgeGlobalIndex| < Real.pi / 2 := by
    have hbridge : |y i.bridgeGlobalIndex| <= |theta| := by
      simpa only [osiiArgumentGeneratorPoint_bridge] using
        hy i.bridgeGlobalIndex
    exact hbridge.trans_lt htheta
  exact ⟨{
    centered := {
      left := left'
      left_rank := hleft'_rank
      theta := y i.bridgeGlobalIndex
      angle_bound := htheta'
      right := right'
      right_rank := hright'_rank
      point_eq := osiiArgumentGeneratorPoint_reconstruct i y }
    left_raw := hleft'_raw
    right_raw := hright'_raw }⟩

namespace TargetHubRadialSlackAnchorData

end TargetHubRadialSlackAnchorData

/-- A named generator successor seed whose two predecessor mixed arguments
are certified simultaneously in the retained analytic rank and in the raw
outer-depth recurrence. -/
structure RawGeneratorRankSuccessorSeedData
    (rank k depth : Nat)
    (x : Fin k -> Real) where
  generator : GeneratorIndex k
  left : Fin generator.n -> Real
  left_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
    rank .mixed generator.n depth left
  left_raw : OSIIRawStrictGeneratedLogarithmicArgument
    .mixed generator.n depth left
  theta : Real
  theta_bound : |theta| < Real.pi / 2
  right : Fin generator.m -> Real
  right_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
    rank .mixed generator.m depth right
  right_raw : OSIIRawStrictGeneratedLogarithmicArgument
    .mixed generator.m depth right
  point_eq : osiiArgumentGeneratorPoint generator left theta right = x

namespace RawGeneratorRankSuccessorSeedData

/-- Forget the raw fields and retain the existing rank-successor predicate. -/
def toIsGeneratorRankSuccessorSeed
    {rank k depth : Nat}
    {x : Fin k -> Real}
    (H : RawGeneratorRankSuccessorSeedData rank k depth x) :
    IsGeneratorRankSuccessorSeed rank k (depth + 1) x :=
  ⟨H.generator, depth, H.left, H.theta, H.right, rfl,
    H.left_rank, H.right_rank, H.theta_bound, H.point_eq⟩

end RawGeneratorRankSuccessorSeedData

namespace RawGeneratorFlatCoefficientRadialRootedChartData

end RawGeneratorFlatCoefficientRadialRootedChartData

end OSIIChapterV
end OSReconstruction
