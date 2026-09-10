/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarSeedCharts
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarPhysicalCharts
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeRankedSafeShift
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621EndpointProbeRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetApproxIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedTwoScaleFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedSourceAnchorCutoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRadialFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeneratorCommonRadialVitaliCover
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedScalarPhysicalSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedL1CoefficientMZ
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicTargetPhysicalPointedSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageExtensionConvexCoreAtlas















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

/-- Coordinatewise shrinking data that retains a fixed generator split.
The ordinary constructor predicate hides this provenance existentially;
equation-`(6.29)` needs the same split on the quantitative common-radial
chart and on the qualitative target extension. -/
structure GeneratorCoordinatewiseShrinkData
    {k : Nat}
    (rank sourceDepth : Nat)
    (i : GeneratorIndex k)
    (y : Fin k -> Real) where
  left : Fin i.n -> Real
  left_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
    rank .mixed i.n sourceDepth left
  theta : Real
  angle_bound : |theta| < Real.pi / 2
  right : Fin i.m -> Real
  right_rank : OSIIStrictGeneratedLogarithmicArgumentAtRank
    rank .mixed i.m sourceDepth right
  point_eq : osiiArgumentGeneratorPoint i left theta right = y

/-- A coordinatewise shrink of one named generator presentation admits a
new presentation with exactly the same split index. -/
theorem nonempty_generatorCoordinatewiseShrinkData
    {k rank sourceDepth : Nat}
    (i : GeneratorIndex k)
    (left : Fin i.n -> Real)
    (hleft : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.n sourceDepth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.m sourceDepth right)
    (y : Fin k -> Real)
    (hy : forall j,
      |y j| <= |osiiArgumentGeneratorPoint i left theta right j|) :
    Nonempty (GeneratorCoordinatewiseShrinkData rank sourceDepth i y) := by
  let left' : Fin i.n -> Real :=
    osiiMixedArgumentOfTail i.hn
      (fun a => -y (i.leftGlobalIndex a))
  let right' : Fin i.m -> Real :=
    osiiMixedArgumentOfTail i.hm
      (fun b => y (i.rightGlobalIndex b))
  have hleft' : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.n sourceDepth left' := by
    apply OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedHyperrectangle
      hleft left'
    apply abs_osiiMixedArgumentOfTail_le i.hn
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
        i.hn hleft)
    intro a
    simpa [left'] using hy (i.leftGlobalIndex a)
  have hright' : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.m sourceDepth right' := by
    apply OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedHyperrectangle
      hright right'
    apply abs_osiiMixedArgumentOfTail_le i.hm
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
        i.hm hright)
    intro b
    simpa [right'] using hy (i.rightGlobalIndex b)
  have htheta' : |y i.bridgeGlobalIndex| < Real.pi / 2 := by
    have hbridge : |y i.bridgeGlobalIndex| <= |theta| := by
      simpa only [osiiArgumentGeneratorPoint_bridge] using
        hy i.bridgeGlobalIndex
    exact hbridge.trans_lt htheta
  exact ⟨{
    left := left'
    left_rank := hleft'
    theta := y i.bridgeGlobalIndex
    angle_bound := htheta'
    right := right'
    right_rank := hright'
    point_eq := osiiArgumentGeneratorPoint_reconstruct i y }⟩

/-- A target-and-hub anchor that spends only half of the radial slack left by
a flat-window contraction.  Besides the ordinary target/hub inequalities it
retains the exact bound needed to subtract the anchor without leaving the
uncontracted principal-argument box. -/
structure TargetHubRadialSlackAnchorData
    {k : Nat}
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k)
    (rho : Real) where
  anchorData : TargetHubHalfAnchorData hub z
  anchor_eq : forall j,
    anchorData.anchor j =
      ((1 - rho) / 2) * min (hub j) (z j).re
  anchor_le_radialSlack : forall j,
    anchorData.anchor j <= (1 - rho) * (z j).re

/-- The scaled coordinatewise minimum gives a canonical radial-slack anchor
for every subunit flat-window radius. -/
def targetHubRadialSlackAnchorData
    {k : Nat}
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ osiiTimeRightHalfPlane k)
    (rho : Real)
    (hrho_nonneg : 0 <= rho)
    (hrho_lt_one : rho < 1) :
    TargetHubRadialSlackAnchorData hub z rho := by
  let scale : Real := (1 - rho) / 2
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    linarith
  have hscale_half : scale <= 1 / 2 := by
    dsimp [scale]
    linarith
  have hscale_slack : scale <= 1 - rho := by
    dsimp [scale]
    linarith
  let anchor : Fin k -> Real := fun j =>
    scale * min (hub j) (z j).re
  let C : TargetHubHalfAnchorData hub z := {
    anchor := anchor
    anchor_positive := by
      intro j
      exact mul_pos hscale_pos (lt_min (hhub j) (hz j))
    anchor_le_half_hub := by
      intro j
      calc
        anchor j <= scale * hub j :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hscale_pos.le
        _ <= (1 / 2 : Real) * hub j :=
          mul_le_mul_of_nonneg_right hscale_half (hhub j).le
        _ = hub j / 2 := by ring
    anchor_le_half_target := by
      intro j
      calc
        anchor j <= scale * (z j).re :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hscale_pos.le
        _ <= (1 / 2 : Real) * (z j).re :=
          mul_le_mul_of_nonneg_right hscale_half (hz j).le
        _ = (z j).re / 2 := by ring
    anchor_lt_hub := by
      intro j
      have h := show anchor j <= hub j / 2 from by
        calc
          anchor j <= scale * hub j :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hscale_pos.le
          _ <= (1 / 2 : Real) * hub j :=
            mul_le_mul_of_nonneg_right hscale_half (hhub j).le
          _ = hub j / 2 := by ring
      linarith [hhub j]
    anchor_lt_target := by
      intro j
      have h := show anchor j <= (z j).re / 2 from by
        calc
          anchor j <= scale * (z j).re :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hscale_pos.le
          _ <= (1 / 2 : Real) * (z j).re :=
            mul_le_mul_of_nonneg_right hscale_half (hz j).le
          _ = (z j).re / 2 := by ring
      linarith [hz j] }
  exact {
    anchorData := C
    anchor_eq := by
      intro j
      rfl
    anchor_le_radialSlack := by
      intro j
      calc
        C.anchor j <= scale * (z j).re :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hscale_pos.le
        _ <= (1 - rho) * (z j).re :=
          mul_le_mul_of_nonneg_right hscale_slack (hz j).le }

namespace TargetHubRadialSlackAnchorData

end TargetHubRadialSlackAnchorData

/-- One generator flat-window point with both coordinate systems needed by
the rank step: the absolute target chart used by qualitative successor
gluing and the same-split centered chart used by equation-`(6.29)`. -/
structure GeneratorFlatCoefficientRadialRootedChartData
    {k n depth rank : Nat} [NeZero k] [NeZero n]
    (hub : Fin k -> Real)
    (seed : Fin n -> Fin k -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    {rho : Real}
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho : rho < 1)
    (hgenerator : IsGeneratorRankSuccessorSeed
      rank k (depth + 1) (seed active)) where
  chart : RootedStrictGeneratedTargetHubChartAtRank k depth rank
  target_eq : chart.target =
    osiiLogExp (osiiStrictScalarSeedCoefficientMap seed r)
  anchor : TargetHubRadialSlackAnchorData hub chart.target rho
  centered : GeneratorCoordinatewiseShrinkData rank depth chart.generator
    (osiiTimeArgumentVector
      (chart.target - osiiPositiveRealTimeEmbed anchor.anchorData.anchor))

namespace GeneratorFlatCoefficientRadialRootedChartData

/-- Every point of the physical hub-to-target segment, after the canonical
anchor recentering, retains a generator presentation with the original split
and source rank.  The parent scalar path is a successor-rank continuation,
but its two exact equation-`(6.21)` source blocks stay at the preceding rank.
-/
theorem nonempty_centeredSegmentCoordinatewiseShrinkData
    {k n depth rank : Nat} [NeZero k] [NeZero n]
    {hub : Fin k -> Real}
    {seed : Fin n -> Fin k -> Real}
    {r : Fin n -> Complex}
    {active : Fin n}
    {rho : Real}
    {hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0}
    {hrho : rho < 1}
    {hgenerator : IsGeneratorRankSuccessorSeed
      rank k (depth + 1) (seed active)}
    (G : GeneratorFlatCoefficientRadialRootedChartData
      hub seed r active hactive hrho hgenerator)
    (w : OSIITimeGapSpace k)
    (hw : w ∈ segment Real
      (osiiPositiveRealTimeEmbed hub) G.chart.target) :
    Nonempty (GeneratorCoordinatewiseShrinkData rank depth G.chart.generator
      (osiiTimeArgumentVector
        (w - osiiPositiveRealTimeEmbed G.anchor.anchorData.anchor))) := by
  rw [segment_eq_image_lineMap] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  apply nonempty_generatorCoordinatewiseShrinkData
    G.chart.generator G.centered.left G.centered.left_rank
      G.centered.theta G.centered.angle_bound
      G.centered.right G.centered.right_rank
  intro j
  rw [G.centered.point_eq]
  let target := G.chart.target j - G.anchor.anchorData.anchor j
  let residual :=
    (1 - s) * (hub j - G.anchor.anchorData.anchor j)
  have htarget : 0 < target.re := by
    simpa [target, osiiPositiveRealTimeEmbed] using
      G.anchor.anchorData.centeredTarget_mem_rightHalfPlane j
  have hresidual : 0 <= residual := by
    dsimp [residual]
    exact mul_nonneg (sub_nonneg.mpr hs.2)
      (sub_nonneg.mpr (G.anchor.anchorData.anchor_lt_hub j).le)
  have hpoint :
      AffineMap.lineMap (k := Real)
            (osiiPositiveRealTimeEmbed hub) G.chart.target s j -
          osiiPositiveRealTimeEmbed G.anchor.anchorData.anchor j =
        (s : Complex) * target + (residual : Complex) := by
    simp [AffineMap.lineMap_apply_module, osiiPositiveRealTimeEmbed,
      target, residual]
    ring
  change
    |Complex.arg
        (AffineMap.lineMap (k := Real)
              (osiiPositiveRealTimeEmbed hub) G.chart.target s j -
            osiiPositiveRealTimeEmbed G.anchor.anchorData.anchor j)| <=
      |Complex.arg
        (G.chart.target j -
          osiiPositiveRealTimeEmbed G.anchor.anchorData.anchor j)|
  rw [hpoint]
  simpa [target, osiiPositiveRealTimeEmbed] using
    abs_arg_real_smul_add_ofReal_le htarget hs.1 hresidual

/-- The same-rank generator chart attached to one centered physical segment
point. -/
noncomputable def centeredSegmentChart
    {k n depth rank : Nat} [NeZero k] [NeZero n]
    {hub : Fin k -> Real}
    {seed : Fin n -> Fin k -> Real}
    {r : Fin n -> Complex}
    {active : Fin n}
    {rho : Real}
    {hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0}
    {hrho : rho < 1}
    {hgenerator : IsGeneratorRankSuccessorSeed
      rank k (depth + 1) (seed active)}
    (G : GeneratorFlatCoefficientRadialRootedChartData
      hub seed r active hactive hrho hgenerator)
    (w : OSIITimeGapSpace k)
    (hw : w ∈ segment Real
      (osiiPositiveRealTimeEmbed hub) G.chart.target) :
    RootedStrictGeneratedTargetHubChartAtRank k depth rank := by
  let C := Classical.choice
    (G.nonempty_centeredSegmentCoordinatewiseShrinkData w hw)
  exact
    { generator := G.chart.generator
      left := C.left
      left_rank := C.left_rank
      theta := C.theta
      angle_bound := C.angle_bound
      right := C.right
      right_rank := C.right_rank
      target := w - osiiPositiveRealTimeEmbed G.anchor.anchorData.anchor
      target_mem := ⟨by
        rw [segment_eq_image_lineMap] at hw
        obtain ⟨s, hs, rfl⟩ := hw
        intro j
        have hhub := G.anchor.anchorData.anchor_lt_hub j
        have htarget := G.anchor.anchorData.anchor_lt_target j
        simp only [AffineMap.lineMap_apply_module,
          osiiPositiveRealTimeEmbed, Pi.sub_apply, Complex.sub_re,
          Complex.ofReal_re, Pi.add_apply, Pi.smul_apply,
          Complex.real_smul, Complex.add_re, Complex.mul_re,
          Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
        rw [show
          (1 - s) * hub j + s * (G.chart.target j).re -
              G.anchor.anchorData.anchor j =
            (1 - s) * (hub j - G.anchor.anchorData.anchor j) +
              s * ((G.chart.target j).re -
                G.anchor.anchorData.anchor j) by ring]
        let lower := min
          (hub j - G.anchor.anchorData.anchor j)
          ((G.chart.target j).re - G.anchor.anchorData.anchor j)
        have hlower : 0 < lower := by
          exact lt_min (sub_pos.mpr hhub) (sub_pos.mpr htarget)
        have hconvex : lower <=
            (1 - s) * (hub j - G.anchor.anchorData.anchor j) +
              s * ((G.chart.target j).re -
                G.anchor.anchorData.anchor j) := by
          calc
            lower = (1 - s) * lower + s * lower := by ring
            _ <= (1 - s) * (hub j - G.anchor.anchorData.anchor j) +
                s * ((G.chart.target j).re -
                  G.anchor.anchorData.anchor j) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (min_le_left _ _)
                  (sub_nonneg.mpr hs.2))
                (mul_le_mul_of_nonneg_left (min_le_right _ _) hs.1)
        exact hlower.trans_le hconvex,
        Set.mem_singleton_iff.mpr C.point_eq.symm⟩ }

@[simp] theorem centeredSegmentChart_generator
    {k n depth rank : Nat} [NeZero k] [NeZero n]
    {hub : Fin k -> Real}
    {seed : Fin n -> Fin k -> Real}
    {r : Fin n -> Complex}
    {active : Fin n}
    {rho : Real}
    {hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0}
    {hrho : rho < 1}
    {hgenerator : IsGeneratorRankSuccessorSeed
      rank k (depth + 1) (seed active)}
    (G : GeneratorFlatCoefficientRadialRootedChartData
      hub seed r active hactive hrho hgenerator)
    (w : OSIITimeGapSpace k)
    (hw : w ∈ segment Real
      (osiiPositiveRealTimeEmbed hub) G.chart.target) :
    (G.centeredSegmentChart w hw).generator = G.chart.generator := rfl

@[simp] theorem centeredSegmentChart_target
    {k n depth rank : Nat} [NeZero k] [NeZero n]
    {hub : Fin k -> Real}
    {seed : Fin n -> Fin k -> Real}
    {r : Fin n -> Complex}
    {active : Fin n}
    {rho : Real}
    {hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0}
    {hrho : rho < 1}
    {hgenerator : IsGeneratorRankSuccessorSeed
      rank k (depth + 1) (seed active)}
    (G : GeneratorFlatCoefficientRadialRootedChartData
      hub seed r active hactive hrho hgenerator)
    (w : OSIITimeGapSpace k)
    (hw : w ∈ segment Real
      (osiiPositiveRealTimeEmbed hub) G.chart.target) :
    (G.centeredSegmentChart w hw).target =
      w - osiiPositiveRealTimeEmbed G.anchor.anchorData.anchor := rfl

end GeneratorFlatCoefficientRadialRootedChartData

namespace GeneratorFlatCoefficientRadialRootedChartData

namespace RadialSlackPointedDirectExtensionData

end RadialSlackPointedDirectExtensionData

namespace RadialSlackMarginPointedDirectExtensionData

end RadialSlackMarginPointedDirectExtensionData

end GeneratorFlatCoefficientRadialRootedChartData

namespace ZeroPointedAmbientChartData

/-- A zero-pointed chart agrees at its target with the logarithmic pullback
of its physical predecessor whenever that predecessor contains the complete
zero-to-target segment.

The proof thickens the compact segment inside the open physical pullback,
uses that thickening as a second zero-pointed convex chart, and invokes chart
compatibility at the common target. -/
theorem distribution_target_eq_logarithmicPullback_of_segment_subset
    {d k : Nat} [NeZero d]
    {physical : OSIITimeContinuationStage d k}
    {target : Fin k -> Complex}
    (Q : ZeroPointedAmbientChartData physical target)
    (hsegment : segment Real 0 target ⊆
      (logarithmicPullbackStage physical).carrier) :
    Q.stage.distribution target =
      physical.distribution (osiiLogExp target) := by
  have hcompact : IsCompact (segment Real 0 target) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨eps, heps, hthick⟩ :=
    hcompact.exists_thickening_subset_open
      (logarithmicPullbackStage physical).carrier_open hsegment
  let domain := Metric.thickening eps (segment Real 0 target)
  let C : ZeroPointedAmbientChartData physical target :=
    ZeroPointedAmbientChartData.ofLogarithmicRestriction
      domain Metric.isOpen_thickening
      ((convex_segment (0 : Fin k -> Complex) target).thickening eps)
      (Metric.self_subset_thickening heps _
        (left_mem_segment Real 0 target))
      (Metric.self_subset_thickening heps _
        (right_mem_segment Real 0 target))
      hthick
  have hcompat := ZeroPointedAmbientChartData.compatible Q C
    ⟨Q.target_mem, C.target_mem⟩
  simpa [C, domain, ZeroPointedAmbientChartData.ofLogarithmicRestriction]
    using hcompat

end ZeroPointedAmbientChartData

namespace WeightedL1ZeroPointedAmbientChartData

/-- Evaluate a quantitative zero-pointed chart at a target whose radial
segment is already contained in the physical predecessor. -/
def targetBoundInPhysical
    {d k p beta depth : Nat} [NeZero d]
    {physical : OSIITimeContinuationStage d k}
    {target : Fin k -> Complex}
    {alpha : Real}
    (Q : WeightedL1ZeroPointedAmbientChartData
      physical target p alpha beta depth)
    (hsegment : segment Real 0 target ⊆
      (logarithmicPullbackStage physical).carrier) :
    OSIIEquation621WeightedL1PointBoundData
      (physical.distribution (osiiLogExp target))
      p alpha beta depth :=
  (Q.weightedL1.pointBound target Q.chart.target_mem).congr
    (Q.chart.distribution_target_eq_logarithmicPullback_of_segment_subset
      hsegment).symm

end WeightedL1ZeroPointedAmbientChartData

namespace WeightedL1PointStageHandoffData

end WeightedL1PointStageHandoffData

namespace WeightedL1RankSuccessorSeedFlatPointProducerData

end WeightedL1RankSuccessorSeedFlatPointProducerData

namespace WeightedL1RankSuccessorSeedFlatNewBranchPointProducerData

end WeightedL1RankSuccessorSeedFlatNewBranchPointProducerData

namespace WeightedL1RankSuccessorSeedFlatChartProducerData

end WeightedL1RankSuccessorSeedFlatChartProducerData

namespace WeightedL1RankSuccessorSeedFlatHandoffProducerData

end WeightedL1RankSuccessorSeedFlatHandoffProducerData

namespace RankSuccessorScalarSeedFlatWeightedL1BoundData

end RankSuccessorScalarSeedFlatWeightedL1BoundData

end OSIIChapterV
end OSReconstruction
