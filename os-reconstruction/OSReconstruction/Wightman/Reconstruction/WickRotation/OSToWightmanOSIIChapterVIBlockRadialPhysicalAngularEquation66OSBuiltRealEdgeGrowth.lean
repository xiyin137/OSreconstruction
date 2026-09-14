/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltPhysicalSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction











noncomputable section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction

open OSIIStep4FullSchwartzAngularContinuationData

/-- Total extension of the OS-built mixed-spatial density away from the
strict-positive real-time region.  Only the positive-time restriction enters
the VI.1 contract. -/
noncomputable def osiiEquation66OSBuiltMixedSpatialDensityTotal
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : Nat) [NeZero k]
    (tau : Fin k → Real)
    (x : Fin (k * d) → Real) : Complex :=
  if htau : tau ∈ section43TimeStrictPositiveRegion k then
    osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau htau x
  else
    0

namespace OSIIChapterV

/-- Canonical compact positive-real edges and the quantitative OS-built
density give the exact non-circular VI.1 density package for an exhausted
Chapter V ladder. -/
noncomputable def
    HasCanonicalReducedCompactStageEdges.toOSBuiltRealEdgeDensityGrowthData
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (L : OSIITimeContinuationLadder d k)
    (stageIndex : Nat)
    (H : HasCanonicalReducedCompactStageEdges OS (L.stage stageIndex))
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc) :
    OSIITimeContinuationLadderRealEdgeDensityGrowthData L := by
  let C0 : Real :=
    equation66E0PolynomialConstant G * 16 ^ (2 * G.scaleDegree)
  have hC0 : 0 ≤ C0 := by
    exact mul_nonneg (equation66E0PolynomialConstant_nonneg G)
      (pow_nonneg (by norm_num) _)
  refine
    { arity_pos := Nat.pos_of_ne_zero (NeZero.ne k)
      density := osiiEquation66OSBuiltMixedSpatialDensityTotal d OS lgc k
      density_continuous := ?_
      represents := ?_
      constant := C0 + 1
      timeDegree := G.scaleDegree + G.growthDegree
      boundaryDegree := 2 * G.scaleDegree
      spatialDegree := G.scaleDegree + G.growthDegree
      constant_pos := by linarith
      pointwise_bound := ?_ }
  · intro tau htau
    have hdensity :
        osiiEquation66OSBuiltMixedSpatialDensityTotal d OS lgc k tau =
          osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau htau := by
      funext x
      simp [osiiEquation66OSBuiltMixedSpatialDensityTotal, htau]
    rw [hdensity]
    exact continuous_osiiEquation66OSBuiltMixedSpatialDensity
      d OS lgc tau htau
  · intro tau htau chi
    obtain ⟨D⟩ := H {tau} isCompact_singleton (by
      intro sigma hsigma
      simpa only [Set.mem_singleton_iff] using hsigma ▸ htau)
    have htauD : tau ∈ D.realRegion :=
      D.compactCarrier_subset (Set.mem_singleton tau)
    have hfull := congrArg
      (fun R : OSIISpatialDistribution d k ↦ R chi)
      (L.fullDistribution_eqOn_stage stageIndex
        (D.edge.stageEdge tau htauD).1)
    calc
      L.fullDistribution (osiiPositiveRealTimeEmbed tau) chi =
          (L.stage stageIndex).distribution
            (osiiPositiveRealTimeEmbed tau) chi := hfull
      _ = ∫ x : Fin (k * d) → Real,
            osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau
                (D.realRegion_subset_strictPositive htauD) x *
              section43SpatialFlatSchwartzCLE d k chi x :=
        osiiEquation66OSBuiltMixedSpatialDensity_stageDistribution_eq_all
          lgc G D tau htauD chi
      _ = ∫ x : Fin (k * d) → Real,
            osiiEquation66OSBuiltMixedSpatialDensityTotal
                d OS lgc k tau x *
              section43SpatialFlatSchwartzCLE d k chi x := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [osiiEquation66OSBuiltMixedSpatialDensityTotal, dif_pos htau]
  · intro tau htau x
    let timeFactor : Real :=
      (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^
        (G.scaleDegree + G.growthDegree)
    let boundaryFactor : Real :=
      (1 + (osiiTimeBoundaryDistance k
        (osiiPositiveRealTimeEmbed tau))⁻¹) ^
        (2 * G.scaleDegree)
    let spatialFactor : Real :=
      (1 + ‖x‖) ^ (G.scaleDegree + G.growthDegree)
    have hzeta :
        osiiPositiveRealTimeEmbed tau ∈ osiiTimeRightHalfPlane k :=
      (osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau
    have hdist : 0 < osiiTimeBoundaryDistance k
        (osiiPositiveRealTimeEmbed tau) :=
      osiiTimeBoundaryDistance_pos
        (Nat.pos_of_ne_zero (NeZero.ne k)) hzeta
    have htime : 0 ≤ timeFactor := by
      dsimp [timeFactor]
      positivity
    have hboundary : 0 ≤ boundaryFactor := by
      dsimp [boundaryFactor]
      exact pow_nonneg
        (add_nonneg zero_le_one (inv_nonneg.mpr hdist.le)) _
    have hspatial : 0 ≤ spatialFactor := by
      dsimp [spatialFactor]
      positivity
    have hraw := osiiEquation66OSBuiltMixedSpatialDensity_norm_le
      d OS lgc G tau htau x
    calc
      ‖osiiEquation66OSBuiltMixedSpatialDensityTotal
          d OS lgc k tau x‖ =
          ‖osiiEquation66OSBuiltMixedSpatialDensity
            d OS lgc tau htau x‖ := by
        simp [osiiEquation66OSBuiltMixedSpatialDensityTotal, htau]
      _ ≤ C0 * (timeFactor * boundaryFactor * spatialFactor) := by
        simpa [C0, timeFactor, boundaryFactor, spatialFactor, mul_assoc]
          using hraw
      _ ≤ (C0 + 1) *
          (timeFactor * boundaryFactor * spatialFactor) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (mul_nonneg (mul_nonneg htime hboundary) hspatial)
      _ = (C0 + 1) * timeFactor * boundaryFactor * spatialFactor := by
        ring

/-- The depth-zero strict-generated stage retains all canonical compact
positive-real edges, stated independently of the selected-BVT route. -/
theorem
    InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder_stage_zero_hasCanonicalEdges_osBuilt
    {d : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    HasCanonicalReducedCompactStageEdges OS
      ((D.toStrictGeneratedTimeContinuationLadder lgc arity).stage 0) := by
  change HasCanonicalReducedCompactStageEdges OS
    (((D.toStrictGeneratedScalarDepthZeroPointedData.depthInduction lgc 0
      ).pointed.stageLevel.stage arity))
  simpa using
    D.toStrictGeneratedScalarDepthZeroPointedData.pointed.canonicalEdges arity

namespace InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

end InitialGeneratedLogarithmicStageLevelData
end OSIIChapterV
end OSReconstruction

