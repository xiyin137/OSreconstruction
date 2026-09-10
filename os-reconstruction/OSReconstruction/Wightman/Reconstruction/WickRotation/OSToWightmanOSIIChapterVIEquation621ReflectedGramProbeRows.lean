/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedDiagonalProbeLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniversalCompactCarrierAnchoredBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation

















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace ReflectedGramSpatialSourceData

variable {d q : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}

/-- The squared norm of an arbitrary source-linear anchored field is bounded
by the norm of its prescribed diagonal Gram scalar, with no extra constant.
-/
theorem norm_spatialFieldCLM_sq_le_norm_diagonalScalar
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    (scale : Nat)
    (test : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ D.reflectedGram.atlas.spatialLinearDomain) :
    ‖D.reflectedGram.atlas.spatialFieldCLM
        D.sourceCLM scale z hz test‖ ^ 2 <=
      ‖(D.reflectedGram.atlas.gram.cauchy
          (D.sourceCLM scale test)
          (D.sourceCLM scale test)).scalar
        (reflectedCauchyCenter z)‖ := by
  exact
    D.reflectedGram.atlas.norm_spatialFieldCLM_sq_le_of_scalar_diagonal_bound
      D.sourceCLM scale z hz test
      ‖(D.reflectedGram.atlas.gram.cauchy
          (D.sourceCLM scale test)
          (D.sourceCLM scale test)).scalar
        (reflectedCauchyCenter z)‖ le_rfl

/-- The diagonal scalar controlling the field norm converges to the actual
represented lower-stage distribution on the coherent marginal probe.  The
moving-slice membership of the reflected center is already part of the
source-linear field domain, so it is not an additional hypothesis. -/
theorem tendsto_diagonalScalar_tailDiagonal_to_distribution_marginalSpatialProbe
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    (timeApprox : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (leftCenter rightCenter : Fin ((q + 1) + 1) -> Real)
    (hleftCenter : leftCenter ∈
      section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hrightCenter : rightCenter ∈
      section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hsource : forall scale spatial,
      UniformCompactTimeSource.source (D.sourceCLM scale spatial) =
        timeApprox.translatedPositiveTimeSpatialSource
          leftCenter hleftCenter spatial scale)
    (hsourceRight : forall scale spatial,
      UniformCompactTimeSource.source (D.sourceCLM scale spatial) =
        timeApprox.translatedPositiveTimeSpatialSource
          rightCenter hrightCenter spatial scale)
    (spatialApprox : Section43ProductTimeApproximateIdentity
      (((q + 1) + 1) * d))
    (spatialCenter : Fin (((q + 1) + 1) * d) -> Real)
    (probeScale : Nat)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ D.reflectedGram.atlas.spatialLinearDomain)
    (physicalTime : Fin ((q + 1) + ((q + 1) + 1)) -> Real)
    (htime : osiiMixedBlockGlobalReducedTime (q + 1)
      (Fin.append leftCenter rightCenter) = physicalTime)
    (hrho : D.reflectedGram.atlas.sourceStage.germ.η physicalTime = 1)
    (leftTail rightTail : Nat) :
    Tendsto
      (fun N =>
        (D.reflectedGram.atlas.gram.cauchy
          (D.sourceCLM (N + leftTail)
            (spatialApprox.toEquation621SpatialApproxIdentity.section43Probe
              spatialCenter probeScale))
          (D.sourceCLM (N + rightTail)
            (spatialApprox.toEquation621SpatialApproxIdentity.section43Probe
              spatialCenter probeScale))).scalar
            (reflectedCauchyCenter z))
      atTop
      (nhds (D.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621ReflectedMovingSlicePoint
          (reflectedCauchyCenter z) physicalTime)
        (spatialApprox.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
          (Section43ProductTimeApproximateIdentity.reflectedSelfPairMarginalSpatialPoint
            d (q + 1) spatialCenter) probeScale))) := by
  exact
    D.tendsto_cauchyScalar_tailDiagonal_to_distribution_marginalSpatialProbe
      timeApprox leftCenter rightCenter hleftCenter hrightCenter
      hsource hsourceRight spatialApprox spatialCenter probeScale
      (reflectedCauchyCenter z) hz.2.2 physicalTime htime hrho
      leftTail rightTail

end ReflectedGramSpatialSourceData

end OSIIChapterV
end OSReconstruction
