/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductSpatialApproxIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedSelfPairProbeIdentification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedRawKernelRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedBounds












noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Two independently shifted copies of the natural-number diagonal remain
cofinal in the product order. -/
theorem tendsto_natTailDiagonal_atTop
    (leftTail rightTail : Nat) :
    Tendsto (fun N : Nat => (N + leftTail, N + rightTail)) atTop atTop := by
  rw [tendsto_atTop]
  intro p
  filter_upwards [eventually_ge_atTop (max p.1 p.2)] with N hN
  exact
    ⟨(le_trans (le_max_left _ _) hN).trans (Nat.le_add_right _ _),
      (le_trans (le_max_right _ _) hN).trans (Nat.le_add_right _ _)⟩

/-- The two-packet reflected moving scalar converges, along any synchronized
cofinal tails, to the represented lower-stage value at the physical reflected
moving-slice point. -/
theorem
    tendsto_reflectedMovingSliceScalar_tailDiagonal_to_distribution_of_cutoff_eq_one
    {d r : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (r + (r + 1)))
    (rho : SchwartzMap (Fin (r + (r + 1)) -> Real) Complex)
    (I J : Section43ProductTimeApproximateIdentity (r + 1))
    (leftCenter rightCenter : Fin (r + 1) -> Real)
    (hleftCenter : leftCenter ∈ section43TimeStrictPositiveRegion (r + 1))
    (hrightCenter : rightCenter ∈ section43TimeStrictPositiveRegion (r + 1))
    (left right : SchwartzMap
      (Section43SpatialSpace d (r + 1)) Complex)
    (w : Fin (r + r) -> Complex)
    (hw : w ∈ reflectedMovingSliceCarrier A rho)
    (physicalTime : Fin (r + (r + 1)) -> Real)
    (htime : osiiMixedBlockGlobalReducedTime r
      (Fin.append leftCenter rightCenter) = physicalTime)
    (hrho : rho physicalTime = 1)
    (leftTail rightTail : Nat) :
    Tendsto
      (fun N =>
        reflectedMovingSliceScalar A rho
          (diffVarReduction d (r + (r + 1))
            (mixedReflectedChronologicalSource
              (I.translatedPositiveTimeSpatialSource
                leftCenter hleftCenter left (N + leftTail)).1
              (J.translatedPositiveTimeSpatialSource
                rightCenter hrightCenter right (N + rightTail)).1))
          w)
      atTop
      (nhds (A.distribution
        (equation621ReflectedMovingSlicePoint w physicalTime)
        (osiiMixedSpatialHeadMarginal left right))) := by
  have hlimit :=
    tendsto_reflectedMovingSliceScalar_translatedApproximateIdentities
      A rho I J leftCenter rightCenter hleftCenter hrightCenter
      left right w hw
  have hdiagonal := hlimit.comp
    (tendsto_natTailDiagonal_atTop leftTail rightTail)
  rw [osiiReflectedMixedMovingKernel_centers_eq_distribution_of_cutoff_eq_one
    A rho left right w leftCenter rightCenter physicalTime htime hrho]
    at hdiagonal
  exact hdiagonal

namespace ReflectedGramSpatialSourceData

variable {d q : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}

/-- Source-indexed reflected Gram scalars converge along synchronized packet
tails to the represented source-stage distribution.  The scalar-to-moving-
slice identity and the exact source realization are discharged internally. -/
theorem tendsto_cauchyScalar_tailDiagonal_to_distribution
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    (I J : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (leftCenter rightCenter : Fin ((q + 1) + 1) -> Real)
    (hleftCenter : leftCenter ∈
      section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hrightCenter : rightCenter ∈
      section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hleftSource : forall scale left,
      UniformCompactTimeSource.source (D.sourceCLM scale left) =
        I.translatedPositiveTimeSpatialSource
          leftCenter hleftCenter left scale)
    (hrightSource : forall scale right,
      UniformCompactTimeSource.source (D.sourceCLM scale right) =
        J.translatedPositiveTimeSpatialSource
          rightCenter hrightCenter right scale)
    (left right : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (w : Fin ((q + 1) + (q + 1)) -> Complex)
    (hw : w ∈ reflectedMovingSliceCarrier
      D.reflectedGram.atlas.sourceStage.stage
      D.reflectedGram.atlas.sourceStage.germ.η)
    (physicalTime : Fin ((q + 1) + ((q + 1) + 1)) -> Real)
    (htime : osiiMixedBlockGlobalReducedTime (q + 1)
      (Fin.append leftCenter rightCenter) = physicalTime)
    (hrho : D.reflectedGram.atlas.sourceStage.germ.η physicalTime = 1)
    (leftTail rightTail : Nat) :
    Tendsto
      (fun N =>
        (D.reflectedGram.atlas.gram.cauchy
          (D.sourceCLM (N + leftTail) left)
          (D.sourceCLM (N + rightTail) right)).scalar w)
      atTop
      (nhds (D.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621ReflectedMovingSlicePoint w physicalTime)
        (osiiMixedSpatialHeadMarginal left right))) := by
  have hlimit :=
    tendsto_reflectedMovingSliceScalar_tailDiagonal_to_distribution_of_cutoff_eq_one
      D.reflectedGram.atlas.sourceStage.stage
      D.reflectedGram.atlas.sourceStage.germ.η
      I J leftCenter rightCenter hleftCenter hrightCenter
      left right w hw physicalTime htime hrho leftTail rightTail
  apply hlimit.congr'
  exact Filter.Eventually.of_forall fun N => by
    change
      reflectedMovingSliceScalar
          D.reflectedGram.atlas.sourceStage.stage
          D.reflectedGram.atlas.sourceStage.germ.η
          (diffVarReduction d ((q + 1) + ((q + 1) + 1))
            (mixedReflectedChronologicalSource
              (I.translatedPositiveTimeSpatialSource
                leftCenter hleftCenter left (N + leftTail))
              (J.translatedPositiveTimeSpatialSource
                rightCenter hrightCenter right (N + rightTail))))
          w =
        (D.reflectedGram.atlas.gram.cauchy
          (D.sourceCLM (N + leftTail) left)
          (D.sourceCLM (N + rightTail) right)).scalar w
    calc
      _ = reflectedMovingSliceScalar
          D.reflectedGram.atlas.sourceStage.stage
          D.reflectedGram.atlas.sourceStage.germ.η
          (D.sourceProductMovingSliceSource
            (N + leftTail) (N + rightTail) left right) w := by
        congr 2
        simp only [sourceProductChronologicalSource]
        rw [hleftSource, hrightSource]
      _ = _ :=
        (D.cauchy_scalar_eq_sourceProductMovingSliceScalar
          (N + leftTail) (N + rightTail) left right w).symm

/-- When both source tests are one coherent product probe, the reflected
Gram diagonal converges directly to the represented distribution tested
against the genuine marginal approximate identity. -/
theorem
    tendsto_cauchyScalar_tailDiagonal_to_distribution_marginalSpatialProbe
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
    (w : Fin ((q + 1) + (q + 1)) -> Complex)
    (hw : w ∈ reflectedMovingSliceCarrier
      D.reflectedGram.atlas.sourceStage.stage
      D.reflectedGram.atlas.sourceStage.germ.η)
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
              spatialCenter probeScale))).scalar w)
      atTop
      (nhds (D.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621ReflectedMovingSlicePoint w physicalTime)
        (spatialApprox.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
          (Section43ProductTimeApproximateIdentity.reflectedSelfPairMarginalSpatialPoint
            d (q + 1) spatialCenter) probeScale))) := by
  have hlimit := D.tendsto_cauchyScalar_tailDiagonal_to_distribution
    timeApprox timeApprox leftCenter rightCenter hleftCenter hrightCenter
    hsource hsourceRight
    (spatialApprox.toEquation621SpatialApproxIdentity.section43Probe
      spatialCenter probeScale)
    (spatialApprox.toEquation621SpatialApproxIdentity.section43Probe
      spatialCenter probeScale)
    w hw physicalTime htime hrho leftTail rightTail
  rw [spatialApprox.reflectedSelfPairMarginal_section43Probe_eq_mixedSpatialHeadMarginal]
  exact hlimit

end ReflectedGramSpatialSourceData
end OSIIChapterV
end OSReconstruction
