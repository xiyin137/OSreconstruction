/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumTailPositiveRealEdge









noncomputable section

open Complex MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace PositiveHeadUniversalAnchoredAtlasData

variable {d q : ℕ} [NeZero d]
variable
  {I : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) → ℝ}
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}

/-- The centered vacuum-tail real germ translated back to absolute time
coordinates. -/
def vacuumTailAbsoluteRealRegion
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    Set (Fin (q + 1) → ℝ) :=
  {u | u + -anchor ∈ D.vacuumTailRealRegion C}

theorem vacuumTailAbsoluteRealRegion_open
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    IsOpen (D.vacuumTailAbsoluteRealRegion C) :=
  (D.vacuumTailRealRegion_open C).preimage
    (continuous_id.add continuous_const)

@[simp]
theorem anchor_mem_vacuumTailAbsoluteRealRegion
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    anchor ∈ D.vacuumTailAbsoluteRealRegion C := by
  simpa [vacuumTailAbsoluteRealRegion] using
    D.zero_mem_vacuumTailRealRegion C

/-- The absolute-coordinate real orbit of the vacuum-tail limit. -/
def vacuumTailAbsoluteOrbit
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A) :
    (Fin (q + 1) → ℝ) → OSIISpatialDistribution d (q + 1) :=
  fun u =>
    D.vacuumTailLimitSpatialDistribution
      (SCV.realToComplex (u + -anchor))

/-- The vacuum-tail continuation stage in absolute time coordinates. -/
noncomputable def vacuumTailAbsoluteStage
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A) :
    OSIITimeContinuationStage d (q + 1) :=
  D.vacuumTailLimitStage.recenter (-anchor)

/-- Translation preserves the centered positive real edge. -/
theorem vacuumTailAbsoluteStage_hasPositiveRealEdge
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    D.vacuumTailAbsoluteStage.HasPositiveRealEdge
      D.vacuumTailAbsoluteOrbit
      (D.vacuumTailAbsoluteRealRegion C) := by
  simpa [vacuumTailAbsoluteStage, vacuumTailAbsoluteOrbit,
    vacuumTailAbsoluteRealRegion] using
    D.vacuumTailLimitStage.recenter_hasPositiveRealEdge
      (fun u =>
        D.vacuumTailLimitSpatialDistribution (SCV.realToComplex u))
      (D.vacuumTailRealRegion C)
      (-anchor)
      (D.vacuumTailLimitStage_hasPositiveRealEdge C)

/-- In absolute coordinates, the vacuum-tail orbit represents the ordinary
ordered transport of the retained current. -/
theorem vacuumTailAbsoluteOrbit_represents
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    OSIITimeSpatialRepresentsDistributionOn
      (orderedTransportDistribution C.current)
      D.vacuumTailAbsoluteOrbit
      (D.vacuumTailAbsoluteRealRegion C) := by
  intro χ φ hφ
  let ψ : SchwartzMap (Fin (q + 1) → ℝ) ℂ :=
    SCV.translateSchwartz anchor φ
  have hψ :
      SCV.SupportsInOpen
        (ψ : (Fin (q + 1) → ℝ) → ℂ)
        (D.vacuumTailRealRegion C) := by
    constructor
    · exact
        hasCompactSupport_translateSchwartz
          φ hφ.1 anchor
    · intro u hu
      have hu' :
          u ∈ tsupport
            ((SCV.translateSchwartz anchor φ :
              SchwartzMap (Fin (q + 1) → ℝ) ℂ) :
                (Fin (q + 1) → ℝ) → ℂ) := by
        simpa [ψ] using hu
      rw [tsupport_translateSchwartz_eq_preimage] at hu'
      have habsolute := hφ.2 hu'
      simpa [vacuumTailAbsoluteRealRegion, add_assoc] using habsolute
  have hcentered :=
    D.vacuumTailLimitSpatialDistribution_represents C χ ψ hψ
  calc
    ((orderedTransportDistribution C.current).comp
        (section43OrderedPullbackTimeSpatialTensorCLM
          d (q + 1) χ)) φ =
        ((anchoredOrderedTransportDistribution C.current anchor).comp
          (section43OrderedPullbackTimeSpatialTensorCLM
            d (q + 1) χ)) ψ := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [orderedTransportDistribution_orderedPullbackTimeSpatialTensor,
        anchoredOrderedTransportDistribution_orderedPullbackTimeSpatialTensor]
      apply congrArg C.current
      ext x
      simp [ψ, SCV.translateSchwartz_apply]
    _ = ∫ u : Fin (q + 1) → ℝ,
          D.vacuumTailLimitSpatialDistribution
              (SCV.realToComplex u) χ *
            ψ u :=
      hcentered
    _ = ∫ u : Fin (q + 1) → ℝ,
          D.vacuumTailAbsoluteOrbit u χ * φ u := by
      let g : (Fin (q + 1) → ℝ) → ℂ :=
        fun u =>
          D.vacuumTailLimitSpatialDistribution
              (SCV.realToComplex u) χ *
            ψ u
      have hshift :
          (fun u : Fin (q + 1) → ℝ =>
            D.vacuumTailAbsoluteOrbit u χ * φ u) =
            fun u => g (u + -anchor) := by
        funext u
        simp [g, ψ, vacuumTailAbsoluteOrbit,
          SCV.translateSchwartz_apply, add_assoc]
      rw [show
        (fun u : Fin (q + 1) → ℝ =>
          D.vacuumTailLimitSpatialDistribution
              (SCV.realToComplex u) χ *
            ψ u) = g by rfl]
      rw [hshift]
      exact
        (MeasureTheory.integral_add_right_eq_self g (-anchor)).symm

end PositiveHeadUniversalAnchoredAtlasData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
