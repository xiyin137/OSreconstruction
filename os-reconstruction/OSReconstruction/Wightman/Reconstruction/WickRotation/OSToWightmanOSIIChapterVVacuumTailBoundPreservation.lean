/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumTailField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniversalCompactCarrierAnchoredBounds












noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]

/-- The canonical Chapter V vacuum has norm one. -/
theorem osiiChapterVVacuumVector_norm
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ‖osiiChapterVVacuumVector OS‖ = 1 := by
  have hsq :=
    osiiPositiveTimeSingleVectorCLM_norm_sq
      OS 0 (osiiChapterVVacuumSource (d := d))
  rw [lgc.normalized_zero] at hsq
  have hvalue :
      (ZeroDiagonalSchwartz.ofClassical
        ((osiiChapterVVacuumSource (d := d)).1.osConjTensorProduct
          (osiiChapterVVacuumSource (d := d)).1)).1 0 = 1 := by
    have hzero : VanishesToInfiniteOrderOnCoincidence
        ((osiiChapterVVacuumSource (d := d)).1.osConjTensorProduct
          (osiiChapterVVacuumSource (d := d)).1) := by
      intro _k _x hx
      rcases hx with ⟨i, j, hij, _⟩
      omega
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes _ hzero]
    change
      (starRingEnd ℂ)
          (osiiChapterVVacuumUnit d
            (timeReflectionN d (splitFirst 0 0 0))) *
        osiiChapterVVacuumUnit d (splitLast 0 0 0) = 1
    simp
  have hsq' : ‖osiiChapterVVacuumVector OS‖ ^ 2 = 1 := by
    change ‖osiiChapterVVacuumVector OS‖ ^ 2 = _ at hsq
    rw [hvalue] at hsq
    exact hsq
  nlinarith [norm_nonneg (osiiChapterVVacuumVector OS)]

/-- A common squared-norm majorant at least one is preserved by vacuum
projection. -/
theorem norm_vacuum_inner_le_of_norm_sq_le
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (v : OSHilbertSpace OS)
    (B : Real)
    (hB : 1 <= B)
    (hv : ‖v‖ ^ 2 <= B) :
    ‖@inner Complex (OSHilbertSpace OS) _
      (osiiChapterVVacuumVector OS) v‖ <= B := by
  calc
    ‖@inner Complex (OSHilbertSpace OS) _
        (osiiChapterVVacuumVector OS) v‖ <=
        ‖osiiChapterVVacuumVector OS‖ * ‖v‖ :=
      norm_inner_le_norm _ _
    _ = ‖v‖ := by
      rw [osiiChapterVVacuumVector_norm OS lgc, one_mul]
    _ <= B := by
      nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - B)]

/-- Vacuum projection preserves the sharp square-root form of a squared-norm
bound.  This is the quantitative form needed when a reflected diagonal is
controlled by a higher-arity VI.2 majorant. -/
theorem norm_vacuum_inner_le_sqrt_of_norm_sq_le
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (v : OSHilbertSpace OS)
    (B : Real)
    (hv : ‖v‖ ^ 2 <= B) :
    ‖@inner Complex (OSHilbertSpace OS) _
      (osiiChapterVVacuumVector OS) v‖ <= Real.sqrt B := by
  calc
    ‖@inner Complex (OSHilbertSpace OS) _
        (osiiChapterVVacuumVector OS) v‖ <=
        ‖osiiChapterVVacuumVector OS‖ * ‖v‖ :=
      norm_inner_le_norm _ _
    _ = ‖v‖ := by
      rw [osiiChapterVVacuumVector_norm OS lgc, one_mul]
    _ = Real.sqrt (‖v‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]
    _ <= Real.sqrt B := Real.sqrt_le_sqrt hv

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace PositiveHeadUniversalAnchoredAtlasData

variable {q : Nat}
variable
  {I : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) -> Real}
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}

/-- A diagonal scalar estimate bounds each finite packet vacuum tail with
the same constant. -/
theorem norm_vacuumTailPacket_le_of_scalar_diagonal_bound
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : Nat)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ D.spatialLinearDomain)
    (test : SchwartzMap (Section43SpatialSpace d (q + 1)) Complex)
    (B : Real)
    (hB : 1 <= B)
    (hdiagonal :
      norm ((D.gram.cauchy
        (A.positiveHeadSpatialAnchoredSourceCLM scale
          (vacuumTailSpatialLiftCLM test))
        (A.positiveHeadSpatialAnchoredSourceCLM scale
          (vacuumTailSpatialLiftCLM test))).scalar
          (reflectedCauchyCenter z)) <= B) :
    norm (D.vacuumTailPacketSpatialDistribution scale z test) <= B := by
  rw [D.vacuumTailPacketSpatialDistribution_apply_of_mem
    scale z hz test]
  apply norm_vacuum_inner_le_of_norm_sq_le OS lgc _ B hB
  exact
    D.gram.norm_anchoredAtlasField_sq_le_of_scalar_diagonal_bound
      D.sourceStage.stage D.sourceStage.germ B _ z hz.1 hdiagonal

/-- Sharp square-root version of the finite packet vacuum-tail bound. -/
theorem norm_vacuumTailPacket_le_sqrt_of_scalar_diagonal_bound
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : Nat)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ D.spatialLinearDomain)
    (test : SchwartzMap (Section43SpatialSpace d (q + 1)) Complex)
    (B : Real)
    (hdiagonal :
      norm ((D.gram.cauchy
        (A.positiveHeadSpatialAnchoredSourceCLM scale
          (vacuumTailSpatialLiftCLM test))
        (A.positiveHeadSpatialAnchoredSourceCLM scale
          (vacuumTailSpatialLiftCLM test))).scalar
          (reflectedCauchyCenter z)) <= B) :
    norm (D.vacuumTailPacketSpatialDistribution scale z test) <=
      Real.sqrt B := by
  rw [D.vacuumTailPacketSpatialDistribution_apply_of_mem
    scale z hz test]
  apply norm_vacuum_inner_le_sqrt_of_norm_sq_le OS lgc
  exact
    D.gram.norm_anchoredAtlasField_sq_le_of_scalar_diagonal_bound
      D.sourceStage.stage D.sourceStage.germ B _ z hz.1 hdiagonal

end PositiveHeadUniversalAnchoredAtlasData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
