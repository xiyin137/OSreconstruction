/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketCarrierCoherence
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPacketTimeTranslation










noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- Evaluation of the common time-shell distribution on any fixed
reduced-time Schwartz test is holomorphic throughout the narrow time
carrier. -/
theorem commonTimeShellDistributionOfOS_fixedTest_differentiableOn
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (level : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    DifferentiableOn ℂ
      (fun ζ =>
        A.commonTimeShellDistributionOfOS
          OS η hηsum level ζ χ φ)
      (osiiNarrowTimeCarrier (k := k) η) := by
  let P := A.commonPacketAt 0 level
  let C :=
    osiiNarrowTimeStageChart P.slope
      (lt_trans zero_lt_one P.slope_gt_one) η hηsum
  have hsum :
      DifferentiableOn ℂ
        (fun ζ : OSIITimeGapSpace k =>
          ∑ a : A.partition.index,
            (P.pieceTimeShellDistributionOfOS OS η hηsum a ζ χ) φ)
        (osiiNarrowTimeCarrier (k := k) η) := by
    exact DifferentiableOn.fun_sum
      (u := (Finset.univ : Finset A.partition.index)) (fun a _ha => by
        have hdiff :
            DifferentiableOn ℂ
              (fun ζ =>
                ((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
                    OS P.slope P.slope_gt_one (P.ordered a)).pairing
                    (P.levelTimePieceFullSourceCLM a χ φ)
                    (C.coordinate ζ))
              C.carrier :=
          ((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
              OS P.slope P.slope_gt_one (P.ordered a)
            ).differentiableOn_pairing_of_productTensor_holomorphic
              (Nat.succ_pos k) (P.levelTimePieceFullSourceCLM a χ φ)
            |>.comp C.coordinate_differentiable C.coordinate_mapsTo
        exact hdiff.congr fun ζ _hζ =>
          P.pieceTimeShellDistributionOfOS_apply
            OS η hηsum a ζ χ φ)
  exact hsum.congr fun ζ _hζ => by
    change (P.timeShellDistributionOfOS OS η hηsum ζ χ) φ =
      ∑ a : A.partition.index,
        (P.pieceTimeShellDistributionOfOS OS η hηsum a ζ χ) φ
    exact InitialBaseTimePartitionData.FixedTimePacketData.timeShellDistributionOfOS_apply
      P OS η hηsum ζ χ φ

/-- Translation covariance of the common time-shell distribution for an
arbitrary carrier-supported test. -/
theorem commonTimeShellDistributionOfOS_translate_timeTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier)
    (shift : Fin k → ℝ)
    (hshift : shift ∈ section43TimeStrictPositiveRegion k)
    (htranslated :
      tsupport
          (SCV.translateSchwartz (-shift) φ :
            (Fin k → ℝ) → ℂ) ⊆
        A.carrierData.carrier)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (level : ℕ)
    (ζ : OSIITimeGapSpace k)
    (hζ : ζ ∈ osiiNarrowTimeCarrier (k := k) η)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    A.commonTimeShellDistributionOfOS
        OS η hηsum level ζ χ
        (SCV.translateSchwartz (-shift) φ) =
      A.commonTimeShellDistributionOfOS
        OS η hηsum level
        (ζ + osiiPositiveRealTimeEmbed shift) χ φ := by
  rw [
    A.commonTimeShellDistributionOfOS_apply_eq_commonPacketForTest
      OS η hηsum level ζ χ
      (SCV.translateSchwartz (-shift) φ) htranslated,
    A.commonTimeShellDistributionOfOS_apply_eq_commonPacketForTest
      OS η hηsum level
      (ζ + osiiPositiveRealTimeEmbed shift) χ φ hφ]
  exact
    InitialSpatialFactorPacketData.narrowDistributionOfOS_translate_timeTest
        shift hshift
        (A.commonPacketForTest
          (SCV.translateSchwartz (-shift) φ) htranslated level
          ).toInitialSpatialFactorPacketData
        (A.commonPacketForTest φ hφ level
          ).toInitialSpatialFactorPacketData
        OS η hη hηsum χ hζ

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
