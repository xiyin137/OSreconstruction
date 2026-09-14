/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialFixedTimePacket















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace InitialBaseTimePartitionData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

/-- One fixed base/time partition weight applied to the canonical full source,
viewed as a continuous linear map in the coupled reduced-time test. -/
noncomputable def timePieceFullSourceCLM
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1) :=
  (SchwartzMap.smulLeftCLM ℂ (D.weight a)).comp
    (initialReducedTimeFullSourceCLM (d := d) χ)

@[simp] theorem timePieceFullSourceCLM_apply
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ) :
    D.timePieceFullSourceCLM a χ ψ =
      SchwartzMap.smulLeftCLM ℂ (D.weight a)
        (initialReducedTimeFullSourceCLM (d := d) χ ψ) :=
  rfl

@[simp] theorem timePieceFullSourceCLM_apply_canonical
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    D.timePieceFullSourceCLM a χ φ = D.piece a χ :=
  rfl

namespace FixedTimePacketData

/-- The level-`N` spatial source used by one packet piece, kept linear in the
coupled reduced-time test. -/
noncomputable def levelTimePieceFullSourceCLM
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (a : D.index)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1) :=
  D.timePieceFullSourceCLM a
    (initialSpatialFactorTruncationCLM d k N χ)

@[simp] theorem levelTimePieceFullSourceCLM_apply_canonical
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (a : D.index)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    P.levelTimePieceFullSourceCLM a χ φ =
      D.levelPiece a N χ :=
  rfl

/-- One finite packet piece as a scalar distribution in the complete coupled
reduced-time test. -/
noncomputable def pieceTimeShellDistribution
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (a : D.index)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
  ((P.pieceSourcewisePacketData OS lgc a
      ).schwartzDistributionFamily.totalDistribution
        ((osiiNarrowTimeStageChart P.slope
          (lt_trans zero_lt_one P.slope_gt_one) η hηsum).coordinate ζ)
    ).comp (P.levelTimePieceFullSourceCLM a χ)

/-- The complete finite-level packet as one continuous scalar distribution in
the coupled reduced-time test.  The finite partition is summed internally. -/
noncomputable def timeShellDistribution
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
  ∑ a : D.index,
    P.pieceTimeShellDistribution OS lgc η hηsum a ζ χ

/-- One finite packet piece as a continuous reduced-time distribution,
constructed directly from the original-OS full-Schwartz family. -/
noncomputable def pieceTimeShellDistributionOfOS
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (a : D.index)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
  (((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
      OS P.slope P.slope_gt_one (P.ordered a)).totalDistribution
        ((osiiNarrowTimeStageChart P.slope
          (lt_trans zero_lt_one P.slope_gt_one) η hηsum).coordinate ζ)
    ).comp (P.levelTimePieceFullSourceCLM a χ)

@[simp] theorem pieceTimeShellDistributionOfOS_apply
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (a : D.index)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ) :
    P.pieceTimeShellDistributionOfOS OS η hηsum a ζ χ ψ =
      ((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
        OS P.slope P.slope_gt_one (P.ordered a)).pairing
          (P.levelTimePieceFullSourceCLM a χ ψ)
          (osiiNarrowTimeLogCoordinate (d := d) P.slope ζ) := by
  simp [pieceTimeShellDistributionOfOS, osiiNarrowTimeStageChart]

/-- Sum the original-OS finite packet pieces before exposing the coupled
reduced-time Schwartz distribution. -/
noncomputable def timeShellDistributionOfOS
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
  ∑ a : D.index,
    P.pieceTimeShellDistributionOfOS OS η hηsum a ζ χ

@[simp] theorem timeShellDistributionOfOS_apply
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ) :
    P.timeShellDistributionOfOS OS η hηsum ζ χ ψ =
      ∑ a : D.index,
        P.pieceTimeShellDistributionOfOS OS η hηsum a ζ χ ψ := by
  simp [timeShellDistributionOfOS]

/-- Applying the original-OS coupled shell to its defining time test
recovers the canonical finite compact continuation stage. -/
@[simp] theorem timeShellDistributionOfOS_apply_canonical
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    P.timeShellDistributionOfOS OS η hηsum ζ χ φ =
      P.toInitialSpatialFactorPacketData.narrowDistributionOfOS
        OS η hηsum ζ χ := by
  simp [timeShellDistributionOfOS,
    InitialSpatialFactorPacketData.narrowDistributionOfOS,
    SpatialChronologicalCompactCoverData.packetSpatialDistribution_apply,
    toInitialSpatialFactorPacketData,
    LevelCover.toSpatialChronologicalCompactCoverData,
    OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily.timeStageDistribution_apply,
    osiiNarrowTimeStageChart]

end FixedTimePacketData
end InitialBaseTimePartitionData
end OSIIChapterV
end OSReconstruction
