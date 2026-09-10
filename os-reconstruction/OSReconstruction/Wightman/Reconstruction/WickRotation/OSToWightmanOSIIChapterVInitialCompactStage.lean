/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVChronologicalCompactCover















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace SpatialChronologicalCompactCoverData

variable
  {L :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1)}

/-- One slope orders every carrier in a finite spatial source-map cover in
every signed axis-pair frame. -/
def AxisPairOrderedAt
    (D : SpatialChronologicalCompactCoverData L)
    (T : ℝ) : Prop :=
  ∀ a : D.index,
    ∀ b : osiiAxisPairIndex d,
      ∀ i j : Fin (k + 1), i < j →
        ∀ y ∈ tsupport
            (((D.carrier a).factors i : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              (((D.carrier a).factors j : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ((osiiAxisPairRotationData T b).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData T b).matrix.mulVec z) 0

/-- The finite sum of sourcewise packet continuations associated with one
uniform chronological cover. -/
noncomputable def packetSpatialDistribution
    (D : SpatialChronologicalCompactCoverData L)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered : D.AxisPairOrderedAt T)
    (C : OSIIMultiGapTimeStageChart d k k)
    (ζ : OSIITimeGapSpace k) :
    OSIISpatialDistribution d k :=
  letI : Fintype D.index := D.indexFintype
  ∑ a : D.index,
    ((D.carrier a).schwartzDistributionFamilyAtSlopeOfOS
      OS T hT (hordered a)).timeStageDistribution C (D.piece a) ζ

@[simp] theorem packetSpatialDistribution_apply
    (D : SpatialChronologicalCompactCoverData L)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered : D.AxisPairOrderedAt T)
    (C : OSIIMultiGapTimeStageChart d k k)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    D.packetSpatialDistribution OS T hT hordered C ζ χ =
      letI : Fintype D.index := D.indexFintype
      ∑ a : D.index,
        ((D.carrier a).schwartzDistributionFamilyAtSlopeOfOS
          OS T hT (hordered a)).timeStageDistribution C (D.piece a) ζ χ := by
  simp [packetSpatialDistribution]

/-- A finite sum of packet branches is weakly holomorphic on their common
time-chart carrier. -/
theorem packetSpatialDistribution_weaklyHolomorphic
    (D : SpatialChronologicalCompactCoverData L)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered : D.AxisPairOrderedAt T)
    (C : OSIIMultiGapTimeStageChart d k k) :
    OSIIWeaklyHolomorphicOn
      (D.packetSpatialDistribution OS T hT hordered C)
      C.carrier := by
  intro χ
  letI : Fintype D.index := D.indexFintype
  simpa only [packetSpatialDistribution_apply] using
    DifferentiableOn.fun_sum
      (u := (Finset.univ : Finset D.index))
      (fun a _ha =>
        ((D.carrier a).schwartzDistributionFamilyAtSlopeOfOS
          OS T hT (hordered a)).timeStageDistribution_weaklyHolomorphic
            (Nat.succ_pos k) C (D.piece a) χ)

/-- The finite sum of the packet's localized zero-diagonal sources. -/
noncomputable def localizedTranslatedZeroSum
    (D : SpatialChronologicalCompactCoverData L)
    (T : ℝ) (hT : 1 < T)
    (hordered : D.AxisPairOrderedAt T)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ZeroDiagonalSchwartz d (k + 1) :=
  letI : Fintype D.index := D.indexFintype
  ∑ a : D.index,
    (D.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
      T hT (hordered a) x (D.piece a χ)

/-- The underlying full Schwartz source of the localized finite sum is the
chronological translate of the original compact source-map value. -/
theorem localizedTranslatedZeroSum_coe
    (D : SpatialChronologicalCompactCoverData L)
    (T : ℝ) (hT : 1 < T)
    (hordered : D.AxisPairOrderedAt T)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (D.localizedTranslatedZeroSum T hT hordered x χ).1 =
      translateSchwartzConfiguration
        (fun i => -osiiAxisPairChronologicalPointTranslation T x i)
        (L χ) := by
  letI : Fintype D.index := D.indexFintype
  have hsum :
      L χ = ∑ a : D.index, D.piece a χ :=
    calc
      L χ = (∑ a : D.index, D.piece a) χ :=
        congrArg
          (fun M :
            SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
              SchwartzNPoint d (k + 1) => M χ)
          D.sum_eq
      _ = ∑ a : D.index, D.piece a χ := by
        rw [ContinuousLinearMap.sum_apply]
  rw [localizedTranslatedZeroSum]
  change
    (∑ a : D.index,
      (D.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
        T hT (hordered a) x (D.piece a χ)).1 =
      translateSchwartzConfiguration
        (fun i => -osiiAxisPairChronologicalPointTranslation T x i)
        (L χ)
  have hcoe :
      (∑ a : D.index,
        (D.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
          T hT (hordered a) x (D.piece a χ)).1 =
        ∑ a : D.index,
          ((D.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
            T hT (hordered a) x (D.piece a χ)).1 := by
    delta ZeroDiagonalSchwartz
    exact
      Submodule.coe_sum
        (zeroDiagonalSubmodule d (k + 1))
        (fun a : D.index =>
          (D.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
            T hT (hordered a) x (D.piece a χ))
        Finset.univ
  rw [hcoe]
  change
    (∑ a : D.index,
      (D.carrier a).sourcewiseLocalizedTranslatedFullCLM
        T x (D.piece a χ)) =
      translateSchwartzConfiguration
        (fun i => -osiiAxisPairChronologicalPointTranslation T x i)
        (L χ)
  rw [hsum]
  change
    (∑ a : D.index,
      (D.carrier a).sourcewiseLocalizedTranslatedFullCLM
        T x (D.piece a χ)) =
      translateSchwartzConfigurationCLM
        (fun i => -osiiAxisPairChronologicalPointTranslation T x i)
        (∑ a : D.index, D.piece a χ)
  rw [map_sum
    (g := translateSchwartzConfigurationCLM
      (fun i => -osiiAxisPairChronologicalPointTranslation T x i))
    (f := fun a : D.index => D.piece a χ)
    (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro a _ha
  exact
    sourcewiseLocalizedTranslatedFullCLM_eq_translate_of_fixed
      (D.carrier a) T x (D.piece a χ) (D.carrier_fix a χ)

/-- On a real point of a common chart, the finite packet sum is the Schwinger
value of its named zero-diagonal source sum. -/
theorem packetSpatialDistribution_realEdge
    (D : SpatialChronologicalCompactCoverData L)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered : D.AxisPairOrderedAt T)
    (C : OSIIMultiGapTimeStageChart d k k)
    (τ : Fin k → ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (hcoordinate :
      C.coordinate (osiiPositiveRealTimeEmbed τ) =
        osiiAxisPairSimultaneousLogRealEmbed x)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    D.packetSpatialDistribution OS T hT hordered C
        (osiiPositiveRealTimeEmbed τ) χ =
      OS.S (k + 1)
        (D.localizedTranslatedZeroSum T hT hordered x χ) := by
  letI : Fintype D.index := D.indexFintype
  rw [packetSpatialDistribution_apply]
  rw [localizedTranslatedZeroSum]
  change
    (∑ a : D.index,
      ((D.carrier a).schwartzDistributionFamilyAtSlopeOfOS
        OS T hT (hordered a)).timeStageDistribution C (D.piece a)
          (osiiPositiveRealTimeEmbed τ) χ) =
      (OsterwalderSchraderAxioms.schwingerCLM
        (d := d) OS (k + 1))
        (∑ a : D.index,
          (D.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
            T hT (hordered a) x (D.piece a χ))
  rw [map_sum
    (g := OsterwalderSchraderAxioms.schwingerCLM
      (d := d) OS (k + 1))
    (f := fun a : D.index =>
      (D.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
        T hT (hordered a) x (D.piece a χ))
    (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [
    OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily.timeStageDistribution_apply,
    hcoordinate,
    OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily.pairing_realEdge,
    (D.carrier a).toSourcewiseCoshGrowthDataAtSlopeOfOS_realEdgeDistribution_eq_fullSchwinger
      OS T hT (hordered a) x]
  rfl

/-- On the narrow pure-time chart, the finite packet stage has the named
chronological source translation as its exact positive-real edge. -/
theorem packetSpatialDistribution_narrow_realEdge
    (D : SpatialChronologicalCompactCoverData L)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered : D.AxisPairOrderedAt T)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    D.packetSpatialDistribution OS T hT hordered
        (osiiNarrowTimeStageChart T (lt_trans zero_lt_one hT) η hηsum)
        (osiiPositiveRealTimeEmbed τ) χ =
      OS.S (k + 1)
        (D.localizedTranslatedZeroSum T hT hordered
          (osiiNarrowTimeRealCoordinate (d := d) T τ) χ) := by
  have _hreal_mem :
      osiiPositiveRealTimeEmbed τ ∈ osiiNarrowTimeCarrier (k := k) η :=
    osiiPositiveRealTimeEmbed_mem_osiiNarrowTimeCarrier η hη τ hτ
  apply
    D.packetSpatialDistribution_realEdge OS T hT hordered
      (osiiNarrowTimeStageChart T (lt_trans zero_lt_one hT) η hηsum)
      τ (osiiNarrowTimeRealCoordinate (d := d) T τ)
  simpa [osiiNarrowTimeStageChart] using
    osiiNarrowTimeLogCoordinate_real
      (d := d) T (lt_trans zero_lt_one hT) τ hτ

end SpatialChronologicalCompactCoverData

end OSIIChapterV
end OSReconstruction
