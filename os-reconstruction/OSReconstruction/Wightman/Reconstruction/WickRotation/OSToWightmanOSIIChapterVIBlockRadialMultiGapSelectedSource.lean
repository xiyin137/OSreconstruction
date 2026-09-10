/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapCommonSlope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSelectedBlockUniformCompactTimeSource









noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

/-- Number of radial blocks strictly after a selected chronological gap. -/
def osiiStep4MultiGapAfterCount {k : Nat} (i : Fin k) : Nat :=
  k - (i.val + 1)

theorem osiiStep4MultiGap_split_count {k : Nat} (i : Fin k) :
    i.val + 1 + osiiStep4MultiGapAfterCount i = k := by
  simp [osiiStep4MultiGapAfterCount]

/-- Reindex the blocks of the selected-gap decomposition as the original
`k` radial blocks. -/
def osiiStep4MultiGapSplitBlockEquiv {k : Nat} (i : Fin k) :
    Fin (i.val + 1 + osiiStep4MultiGapAfterCount i) ≃ Fin k :=
  finCongr (osiiStep4MultiGap_split_count i)

/-- Flattened-coordinate form of `osiiStep4MultiGapSplitBlockEquiv`. -/
def osiiStep4MultiGapSplitCoordinateEquiv
    (q : Nat) {k : Nat} (i : Fin k) :
    Fin ((i.val + 1 + osiiStep4MultiGapAfterCount i) * q) ≃
      Fin (k * q) :=
  finCongr (congrArg (fun r => r * q)
    (osiiStep4MultiGap_split_count i))

theorem osiiStep4MultiGapSplitCoordinateEquiv_finProdFinEquiv
    (q : Nat) {k : Nat} (i : Fin k)
    (j : Fin (i.val + 1 + osiiStep4MultiGapAfterCount i))
    (mu : Fin q) :
    osiiStep4MultiGapSplitCoordinateEquiv q i (finProdFinEquiv (j, mu)) =
      finProdFinEquiv (osiiStep4MultiGapSplitBlockEquiv i j, mu) := by
  apply Fin.ext
  rfl

/-- Pull a flattened `k`-block tuple back to the arithmetic shape expected by
the selected-block source at gap `i`. -/
def osiiStep4MultiGapSplitCoordinates
    (q : Nat) {k : Nat} (i : Fin k)
    (x : Fin (k * q) -> Real) :
    Fin ((i.val + 1 + osiiStep4MultiGapAfterCount i) * q) -> Real :=
  fun a => x (osiiStep4MultiGapSplitCoordinateEquiv q i a)

theorem osiiStep4MultiGapSplitCoordinates_time_lower
    (d k : Nat) {rho : Real}
    (i : Fin k)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    forall j : Fin (i.val + 1 + osiiStep4MultiGapAfterCount i),
      rho / 2 <= osiiStep4MultiGapSplitCoordinates (d + 1) i center
        (finProdFinEquiv (j, (0 : Fin (d + 1)))) := by
  intro j
  rw [osiiStep4MultiGapSplitCoordinates,
    osiiStep4MultiGapSplitCoordinateEquiv_finProdFinEquiv]
  exact hcenter (osiiStep4MultiGapSplitBlockEquiv i j)

/-- Left positive-time radial source at a chronological gap of a fixed
multi-gap tuple. -/
noncomputable def osiiStep4MultiGapSelectedLeftPositiveTimeSource
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (i : Fin k) :
    euclideanPositiveTimeSubmodule (d := d) (i.val + 1) :=
  osiiStep4SelectedBlockLeftPositiveTimeSource
    d i.val (osiiStep4MultiGapAfterCount i) hrho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)
    (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
    (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
    (osiiStep4MultiGapSplitCoordinates_time_lower d k i center hcenter)

/-- Right positive-time radial source at a chronological gap of a fixed
multi-gap tuple. -/
noncomputable def osiiStep4MultiGapSelectedRightPositiveTimeSource
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (i : Fin k) :
    euclideanPositiveTimeSubmodule
      (d := d) (osiiStep4MultiGapAfterCount i + 1) :=
  osiiStep4SelectedBlockRightPositiveTimeSource
    d i.val (osiiStep4MultiGapAfterCount i) hrho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)
    (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
    (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
    (osiiStep4MultiGapSplitCoordinates_time_lower d k i center hcenter)

/-- Common absolute carrier of all left radial sources at split `i`.  It is
independent of the two radial source parameters. -/
noncomputable def osiiStep4MultiGapSelectedLeftCommonCarrier
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    Set (NPointDomain d (i.val + 1)) :=
  osiiStep4SelectedBlockLeftCommonCarrier
    d i.val (osiiStep4MultiGapAfterCount i) rho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)

/-- Common absolute carrier of all right radial sources at split `i`. -/
noncomputable def osiiStep4MultiGapSelectedRightCommonCarrier
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    Set (NPointDomain d (osiiStep4MultiGapAfterCount i + 1)) :=
  osiiStep4SelectedBlockRightCommonCarrier
    d i.val (osiiStep4MultiGapAfterCount i) rho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)

/-- The left common carrier is monotone in the radial scale. -/
theorem osiiStep4MultiGapSelectedLeftCommonCarrier_mono
    (d k : Nat) [NeZero d]
    {sigma rho : Real} (hscale : sigma <= rho)
    (center : Fin (k * (d + 1)) -> Real) (i : Fin k) :
    osiiStep4MultiGapSelectedLeftCommonCarrier d k sigma center i ⊆
      osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center i := by
  exact osiiStep4RadialEndpointCommonCarrier_mono
    d i.val hscale
      (osiiStep4SelectedBlockLeftEndpointCenter
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center))
      (osiiStep4ParityReversedBeforeRealBlocks
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center))

/-- The right common carrier is monotone in the radial scale. -/
theorem osiiStep4MultiGapSelectedRightCommonCarrier_mono
    (d k : Nat) [NeZero d]
    {sigma rho : Real} (hscale : sigma <= rho)
    (center : Fin (k * (d + 1)) -> Real) (i : Fin k) :
    osiiStep4MultiGapSelectedRightCommonCarrier d k sigma center i ⊆
      osiiStep4MultiGapSelectedRightCommonCarrier d k rho center i := by
  exact osiiStep4RadialEndpointCommonCarrier_mono
    d (osiiStep4MultiGapAfterCount i) hscale
      (osiiStep4SelectedBlockRightEndpointCenter
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center))
      (osiiStep4AfterRealBlocks i.val (osiiStep4MultiGapAfterCount i)
        (d + 1) (osiiStep4MultiGapSplitCoordinates (d + 1) i center))

theorem osiiStep4MultiGapSelectedLeftCommonCarrier_isCompact
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    IsCompact
      (osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center i) :=
  osiiStep4SelectedBlockLeftCommonCarrier_isCompact
    d i.val (osiiStep4MultiGapAfterCount i) rho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)

theorem osiiStep4MultiGapSelectedRightCommonCarrier_isCompact
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    IsCompact
      (osiiStep4MultiGapSelectedRightCommonCarrier d k rho center i) :=
  osiiStep4SelectedBlockRightCommonCarrier_isCompact
    d i.val (osiiStep4MultiGapAfterCount i) rho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)

theorem osiiStep4MultiGapSelectedLeftCommonCarrier_orderedPositive
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (i : Fin k) :
    osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center i ⊆
      OrderedPositiveTimeRegion d (i.val + 1) :=
  osiiStep4SelectedBlockLeftCommonCarrier_orderedPositive
    d i.val (osiiStep4MultiGapAfterCount i) hrho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)
    (osiiStep4MultiGapSplitCoordinates_time_lower d k i center hcenter)

theorem osiiStep4MultiGapSelectedRightCommonCarrier_orderedPositive
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (i : Fin k) :
    osiiStep4MultiGapSelectedRightCommonCarrier d k rho center i ⊆
      OrderedPositiveTimeRegion d
        (osiiStep4MultiGapAfterCount i + 1) :=
  osiiStep4SelectedBlockRightCommonCarrier_orderedPositive
    d i.val (osiiStep4MultiGapAfterCount i) hrho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)
    (osiiStep4MultiGapSplitCoordinates_time_lower d k i center hcenter)

theorem osiiStep4MultiGapSelectedLeftPositiveTimeSource_tsupport_subset_commonCarrier
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (i : Fin k) :
    tsupport
        ((osiiStep4MultiGapSelectedLeftPositiveTimeSource
          d k hrho center y y' hcenter i).1 :
          NPointDomain d (i.val + 1) -> Complex) ⊆
      osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center i := by
  exact osiiStep4SelectedBlockLeftPositiveTimeSource_tsupport_subset_commonCarrier
    d i.val (osiiStep4MultiGapAfterCount i) hrho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)
    (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
    (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
    (osiiStep4MultiGapSplitCoordinates_time_lower d k i center hcenter)

theorem osiiStep4MultiGapSelectedRightPositiveTimeSource_tsupport_subset_commonCarrier
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (i : Fin k) :
    tsupport
        ((osiiStep4MultiGapSelectedRightPositiveTimeSource
          d k hrho center y y' hcenter i).1 :
          NPointDomain d (osiiStep4MultiGapAfterCount i + 1) -> Complex) ⊆
      osiiStep4MultiGapSelectedRightCommonCarrier d k rho center i := by
  exact osiiStep4SelectedBlockRightPositiveTimeSource_tsupport_subset_commonCarrier
    d i.val (osiiStep4MultiGapAfterCount i) hrho
    (osiiStep4MultiGapSplitCoordinates (d + 1) i center)
    (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
    (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
    (osiiStep4MultiGapSplitCoordinates_time_lower d k i center hcenter)

/-- A slope chosen from the full compact radial carriers, before the source
parameters `y,y'` are introduced. -/
structure OSIIStep4MultiGapUniformCommonSlopeData
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) where
  T : Real
  hT : 1 < T
  left_carrier_support : forall i a,
    osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center i ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := i.val + 1)
        (osiiAxisPairRotationData T a).matrix
  right_carrier_support : forall i a,
    osiiStep4MultiGapSelectedRightCommonCarrier d k rho center i ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := osiiStep4MultiGapAfterCount i + 1)
        (osiiAxisPairRotationData T a).matrix

theorem nonempty_osiiStep4MultiGapUniformCommonSlopeData
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    Nonempty (OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter) := by
  letI : Nonempty (Fin k) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne k))
  obtain ⟨T, hT, hleft, hright⟩ :=
    exists_common_axisPairSlope_twoCompactCarrierFamilies
      (fun i : Fin k => i.val + 1)
      (fun i : Fin k => osiiStep4MultiGapAfterCount i + 1)
      (osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center)
      (osiiStep4MultiGapSelectedRightCommonCarrier d k rho center)
      (osiiStep4MultiGapSelectedLeftCommonCarrier_isCompact d k rho center)
      (osiiStep4MultiGapSelectedRightCommonCarrier_isCompact d k rho center)
      (osiiStep4MultiGapSelectedLeftCommonCarrier_orderedPositive
        d k hrho center hcenter)
      (osiiStep4MultiGapSelectedRightCommonCarrier_orderedPositive
        d k hrho center hcenter)
  exact ⟨{
    T := T
    hT := hT
    left_carrier_support := hleft
    right_carrier_support := hright }⟩

noncomputable def osiiStep4MultiGapUniformCommonSlopeData
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    OSIIStep4MultiGapUniformCommonSlopeData d k hrho center hcenter :=
  Classical.choice
    (nonempty_osiiStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)

namespace OSIIStep4MultiGapUniformCommonSlopeData

/-- A slope selected for a radial carrier remains valid after shrinking the
scale, because both left and right common carriers only become smaller. -/
def shrink
    {d k : Nat} [NeZero d] [NeZero k]
    {sigma rho : Real} {hsigma : 0 < sigma} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenterRho : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenterRho)
    (hscale : sigma <= rho)
    (hcenterSigma : forall j : Fin k,
      sigma / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    OSIIStep4MultiGapUniformCommonSlopeData
      d k hsigma center hcenterSigma where
  T := D.T
  hT := D.hT
  left_carrier_support := fun i a =>
    (osiiStep4MultiGapSelectedLeftCommonCarrier_mono
      d k hscale center i).trans (D.left_carrier_support i a)
  right_carrier_support := fun i a =>
    (osiiStep4MultiGapSelectedRightCommonCarrier_mono
      d k hscale center i).trans (D.right_carrier_support i a)

theorem left_source_support
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (y y' : Fin (k * (d + 1)) -> Real)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    tsupport
        ((osiiStep4MultiGapSelectedLeftPositiveTimeSource
          d k hrho center y y' hcenter i).1 :
          NPointDomain d (i.val + 1) -> Complex) ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := i.val + 1)
        (osiiAxisPairRotationData D.T a).matrix :=
  (osiiStep4MultiGapSelectedLeftPositiveTimeSource_tsupport_subset_commonCarrier
    d k hrho center y y' hcenter i).trans (D.left_carrier_support i a)

theorem right_source_support
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (y y' : Fin (k * (d + 1)) -> Real)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    tsupport
        ((osiiStep4MultiGapSelectedRightPositiveTimeSource
          d k hrho center y y' hcenter i).1 :
          NPointDomain d (osiiStep4MultiGapAfterCount i + 1) -> Complex) ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := osiiStep4MultiGapAfterCount i + 1)
        (osiiAxisPairRotationData D.T a).matrix :=
  (osiiStep4MultiGapSelectedRightPositiveTimeSource_tsupport_subset_commonCarrier
    d k hrho center y y' hcenter i).trans (D.right_carrier_support i a)

end OSIIStep4MultiGapUniformCommonSlopeData

end OSReconstruction
