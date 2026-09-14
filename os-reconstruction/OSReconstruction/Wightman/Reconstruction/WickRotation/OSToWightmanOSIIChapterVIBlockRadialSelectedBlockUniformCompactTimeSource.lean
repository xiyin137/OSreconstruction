/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialEndpointUniformCompactTimeSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSelectedBlockPositiveSource











noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

variable {d n m : Nat} [NeZero d]

/-- The two full-chain imaginary variables used by a selected-block source
pair. -/
abbrev OSIIStep4SelectedBlockSourceParameter (d n m : Nat) :=
  (Fin ((n + 1 + m) * (d + 1)) -> Real) ×
    (Fin ((n + 1 + m) * (d + 1)) -> Real)

/-- Restrict the full-chain parameters to the reflected left endpoint and
the reversed left reduced blocks. -/
def osiiStep4SelectedBlockLeftEndpointSourceParameter
    (d n m : Nat)
    (p : OSIIStep4SelectedBlockSourceParameter d n m) :
    OSIIStep4RadialEndpointSourceParameter d n :=
  (osiiStep4SelectedBlockLeftEndpointImag d n m p.1 p.2,
    (osiiStep4ParityReversedBeforeRealBlocks d n m p.1,
      osiiStep4ParityReversedBeforeRealBlocks d n m p.2))

/-- Restrict the full-chain parameters to the right endpoint and right
reduced blocks. -/
def osiiStep4SelectedBlockRightEndpointSourceParameter
    (d n m : Nat)
    (p : OSIIStep4SelectedBlockSourceParameter d n m) :
    OSIIStep4RadialEndpointSourceParameter d m :=
  (osiiStep4SelectedBlockRightEndpointImag d n m p.2,
    (osiiStep4AfterRealBlocks n m (d + 1) p.1,
      osiiStep4AfterRealBlocks n m (d + 1) p.2))

/-- One compact absolute-coordinate carrier for every left selected-block
source at a fixed center. -/
noncomputable def osiiStep4SelectedBlockLeftCommonCarrier
    (d n m : Nat) [NeZero d]
    (rho : Real)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    Set (NPointDomain d (n + 1)) :=
  osiiStep4RadialEndpointCommonCarrier d n rho
    (osiiStep4SelectedBlockLeftEndpointCenter d n m center)
    (osiiStep4ParityReversedBeforeRealBlocks d n m center)

/-- One compact absolute-coordinate carrier for every right selected-block
source at a fixed center. -/
noncomputable def osiiStep4SelectedBlockRightCommonCarrier
    (d n m : Nat) [NeZero d]
    (rho : Real)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    Set (NPointDomain d (m + 1)) :=
  osiiStep4RadialEndpointCommonCarrier d m rho
    (osiiStep4SelectedBlockRightEndpointCenter d n m center)
    (osiiStep4AfterRealBlocks n m (d + 1) center)

theorem osiiStep4SelectedBlockLeftCommonCarrier_isCompact
    (d n m : Nat) [NeZero d]
    (rho : Real)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    IsCompact (osiiStep4SelectedBlockLeftCommonCarrier
      d n m rho center) :=
  osiiStep4RadialEndpointCommonCarrier_isCompact d n rho
    (osiiStep4SelectedBlockLeftEndpointCenter d n m center)
    (osiiStep4ParityReversedBeforeRealBlocks d n m center)

theorem osiiStep4SelectedBlockRightCommonCarrier_isCompact
    (d n m : Nat) [NeZero d]
    (rho : Real)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    IsCompact (osiiStep4SelectedBlockRightCommonCarrier
      d n m rho center) :=
  osiiStep4RadialEndpointCommonCarrier_isCompact d m rho
    (osiiStep4SelectedBlockRightEndpointCenter d n m center)
    (osiiStep4AfterRealBlocks n m (d + 1) center)

theorem osiiStep4SelectedBlockLeftCommonCarrier_orderedPositive
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    osiiStep4SelectedBlockLeftCommonCarrier d n m rho center ⊆
      OrderedPositiveTimeRegion d (n + 1) :=
  osiiStep4RadialEndpointCommonCarrier_orderedPositive d n hrho
    (osiiStep4SelectedBlockLeftEndpointCenter d n m center)
    (osiiStep4ParityReversedBeforeRealBlocks d n m center)
    (osiiStep4SelectedBlockLeftEndpointCenter_time_lower
      d n m hrho center hcenter)
    (osiiStep4ParityReversedBeforeRealBlocks_time_lower
      d n m center hcenter)

theorem osiiStep4SelectedBlockRightCommonCarrier_orderedPositive
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    osiiStep4SelectedBlockRightCommonCarrier d n m rho center ⊆
      OrderedPositiveTimeRegion d (m + 1) :=
  osiiStep4RadialEndpointCommonCarrier_orderedPositive d m hrho
    (osiiStep4SelectedBlockRightEndpointCenter d n m center)
    (osiiStep4AfterRealBlocks n m (d + 1) center)
    (osiiStep4SelectedBlockRightEndpointCenter_time_lower
      d n m hrho center hcenter)
    (osiiStep4AfterRealBlocks_time_lower d n m center hcenter)

theorem osiiStep4SelectedBlockLeftPositiveTimeSource_tsupport_subset_commonCarrier
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    tsupport
        ((osiiStep4SelectedBlockLeftPositiveTimeSource
          d n m hrho center y y' hcenter).1 :
          NPointDomain d (n + 1) -> Complex) ⊆
      osiiStep4SelectedBlockLeftCommonCarrier d n m rho center := by
  simpa [osiiStep4SelectedBlockLeftPositiveTimeSource,
    osiiStep4RadialEndpointPositiveTimeSource,
    osiiStep4RadialEndpointSourceFamily,
    osiiStep4SelectedBlockLeftEndpointSourceParameter] using
    osiiStep4RadialEndpointSourceFamily_tsupport_subset_commonCarrier
      d n hrho
      (osiiStep4SelectedBlockLeftEndpointCenter d n m center)
      (osiiStep4ParityReversedBeforeRealBlocks d n m center)
      (osiiStep4SelectedBlockLeftEndpointSourceParameter
        d n m (y, y'))

theorem osiiStep4SelectedBlockRightPositiveTimeSource_tsupport_subset_commonCarrier
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    tsupport
        ((osiiStep4SelectedBlockRightPositiveTimeSource
          d n m hrho center y y' hcenter).1 :
          NPointDomain d (m + 1) -> Complex) ⊆
      osiiStep4SelectedBlockRightCommonCarrier d n m rho center := by
  simpa [osiiStep4SelectedBlockRightPositiveTimeSource,
    osiiStep4RadialEndpointPositiveTimeSource,
    osiiStep4RadialEndpointSourceFamily,
    osiiStep4SelectedBlockRightEndpointSourceParameter] using
    osiiStep4RadialEndpointSourceFamily_tsupport_subset_commonCarrier
      d m hrho
      (osiiStep4SelectedBlockRightEndpointCenter d n m center)
      (osiiStep4AfterRealBlocks n m (d + 1) center)
      (osiiStep4SelectedBlockRightEndpointSourceParameter
        d n m (y, y'))

/-- Fixed difference-time carrier for the complete left selected-block
source family. -/
noncomputable def osiiStep4SelectedBlockLeftTimeCarrier
    (d n m : Nat) [NeZero d]
    (rho : Real)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    Set (Fin (n + 1) -> Real) :=
  osiiStep4RadialEndpointTimeCarrier d n rho
    (osiiStep4SelectedBlockLeftEndpointCenter d n m center)
    (osiiStep4ParityReversedBeforeRealBlocks d n m center)

/-- Fixed difference-time carrier for the complete right selected-block
source family. -/
noncomputable def osiiStep4SelectedBlockRightTimeCarrier
    (d n m : Nat) [NeZero d]
    (rho : Real)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    Set (Fin (m + 1) -> Real) :=
  osiiStep4RadialEndpointTimeCarrier d m rho
    (osiiStep4SelectedBlockRightEndpointCenter d n m center)
    (osiiStep4AfterRealBlocks n m (d + 1) center)

/-- The physical left selected-block source in its universal fixed-carrier
source space. -/
noncomputable def osiiStep4SelectedBlockLeftUniformCompactTimeSource
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (p : OSIIStep4SelectedBlockSourceParameter d n m) :
    OSIIChapterV.UniformCompactTimeSource d (n + 1)
      (osiiStep4SelectedBlockLeftTimeCarrier d n m rho center) :=
  osiiStep4RadialEndpointUniformCompactTimeSource d n hrho
    (osiiStep4SelectedBlockLeftEndpointCenter d n m center)
    (osiiStep4ParityReversedBeforeRealBlocks d n m center)
    (osiiStep4SelectedBlockLeftEndpointCenter_time_lower
      d n m hrho center hcenter)
    (osiiStep4ParityReversedBeforeRealBlocks_time_lower
      d n m center hcenter)
    (osiiStep4SelectedBlockLeftEndpointSourceParameter d n m p)

/-- The physical right selected-block source in its universal fixed-carrier
source space. -/
noncomputable def osiiStep4SelectedBlockRightUniformCompactTimeSource
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (p : OSIIStep4SelectedBlockSourceParameter d n m) :
    OSIIChapterV.UniformCompactTimeSource d (m + 1)
      (osiiStep4SelectedBlockRightTimeCarrier d n m rho center) :=
  osiiStep4RadialEndpointUniformCompactTimeSource d m hrho
    (osiiStep4SelectedBlockRightEndpointCenter d n m center)
    (osiiStep4AfterRealBlocks n m (d + 1) center)
    (osiiStep4SelectedBlockRightEndpointCenter_time_lower
      d n m hrho center hcenter)
    (osiiStep4AfterRealBlocks_time_lower d n m center hcenter)
    (osiiStep4SelectedBlockRightEndpointSourceParameter d n m p)

@[simp] theorem
    osiiStep4SelectedBlockLeftUniformCompactTimeSource_source_coe
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (p : OSIIStep4SelectedBlockSourceParameter d n m) :
    (OSIIChapterV.UniformCompactTimeSource.source
      (osiiStep4SelectedBlockLeftUniformCompactTimeSource
        d n m hrho center hcenter p)).1 =
      (osiiStep4SelectedBlockLeftPositiveTimeSource
        d n m hrho center p.1 p.2 hcenter).1 :=
  rfl

@[simp] theorem
    osiiStep4SelectedBlockRightUniformCompactTimeSource_source_coe
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (p : OSIIStep4SelectedBlockSourceParameter d n m) :
    (OSIIChapterV.UniformCompactTimeSource.source
      (osiiStep4SelectedBlockRightUniformCompactTimeSource
        d n m hrho center hcenter p)).1 =
      (osiiStep4SelectedBlockRightPositiveTimeSource
        d n m hrho center p.1 p.2 hcenter).1 :=
  rfl

end OSReconstruction
