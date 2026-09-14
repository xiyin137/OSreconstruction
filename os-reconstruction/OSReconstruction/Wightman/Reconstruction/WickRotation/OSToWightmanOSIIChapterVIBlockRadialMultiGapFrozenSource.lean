/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapTranslation










noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

def osiiStep4MultiGapLeftSpectatorLogCoordinates
    (d k : Nat)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    Fin i.val -> osiiAxisPairIndex d -> Real :=
  fun j a =>
    x (osiiStep4MultiGapSplitBlockEquiv i
        (osiiStep4ReversedBeforeBlockIndex
          i.val (osiiStep4MultiGapAfterCount i) j))
      (osiiAxisPairOpposite a)

def osiiStep4MultiGapRightSpectatorLogCoordinates
    (d k : Nat)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    Fin (osiiStep4MultiGapAfterCount i) ->
      osiiAxisPairIndex d -> Real :=
  fun j a =>
    x (osiiStep4MultiGapSplitBlockEquiv i
        (osiiStep4AfterBlockIndex
          i.val (osiiStep4MultiGapAfterCount i) j)) a

theorem multiGapSplitBlockEquiv_reversedBefore_ne
    {k : Nat} (i : Fin k) (j : Fin i.val) :
    osiiStep4MultiGapSplitBlockEquiv i
        (osiiStep4ReversedBeforeBlockIndex
          i.val (osiiStep4MultiGapAfterCount i) j) ≠ i := by
  apply Fin.ne_of_val_ne
  simp [osiiStep4MultiGapSplitBlockEquiv,
    osiiStep4ReversedBeforeBlockIndex]
  omega

theorem multiGapSplitBlockEquiv_after_ne
    {k : Nat} (i : Fin k)
    (j : Fin (osiiStep4MultiGapAfterCount i)) :
    osiiStep4MultiGapSplitBlockEquiv i
        (osiiStep4AfterBlockIndex
          i.val (osiiStep4MultiGapAfterCount i) j) ≠ i := by
  apply Fin.ne_of_val_ne
  simp [osiiStep4MultiGapSplitBlockEquiv,
    osiiStep4AfterBlockIndex]
  omega

noncomputable def osiiStep4MultiGapFrozenLeftPositiveSource
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) : SchwartzNPoint d (i.val + 1) :=
  translateSchwartzConfiguration
    (fun j => -osiiAxisPairChronologicalPointTranslation T
      (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j)
    (osiiStep4MultiGapSelectedLeftPositiveTimeSource
      d k hrho center y y' hcenter i).1

noncomputable def osiiStep4MultiGapFrozenRightPositiveSource
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    SchwartzNPoint d (osiiStep4MultiGapAfterCount i + 1) :=
  translateSchwartzConfiguration
    (fun j => -osiiAxisPairChronologicalPointTranslation T
      (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j)
    (osiiStep4MultiGapSelectedRightPositiveTimeSource
      d k hrho center y y' hcenter i).1

theorem osiiStep4MultiGapFrozenLeftPositiveSource_support
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (T : Real) (hT : 1 < T)
    (hleft : forall i a,
      tsupport
          ((osiiStep4MultiGapSelectedLeftPositiveTimeSource
            d k hrho center y y' hcenter i).1 :
            NPointDomain d (i.val + 1) -> Complex) <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := i.val + 1)
          (osiiAxisPairRotationData T a).matrix)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    tsupport
        (osiiStep4MultiGapFrozenLeftPositiveSource
          d k hrho center y y' hcenter T x i :
          NPointDomain d (i.val + 1) -> Complex) <=
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := i.val + 1)
        (osiiAxisPairRotationData T a).matrix := by
  exact translateConfiguration_axisPairGaps_preserves_all_orientedPositive_all
    d i.val T hT
    (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i)
    (osiiStep4MultiGapSelectedLeftPositiveTimeSource
      d k hrho center y y' hcenter i).1
    (hleft i) a

theorem osiiStep4MultiGapFrozenRightPositiveSource_support
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (T : Real) (hT : 1 < T)
    (hright : forall i a,
      tsupport
          ((osiiStep4MultiGapSelectedRightPositiveTimeSource
            d k hrho center y y' hcenter i).1 :
            NPointDomain d (osiiStep4MultiGapAfterCount i + 1) -> Complex) <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := osiiStep4MultiGapAfterCount i + 1)
          (osiiAxisPairRotationData T a).matrix)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    tsupport
        (osiiStep4MultiGapFrozenRightPositiveSource
          d k hrho center y y' hcenter T x i :
          NPointDomain d (osiiStep4MultiGapAfterCount i + 1) -> Complex) <=
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := osiiStep4MultiGapAfterCount i + 1)
        (osiiAxisPairRotationData T a).matrix := by
  exact translateConfiguration_axisPairGaps_preserves_all_orientedPositive_all
    d (osiiStep4MultiGapAfterCount i) T hT
    (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i)
    (osiiStep4MultiGapSelectedRightPositiveTimeSource
      d k hrho center y y' hcenter i).1
    (hright i) a

theorem osiiStep4MultiGapFrozenLeftPositiveSource_eq_radialEndpoint
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    osiiStep4MultiGapFrozenLeftPositiveSource
        d k hrho center y y' hcenter T x i =
      osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d i.val hrho
        (osiiStep4SelectedBlockLeftEndpointCenter
          d i.val (osiiStep4MultiGapAfterCount i)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i center))
        (osiiStep4SelectedBlockLeftEndpointImag
          d i.val (osiiStep4MultiGapAfterCount i)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i y'))
        (osiiStep4ParityReversedBeforeRealBlocks
            d i.val (osiiStep4MultiGapAfterCount i)
            (osiiStep4MultiGapSplitCoordinates (d + 1) i center) +
          osiiStep4AxisPairGapTranslationFlat d T
            (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i))
        (osiiStep4ParityReversedBeforeRealBlocks
          d i.val (osiiStep4MultiGapAfterCount i)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i y))
        (osiiStep4ParityReversedBeforeRealBlocks
          d i.val (osiiStep4MultiGapAfterCount i)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i y')) := by
  simpa [osiiStep4MultiGapFrozenLeftPositiveSource,
    osiiStep4MultiGapSelectedLeftPositiveTimeSource,
    osiiStep4SelectedBlockLeftPositiveTimeSource,
    osiiStep4RadialEndpointPositiveTimeSource] using
    (translateConfiguration_radialEndpoint_axisPairGaps_all
      d i.val hrho
      (osiiStep4SelectedBlockLeftEndpointCenter
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center))
      (osiiStep4SelectedBlockLeftEndpointImag
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y'))
      (osiiStep4ParityReversedBeforeRealBlocks
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center))
      (osiiStep4ParityReversedBeforeRealBlocks
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y))
      (osiiStep4ParityReversedBeforeRealBlocks
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y'))
      T (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i))

theorem osiiStep4MultiGapFrozenRightPositiveSource_eq_radialEndpoint
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    osiiStep4MultiGapFrozenRightPositiveSource
        d k hrho center y y' hcenter T x i =
      osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d (osiiStep4MultiGapAfterCount i) hrho
        (osiiStep4SelectedBlockRightEndpointCenter
          d i.val (osiiStep4MultiGapAfterCount i)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i center))
        (osiiStep4SelectedBlockRightEndpointImag
          d i.val (osiiStep4MultiGapAfterCount i)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i y'))
        (osiiStep4AfterRealBlocks
            i.val (osiiStep4MultiGapAfterCount i) (d + 1)
            (osiiStep4MultiGapSplitCoordinates (d + 1) i center) +
          osiiStep4AxisPairGapTranslationFlat d T
            (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i))
        (osiiStep4AfterRealBlocks
          i.val (osiiStep4MultiGapAfterCount i) (d + 1)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i y))
        (osiiStep4AfterRealBlocks
          i.val (osiiStep4MultiGapAfterCount i) (d + 1)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i y')) := by
  simpa [osiiStep4MultiGapFrozenRightPositiveSource,
    osiiStep4MultiGapSelectedRightPositiveTimeSource,
    osiiStep4SelectedBlockRightPositiveTimeSource,
    osiiStep4RadialEndpointPositiveTimeSource] using
    (translateConfiguration_radialEndpoint_axisPairGaps_all
      d (osiiStep4MultiGapAfterCount i) hrho
      (osiiStep4SelectedBlockRightEndpointCenter
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center))
      (osiiStep4SelectedBlockRightEndpointImag
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y'))
      (osiiStep4AfterRealBlocks
        i.val (osiiStep4MultiGapAfterCount i) (d + 1)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center))
      (osiiStep4AfterRealBlocks
        i.val (osiiStep4MultiGapAfterCount i) (d + 1)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y))
      (osiiStep4AfterRealBlocks
        i.val (osiiStep4MultiGapAfterCount i) (d + 1)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y'))
      T (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i))

end OSReconstruction
