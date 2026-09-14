/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitRankGenerator
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapTargetGeometry
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIStep4MultiGapUniformCommonSlopeData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}

/-- Real parts of every physical target logarithm over the complete closed
radial support, at the genuine gap arity `k`. -/
def fixedAxisAllSplitTargetLogRealCarrier
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter) :
    Set (Fin k -> osiiAxisPairIndex d -> Real) :=
  (fun z j a =>
    (osiiStep4MultiGapTargetLog
      d k D.T center (fun u => (z u).re) j a).re) ''
    SCV.closedPolydisc
      (0 : Fin (k * (d + 1)) -> Complex) (fun _ => rho / 8)

/-- Native selected-block left carrier, uniform in the physical target,
signed axis, and radial source parameter. -/
def fixedAxisSplitUniformTargetLeftCommonCarrierNative
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k) :
    Set (NPointDomain d (i.toGap.val + 1)) :=
  ⋃ a : osiiAxisPairIndex d,
    (fun p =>
      osiiStep4MultiGapRotatedFrozenLeftCarrierMap
        d k D.T p.1 (i.toGap, a) p.2) ''
      (D.fixedAxisAllSplitTargetLogRealCarrier ×ˢ
        osiiStep4MultiGapSelectedLeftCommonCarrier
          d k rho center i.toGap)

/-- Native selected-block right carrier, uniform in the physical target,
signed axis, and radial source parameter. -/
def fixedAxisSplitUniformTargetRightCommonCarrierNative
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k) :
    Set (NPointDomain d (osiiStep4MultiGapAfterCount i.toGap + 1)) :=
  ⋃ a : osiiAxisPairIndex d,
    (fun p =>
      osiiStep4MultiGapRotatedFrozenRightCarrierMap
        d k D.T p.1 (i.toGap, a) p.2) ''
      (D.fixedAxisAllSplitTargetLogRealCarrier ×ˢ
        osiiStep4MultiGapSelectedRightCommonCarrier
          d k rho center i.toGap)

/-- Native difference-time projection of the uniform left absolute carrier.
-/
def fixedAxisSplitUniformTargetLeftTimeCarrierNative
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k) :
    Set (Fin (i.toGap.val + 1) -> Real) :=
  osiiStep4FullDifferenceTimeProjectionCLM d i.toGap.val ''
    D.fixedAxisSplitUniformTargetLeftCommonCarrierNative i

/-- Native difference-time projection of the uniform right absolute carrier.
-/
def fixedAxisSplitUniformTargetRightTimeCarrierNative
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k) :
    Set (Fin (osiiStep4MultiGapAfterCount i.toGap + 1) -> Real) :=
  osiiStep4FullDifferenceTimeProjectionCLM d
      (osiiStep4MultiGapAfterCount i.toGap) ''
    D.fixedAxisSplitUniformTargetRightCommonCarrierNative i

/-- Uniform left time carrier normalized to the exact generator arity. -/
def fixedAxisSplitUniformTargetLeftTimeCarrier
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k) :
    Set (Fin i.n -> Real) :=
  castFiniteTimeCarrier i.rotatedFrozenLeftArity
    (D.fixedAxisSplitUniformTargetLeftTimeCarrierNative i)

/-- Uniform right time carrier normalized to the exact generator arity. -/
def fixedAxisSplitUniformTargetRightTimeCarrier
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k) :
    Set (Fin i.m -> Real) :=
  castFiniteTimeCarrier i.rotatedFrozenRightArity
    (D.fixedAxisSplitUniformTargetRightTimeCarrierNative i)

/-- Native-arity physical left source in the common all-target source
universe. -/
def fixedAxisSplitUniformTargetLeftSourceNative
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : x ∈ D.fixedAxisAllSplitTargetLogRealCarrier)
    (a : osiiAxisPairIndex d)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource d (i.toGap.val + 1)
      (D.fixedAxisSplitUniformTargetLeftTimeCarrierNative i) := by
  let source := (D.toSelectedCommonSlopeData p.1 p.2
    ).rotatedFrozenLeftPositiveSource x (i.toGap, a)
  refine ⟨source, ?_⟩
  intro y hy
  refine ⟨y, ?_, rfl⟩
  obtain ⟨u, hu, rfl⟩ :=
    D.rotatedFrozenLeftSource_tsupport_subset_commonCarrier
      x (i.toGap, a) p hy
  exact Set.mem_iUnion_of_mem a ⟨(x, u), ⟨hx, hu⟩, rfl⟩

/-- Native-arity physical right source in the common all-target source
universe. -/
def fixedAxisSplitUniformTargetRightSourceNative
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : x ∈ D.fixedAxisAllSplitTargetLogRealCarrier)
    (a : osiiAxisPairIndex d)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource d
      (osiiStep4MultiGapAfterCount i.toGap + 1)
      (D.fixedAxisSplitUniformTargetRightTimeCarrierNative i) := by
  let source := (D.toSelectedCommonSlopeData p.1 p.2
    ).rotatedFrozenRightPositiveSource x (i.toGap, a)
  refine ⟨source, ?_⟩
  intro y hy
  refine ⟨y, ?_, rfl⟩
  obtain ⟨u, hu, rfl⟩ :=
    D.rotatedFrozenRightSource_tsupport_subset_commonCarrier
      x (i.toGap, a) p hy
  exact Set.mem_iUnion_of_mem a ⟨(x, u), ⟨hx, hu⟩, rfl⟩

/-- Physical left source normalized to the exact generator arity. -/
def fixedAxisSplitUniformTargetLeftSource
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : x ∈ D.fixedAxisAllSplitTargetLogRealCarrier)
    (a : osiiAxisPairIndex d)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource d i.n
      (D.fixedAxisSplitUniformTargetLeftTimeCarrier i) :=
  castUniformCompactTimeSource i.rotatedFrozenLeftArity
    (D.fixedAxisSplitUniformTargetLeftSourceNative i x hx a p)

/-- Physical right source normalized to the exact generator arity. -/
def fixedAxisSplitUniformTargetRightSource
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : x ∈ D.fixedAxisAllSplitTargetLogRealCarrier)
    (a : osiiAxisPairIndex d)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource d i.m
      (D.fixedAxisSplitUniformTargetRightTimeCarrier i) :=
  castUniformCompactTimeSource i.rotatedFrozenRightArity
    (D.fixedAxisSplitUniformTargetRightSourceNative i x hx a p)

end OSIIStep4MultiGapUniformCommonSlopeData
end OSReconstruction
