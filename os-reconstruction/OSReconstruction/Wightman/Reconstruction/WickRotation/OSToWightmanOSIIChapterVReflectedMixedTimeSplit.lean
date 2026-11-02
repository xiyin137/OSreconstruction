/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Init
public import OSReconstruction.SCV.DistributionalEOWCutoff
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedMixedMovingSlice
public import Mathlib.Topology.CompactOpen
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTargetAdaptedMovingSliceCoverage

@[expose] public section

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Left absolute-time block associated with a reduced reflected time. -/
def reflectedMixedLeftTimeSplit
    {k : Nat}
    (tau : Fin (k + (k + 1)) -> Real) :
    Fin (k + 1) -> Real :=
  Fin.cases
    (tau (Fin.natAdd k (0 : Fin (k + 1))) / 2)
    (fun i => tau (Fin.castAdd (k + 1) (Fin.rev i)))

/-- Right absolute-time block associated with a reduced reflected time. -/
def reflectedMixedRightTimeSplit
    {k : Nat}
    (tau : Fin (k + (k + 1)) -> Real) :
    Fin (k + 1) -> Real :=
  Fin.cases
    (tau (Fin.natAdd k (0 : Fin (k + 1))) / 2)
    (fun i => tau (Fin.natAdd k i.succ))

end OSIIChapterV
end OSReconstruction
