/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialEndpointSeminorm








noncomputable section

namespace OSReconstruction

/-- Extract the Section 4.3 basepoint-time and consecutive-gap coordinates
from an absolute `(k+1)`-point configuration. -/
noncomputable def osiiStep4FullDifferenceTimeProjectionCLM
    (d k : Nat) [NeZero d] :
    NPointDomain d (k + 1) →L[Real] (Fin (k + 1) → Real) :=
  (section43QTimeCLM d (k + 1)).comp
    (section43DiffCoordRealCLE d (k + 1)).toContinuousLinearMap

@[simp] theorem osiiStep4FullDifferenceTimeProjectionCLM_apply
    (d k : Nat) [NeZero d]
    (x : NPointDomain d (k + 1)) :
    osiiStep4FullDifferenceTimeProjectionCLM d k x =
      section43QTime (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1) x) :=
  rfl

end OSReconstruction
