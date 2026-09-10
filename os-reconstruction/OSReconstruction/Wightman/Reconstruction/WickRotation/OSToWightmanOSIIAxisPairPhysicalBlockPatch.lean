/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairPhysicalChart
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.SCV.DistributionalEOWKernel
import OSReconstruction.SCV.DistributionalEOWKernelRecovery















noncomputable section

open Complex Topology
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d]

/-- Embed one real axis-pair logarithmic coordinate family for every
chronological displacement block. -/
def osiiAxisPairSimultaneousLogRealEmbed
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    Fin k → osiiAxisPairIndex d → ℂ :=
  fun i => osiiAxisPairLogRealEmbed (x i)

/-- One simultaneous physical patch, consisting of one positive-center
axis-pair chart for each chronological displacement block. -/
structure OSIIAxisPairPhysicalBlockPatch
    (d k : ℕ) [NeZero d] where
  slope : Fin k → ℝ
  center : Fin k → Fin (d + 1) → ℝ
  chart :
    ∀ i : Fin k,
      OSIIAxisPairPhysicalChart d (slope i) (center i)

namespace OSIIAxisPairPhysicalBlockPatch

/-- The finite product of the chosen one-block physical carriers. -/
def carrier
    (P : OSIIAxisPairPhysicalBlockPatch d k) :
    Set (Fin (k * (d + 1)) → ℂ) :=
  ⋂ i : Fin k,
    (fun z : Fin (k * (d + 1)) → ℂ => flatDiffBlock z i) ⁻¹'
      (P.chart i).carrier

/-- The simultaneous logarithmic coefficient map in flattened difference
coordinates. -/
def blockLogMap
    (P : OSIIAxisPairPhysicalBlockPatch d k)
    (z : Fin (k * (d + 1)) → ℂ) :
    Fin k → osiiAxisPairIndex d → ℂ :=
  fun i => (P.chart i).logMap (flatDiffBlock z i)

end OSIIAxisPairPhysicalBlockPatch

end OSReconstruction
