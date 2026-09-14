/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIPositiveTimeHilbertRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51AxisPair
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.SCV.Osgood
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIMZFlatTubeEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProductDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent











noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Principal-log coordinate of the physical axis-pair coefficient chart. -/
def osiiAxisPairLogCoeffMap
    (T : ℝ) (ξ : Fin (d + 1) → ℝ) (ζ : Fin (d + 1) → ℂ) :
    osiiAxisPairIndex d → ℂ :=
  fun a => Complex.log (osiiAxisPairCoeffMap T ξ ζ a)

/-- On a positive real coefficient chart, principal logarithms are exactly
the real logarithmic embedding used by the sourcewise MZ family. -/
theorem osiiAxisPairLogCoeffMap_real_eq_embed
    (T : ℝ)
    (ξ ζ : Fin (d + 1) → ℝ)
    (hcoeff_pos :
      ∀ a : osiiAxisPairIndex d,
        0 < (osiiAxisPairCoeffMap T ξ
          (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re) :
    osiiAxisPairLogCoeffMap T ξ
        (fun ν : Fin (d + 1) => (ζ ν : ℂ)) =
      osiiAxisPairLogRealEmbed
        (fun a =>
          Real.log
            (osiiAxisPairCoeffMap T ξ
              (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re) := by
  funext a
  have him :
      (osiiAxisPairCoeffMap T ξ
        (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).im = 0 := by
    cases ha : a.2 <;>
      simp [osiiAxisPairCoeffMap, osiiAxisPairCoeff,
        Complex.div_im, ha]
  have hreal :
      osiiAxisPairCoeffMap T ξ
          (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a =
        ((osiiAxisPairCoeffMap T ξ
          (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [him]
  rw [osiiAxisPairLogCoeffMap, hreal]
  exact (Complex.ofReal_log (le_of_lt (hcoeff_pos a))).symm

end OSReconstruction
