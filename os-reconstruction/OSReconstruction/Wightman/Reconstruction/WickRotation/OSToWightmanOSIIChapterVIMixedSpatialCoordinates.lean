import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRealEdgeRegularizedGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIPartialConvolutionKernel
import OSReconstruction.SCV.DistributionalEOWApproxIdentity

/-!
# OS II Chapter VI: mixed spatial coordinates

This module contains the neutral coordinate insertion used by both the
OS-built equation-(6.6) route and the legacy reduced-BVT comparison route.
-/

namespace OSReconstruction

/-- Insert fixed Euclidean time coordinates and free real spatial coordinates
in the block-major order used by the Chapter-VI radial regularizer. -/
def osiiStep4MixedSpatialRealPoint
    (d k : Nat)
    (tau : Fin k -> Real)
    (x : Fin (k * d) -> Real) :
    Fin (k * (d + 1)) -> Real :=
  fun q =>
    let p : Fin k × Fin (d + 1) := finProdFinEquiv.symm q
    Fin.cases (tau p.1)
      (fun j => x (finProdFinEquiv (p.1, j))) p.2

/-- Varying only the free spatial coordinates gives a continuous mixed-point
map. -/
theorem continuous_osiiStep4MixedSpatialRealPoint
    (d k : Nat)
    (tau : Fin k -> Real) :
    Continuous (osiiStep4MixedSpatialRealPoint d k tau) := by
  apply continuous_pi
  intro q
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
  cases mu using Fin.cases with
  | zero =>
      simpa [osiiStep4MixedSpatialRealPoint] using
        (continuous_const : Continuous (fun _x : Fin (k * d) -> Real => tau i))
  | succ j =>
      simpa [osiiStep4MixedSpatialRealPoint] using
        (continuous_apply (finProdFinEquiv (i, j)) :
          Continuous (fun x : Fin (k * d) -> Real =>
            x (finProdFinEquiv (i, j))))

/-- At fixed time, insertion into mixed spacetime coordinates preserves the
distance between free spatial centers. -/
theorem osiiStep4MixedSpatialRealPoint_dist
    (d k : Nat)
    (tau : Fin k -> Real)
    (x y : Fin (k * d) -> Real) :
    dist (osiiStep4MixedSpatialRealPoint d k tau x)
        (osiiStep4MixedSpatialRealPoint d k tau y) =
      dist x y := by
  simp only [dist_eq_norm]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).2
    intro q
    obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
    cases mu using Fin.cases with
    | zero =>
        simp [osiiStep4MixedSpatialRealPoint]
    | succ j =>
        simpa [osiiStep4MixedSpatialRealPoint] using
          (norm_le_pi_norm (x - y) (finProdFinEquiv (i, j)))
  · apply (pi_norm_le_iff_of_nonneg
      (norm_nonneg
        (osiiStep4MixedSpatialRealPoint d k tau x -
          osiiStep4MixedSpatialRealPoint d k tau y))).2
    intro q
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
    have h := norm_le_pi_norm
      (osiiStep4MixedSpatialRealPoint d k tau x -
        osiiStep4MixedSpatialRealPoint d k tau y)
      (finProdFinEquiv (i, Fin.succ j))
    simpa [osiiStep4MixedSpatialRealPoint] using h

/-- The real mixed-point embedding into the equation-(6.6) complex
coordinates is continuous in the free spatial center. -/
theorem continuous_osiiStep4MixedSpatialComplexRealPoint
    (d k : Nat)
    (tau : Fin k -> Real) :
    Continuous (fun x : Fin (k * d) -> Real =>
      osiiStep4ComplexOfRealImag
        (osiiStep4MixedSpatialRealPoint d k tau x) 0) := by
  apply continuous_pi
  intro q
  have hq : Continuous (fun x : Fin (k * d) -> Real =>
      osiiStep4MixedSpatialRealPoint d k tau x q) :=
    (continuous_apply q).comp
      (continuous_osiiStep4MixedSpatialRealPoint d k tau)
  convert Complex.continuous_ofReal.comp hq using 1 <;>
    funext a <;>
    apply Complex.ext <;>
    simp [osiiStep4ComplexOfRealImag, Complex.ofReal_def]

/-- The complex real embedding of a fixed-time mixed point preserves spatial
distance exactly. -/
theorem osiiStep4MixedSpatialComplexRealPoint_dist
    (d k : Nat)
    (tau : Fin k -> Real)
    (x y : Fin (k * d) -> Real) :
    dist
        (osiiStep4ComplexOfRealImag
          (osiiStep4MixedSpatialRealPoint d k tau x) 0)
        (osiiStep4ComplexOfRealImag
          (osiiStep4MixedSpatialRealPoint d k tau y) 0) =
      dist x y := by
  calc
    dist
        (osiiStep4ComplexOfRealImag
          (osiiStep4MixedSpatialRealPoint d k tau x) 0)
        (osiiStep4ComplexOfRealImag
          (osiiStep4MixedSpatialRealPoint d k tau y) 0) =
      ‖SCV.realEmbed
        (osiiStep4MixedSpatialRealPoint d k tau x -
          osiiStep4MixedSpatialRealPoint d k tau y)‖ := by
        rw [dist_eq_norm]
        congr 1
        ext q
        simp [osiiStep4ComplexOfRealImag, SCV.realEmbed]
    _ = ‖osiiStep4MixedSpatialRealPoint d k tau x -
          osiiStep4MixedSpatialRealPoint d k tau y‖ :=
      SCV.norm_realEmbed_eq _
    _ = dist
        (osiiStep4MixedSpatialRealPoint d k tau x)
        (osiiStep4MixedSpatialRealPoint d k tau y) := by
      rw [dist_eq_norm]
    _ = dist x y :=
      osiiStep4MixedSpatialRealPoint_dist d k tau x y

end OSReconstruction
