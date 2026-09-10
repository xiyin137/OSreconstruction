/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientSegmentGerm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientAmbientAtlas





















open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

theorem exists_real_strictScalarSeedCoefficient_preimage
    {n k : Nat}
    (seed : Fin n -> Fin k -> Real)
    (hsurj :
      Function.Surjective
        (osiiStrictScalarSeedCoefficientMap seed))
    (x : Fin k -> Real) :
    ∃ v : Fin n -> Real,
      osiiStrictScalarSeedCoefficientMap seed
          (fun i => (v i : Complex)) =
        fun j => (x j : Complex) := by
  obtain ⟨q, hq⟩ :=
    hsurj (fun j => (x j : Complex))
  refine ⟨fun i => (q i).re, ?_⟩
  funext j
  apply Complex.ext
  · have hj :=
      congrArg Complex.re (congrFun hq j)
    simpa [osiiStrictScalarSeedCoefficientMap] using hj
  · simp [osiiStrictScalarSeedCoefficientMap]

theorem nonempty_strictCoefficientTargetConvexChartData_of_segment_subset
    {n : Nat} {S rho : Real}
    {P : SCV.StripCompactificationParameters S rho}
    {r0 : Fin n -> Complex}
    (hsegment :
      segment Real 0 r0 ⊆
        osiiStrictCoefficientGermDomain P) :
    Nonempty (StrictCoefficientTargetConvexChartData P r0) := by
  have hcompact :
      IsCompact (segment Real 0 r0) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨r, hr, hthick⟩ :=
    hcompact.exists_thickening_subset_open
      (isOpen_osiiStrictCoefficientGermDomain P)
      hsegment
  exact
    ⟨{
      domain := Metric.thickening r (segment Real 0 r0)
      domain_open := Metric.isOpen_thickening
      domain_convex :=
        (convex_segment (0 : Fin n -> Complex) r0).thickening r
      zero_mem :=
        Metric.self_subset_thickening hr _
          (left_mem_segment Real 0 r0)
      target_mem :=
        Metric.self_subset_thickening hr _
          (right_mem_segment Real 0 r0)
      domain_subset := hthick }⟩

namespace StrictGeneratedScalarLogarithmicTargetIndex

end StrictGeneratedScalarLogarithmicTargetIndex

end OSIIChapterV
end OSReconstruction
