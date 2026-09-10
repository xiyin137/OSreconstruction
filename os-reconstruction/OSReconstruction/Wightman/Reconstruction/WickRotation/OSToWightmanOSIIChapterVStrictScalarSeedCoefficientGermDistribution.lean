import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientGerm

/-!
# Distribution-valued strict coefficient germs

The selected compactified MZ continuation is linear in the spatial Schwartz
test and obeys one uniform Schwartz seminorm bound throughout its logarithmic
domain. Pulling back through the local compactification inverse therefore
gives a weakly holomorphic family of genuine spatial distributions on the
complete coefficient germ.

The family is set to zero outside the germ domain, where no continuation
claim is made.
-/

noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace StrictScalarSeedCoefficientMZBoundData

variable
  {d : Nat} [NeZero d]
  {n k : Nat} [NeZero n]
  {A : OSIITimeContinuationStage d k}
  {S rho : Real}
  {P : SCV.StripCompactificationParameters S rho}
  {seed : Fin n -> Fin k -> Real}

/-- The coefficient germ is additive in the spatial Schwartz test at every
point of its domain. -/
theorem coefficientGerm_add
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (r : Fin n -> Complex)
    (hr : r ∈ osiiStrictCoefficientGermDomain P)
    (chi psi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    B.coefficientGerm (chi + psi) r =
      B.coefficientGerm chi r + B.coefficientGerm psi r :=
  B.extension_add chi psi hr.2

/-- The coefficient germ is complex homogeneous in the spatial Schwartz
test at every point of its domain. -/
theorem coefficientGerm_smul
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (r : Fin n -> Complex)
    (hr : r ∈ osiiStrictCoefficientGermDomain P)
    (c : Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    B.coefficientGerm (c • chi) r =
      c * B.coefficientGerm chi r :=
  B.extension_smul c chi hr.2

/-- Every point of the coefficient germ obeys the original compact-window
Schwartz seminorm bound. -/
theorem norm_coefficientGerm_le
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (r : Fin n -> Complex)
    (hr : r ∈ osiiStrictCoefficientGermDomain P)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖B.coefficientGerm chi r‖ <=
      B.constant *
        B.seminormIndices.sup
          (schwartzSeminormFamily Complex
            (Section43SpatialSpace d k) Complex) chi :=
  B.norm_extension_le chi _ hr.2

/-- The coefficient germ packaged pointwise as a spatial Schwartz
distribution. -/
noncomputable def coefficientGermDistribution
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (r : Fin n -> Complex) :
    OSIISpatialDistribution d k :=
  if hr : r ∈ osiiStrictCoefficientGermDomain P then
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := Complex)
      (fun chi => B.coefficientGerm chi r)
      (B.coefficientGerm_add r hr)
      (fun c chi => by
        simpa [smul_eq_mul] using
          B.coefficientGerm_smul r hr c chi)
      ⟨B.seminormIndices, B.constant, B.constant_pos.le,
        B.norm_coefficientGerm_le r hr⟩
  else
    0

/-- On the coefficient germ domain, the packaged distribution evaluates to
the selected scalar germ. -/
theorem coefficientGermDistribution_apply_of_mem
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (r : Fin n -> Complex)
    (hr : r ∈ osiiStrictCoefficientGermDomain P)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    B.coefficientGermDistribution r chi =
      B.coefficientGerm chi r := by
  rw [coefficientGermDistribution, dif_pos hr]
  rfl

/-- Every scalar pairing of the distribution-valued coefficient germ is
holomorphic on the coefficient germ domain. -/
theorem coefficientGermDistribution_weaklyHolomorphic
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    DifferentiableOn Complex
      (fun r => B.coefficientGermDistribution r chi)
      (osiiStrictCoefficientGermDomain P) :=
  (B.coefficientGerm_differentiableOn chi).congr
    (fun r hr =>
      B.coefficientGermDistribution_apply_of_mem r hr chi)

end StrictScalarSeedCoefficientMZBoundData
end OSIIChapterV
end OSReconstruction
