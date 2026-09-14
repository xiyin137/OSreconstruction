/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertVectorField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedRealEdge














noncomputable section

open Complex Filter Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace PositiveTimeSourceTaylorFamily

variable {d n k : ℕ} [NeZero d]

/-- The fixed source Taylor family consisting of normalized multi-derivatives
of one positive-time source. -/
def ofNormalizedDerivatives
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin k → NPointDomain d n) :
    PositiveTimeSourceTaylorFamily d n k where
  coefficient α :=
    ⟨normalizedSourceMultiDerivative directions α f.1,
      (tsupport_normalizedSourceMultiDerivative_subset
        directions α f.1).trans f.2⟩

/-- Normalized source multi-differentiation preserves the positive-time
submodule and is continuous linear there. -/
noncomputable def normalizedDerivativeCLM
    (directions : Fin k → NPointDomain d n)
    (α : Fin k → ℕ) :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ]
      euclideanPositiveTimeSubmodule (d := d) n :=
  ((normalizedSourceMultiDerivativeCLM directions α).comp
      (euclideanPositiveTimeSubmodule (d := d) n).subtypeL).codRestrict
    (euclideanPositiveTimeSubmodule (d := d) n)
    (fun f => by
      change
        tsupport
            (((normalizedSourceMultiDerivativeCLM directions α).comp
              (euclideanPositiveTimeSubmodule (d := d) n).subtypeL) f :
              NPointDomain d n → ℂ) ⊆
          OrderedPositiveTimeRegion d n
      simpa using
        (tsupport_normalizedSourceMultiDerivative_subset
          directions α f.1).trans f.2)

@[simp]
theorem normalizedDerivativeCLM_apply
    (directions : Fin k → NPointDomain d n)
    (α : Fin k → ℕ)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    normalizedDerivativeCLM directions α f =
      (ofNormalizedDerivatives f directions).coefficient α := by
  apply Subtype.ext
  simp [normalizedDerivativeCLM, ofNormalizedDerivatives]

@[simp] theorem coefficientData_ofNormalizedDerivatives
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin k → NPointDomain d n)
    (increment : Fin k → ℂ) :
    (ofNormalizedDerivatives f directions).coefficientData increment =
      PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
        f directions increment :=
  rfl

@[simp] theorem homogeneousSource_ofNormalizedDerivatives
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin k → NPointDomain d n)
    (increment : Fin k → ℂ)
    (p : ℕ) :
    (ofNormalizedDerivatives f directions).homogeneousSource increment p =
      (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
        f directions increment).homogeneousSource p :=
  rfl

end PositiveTimeSourceTaylorFamily

end OSIIChapterV
end OSReconstruction
