import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEReflectionPositivity

/-!
# R→E Reflection Positivity Compatibility

This downstream file exposes the proved R→E reflection-positivity theorem under
Schwinger-axiom-facing names.  It deliberately sits after both
`SchwingerAxioms.lean` and `RToEReflectionPositivity.lean`: importing the R→E
lane directly into `SchwingerAxioms.lean` would create a cycle through the
OS→Wightman files.
-/

noncomputable section

open scoped Topology FourierTransform BigOperators
open Set MeasureTheory Filter

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Reflection positivity for the Wick-restricted Schwinger family, routed
through the completed R→E compact approximation and Section 4.3
spectral-positivity bridge.

This theorem carries the historical public name.  It lives downstream of
`SchwingerAxioms.lean` because the proof imports the Section 4.3 R→E lane,
which would create a cycle if imported into `SchwingerAxioms.lean` itself. -/
theorem schwingerExtension_os_reflection_positive_from_spectralLaplace
    (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n,
      tsupport ((F.funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 :=
  rToE_schwingerExtension_os_positivity Wfn F hsupp

/-- Compatibility alias for callers that want the explicitly R→E-suffixed
name. -/
theorem schwingerExtension_os_reflection_positive_from_spectralLaplace_rToE
    (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n,
      tsupport ((F.funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 :=
  schwingerExtension_os_reflection_positive_from_spectralLaplace Wfn F hsupp

/-- Compatibility alias for the historical Schwinger-extension positivity name,
available downstream of the R→E proof lane. -/
theorem schwingerExtension_os_positivity
    (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n,
      tsupport ((F.funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 :=
  schwingerExtension_os_reflection_positive_from_spectralLaplace Wfn F hsupp

/-- Explicitly R→E-suffixed alias for
`schwingerExtension_os_positivity`. -/
theorem schwingerExtension_os_positivity_rToE
    (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n,
      tsupport ((F.funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 :=
  schwingerExtension_os_positivity Wfn F hsupp

/-- Compatibility alias for the wick-rotated boundary-pairing positivity name,
available downstream of the R→E proof lane. -/
theorem wickRotatedBoundaryPairing_reflection_positive
    (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n,
      tsupport ((F.funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 :=
  schwingerExtension_os_reflection_positive_from_spectralLaplace Wfn F hsupp

/-- Explicitly R→E-suffixed alias for
`wickRotatedBoundaryPairing_reflection_positive`. -/
theorem wickRotatedBoundaryPairing_reflection_positive_rToE
    (Wfn : WightmanFunctions d)
    (F : BorchersSequence d)
    (hsupp : ∀ n,
      tsupport ((F.funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 :=
  wickRotatedBoundaryPairing_reflection_positive Wfn F hsupp

end OSReconstruction
