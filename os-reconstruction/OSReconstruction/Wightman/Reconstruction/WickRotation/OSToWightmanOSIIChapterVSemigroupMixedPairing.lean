/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMixedHilbertPairing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup









noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- The Chapter V mixed pairing with the complex OS time semigroup in the
distinguished bridge coordinate. -/
def osiiSemigroupMixedHilbertPairing
    {E₁ E₂ : Type*}
    [Star E₁]
    (OS : OsterwalderSchraderAxioms d)
    (left : E₁ → OSHilbertSpace OS)
    (right : E₂ → OSHilbertSpace OS) :
    ℂ × (E₁ × E₂) → ℂ :=
  bridgedMixedHilbertPairing
    (osiiOriginalOSHilbertComplex OS)
    left right

/-- Holomorphy of the semigroup-bridged Chapter V pairing on the product of
the bridge right half-plane with the two vector-field domains. -/
theorem differentiableOn_osiiSemigroupMixedHilbertPairing
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [StarAddMonoid E₁]
    [StarModule ℂ E₁] [ContinuousStar E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
    (OS : OsterwalderSchraderAxioms d)
    {U : Set E₁} {V : Set E₂}
    (hU : IsOpen U) (hV : IsOpen V)
    {left : E₁ → OSHilbertSpace OS}
    {right : E₂ → OSHilbertSpace OS}
    (hleft : DifferentiableOn ℂ left U)
    (hright : DifferentiableOn ℂ right V) :
    DifferentiableOn ℂ
      (osiiSemigroupMixedHilbertPairing OS left right)
      (bridgedMixedHilbertPairingDomain
        {z : ℂ | 0 < z.re} U V) := by
  exact
    differentiableOn_bridgedMixedHilbertPairing
      (isOpen_lt continuous_const Complex.continuous_re)
      hU hV
      (osiiOriginalOSHilbertComplex OS)
      (continuousOn_osiiOriginalOSHilbertComplex_jointly OS)
      (differentiableOn_osiiOriginalOSHilbertComplex_inner OS)
      hleft hright

end OSIIChapterV
end OSReconstruction
