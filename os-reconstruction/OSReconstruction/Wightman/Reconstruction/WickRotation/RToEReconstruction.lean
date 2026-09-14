import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEIntegralClustering
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEWickPair
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEReflectionPositivity

/-!
# Full R-to-E Reconstruction

The literal Wick-restricted Schwinger family satisfies every field of the
unchanged OS record on zero-diagonal Schwartz tests. Its analytic kernel also
recovers the original Wightman distributions on full Schwartz space.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace OSReconstruction
variable {d : ℕ} [NeZero d]

/-- All OS axioms for the actual Schwinger constructor, without extra input. -/
def constructOsterwalderSchraderAxioms (Wfn : WightmanFunctions d) :
    OsterwalderSchraderAxioms d where
  S := constructSchwingerFunctions Wfn
  E0_tempered := constructedSchwinger_tempered_zeroDiagonal Wfn
  E0_linear := constructedZeroDiagonalSchwinger_linear Wfn
  E0_reality := by
    intro n f g hfg
    have hg : g.1 = f.1.osConj := by
      ext x
      simpa only [SchwartzNPoint.osConj_apply] using hfg x
    change starRingEnd ℂ (wickRotatedBoundaryPairing Wfn n f.1) =
      wickRotatedBoundaryPairing Wfn n g.1
    rw [hg]
    exact wickRotatedBoundaryPairing_reality Wfn n f.1
  E1_translation_invariant := fun n a f g hfg =>
    wickRotatedBoundaryPairing_translation_invariant Wfn n a f.1 g.1 hfg
  E1_rotation_invariant := fun n R hR hdet f g hfg =>
    wickRotatedBoundaryPairing_rotation_invariant Wfn n R hR hdet f.1 g.1 hfg
  E2_reflection_positive := rToE_schwingerExtension_os_positivity Wfn
  E3_symmetric := fun n σ f g hfg =>
    wickRotatedBoundaryPairing_symmetric Wfn n σ f.1 g.1 hfg
  E4_cluster := fun _n _m f g ε hε => rToE_constructed_full_E4 Wfn f g ε hε

@[simp]
theorem constructOsterwalderSchraderAxioms_S (Wfn : WightmanFunctions d) :
    (constructOsterwalderSchraderAxioms Wfn).S = constructSchwingerFunctions Wfn := rfl

/-- The full OS record retains the original full-Schwartz Wightman boundary values. -/
theorem constructOsterwalderSchraderAxioms_isWickRotationPair (Wfn : WightmanFunctions d) :
    IsWickRotationPair (constructOsterwalderSchraderAxioms Wfn).S Wfn.W :=
  constructSchwingerFunctions_isWickRotationPair Wfn

/-- General-positive-dimension R-to-E reconstruction, pinned to the actual constructor. -/
theorem wightman_to_os_axioms (Wfn : WightmanFunctions d) :
    ∃ OS : OsterwalderSchraderAxioms d,
      OS.S = constructSchwingerFunctions Wfn ∧ IsWickRotationPair OS.S Wfn.W :=
  ⟨constructOsterwalderSchraderAxioms Wfn, rfl,
    constructOsterwalderSchraderAxioms_isWickRotationPair Wfn⟩

end OSReconstruction
