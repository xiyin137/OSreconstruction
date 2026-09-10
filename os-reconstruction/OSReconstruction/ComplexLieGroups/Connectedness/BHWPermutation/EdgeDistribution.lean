/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlow

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-- Permutations preserve the ambient product volume on `NPointDomain d n`. -/
theorem integral_perm_eq_self {n : ℕ} (σ : Equiv.Perm (Fin n))
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun k => x (σ k)) =
    ∫ x : NPointDomain d n, h x :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp' h

end BHW
