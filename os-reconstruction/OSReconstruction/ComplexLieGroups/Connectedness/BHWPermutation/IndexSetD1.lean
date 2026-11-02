/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
public import OSReconstruction.ComplexLieGroups.D1OrbitSet

@[expose] public section

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Permutation action on particle labels. -/
def permAct {n d : ℕ} (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k => z (σ k)

end BHW
