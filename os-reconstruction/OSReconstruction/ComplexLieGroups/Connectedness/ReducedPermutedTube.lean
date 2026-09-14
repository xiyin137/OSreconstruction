/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesReduced
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Reduced PET defined as the image of absolute PET under the reduced
    difference map. This is the clean reduced domain available before a converse
    lift from reduced sectors back to absolute sectors is constructed. -/
def reducedPermutedExtendedTube (d n : ℕ) :
    Set (Fin (n - 1) → Fin (d + 1) → ℂ) :=
  reducedDiffMap n d '' PermutedExtendedTube d n

theorem reducedPermutedExtendedTube_isPreconnected [NeZero d] :
    IsPreconnected (reducedPermutedExtendedTube d n) := by
  exact permutedExtendedTube_isPreconnected.image _ (reducedDiffMap n d).continuous.continuousOn

theorem reducedPermutedExtendedTube_nonempty [NeZero d] :
    (reducedPermutedExtendedTube d n).Nonempty := by
  rcases (forwardTube_nonempty (d := d) (n := n)) with ⟨z, hz⟩
  refine ⟨reducedDiffMap n d z, ?_⟩
  exact ⟨z, forwardTube_subset_permutedExtendedTube hz, rfl⟩

theorem isConnected_reducedPermutedExtendedTube [NeZero d] :
    IsConnected (reducedPermutedExtendedTube d n) :=
  ⟨reducedPermutedExtendedTube_nonempty (d := d) (n := n),
    reducedPermutedExtendedTube_isPreconnected (d := d) (n := n)⟩

end BHW
