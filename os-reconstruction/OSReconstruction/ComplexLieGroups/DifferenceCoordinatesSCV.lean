/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.ComplexLieGroups.DifferenceCoordinates
import OSReconstruction.SCV.TubeDomainExtension

noncomputable section

open Complex

namespace BHW

variable {d n : ℕ}

/-- `SCV.TubeDomain` membership for flattened configurations is exactly
    the flattened-imaginary-part cone condition. -/
theorem mem_tubeDomain_flatProductForwardConeReal
    (ξ : Fin n → Fin (d + 1) → ℂ) :
    flattenCfg n d ξ ∈ SCV.TubeDomain (FlatProductForwardConeReal d n) ↔
      (fun i => (flattenCfg n d ξ i).im) ∈ FlatProductForwardConeReal d n := by
  rfl

/-- Flattened difference-coordinate chart map. -/
def toDiffFlat (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → (Fin (n * (d + 1)) → ℂ) :=
  fun z => flattenCfg n d (diffCoordEquiv n d z)

/-- Inverse chart from flattened difference coordinates back to configurations. -/
def fromDiffFlat (n d : ℕ) :
    (Fin (n * (d + 1)) → ℂ) → (Fin n → Fin (d + 1) → ℂ) :=
  fun u => (diffCoordEquiv n d).symm (unflattenCfg n d u)

lemma toDiffFlat_fromDiffFlat (n d : ℕ) (u : Fin (n * (d + 1)) → ℂ) :
    toDiffFlat n d (fromDiffFlat n d u) = u := by
  unfold toDiffFlat fromDiffFlat
  simp [flatten_unflatten_cfg]

lemma fromDiffFlat_toDiffFlat (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ) :
    fromDiffFlat n d (toDiffFlat n d z) = z := by
  unfold toDiffFlat fromDiffFlat
  simp [unflatten_flatten_cfg]

end BHW
