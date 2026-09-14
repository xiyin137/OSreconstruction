/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicArgumentDomains














noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The Chapter V split at the first chronological gap. Its reflected-left
block is empty and its right block contains all remaining gaps. -/
def firstBridgeGeneratorIndex (k : ℕ) : GeneratorIndex (k + 1) :=
  GeneratorIndex.ofGap ⟨0, Nat.succ_pos k⟩

@[simp]
theorem firstBridgeGeneratorIndex_toGap (k : ℕ) :
    (firstBridgeGeneratorIndex k).toGap = ⟨0, Nat.succ_pos k⟩ := by
  simp [firstBridgeGeneratorIndex]

/-- At the first split, the paper's generator argument vector is a bridge
angle followed by the tail of the mixed right-block vector. -/
theorem osiiArgumentGeneratorPoint_firstBridge
    (k : ℕ)
    (left : Fin 1 → ℝ)
    (θ : ℝ)
    (right : Fin (k + 1) → ℝ) :
    osiiArgumentGeneratorPoint
        (firstBridgeGeneratorIndex k) left θ right =
      Fin.cons θ (Fin.tail right) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [osiiArgumentGeneratorPoint, firstBridgeGeneratorIndex]
  · simp [osiiArgumentGeneratorPoint, firstBridgeGeneratorIndex]
    change right ⟨i.val + 1, by omega⟩ = right i.succ
    apply congrArg right
    apply Fin.ext
    rfl

end OSIIChapterV
end OSReconstruction
