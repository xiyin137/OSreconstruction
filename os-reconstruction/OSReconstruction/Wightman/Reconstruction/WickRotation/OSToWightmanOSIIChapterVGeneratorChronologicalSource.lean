/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairChronologicalTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorCoordinates















noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

namespace GeneratorIndex

variable {k : ℕ} (i : GeneratorIndex k)

/-- The generator bridge is exactly its chronological gap index. -/
@[simp]
theorem bridgeGlobalIndex_eq_toGap :
    i.bridgeGlobalIndex = i.toGap := by
  apply Fin.ext
  rfl

/-- The two generator block arities contain exactly the global `k + 1`
points. -/
theorem pointArity_add :
    i.n + i.m = k + 1 := by
  have hn := i.hn
  have hm := i.hm
  have hnm := i.hnm
  omega

end GeneratorIndex

variable {d k : ℕ} [NeZero d] [NeZero k]

end OSIIChapterV
end OSReconstruction
