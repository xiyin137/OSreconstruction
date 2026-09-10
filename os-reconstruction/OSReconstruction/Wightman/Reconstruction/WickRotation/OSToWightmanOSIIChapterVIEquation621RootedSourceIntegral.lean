/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621Recovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformEquation621Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeBoundedRankInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope











noncomputable section

open Complex MeasureTheory Set Filter
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

/-- The generator index determined by two nontrivial lower blocks, written
in the natural source ranks `qLeft` and `qRight`. -/
def equation621NontrivialGeneratorIndex
    {k : Nat}
    (qLeft qRight : Nat)
    (hindex : k = (qLeft + 2) + (qRight + 2) - 1) :
    GeneratorIndex k where
  n := qLeft + 2
  m := qRight + 2
  hn := by omega
  hm := by omega
  hnm := hindex

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
