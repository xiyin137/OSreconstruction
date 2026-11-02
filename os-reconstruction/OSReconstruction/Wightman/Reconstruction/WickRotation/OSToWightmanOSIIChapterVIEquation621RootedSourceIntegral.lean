/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeometry
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621Recovery
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformEquation621Seed
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeBoundedRankInduction
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope

@[expose] public section

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
