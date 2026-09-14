/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedSourceIntegral












noncomputable section

open Complex Filter MeasureTheory Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

/-- Generator presentation with a one-particle left endpoint and a
nontrivial right block. -/
def equation621LeftEndpointGeneratorIndex
    {k : Nat}
    (qRight : Nat)
    (hindex : k = 1 + (qRight + 2) - 1) :
    GeneratorIndex k where
  n := 1
  m := qRight + 2
  hn := le_rfl
  hm := by omega
  hnm := hindex

/-- Generator presentation with a nontrivial left block and a one-particle
right endpoint. -/
def equation621RightEndpointGeneratorIndex
    {k : Nat}
    (qLeft : Nat)
    (hindex : k = (qLeft + 2) + 1 - 1) :
    GeneratorIndex k where
  n := qLeft + 2
  m := 1
  hn := by omega
  hm := le_rfl
  hnm := hindex

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
