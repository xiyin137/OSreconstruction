/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.GaussianSolidShift
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedLogarithmicDomains
















noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Scalar arguments whose outermost construction is analytic rather than
convex.  The convex-envelope step should start from these points. -/
inductive OSIIGeneratedScalarSeed :
    (k N : ℕ) -> (Fin k -> ℝ) -> Prop where
  | generatorMemSucc
      {k : ℕ} (i : GeneratorIndex k) (N : ℕ)
      (left : Fin i.n -> ℝ) (theta : ℝ) (right : Fin i.m -> ℝ)
      (hleft :
        OSIIGeneratedLogarithmicArgument .mixed i.n N left)
      (hright :
        OSIIGeneratedLogarithmicArgument .mixed i.m N right)
      (htheta : |theta| <= Real.pi / 2) :
      OSIIGeneratedScalarSeed k (N + 1)
        (osiiArgumentGeneratorPoint i left theta right)
  | mixedTailMemScalar
      (k N : ℕ) (x : Fin (k + 1) -> ℝ)
      (hx :
        OSIIGeneratedLogarithmicArgument .mixed (k + 1) N x) :
      OSIIGeneratedScalarSeed k N (Fin.tail x)

namespace OSIIGeneratedScalarSeed

end OSIIGeneratedScalarSeed

end OSIIChapterV
end OSReconstruction
