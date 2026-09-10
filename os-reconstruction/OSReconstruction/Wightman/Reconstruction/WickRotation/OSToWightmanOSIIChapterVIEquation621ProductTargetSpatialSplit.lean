/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetApproxIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedSelfPairProbeIdentification











noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace GeneratorIndex

open Section43ProductTimeApproximateIdentity

variable {k : Nat}

/-- The generator equation-`(6.29)` split precomposed by the exact target
coordinate involution. -/
def equation621TargetAdaptedSpatialSplitData
    (d : Nat) [NeZero d] (i : GeneratorIndex k) :
    OSIIEquation621SpatialSplitData d k
      ((i.n - 1) + ((i.n - 1) + 1))
      ((i.m - 1) + ((i.m - 1) + 1)) where
  leftPoint := fun x =>
    i.leftReflectedSelfPairSpatialPoint d
      (equation621SplitTargetSpatialPoint i x)
  rightPoint := fun x =>
    i.rightReflectedSelfPairSpatialPoint d
      (equation621SplitTargetSpatialPoint i x)
  norm_leftPoint_le := fun x =>
    (i.norm_leftReflectedSelfPairSpatialPoint_le d
      (equation621SplitTargetSpatialPoint i x)).trans
        (norm_equation621SplitTargetSpatialPoint_le i x)
  norm_rightPoint_le := fun x =>
    (i.norm_rightReflectedSelfPairSpatialPoint_le d
      (equation621SplitTargetSpatialPoint i x)).trans
        (norm_equation621SplitTargetSpatialPoint_le i x)

@[simp]
theorem equation621TargetAdaptedSpatialSplitData_leftPoint
    (d : Nat) [NeZero d] (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    (i.equation621TargetAdaptedSpatialSplitData d).leftPoint x =
      i.leftReflectedSelfPairSpatialPoint d
        (equation621SplitTargetSpatialPoint i x) := rfl

@[simp]
theorem equation621TargetAdaptedSpatialSplitData_rightPoint
    (d : Nat) [NeZero d] (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    (i.equation621TargetAdaptedSpatialSplitData d).rightPoint x =
      i.rightReflectedSelfPairSpatialPoint d
        (equation621SplitTargetSpatialPoint i x) := rfl

end GeneratorIndex

namespace Section43ProductTimeApproximateIdentity

/-- At a common target coordinate `x`, the exact coherent product row is
obtained by evaluating its old center parameter at the target involution. -/
theorem equation621SplitTargetSpatialApproxIdentity_section43Probe_adapted_eq
    {d k : Nat} [NeZero d] [NeZero k]
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    (P.equation621SplitTargetSpatialApproxIdentity i).section43Probe x N =
      AnchoredPacketTimeShellFamilyData.RootedA0BlockContinuousTranslationData.absoluteProductTargetReducedSpatialTest
        P i (equation621SplitTargetSpatialPoint i x) N := by
  have h :=
    P.equation621SplitTargetSpatialApproxIdentity_section43Probe_eq
      i (equation621SplitTargetSpatialPoint i x) N
  rw [equation621SplitTargetSpatialPoint_involutive] at h
  exact h

namespace AnchoredPacketTimeShellFamilyData
namespace RootedA0BlockContinuousTranslationData

variable {d k : Nat} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

/-- The left arbitrary block test used by the target-adapted product row. -/
noncomputable def targetAdaptedLeftBlockSpatialTest
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) (N : Nat) :
    SchwartzMap (Section43SpatialSpace d ((i.n - 1) + 1)) Complex :=
  positiveBlockSpatialTest (d := d) i.hn
    (absoluteProductTargetLeftSpatialTest P i
      (equation621SplitTargetSpatialPoint i x) N)

/-- The right arbitrary block test used by the target-adapted product row. -/
noncomputable def targetAdaptedRightBlockSpatialTest
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) (N : Nat) :
    SchwartzMap (Section43SpatialSpace d ((i.m - 1) + 1)) Complex :=
  positiveBlockSpatialTest (d := d) i.hm
    (absoluteProductTargetRightSpatialTest P i
      (equation621SplitTargetSpatialPoint i x) N)

/-- The coherent left block probe is literally the arbitrary left test used
by the rooted product target row. -/
theorem generatorLeftBlockProbe_eq_positiveTargetTest
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    (P.generatorLeftBlockProductApproxIdentity i
      ).toEquation621SpatialApproxIdentity.section43Probe
        (generatorLeftBlockSpatialPoint d i x) N =
      positiveBlockSpatialTest (d := d) i.hn
        (absoluteProductTargetLeftSpatialTest P i x N) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  cases n with
  | zero => omega
  | succ n =>
      rw [P.generatorLeftBlock_section43Probe_eq_spatialProduct]
      simp [absoluteProductTargetLeftSpatialTest, positiveBlockSpatialTest]
      symm
      apply cast_eq_iff_heq.mpr
      rfl

/-- The coherent right block probe is literally the arbitrary right test used
by the rooted product target row. -/
theorem generatorRightBlockProbe_eq_positiveTargetTest
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    (P.generatorRightBlockProductApproxIdentity i
      ).toEquation621SpatialApproxIdentity.section43Probe
        (generatorRightBlockSpatialPoint d i x) N =
      positiveBlockSpatialTest (d := d) i.hm
        (absoluteProductTargetRightSpatialTest P i x N) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  cases m with
  | zero => omega
  | succ m =>
      rw [P.generatorRightBlock_section43Probe_eq_spatialProduct]
      simp [absoluteProductTargetRightSpatialTest, positiveBlockSpatialTest]
      symm
      apply cast_eq_iff_heq.mpr
      rfl

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
