/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SplitGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubGeometry










noncomputable section

open Complex Set Filter
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData





/-- Cauchy center of the reflected left Hilbert field at a rooted parent
point. -/
def equation621RootedLeftCenter
    {k : Nat}
    (i : GeneratorIndex k)
    (anchor : Fin k -> Real)
    (w : OSIITimeGapSpace k) :
    Fin (i.n - 1) -> Complex :=
  fun a =>
    -star ((generatorChronologicalParameterComplexCLE i
      (w - osiiPositiveRealTimeEmbed anchor)) (i.leftGlobalIndex a))

/-- Cauchy center of the right Hilbert field at a rooted parent point. -/
def equation621RootedRightCenter
    {k : Nat}
    (i : GeneratorIndex k)
    (anchor : Fin k -> Real)
    (w : OSIITimeGapSpace k) :
    Fin (i.m - 1) -> Complex :=
  fun b =>
    (generatorChronologicalParameterComplexCLE i
      (w - osiiPositiveRealTimeEmbed anchor)) (i.rightGlobalIndex b)

@[simp]
theorem equation621RootedLeftCenter_apply
    {k : Nat}
    (i : GeneratorIndex k)
    (anchor : Fin k -> Real)
    (w : OSIITimeGapSpace k)
    (a : Fin (i.n - 1)) :
    equation621RootedLeftCenter i anchor w a =
      star (w (i.leftGlobalIndex a) - anchor (i.leftGlobalIndex a)) := by
  have ha : i.leftGlobalIndex a < i.toGap := by
    change (Fin.rev a).val < i.n - 1
    exact (Fin.rev a).isLt
  simp [equation621RootedLeftCenter,
    generatorChronologicalParameterComplexCLE, ha,
    osiiPositiveRealTimeEmbed]

@[simp]
theorem equation621RootedRightCenter_apply
    {k : Nat}
    (i : GeneratorIndex k)
    (anchor : Fin k -> Real)
    (w : OSIITimeGapSpace k)
    (b : Fin (i.m - 1)) :
    equation621RootedRightCenter i anchor w b =
      w (i.rightGlobalIndex b) - anchor (i.rightGlobalIndex b) := by
  have hb : ¬i.rightGlobalIndex b < i.toGap := by
    change ¬i.n + b.val < i.n - 1
    omega
  simp [equation621RootedRightCenter,
    generatorChronologicalParameterComplexCLE, hb,
    osiiPositiveRealTimeEmbed]

/-- Real-part sum of the centered reflected-left parameter. -/
theorem sum_re_equation621RootedLeftCenter
    {k : Nat}
    (i : GeneratorIndex k)
    (anchor : Fin k -> Real)
    (w : OSIITimeGapSpace k) :
    (∑ a : Fin (i.n - 1),
        (equation621RootedLeftCenter i anchor w a).re) =
      (∑ a : Fin (i.n - 1), (w (i.leftGlobalIndex a)).re) -
        ∑ a : Fin (i.n - 1), anchor (i.leftGlobalIndex a) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  simp

/-- Real-part sum of the centered right parameter. -/
theorem sum_re_equation621RootedRightCenter
    {k : Nat}
    (i : GeneratorIndex k)
    (anchor : Fin k -> Real)
    (w : OSIITimeGapSpace k) :
    (∑ b : Fin (i.m - 1),
        (equation621RootedRightCenter i anchor w b).re) =
      (∑ b : Fin (i.m - 1), (w (i.rightGlobalIndex b)).re) -
        ∑ b : Fin (i.m - 1), anchor (i.rightGlobalIndex b) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  simp



theorem sum_rootedLeftBlockAnchor
    {d k : Nat} [NeZero d] [NeZero k]
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    (∑ j : Fin ((i.n - 1) + 1), A.rootedLeftBlockAnchor i j) =
      anchor i.bridgeGlobalIndex / 3 +
        ∑ a : Fin (i.n - 1), anchor (i.leftGlobalIndex a) := by
  rw [Fin.sum_univ_succ]
  rfl

theorem sum_rootedRightBlockAnchor
    {d k : Nat} [NeZero d] [NeZero k]
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    (∑ j : Fin ((i.m - 1) + 1), A.rootedRightBlockAnchor i j) =
      anchor i.bridgeGlobalIndex / 3 +
        ∑ b : Fin (i.m - 1), anchor (i.rightGlobalIndex b) := by
  rw [Fin.sum_univ_succ]
  rfl



end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
