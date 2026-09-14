/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621Split
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertCauchyKernel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTimeChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTargetAdaptedMovingSliceCoverage











noncomputable section

open Complex
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV



/-- The reflected reduced-time displacement has zero bridge coordinate and
negates both `r`-coordinate blocks.  Reversal of the left block does not
change its sum. -/
theorem sum_reflectedReducedTimeDisplacement
    {r : Nat} (u : Fin (r + r) -> Complex) :
    (∑ j : Fin (r + (r + 1)), reflectedReducedTimeDisplacement u j) =
      -(∑ j : Fin (r + r), u j) := by
  rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_succ
    (fun j : Fin (r + 1) =>
      reflectedReducedTimeDisplacement u (Fin.natAdd r j))]
  simp only [reflectedReducedTimeDisplacement_left,
    reflectedReducedTimeDisplacement_bridge,
    reflectedReducedTimeDisplacement_right,
    Finset.sum_neg_distrib, zero_add]
  have hrev :
      (∑ i : Fin r, u (Fin.castAdd r (Fin.rev i))) =
        ∑ i : Fin r, u (Fin.castAdd r i) := by
    simpa using (Equiv.sum_comp Fin.revPerm
      (fun i : Fin r => u (Fin.castAdd r i)))
  rw [hrev]
  rw [Fin.sum_univ_add (fun j : Fin (r + r) => u j)]
  ring

/-- Complex-linear form of `sum_reflectedReducedTimeDisplacement`. -/
theorem sum_reflectedReducedTimeDisplacementCLM
    {r : Nat} (u : Fin (r + r) -> Complex) :
    (∑ j : Fin (r + (r + 1)),
        reflectedReducedTimeDisplacementCLM r u j) =
      -(∑ j : Fin (r + r), u j) := by
  rw [reflectedReducedTimeDisplacementCLM_apply]
  exact sum_reflectedReducedTimeDisplacement u

/-- The sum of a reflected Cauchy center is twice the real part of the
original center sum, written without choosing real coordinates. -/
theorem sum_reflectedCauchyCenter
    {r : Nat} (center : Fin r -> Complex) :
    (∑ j : Fin (r + r), reflectedCauchyCenter center j) =
      starRingEnd Complex (∑ i : Fin r, center i) +
        ∑ i : Fin r, center i := by
  rw [Fin.sum_univ_add]
  simp only [reflectedCauchyCenter_left, reflectedCauchyCenter_right,
    map_sum]

/-- The three rooted generator blocks partition the global time-gap sum.
The left block is reversed by `leftGlobalIndex`, which does not change its
sum. -/
theorem GeneratorIndex.sum_eq_left_add_bridge_add_right
    {k : Nat}
    (i : GeneratorIndex k)
    (w : Fin k -> Complex) :
    (∑ j : Fin k, w j) =
      (∑ a : Fin (i.n - 1), w (i.leftGlobalIndex a)) +
        w i.bridgeGlobalIndex +
          ∑ b : Fin (i.m - 1), w (i.rightGlobalIndex b) := by
  have hk : k = (i.n - 1) + i.m := by
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega
  calc
    (∑ j : Fin k, w j) =
        ∑ j : Fin ((i.n - 1) + i.m),
          w ((finCongr hk).symm j) := by
      symm
      simpa using (Equiv.sum_comp (finCongr hk).symm w)
    _ = (∑ a : Fin (i.n - 1), w (i.leftGlobalIndex a)) +
          w i.bridgeGlobalIndex +
            ∑ b : Fin (i.m - 1), w (i.rightGlobalIndex b) := by
      rw [Fin.sum_univ_add]
      have hleft :
          (∑ a : Fin (i.n - 1),
              w ((finCongr hk).symm (Fin.castAdd i.m a))) =
            ∑ a : Fin (i.n - 1), w (i.leftGlobalIndex a) := by
        rw [← Equiv.sum_comp Fin.revPerm
          (fun a : Fin (i.n - 1) =>
            w ((finCongr hk).symm (Fin.castAdd i.m a)))]
        apply Finset.sum_congr rfl
        intro a _ha
        congr 1
      have htail :
          (∑ c : Fin i.m,
              w ((finCongr hk).symm (Fin.natAdd (i.n - 1) c))) =
            w i.bridgeGlobalIndex +
              ∑ b : Fin (i.m - 1), w (i.rightGlobalIndex b) := by
        have hm : i.m = (i.m - 1) + 1 := by
          have hm' := i.hm
          omega
        calc
          (∑ c : Fin i.m,
              w ((finCongr hk).symm (Fin.natAdd (i.n - 1) c))) =
              ∑ c : Fin ((i.m - 1) + 1),
                w ((finCongr hk).symm
                  (Fin.natAdd (i.n - 1) ((finCongr hm).symm c))) := by
            symm
            simpa using (Equiv.sum_comp (finCongr hm).symm
              (fun c : Fin i.m =>
                w ((finCongr hk).symm (Fin.natAdd (i.n - 1) c))))
          _ = w i.bridgeGlobalIndex +
                ∑ b : Fin (i.m - 1), w (i.rightGlobalIndex b) := by
            rw [Fin.sum_univ_succ]
            congr 1
            apply Finset.sum_congr rfl
            intro b _hb
            apply congrArg w
            apply Fin.ext
            simp [GeneratorIndex.rightGlobalIndex]
            omega
      rw [hleft, htail]
      ring

/-- Chronological reflection preserves the total gap sum: it reverses the
left tail, combines the two head gaps at the bridge, and keeps the right
tail in order. -/
theorem sum_reflectedChronologicalGapMap
    {r : Nat}
    (tauLeft tauRight : Fin (r + 1) -> Real) :
    (∑ j : Fin (r + (r + 1)),
        reflectedChronologicalGapMap r (tauLeft, tauRight) j) =
      (∑ j : Fin (r + 1), tauLeft j) +
        ∑ j : Fin (r + 1), tauRight j := by
  rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_succ
    (fun j : Fin (r + 1) =>
      reflectedChronologicalGapMap r (tauLeft, tauRight)
        (Fin.natAdd r j))]
  simp only [reflectedChronologicalGapMap_left,
    reflectedChronologicalGapMap_bridge,
    reflectedChronologicalGapMap_right]
  have hrev :
      (∑ i : Fin r, tauLeft (Fin.rev i).succ) =
        ∑ i : Fin r, tauLeft i.succ := by
    simpa using (Equiv.sum_comp Fin.revPerm
      (fun i : Fin r => tauLeft i.succ))
  rw [hrev, Fin.sum_univ_succ tauLeft, Fin.sum_univ_succ tauRight]
  ring



/-- The exact `2 * r + 1`-gap physical point evaluated under a reflected
moving-slice integral.  Naming this map prevents the lower scalar parameter
space `Fin (r + r)` from being confused with the physical equation-`(6.21)`
arity `Fin (r + (r + 1))`. -/
def equation621ReflectedMovingSlicePoint
    {r : Nat}
    (w : Fin (r + r) -> Complex)
    (sigma : Fin (r + (r + 1)) -> Real) :
    OSIITimeGapSpace (r + (r + 1)) :=
  -(reflectedReducedTimeDisplacementCLM r w) +
    osiiPositiveRealTimeEmbed sigma

/-- On a Cauchy center, the arbitrary moving-slice point above is exactly
the canonical reflected stage point already used throughout Chapter V. -/
theorem equation621ReflectedMovingSlicePoint_reflectedCauchyCenter
    {r : Nat}
    (sigma : Fin (r + (r + 1)) -> Real)
    (z : Fin r -> Complex) :
    equation621ReflectedMovingSlicePoint
        (reflectedCauchyCenter z) sigma =
      reflectedCauchyShiftedStagePoint sigma z := by
  rfl

/-- The sum of the physical reflected moving-slice point is the sum of its
scalar reflected-center parameter plus the integrated positive-real source
coordinates. -/
theorem sum_equation621ReflectedMovingSlicePoint
    {r : Nat}
    (w : Fin (r + r) -> Complex)
    (sigma : Fin (r + (r + 1)) -> Real) :
    (∑ j : Fin (r + (r + 1)),
        equation621ReflectedMovingSlicePoint w sigma j) =
      (∑ j : Fin (r + r), w j) +
        ((∑ j : Fin (r + (r + 1)), sigma j) : Complex) := by
  unfold equation621ReflectedMovingSlicePoint
  simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  rw [sum_reflectedReducedTimeDisplacementCLM]
  simp only [osiiPositiveRealTimeEmbed]
  ring

/-- Total-gap formula for the canonical reflected stage point. -/
theorem sum_reflectedCauchyShiftedStagePoint
    {r : Nat}
    (sigma : Fin (r + (r + 1)) -> Real)
    (z : Fin r -> Complex) :
    (∑ j : Fin (r + (r + 1)),
        reflectedCauchyShiftedStagePoint sigma z j) =
      starRingEnd Complex (∑ i : Fin r, z i) +
        ∑ i : Fin r, z i +
          ((∑ j : Fin (r + (r + 1)), sigma j) : Complex) := by
  rw [← equation621ReflectedMovingSlicePoint_reflectedCauchyCenter]
  rw [sum_equation621ReflectedMovingSlicePoint,
    sum_reflectedCauchyCenter]

/-- The numerator contributed by a reflected chronological source is real.
Its value is one plus twice the real part of the Cauchy center sum plus the
total times of the two positive-time source blocks. -/
theorem equation621ReflectedChronologicalSourceNumerator
    {r : Nat}
    (tauLeft tauRight : Fin (r + 1) -> Real)
    (z : Fin r -> Complex) :
    1 + ∑ j : Fin (r + (r + 1)),
        reflectedCauchyShiftedStagePoint
          (reflectedChronologicalGapMap r (tauLeft, tauRight)) z j =
      ((1 + 2 * ∑ i : Fin r, (z i).re +
          ∑ j : Fin (r + 1), tauLeft j +
          ∑ j : Fin (r + 1), tauRight j : Real) : Complex) := by
  rw [sum_reflectedCauchyShiftedStagePoint,
    ← Complex.ofReal_sum, sum_reflectedChronologicalGapMap]
  apply Complex.ext
  · simp [map_sum]
    ring
  · simp [map_sum]

end OSIIChapterV
end OSReconstruction
