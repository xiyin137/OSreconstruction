/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedInitial
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapTargetGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedClosureRank
















noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

end OSIIChapterV

/-- Real center parameter which makes the selected target logarithm a
pure-imaginary displacement in the bounded initial continuation. -/
def osiiStep4MultiGapTargetCenteredInput
    (d k : Nat) [NeZero d]
    (shift T : Real)
    (center y : Fin (k * (d + 1)) -> Real) :
    Fin k -> osiiAxisPairIndex d -> Real :=
  fun i a =>
    (osiiStep4MultiGapTargetLog d k T center y i a).re + shift

/-- Pure-imaginary finite-coordinate displacement from the centered real
logarithmic base to the radial target. -/
def osiiStep4MultiGapTargetDisplacementFin
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real) :
    Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex :=
  osiiAxisPairMultiGapFinFlatten
    (fun i a =>
      I *
        ((osiiStep4MultiGapTargetLog d k T center y i a).im : Complex))

/-- Along the real radial parameter, unflattening the finite target
displacement gives the corresponding signed pure-imaginary angle tuple. -/
theorem osiiAxisPairMultiGapFinUnflatten_lineMap_targetDisplacementFin
    (d k : Nat) [NeZero d]
    (T t : Real)
    (center y : Fin (k * (d + 1)) -> Real) :
    osiiAxisPairMultiGapFinUnflatten
        (AffineMap.lineMap
          (0 : Fin (Fintype.card
            (osiiAxisPairMultiGapIndex d k)) -> Complex)
          (osiiStep4MultiGapTargetDisplacementFin d k T center y) t) =
      fun i a =>
        (t * (osiiStep4MultiGapTargetLog
          d k T center y i a).im : Complex) * I := by
  rw [AffineMap.lineMap_apply_module]
  funext i a
  simp [osiiStep4MultiGapTargetDisplacementFin,
    osiiAxisPairMultiGapFinUnflatten,
    osiiAxisPairMultiGapFinFlatten]
  ring

/-- A signed pure-imaginary coefficient tuple whose total absolute weight
fits the compactification budget lies in every centered coefficient germ.
This is the reusable core of the target-segment argument. -/
theorem osiiStep4MultiGapCenteredCoefficientTranslate_pureImaginary_mem_germ
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    (d k : Nat) [NeZero d] [NeZero k]
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (w : osiiAxisPairMultiGapIndex d k -> Real)
    (hsum : (∑ q, |w q|) <= S) :
    osiiStep4MultiGapCenteredCoefficientTranslate shift u
        (fun i a => (w (i, a) : Complex) * I) ∈
      osiiStep4MultiGapCenteredCoefficientGermDomain P shift u := by
  have hterm (q : osiiAxisPairMultiGapIndex d k) : |w q| <= S :=
    (Finset.single_le_sum
      (fun p _hp => abs_nonneg (w p)) (Finset.mem_univ q)).trans hsum
  have hball :
      (fun i a => (w (i, a) : Complex) * I) ∈ Metric.ball 0 P.radius := by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff P.radius_pos]
    intro i
    rw [pi_norm_lt_iff P.radius_pos]
    intro a
    simpa using (hterm (i, a)).trans_lt P.targetBudget_lt_radius
  have hlift :
      osiiStep4MultiGapCenteredCoefficientLift P shift u
          (osiiStep4MultiGapCenteredCoefficientTranslate shift u
            (fun i a => (w (i, a) : Complex) * I)) ∈
        osiiAxisPairMultiGapLogDomain d k := by
    change
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |(osiiStep4MultiGapCenteredCoefficientLift P shift u
          (osiiStep4MultiGapCenteredCoefficientTranslate shift u
            (fun i a => (w (i, a) : Complex) * I)) i a).im|) <
          Real.pi / 2
    simp only [osiiStep4MultiGapCenteredCoefficientLift,
      osiiStep4MultiGapCenteredCoefficientOffset_translate]
    simp_rw [SCV.stripCompactificationLocalInverse_pureImaginary]
    simpa [Fintype.sum_prod_type] using
      P.sum_abs_preimage_im_lt_of_sum_abs_le w hsum
  exact ⟨by
    simpa only [Set.mem_preimage,
      osiiStep4MultiGapCenteredCoefficientOffset_translate] using hball,
    hlift⟩

set_option maxHeartbeats 1200000 in
/-- If the total target argument fits the compactification budget, the
complete zero-to-target displacement segment lies in the bounded centered
coefficient germ.  Signed angles are handled by the signed preimage `l1`
estimate. -/
theorem osiiStep4MultiGapTargetDisplacementFin_segment_mem_centeredCoefficientGermDomain
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (hsum :
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |(osiiStep4MultiGapTargetLog d k T center y i a).im|) <= S) :
    forall z,
      z ∈ segment Real 0
          (osiiStep4MultiGapTargetDisplacementFin d k T center y) ->
        osiiStep4MultiGapCenteredCoefficientTranslate shift u
            (osiiAxisPairMultiGapFinUnflatten z) ∈
          osiiStep4MultiGapCenteredCoefficientGermDomain P shift u := by
  intro z hz
  rw [segment_eq_image_lineMap Real
    (0 : Fin (Fintype.card
      (osiiAxisPairMultiGapIndex d k)) -> Complex)
    (osiiStep4MultiGapTargetDisplacementFin d k T center y)] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let angle : osiiAxisPairMultiGapIndex d k -> Real := fun q =>
    (osiiStep4MultiGapTargetLog d k T center y q.1 q.2).im
  let w : osiiAxisPairMultiGapIndex d k -> Real := fun q => t * angle q
  have hangle_nonneg :
      0 <= ∑ q : osiiAxisPairMultiGapIndex d k, |angle q| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hangle_sum :
      (∑ q : osiiAxisPairMultiGapIndex d k, |angle q|) <= S := by
    simpa [angle, Fintype.sum_prod_type] using hsum
  have hsum_w :
      (∑ q : osiiAxisPairMultiGapIndex d k, |w q|) <= S := by
    calc
      (∑ q : osiiAxisPairMultiGapIndex d k, |w q|) =
          t * ∑ q : osiiAxisPairMultiGapIndex d k, |angle q| := by
        simp only [w, abs_mul, abs_of_nonneg ht.1]
        rw [Finset.mul_sum]
      _ <= 1 * ∑ q : osiiAxisPairMultiGapIndex d k, |angle q| :=
        mul_le_mul_of_nonneg_right ht.2 hangle_nonneg
      _ <= S := by simpa using hangle_sum
  have hdisp :=
    osiiAxisPairMultiGapFinUnflatten_lineMap_targetDisplacementFin
      d k T t center y
  have hdisp' :
      osiiAxisPairMultiGapFinUnflatten
          (AffineMap.lineMap
            (0 : Fin (Fintype.card
              (osiiAxisPairMultiGapIndex d k)) -> Complex)
            (osiiStep4MultiGapTargetDisplacementFin d k T center y) t) =
        fun i a => (w (i, a) : Complex) * I := by
    simpa [w, angle] using hdisp
  rw [hdisp']
  exact
    osiiStep4MultiGapCenteredCoefficientTranslate_pureImaginary_mem_germ
      P shift d k u w hsum_w

/-- The same total argument budget places the centered original-coordinate
target segment in the uncompactified multi-gap logarithmic carrier. -/
theorem osiiStep4MultiGapTargetDisplacementFin_segment_mem_centeredLogDomain
    (shift : Real)
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (hsum :
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |(osiiStep4MultiGapTargetLog d k T center y i a).im|) <
          Real.pi / 2) :
    forall z,
      z ∈ segment Real 0
          (osiiStep4MultiGapTargetDisplacementFin d k T center y) ->
        osiiStep4MultiGapCenteredCoefficientTranslate shift u
            (osiiAxisPairMultiGapFinUnflatten z) ∈
          osiiAxisPairMultiGapLogDomain d k := by
  intro z hz
  rw [segment_eq_image_lineMap Real
    (0 : Fin (Fintype.card
      (osiiAxisPairMultiGapIndex d k)) -> Complex)
    (osiiStep4MultiGapTargetDisplacementFin d k T center y)] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let angle : osiiAxisPairMultiGapIndex d k -> Real := fun q =>
    (osiiStep4MultiGapTargetLog d k T center y q.1 q.2).im
  let w : osiiAxisPairMultiGapIndex d k -> Real := fun q => t * angle q
  have hangle_nonneg :
      0 <= ∑ q : osiiAxisPairMultiGapIndex d k, |angle q| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hangle_sum :
      (∑ q : osiiAxisPairMultiGapIndex d k, |angle q|) < Real.pi / 2 := by
    simpa [angle, Fintype.sum_prod_type] using hsum
  have hsum_w :
      (∑ q : osiiAxisPairMultiGapIndex d k, |w q|) < Real.pi / 2 := by
    calc
      (∑ q : osiiAxisPairMultiGapIndex d k, |w q|) =
          t * ∑ q : osiiAxisPairMultiGapIndex d k, |angle q| := by
        simp only [w, abs_mul, abs_of_nonneg ht.1]
        rw [Finset.mul_sum]
      _ <= 1 * ∑ q : osiiAxisPairMultiGapIndex d k, |angle q| :=
        mul_le_mul_of_nonneg_right ht.2 hangle_nonneg
      _ < Real.pi / 2 := by simpa using hangle_sum
  have hdisp :=
    osiiAxisPairMultiGapFinUnflatten_lineMap_targetDisplacementFin
      d k T t center y
  change
    (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
      |(osiiStep4MultiGapCenteredCoefficientTranslate shift u
        (osiiAxisPairMultiGapFinUnflatten
          (AffineMap.lineMap
            (0 : Fin (Fintype.card
              (osiiAxisPairMultiGapIndex d k)) -> Complex)
            (osiiStep4MultiGapTargetDisplacementFin
              d k T center y) t)) i a).im|) < Real.pi / 2
  rw [hdisp]
  simpa [osiiStep4MultiGapCenteredCoefficientTranslate,
    osiiAxisPairSimultaneousLogRealEmbed,
    osiiAxisPairLogRealEmbed, w, Fintype.sum_prod_type] using hsum_w

/-- Translating the centered displacement back to original logarithmic
coordinates reaches the target logarithm exactly. -/
theorem osiiStep4MultiGapCenteredTranslate_targetDisplacement
    (d k : Nat) [NeZero d]
    (shift T : Real)
    (center y : Fin (k * (d + 1)) -> Real) :
    osiiStep4MultiGapCenteredCoefficientTranslate shift
        (osiiStep4MultiGapTargetCenteredInput
          d k shift T center y)
        (osiiAxisPairMultiGapFinUnflatten
          (osiiStep4MultiGapTargetDisplacementFin
            d k T center y)) =
      osiiStep4MultiGapTargetLog d k T center y := by
  rw [show
    osiiAxisPairMultiGapFinUnflatten
        (osiiStep4MultiGapTargetDisplacementFin d k T center y) =
      (fun i a =>
        I *
          ((osiiStep4MultiGapTargetLog
            d k T center y i a).im : Complex)) by
    simpa only [osiiStep4MultiGapTargetDisplacementFin] using
      (osiiAxisPairMultiGapFinUnflatten_flatten
        (fun i a =>
          I *
            ((osiiStep4MultiGapTargetLog
              d k T center y i a).im : Complex)))]
  funext i a
  apply Complex.ext
  · simp [osiiStep4MultiGapCenteredCoefficientTranslate,
      osiiStep4MultiGapCenteredCoefficientBase,
      osiiStep4MultiGapTargetCenteredInput,
      osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed]
  · simp [osiiStep4MultiGapCenteredCoefficientTranslate,
      osiiStep4MultiGapCenteredCoefficientBase,
      osiiStep4MultiGapTargetCenteredInput,
      osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed]

end OSReconstruction
