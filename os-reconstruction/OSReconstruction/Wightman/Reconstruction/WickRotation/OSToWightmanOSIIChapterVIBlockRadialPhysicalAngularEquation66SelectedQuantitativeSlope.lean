/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66FixedBoundedTarget
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSelectedBlockMZUniform
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapUniform

/-!
# Quantitative synchronized-slope geometry for equation (6.6)

This file gives explicit temporal margins, absolute-coordinate norm bounds,
and one polynomially controlled common slope for every selected left/right
radial carrier.  All constants are fixed by the spacetime dimension and
chronological arity before the center and radial source parameters.
-/
noncomputable section

open Complex Metric Set Topology
open scoped BigOperators Classical

namespace OSReconstruction

set_option maxHeartbeats 1200000

/-- Quantitative version of positivity for the common reduced carrier. -/
theorem osiiStep4CommonReducedCarrier_time_lower
    (d k : Nat)
    {rho : Real}
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (xi : NPointDomain d k)
    (hxi : xi ∈ osiiStep4CenteredPartialKernelCommonReducedCarrier
      d k rho center)
    (i : Fin k) :
    rho / 4 <= xi i 0 := by
  rcases hxi with ⟨u, hu, rfl⟩
  have hnorm : norm (u - center) <= rho / 4 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  let idx : Fin (k * (d + 1)) :=
    finProdFinEquiv (i, (0 : Fin (d + 1)))
  have hcoord : |u idx - center idx| <= rho / 4 := by
    calc
      |u idx - center idx| = norm ((u - center) idx) := by
        simp [Real.norm_eq_abs]
      _ <= norm (u - center) := norm_le_pi_norm _ idx
      _ <= rho / 4 := hnorm
  have hlower := (abs_le.mp hcoord).1
  have hc := hcenter i
  dsimp only [idx] at hlower hc
  change rho / 4 <= u (finProdFinEquiv (i, (0 : Fin (d + 1))))
  nlinarith

/-- The explicit endpoint/reduced support boxes give a uniform temporal
margin in absolute coordinates. -/
theorem osiiStep4RadialEndpointCommonCarrier_margin
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real)
    (hEndpointCenter : rho / 4 <= endpointCenter 0)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    forall x, x ∈ osiiStep4RadialEndpointCommonCarrier
        d k rho endpointCenter center ->
      (forall i : Fin (k + 1), rho / 8 <= x i 0) ∧
      forall i j : Fin (k + 1), i < j ->
        rho / 8 <= x j 0 - x i 0 := by
  intro x hx
  have hordered := osiiStep4RadialEndpointCommonCarrier_ordered
    d k hrho endpointCenter center hcenter x hx
  rcases hx with ⟨p, hp, rfl⟩
  let X : NPointDomain d (k + 1) :=
    (BHW.realDiffCoordCLE (k + 1) d).symm
      (BHW.prependBasepointReal d k p.1 p.2)
  have hendpointNorm : norm (p.1 - endpointCenter) <= rho / 8 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hp.1
  have hendpointCoord : |p.1 0 - endpointCenter 0| <= rho / 8 := by
    calc
      |p.1 0 - endpointCenter 0| =
          norm ((p.1 - endpointCenter) 0) := by
        simp [Real.norm_eq_abs]
      _ <= norm (p.1 - endpointCenter) := norm_le_pi_norm _ 0
      _ <= rho / 8 := hendpointNorm
  have hbase : rho / 8 <= p.1 0 := by
    nlinarith [(abs_le.mp hendpointCoord).1]
  have hstrict : StrictMono (fun i : Fin (k + 1) => X i 0) := by
    intro i j hij
    exact hordered i j hij
  constructor
  · intro i
    change rho / 8 <= X i 0
    by_cases hi : i = 0
    · subst i
      simpa [X] using hbase
    · have h0i : (0 : Fin (k + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
      have hmono := (hstrict h0i).le
      have hbaseX : rho / 8 <= X 0 0 := by
        simpa [X] using hbase
      exact hbaseX.trans hmono
  · intro i j hij
    let q : Fin k := ⟨i.val, by omega⟩
    have hq_cast : q.castSucc = i := by
      apply Fin.ext
      rfl
    have hq_succ_le : q.succ <= j := by
      change i.val + 1 <= j.val
      omega
    have hred :=
      BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
        d k p.1 p.2
    have hcoord := congrFun (congrFun hred q) (0 : Fin (d + 1))
    change X q.succ 0 - X q.castSucc 0 = p.2 q 0 at hcoord
    have hadj : rho / 4 <= X q.succ 0 - X q.castSucc 0 := by
      rw [hcoord]
      exact osiiStep4CommonReducedCarrier_time_lower
        d k center hcenter p.2 hp.2 q
    have hright : X q.succ 0 <= X j 0 := hstrict.monotone hq_succ_le
    rw [hq_cast] at hadj
    change rho / 8 <= X j 0 - X i 0
    nlinarith

/-- The absolute-coordinate reconstruction is bounded by its operator norm
times a simple endpoint/reduced-center radius. -/
theorem osiiStep4RadialEndpointCommonCarrier_norm_le
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real) :
    forall x, x ∈ osiiStep4RadialEndpointCommonCarrier
        d k rho endpointCenter center ->
      norm x <=
        norm (BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap *
          (norm endpointCenter + norm center + 2 * rho) := by
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  rcases hp.2 with ⟨u, hu, hup⟩
  change norm ((BHW.realDiffCoordCLE (k + 1) d).symm
      (BHW.prependBasepointReal d k p.1 p.2)) <= _
  rw [← hup]
  let e := flattenCLEquivReal k (d + 1)
  let p2 : NPointDomain d k := e.symm u
  change norm ((BHW.realDiffCoordCLE (k + 1) d).symm
      (BHW.prependBasepointReal d k p.1 p2)) <= _
  have hendpointRadius : norm (p.1 - endpointCenter) <= rho / 8 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hp.1
  have hendpointNorm : norm p.1 <= norm endpointCenter + rho := by
    have htriangle : norm p.1 <=
        norm (p.1 - endpointCenter) + norm endpointCenter := by
      conv_lhs => rw [← sub_add_cancel p.1 endpointCenter]
      exact norm_add_le _ _
    nlinarith [norm_nonneg endpointCenter]
  have huRadius : norm (u - center) <= rho / 4 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  have huNorm : norm u <= norm center + rho := by
    have htriangle : norm u <= norm (u - center) + norm center := by
      conv_lhs => rw [← sub_add_cancel u center]
      exact norm_add_le _ _
    nlinarith [norm_nonneg center]
  have hp2NormEq : norm p2 = norm u := by
    calc
      norm p2 = norm (e p2) := by
        symm
        exact flattenCLEquivReal_norm_eq k (d + 1) p2
      _ = norm u := by simp [p2, e]
  have hp2Norm : norm p2 <= norm center + rho := by
    rw [hp2NormEq]
    exact huNorm
  have hprepend :
      norm (BHW.prependBasepointReal d k p.1 p2) <=
        norm p.1 + norm p2 := by
    rw [pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg p.1) (norm_nonneg p2))]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [BHW.prependBasepointReal_zero]
      exact le_add_of_nonneg_right (norm_nonneg p2)
    · simp only [BHW.prependBasepointReal_succ]
      exact (norm_le_pi_norm p2 j).trans
        (le_add_of_nonneg_left (norm_nonneg p.1))
  let L := (BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap
  have hop := ContinuousLinearMap.le_opNorm L
    (BHW.prependBasepointReal d k p.1 p2)
  have hinput :
      norm (BHW.prependBasepointReal d k p.1 p2) <=
        norm endpointCenter + norm center + 2 * rho := by
    calc
      norm (BHW.prependBasepointReal d k p.1 p2) <=
          norm p.1 + norm p2 := hprepend
      _ <= (norm endpointCenter + rho) + (norm center + rho) :=
        add_le_add hendpointNorm hp2Norm
      _ = norm endpointCenter + norm center + 2 * rho := by ring
  have hL : 0 <= norm L := norm_nonneg L
  calc
    norm ((BHW.realDiffCoordCLE (k + 1) d).symm
          (BHW.prependBasepointReal d k p.1 p2)) <=
        norm L * norm (BHW.prependBasepointReal d k p.1 p2) := by
      simpa only [L] using hop
    _ <= norm L * (norm endpointCenter + norm center + 2 * rho) :=
      mul_le_mul_of_nonneg_left hinput hL
    _ = norm (BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap *
          (norm endpointCenter + norm center + 2 * rho) := by rfl

/-- An explicit slope obtained from quantitative carrier margin and norm
bounds. -/
theorem osiiStep4RadialEndpointCommonCarrier_explicitSlope
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real)
    (hEndpointCenter : rho / 4 <= endpointCenter 0)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    let C :=
      norm (BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap *
        (norm endpointCenter + norm center + 2 * rho)
    let T := 2 + 16 * C / rho
    1 < T ∧ forall a : osiiAxisPairIndex d,
      osiiStep4RadialEndpointCommonCarrier d k rho endpointCenter center ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := k + 1) (osiiAxisPairRotationData T a).matrix := by
  dsimp only
  let C :=
    norm (BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap *
      (norm endpointCenter + norm center + 2 * rho)
  have hsecond :
      0 <= norm endpointCenter + norm center + 2 * rho := by
    positivity
  have hC : 0 <= C := mul_nonneg (norm_nonneg _) hsecond
  have hT : 1 < 2 + 16 * C / rho := by
    have hdiv : 0 <= 16 * C / rho := div_nonneg (mul_nonneg (by norm_num) hC) hrho.le
    linarith
  refine ⟨hT, ?_⟩
  intro a x hx
  have hmargin := osiiStep4RadialEndpointCommonCarrier_margin
    d k hrho endpointCenter center hEndpointCenter hcenter x hx
  have hnorm : norm x <= C := by
    exact osiiStep4RadialEndpointCommonCarrier_norm_le
      d k hrho endpointCenter center x hx
  have hratio : 2 * C / (rho / 8) < 2 + 16 * C / rho := by
    have hrho_ne : rho ≠ 0 := ne_of_gt hrho
    rw [show 2 * C / (rho / 8) = 16 * C / rho by
      field_simp
      <;> ring]
    linarith
  exact (osiiAxisPairRotationData (2 + 16 * C / rho) a).mem_orderedPositive_of_margin_norm
      (by positivity : 0 < rho / 8) hC hratio x hmargin.1 hmargin.2 hnorm

/-- The exact norm constant used by the endpoint-carrier slope theorem. -/
noncomputable def osiiStep4RadialEndpointCarrierNormConstant
    (d k : Nat)
    (rho : Real)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real) : Real :=
  norm (BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap *
    (norm endpointCenter + norm center + 2 * rho)

noncomputable def osiiStep4MultiGapSelectedLeftCarrierNormConstant
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) : Real :=
  let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i center
  osiiStep4RadialEndpointCarrierNormConstant d i.val rho
    (osiiStep4SelectedBlockLeftEndpointCenter d i.val
      (osiiStep4MultiGapAfterCount i) splitCenter)
    (osiiStep4ParityReversedBeforeRealBlocks d i.val
      (osiiStep4MultiGapAfterCount i) splitCenter)

noncomputable def osiiStep4MultiGapSelectedRightCarrierNormConstant
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) : Real :=
  let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i center
  osiiStep4RadialEndpointCarrierNormConstant d
    (osiiStep4MultiGapAfterCount i) rho
    (osiiStep4SelectedBlockRightEndpointCenter d i.val
      (osiiStep4MultiGapAfterCount i) splitCenter)
    (osiiStep4AfterRealBlocks i.val (osiiStep4MultiGapAfterCount i)
      (d + 1) splitCenter)

/-- Sum rather than a nonconstructive supremum: every summand is nonnegative,
so this is an explicit common norm constant for all selected splits. -/
noncomputable def osiiStep4MultiGapSelectedCarrierNormConstant
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real) : Real :=
  Finset.univ.sum fun i : Fin k =>
    osiiStep4MultiGapSelectedLeftCarrierNormConstant d k rho center i +
      osiiStep4MultiGapSelectedRightCarrierNormConstant d k rho center i

/-- Dimension/arity-only sum of the absolute reconstruction operator norms
appearing in all left and right selected carriers. -/
noncomputable def osiiStep4MultiGapReconstructionNormSum
    (d k : Nat) : Real :=
  Finset.univ.sum fun i : Fin k =>
    norm (BHW.realDiffCoordCLE (i.val + 1) d).symm.toContinuousLinearMap +
      norm (BHW.realDiffCoordCLE
        (osiiStep4MultiGapAfterCount i + 1) d).symm.toContinuousLinearMap

theorem osiiStep4MultiGapReconstructionNormSum_nonneg
    (d k : Nat) :
    0 <= osiiStep4MultiGapReconstructionNormSum d k := by
  unfold osiiStep4MultiGapReconstructionNormSum
  apply Finset.sum_nonneg
  intro i _hi
  exact add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem osiiStep4MultiGapSelectedLeftCarrierNormConstant_nonneg
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    0 <= osiiStep4MultiGapSelectedLeftCarrierNormConstant
      d k rho center i := by
  unfold osiiStep4MultiGapSelectedLeftCarrierNormConstant
    osiiStep4RadialEndpointCarrierNormConstant
  positivity

theorem osiiStep4MultiGapSelectedRightCarrierNormConstant_nonneg
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    0 <= osiiStep4MultiGapSelectedRightCarrierNormConstant
      d k rho center i := by
  unfold osiiStep4MultiGapSelectedRightCarrierNormConstant
    osiiStep4RadialEndpointCarrierNormConstant
  positivity

theorem osiiStep4MultiGapSelectedCarrierNormConstant_nonneg
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real) :
    0 <= osiiStep4MultiGapSelectedCarrierNormConstant d k rho center := by
  unfold osiiStep4MultiGapSelectedCarrierNormConstant
  apply Finset.sum_nonneg
  intro i _hi
  exact add_nonneg
    (osiiStep4MultiGapSelectedLeftCarrierNormConstant_nonneg
      d k hrho center i)
    (osiiStep4MultiGapSelectedRightCarrierNormConstant_nonneg
      d k hrho center i)

theorem osiiStep4MultiGapSelectedLeftCarrierNormConstant_center_bound
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4MultiGapSelectedLeftCarrierNormConstant d k rho center i <=
      norm (BHW.realDiffCoordCLE
          (i.val + 1) d).symm.toContinuousLinearMap *
        (2 * norm center + 2 * rho) := by
  let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i center
  have hsplit : norm splitCenter <= norm center :=
    norm_osiiStep4MultiGapSplitCoordinates_le (d + 1) i center
  have hendpoint :
      norm (osiiStep4SelectedBlockLeftEndpointCenter d i.val
        (osiiStep4MultiGapAfterCount i) splitCenter) <= norm center :=
    (norm_selectedBlockLeftEndpointCenter_le d i.val
      (osiiStep4MultiGapAfterCount i) splitCenter).trans hsplit
  have hreduced :
      norm (osiiStep4ParityReversedBeforeRealBlocks d i.val
        (osiiStep4MultiGapAfterCount i) splitCenter) <= norm center :=
    (norm_parityReversedBefore_le d i.val
      (osiiStep4MultiGapAfterCount i) splitCenter).trans hsplit
  have hinside :
      norm (osiiStep4SelectedBlockLeftEndpointCenter d i.val
          (osiiStep4MultiGapAfterCount i) splitCenter) +
        norm (osiiStep4ParityReversedBeforeRealBlocks d i.val
          (osiiStep4MultiGapAfterCount i) splitCenter) + 2 * rho <=
          2 * norm center + 2 * rho := by
    linarith
  unfold osiiStep4MultiGapSelectedLeftCarrierNormConstant
    osiiStep4RadialEndpointCarrierNormConstant
  dsimp only [splitCenter] at hinside ⊢
  exact mul_le_mul_of_nonneg_left hinside (norm_nonneg _)

theorem osiiStep4MultiGapSelectedRightCarrierNormConstant_center_bound
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4MultiGapSelectedRightCarrierNormConstant d k rho center i <=
      norm (BHW.realDiffCoordCLE
          (osiiStep4MultiGapAfterCount i + 1) d).symm.toContinuousLinearMap *
        (2 * norm center + 2 * rho) := by
  let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i center
  have hsplit : norm splitCenter <= norm center :=
    norm_osiiStep4MultiGapSplitCoordinates_le (d + 1) i center
  have hendpoint :
      norm (osiiStep4SelectedBlockRightEndpointCenter d i.val
        (osiiStep4MultiGapAfterCount i) splitCenter) <= norm center :=
    (norm_selectedBlockRightEndpointCenter_le d i.val
      (osiiStep4MultiGapAfterCount i) splitCenter).trans hsplit
  have hreduced :
      norm (osiiStep4AfterRealBlocks i.val
        (osiiStep4MultiGapAfterCount i) (d + 1) splitCenter) <= norm center :=
    (norm_afterBlocks_le i.val (osiiStep4MultiGapAfterCount i)
      (d + 1) splitCenter).trans hsplit
  have hinside :
      norm (osiiStep4SelectedBlockRightEndpointCenter d i.val
          (osiiStep4MultiGapAfterCount i) splitCenter) +
        norm (osiiStep4AfterRealBlocks i.val
          (osiiStep4MultiGapAfterCount i) (d + 1) splitCenter) + 2 * rho <=
          2 * norm center + 2 * rho := by
    linarith
  unfold osiiStep4MultiGapSelectedRightCarrierNormConstant
    osiiStep4RadialEndpointCarrierNormConstant
  dsimp only [splitCenter] at hinside ⊢
  exact mul_le_mul_of_nonneg_left hinside (norm_nonneg _)

theorem osiiStep4MultiGapSelectedCarrierNormConstant_center_bound
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real) :
    osiiStep4MultiGapSelectedCarrierNormConstant d k rho center <=
      osiiStep4MultiGapReconstructionNormSum d k *
        (2 * norm center + 2 * rho) := by
  unfold osiiStep4MultiGapSelectedCarrierNormConstant
    osiiStep4MultiGapReconstructionNormSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _hi
  calc
    osiiStep4MultiGapSelectedLeftCarrierNormConstant d k rho center i +
        osiiStep4MultiGapSelectedRightCarrierNormConstant d k rho center i <=
      norm (BHW.realDiffCoordCLE
          (i.val + 1) d).symm.toContinuousLinearMap *
          (2 * norm center + 2 * rho) +
        norm (BHW.realDiffCoordCLE
          (osiiStep4MultiGapAfterCount i + 1) d).symm.toContinuousLinearMap *
          (2 * norm center + 2 * rho) :=
      add_le_add
        (osiiStep4MultiGapSelectedLeftCarrierNormConstant_center_bound
          d k hrho center i)
        (osiiStep4MultiGapSelectedRightCarrierNormConstant_center_bound
          d k hrho center i)
    _ = (norm (BHW.realDiffCoordCLE
            (i.val + 1) d).symm.toContinuousLinearMap +
          norm (BHW.realDiffCoordCLE
            (osiiStep4MultiGapAfterCount i + 1) d).symm.toContinuousLinearMap) *
          (2 * norm center + 2 * rho) := by ring

theorem osiiStep4MultiGapSelectedLeftCarrierNormConstant_le
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4MultiGapSelectedLeftCarrierNormConstant d k rho center i <=
      osiiStep4MultiGapSelectedCarrierNormConstant d k rho center := by
  unfold osiiStep4MultiGapSelectedCarrierNormConstant
  have hsum :
      osiiStep4MultiGapSelectedLeftCarrierNormConstant d k rho center i +
          osiiStep4MultiGapSelectedRightCarrierNormConstant d k rho center i <=
        Finset.univ.sum fun j : Fin k =>
          osiiStep4MultiGapSelectedLeftCarrierNormConstant d k rho center j +
            osiiStep4MultiGapSelectedRightCarrierNormConstant d k rho center j := by
    exact Finset.single_le_sum
      (fun j _hj => add_nonneg
        (osiiStep4MultiGapSelectedLeftCarrierNormConstant_nonneg
          d k hrho center j)
        (osiiStep4MultiGapSelectedRightCarrierNormConstant_nonneg
          d k hrho center j))
      (Finset.mem_univ i)
  exact (le_add_of_nonneg_right
    (osiiStep4MultiGapSelectedRightCarrierNormConstant_nonneg
      d k hrho center i)).trans hsum

theorem osiiStep4MultiGapSelectedRightCarrierNormConstant_le
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4MultiGapSelectedRightCarrierNormConstant d k rho center i <=
      osiiStep4MultiGapSelectedCarrierNormConstant d k rho center := by
  unfold osiiStep4MultiGapSelectedCarrierNormConstant
  have hsum :
      osiiStep4MultiGapSelectedLeftCarrierNormConstant d k rho center i +
          osiiStep4MultiGapSelectedRightCarrierNormConstant d k rho center i <=
        Finset.univ.sum fun j : Fin k =>
          osiiStep4MultiGapSelectedLeftCarrierNormConstant d k rho center j +
            osiiStep4MultiGapSelectedRightCarrierNormConstant d k rho center j := by
    exact Finset.single_le_sum
      (fun j _hj => add_nonneg
        (osiiStep4MultiGapSelectedLeftCarrierNormConstant_nonneg
          d k hrho center j)
        (osiiStep4MultiGapSelectedRightCarrierNormConstant_nonneg
          d k hrho center j))
      (Finset.mem_univ i)
  exact (le_add_of_nonneg_left
    (osiiStep4MultiGapSelectedLeftCarrierNormConstant_nonneg
      d k hrho center i)).trans hsum

/-- A fully explicit common slope for every selected left/right carrier. -/
noncomputable def osiiStep4MultiGapExplicitUniformCommonSlopeData
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    OSIIStep4MultiGapUniformCommonSlopeData d k hrho center hcenter := by
  let C := osiiStep4MultiGapSelectedCarrierNormConstant d k rho center
  let T := 2 + 16 * C / rho
  have hC : 0 <= C :=
    osiiStep4MultiGapSelectedCarrierNormConstant_nonneg d k hrho center
  have hT : 1 < T := by
    have hdiv : 0 <= 16 * C / rho :=
      div_nonneg (mul_nonneg (by norm_num) hC) hrho.le
    dsimp only [T]
    linarith
  refine {
    T := T
    hT := hT
    left_carrier_support := ?_
    right_carrier_support := ?_ }
  · intro i a
    let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i center
    let endpointCenter := osiiStep4SelectedBlockLeftEndpointCenter d i.val
      (osiiStep4MultiGapAfterCount i) splitCenter
    let reducedCenter := osiiStep4ParityReversedBeforeRealBlocks d i.val
      (osiiStep4MultiGapAfterCount i) splitCenter
    let Ci := osiiStep4MultiGapSelectedLeftCarrierNormConstant
      d k rho center i
    let Ti := 2 + 16 * Ci / rho
    have hsplit := osiiStep4MultiGapSplitCoordinates_time_lower
      d k i center hcenter
    have hi := osiiStep4RadialEndpointCommonCarrier_explicitSlope
      d i.val hrho endpointCenter reducedCenter
      (osiiStep4SelectedBlockLeftEndpointCenter_time_lower
        d i.val (osiiStep4MultiGapAfterCount i) hrho splitCenter hsplit)
      (osiiStep4ParityReversedBeforeRealBlocks_time_lower
        d i.val (osiiStep4MultiGapAfterCount i) splitCenter hsplit)
    have hCi : Ci <= C := by
      exact osiiStep4MultiGapSelectedLeftCarrierNormConstant_le
        d k hrho center i
    have hTiT : Ti <= T := by
      have hfrac : 16 * Ci / rho <= 16 * C / rho :=
        (div_le_div_iff_of_pos_right hrho).2
          (mul_le_mul_of_nonneg_left hCi (by norm_num))
      dsimp only [Ti, T]
      linarith
    have hsupport : forall b : osiiAxisPairIndex d,
        osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center i ⊆
          osiiEuclideanRotationOrderedPositiveTimeRegion
            (d := d) (n := i.val + 1)
            (osiiAxisPairRotationData Ti b).matrix := by
      intro b
      simpa [osiiStep4MultiGapSelectedLeftCommonCarrier,
        osiiStep4SelectedBlockLeftCommonCarrier, endpointCenter,
        reducedCenter, splitCenter, Ti, Ci,
        osiiStep4MultiGapSelectedLeftCarrierNormConstant,
        osiiStep4RadialEndpointCarrierNormConstant] using hi.2 b
    exact subset_all_orientedPositive_mono
      (osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center i)
      (lt_trans zero_lt_one hi.1) hTiT hsupport a
  · intro i a
    let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i center
    let endpointCenter := osiiStep4SelectedBlockRightEndpointCenter d i.val
      (osiiStep4MultiGapAfterCount i) splitCenter
    let reducedCenter := osiiStep4AfterRealBlocks i.val
      (osiiStep4MultiGapAfterCount i) (d + 1) splitCenter
    let Ci := osiiStep4MultiGapSelectedRightCarrierNormConstant
      d k rho center i
    let Ti := 2 + 16 * Ci / rho
    have hsplit := osiiStep4MultiGapSplitCoordinates_time_lower
      d k i center hcenter
    have hi := osiiStep4RadialEndpointCommonCarrier_explicitSlope
      d (osiiStep4MultiGapAfterCount i) hrho endpointCenter reducedCenter
      (osiiStep4SelectedBlockRightEndpointCenter_time_lower
        d i.val (osiiStep4MultiGapAfterCount i) hrho splitCenter hsplit)
      (osiiStep4AfterRealBlocks_time_lower d i.val
        (osiiStep4MultiGapAfterCount i) splitCenter hsplit)
    have hCi : Ci <= C := by
      exact osiiStep4MultiGapSelectedRightCarrierNormConstant_le
        d k hrho center i
    have hTiT : Ti <= T := by
      have hfrac : 16 * Ci / rho <= 16 * C / rho :=
        (div_le_div_iff_of_pos_right hrho).2
          (mul_le_mul_of_nonneg_left hCi (by norm_num))
      dsimp only [Ti, T]
      linarith
    have hsupport : forall b : osiiAxisPairIndex d,
        osiiStep4MultiGapSelectedRightCommonCarrier d k rho center i ⊆
          osiiEuclideanRotationOrderedPositiveTimeRegion
            (d := d) (n := osiiStep4MultiGapAfterCount i + 1)
            (osiiAxisPairRotationData Ti b).matrix := by
      intro b
      simpa [osiiStep4MultiGapSelectedRightCommonCarrier,
        osiiStep4SelectedBlockRightCommonCarrier, endpointCenter,
        reducedCenter, splitCenter, Ti, Ci,
        osiiStep4MultiGapSelectedRightCarrierNormConstant,
        osiiStep4RadialEndpointCarrierNormConstant] using hi.2 b
    exact subset_all_orientedPositive_mono
      (osiiStep4MultiGapSelectedRightCommonCarrier d k rho center i)
      (lt_trans zero_lt_one hi.1) hTiT hsupport a

@[simp] theorem osiiStep4MultiGapExplicitUniformCommonSlopeData_T
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    (osiiStep4MultiGapExplicitUniformCommonSlopeData
      d k hrho center hcenter).T =
      2 + 16 * osiiStep4MultiGapSelectedCarrierNormConstant
        d k rho center / rho := by
  rfl

/-- The explicit selected-family slope has the standard inverse-scale and
center polynomial form used by the Chapter VI growth estimates. -/
theorem osiiStep4MultiGapExplicitUniformCommonSlopeData_T_le
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    (osiiStep4MultiGapExplicitUniformCommonSlopeData
      d k hrho center hcenter).T <=
      (2 + 32 * osiiStep4MultiGapReconstructionNormSum d k) *
        (16 / rho) * (1 + norm center) := by
  let C := osiiStep4MultiGapSelectedCarrierNormConstant d k rho center
  let R := osiiStep4MultiGapReconstructionNormSum d k
  have hC : C <= R * (2 * norm center + 2 * rho) :=
    osiiStep4MultiGapSelectedCarrierNormConstant_center_bound
      d k hrho center
  have hR : 0 <= R := osiiStep4MultiGapReconstructionNormSum_nonneg d k
  have hn : 0 <= norm center := norm_nonneg center
  have hscale : 2 * norm center + 2 * rho <= 32 * (1 + norm center) := by
    nlinarith
  have hCR : C <= 32 * R * (1 + norm center) := by
    calc
      C <= R * (2 * norm center + 2 * rho) := hC
      _ <= R * (32 * (1 + norm center)) :=
        mul_le_mul_of_nonneg_left hscale hR
      _ = 32 * R * (1 + norm center) := by ring
  have hnum :
      2 * rho + 16 * C <=
        16 * (2 + 32 * R) * (1 + norm center) := by
    have htwo : 2 * rho <= 32 * (1 + norm center) := by nlinarith
    have hsixteen : 16 * C <= 512 * R * (1 + norm center) := by
      nlinarith
    calc
      2 * rho + 16 * C <=
          32 * (1 + norm center) + 512 * R * (1 + norm center) :=
        add_le_add htwo hsixteen
      _ = 16 * (2 + 32 * R) * (1 + norm center) := by ring
  rw [osiiStep4MultiGapExplicitUniformCommonSlopeData_T]
  have hleft : 2 + 16 * C / rho = (2 * rho + 16 * C) / rho := by
    field_simp
  have hright :
      (2 + 32 * R) * (16 / rho) * (1 + norm center) =
        (16 * (2 + 32 * R) * (1 + norm center)) / rho := by
    field_simp
  rw [show osiiStep4MultiGapSelectedCarrierNormConstant
      d k rho center = C by rfl,
    show osiiStep4MultiGapReconstructionNormSum d k = R by rfl,
    hleft, hright]
  exact (div_le_div_iff_of_pos_right hrho).2 hnum

end OSReconstruction

