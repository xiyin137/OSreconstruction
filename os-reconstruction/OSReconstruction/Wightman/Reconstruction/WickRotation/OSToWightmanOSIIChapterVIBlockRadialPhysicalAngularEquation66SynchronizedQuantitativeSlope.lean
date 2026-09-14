/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66SelectedQuantitativeSlope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapSynchronizedCommonSlope

/-!
# Quantitative coherent and synchronized slopes for equation (6.6)

A compact chronological carrier with explicit gap and norm bounds admits a
quantitative partition into product carriers.  Specializing that theorem to
the positive-lifted radial carrier gives an explicit coherent continuation;
taking the maximum with the selected-carrier slope preserves a polynomial
inverse-scale and center bound for the fully synchronized data.
-/

noncomputable section

open Complex Metric Set Topology
open scoped BigOperators Classical

namespace OSReconstruction

set_option maxHeartbeats 1200000
/-- Quantitative chronological localization.  A compact carrier with a fixed
time-gap margin and norm bound is partitioned in boxes of radius `delta / 16`;
the factor cutoffs live in boxes of radius `delta / 8`.  Consequently the
common axis-pair slope is explicit and independent of all partition choices. -/
theorem nonempty_osiiChronologicalQuantitativeLocalizationContinuationData
    (d k : Nat) [NeZero d] [NeZero k]
    (K : Set (NPointDomain d (k + 1)))
    (hKcompact : IsCompact K)
    (delta C : Real) (hdelta : 0 < delta) (hC : 0 <= C)
    (hmargin : forall x, x ∈ K ->
      forall i j : Fin (k + 1), i < j ->
        delta <= x j 0 - x i 0)
    (hnorm : forall x, x ∈ K -> norm x <= C) :
    ∃ D : OSIIChronologicalCompactLocalizationContinuationData d k K,
      D.T = 2 + 8 * (C + delta) / delta := by
  let epsilon : Real := delta / 16
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  let Vbeta : K -> Set (NPointDomain d (k + 1)) := fun y =>
    {z | forall i : Fin (k + 1), z i ∈ Metric.ball (y.1 i) epsilon}
  have hVbetaOpen : forall y : K, IsOpen (Vbeta y) := by
    intro y
    have hopen : IsOpen
        (⋂ i : Fin (k + 1),
          {z : NPointDomain d (k + 1) |
            z i ∈ Metric.ball (y.1 i) epsilon}) :=
      isOpen_iInter_of_finite fun i =>
        Metric.isOpen_ball.preimage (continuous_apply i)
    convert hopen using 1
    ext z
    simp [Vbeta]
  have hKcover : K ⊆ ⋃ y : K, Vbeta y := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    intro i
    exact Metric.mem_ball_self hepsilon
  obtain ⟨s, hscover⟩ :=
    hKcompact.elim_finite_subcover Vbeta hVbetaOpen hKcover
  let alpha := {y : K // y ∈ s}
  let V : alpha -> Set (NPointDomain d (k + 1)) := fun a => Vbeta a.1
  let Q : alpha -> NPointDomain d (k + 1) := fun a => a.1.1
  letI : Fintype alpha := Fintype.ofFinite alpha
  have hVopen : forall a : alpha, IsOpen (V a) := fun a => hVbetaOpen a.1
  have hVrelcompact : forall a : alpha,
      exists c r, V a ⊆ Metric.closedBall c r := by
    intro a
    refine ⟨Q a, epsilon, ?_⟩
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm,
      pi_norm_le_iff_of_nonneg hepsilon.le]
    intro i
    have hi := hz i
    rw [Metric.mem_ball, dist_eq_norm] at hi
    exact hi.le
  have hcover : K ⊆ ⋃ a : alpha, V a := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hscover hx) with ⟨y, hys, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
  obtain ⟨theta, hthetaCompact, hthetaSupport, hthetaSum⟩ :=
    SCV.exists_finite_schwartz_partitionOfUnity_on_compact
      hKcompact hVopen hVrelcompact hcover
  let piece : alpha -> SchwartzNPoint d (k + 1) →L[Complex]
      SchwartzNPoint d (k + 1) := fun a =>
    SchwartzMap.smulLeftCLM Complex
      (theta a : NPointDomain d (k + 1) -> Complex)
  have hpieceSum : forall f : SchwartzNPoint d (k + 1),
      tsupport (f : NPointDomain d (k + 1) -> Complex) ⊆ K ->
        f = Finset.univ.sum fun a : alpha => piece a f := by
    intro f hf
    simpa [piece] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset alpha) theta f
        (fun x hx => hthetaSum x (hf hx))
  let projectedSupport (a : alpha) (i : Fin (k + 1)) :
      Set (SpacetimeDim d) :=
    (fun x : NPointDomain d (k + 1) => x i) ''
      tsupport (theta a : NPointDomain d (k + 1) -> Complex)
  have hprojectedCompact : forall a i, IsCompact (projectedSupport a i) := by
    intro a i
    exact (hthetaCompact a).isCompact.image (continuous_apply i)
  have hprojectedSub : forall a i,
      projectedSupport a i ⊆ Metric.ball (Q a i) (2 * epsilon) := by
    intro a i y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxi := hthetaSupport a hx i
    exact Metric.ball_subset_ball (by linarith [hepsilon]) hxi
  have hcutoff : forall a : alpha, forall i : Fin (k + 1),
      exists chi : SchwartzSpacetime d,
        (∀ y ∈ projectedSupport a i, chi y = 1) ∧
        tsupport ((chi : SchwartzSpacetime d) : SpacetimeDim d -> Complex) ⊆
          Metric.ball (Q a i) (2 * epsilon) ∧
        HasCompactSupport
          ((chi : SchwartzSpacetime d) : SpacetimeDim d -> Complex) := by
    intro a i
    exact OSIIChapterV.exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open
      (m := d + 1) (hprojectedCompact a i) Metric.isOpen_ball
        (hprojectedSub a i)
  choose chi hchiOne hchiSupport hchiCompact using hcutoff
  have hfactorTimeGap : forall a : alpha,
      forall i j : Fin (k + 1), i < j ->
        ∀ y ∈ tsupport
            (((chi a i : SchwartzSpacetime d)) : SpacetimeDim d -> Complex),
          ∀ z ∈ tsupport
              (((chi a j : SchwartzSpacetime d)) : SpacetimeDim d -> Complex),
            delta / 2 < z 0 - y 0 := by
    intro a i j hij y hy z hz
    have hyBall := hchiSupport a i hy
    have hzBall := hchiSupport a j hz
    rw [Metric.mem_ball, dist_eq_norm] at hyBall hzBall
    have hyTime : abs (y 0 - Q a i 0) < 2 * epsilon := by
      calc
        abs (y 0 - Q a i 0) = norm ((y - Q a i) 0) := by
          simp [Real.norm_eq_abs]
        _ <= norm (y - Q a i) := norm_le_pi_norm _ 0
        _ < 2 * epsilon := hyBall
    have hzTime : abs (z 0 - Q a j 0) < 2 * epsilon := by
      calc
        abs (z 0 - Q a j 0) = norm ((z - Q a j) 0) := by
          simp [Real.norm_eq_abs]
        _ <= norm (z - Q a j) := norm_le_pi_norm _ 0
        _ < 2 * epsilon := hzBall
    have hcenterGap : delta <= Q a j 0 - Q a i 0 :=
      hmargin (Q a) a.1.2 i j hij
    dsimp only [epsilon] at hyTime hzTime
    rcases abs_lt.mp hyTime with ⟨hyLower, hyUpper⟩
    rcases abs_lt.mp hzTime with ⟨hzLower, hzUpper⟩
    nlinarith
  let carrier : alpha -> OSIIChronologicalCompactFactors d k := fun a => {
    factors := chi a
    factor_compact := hchiCompact a
    ordered_support := by
      intro i j hij y hy z hz
      exact sub_pos.mp (lt_trans (by positivity : 0 < delta / 2)
        (hfactorTimeGap a i j hij y hy z hz)) }
  have hcarrierPiece : forall a f,
      SchwartzMap.smulLeftCLM Complex
          (SchwartzMap.productTensor (carrier a).factors)
          (piece a f) = piece a f := by
    intro a f
    ext x
    have hfixpoint :
        SchwartzMap.productTensor (carrier a).factors x * theta a x =
          theta a x := by
      by_cases hx : x ∈ tsupport
          (theta a : NPointDomain d (k + 1) -> Complex)
      · have hprod :
          (SchwartzMap.productTensor (carrier a).factors :
            SchwartzNPoint d (k + 1)) x = 1 := by
          rw [SchwartzMap.productTensor_apply]
          apply Finset.prod_eq_one
          intro i _hi
          exact hchiOne a i (x i) ⟨x, hx, rfl⟩
        rw [hprod, one_mul]
      · have hzero : theta a x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [hzero]
    simp only [piece]
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (SchwartzMap.productTensor (carrier a).factors).hasTemperateGrowth]
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (theta a).hasTemperateGrowth]
    simpa only [smul_eq_mul, mul_assoc] using
      congrArg (fun w : Complex => w * f x) hfixpoint
  let localization : OSIIChronologicalCompactLocalizationData d k K := {
    index := alpha
    indexFintype := inferInstance
    piece := piece
    carrier := carrier
    sum_eq := hpieceSum
    carrier_fix := hcarrierPiece }
  let T : Real := 2 + 8 * (C + delta) / delta
  have hT : 1 < T := by
    have hquot : 0 < 8 * (C + delta) / delta := by
      apply div_pos
      · positivity
      · exact hdelta
    dsimp only [T]
    linarith
  have hTpos : 0 < T := lt_trans zero_lt_one hT
  have haxis : forall a : alpha, forall b : osiiAxisPairIndex d,
      forall i j : Fin (k + 1), i < j ->
        ∀ y ∈ tsupport
            (((carrier a).factors i : SchwartzSpacetime d) :
              SpacetimeDim d -> Complex),
          ∀ z ∈ tsupport
              (((carrier a).factors j : SchwartzSpacetime d) :
                SpacetimeDim d -> Complex),
            ((osiiAxisPairRotationData T b).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData T b).matrix.mulVec z) 0 := by
    intro a b i j hij y hy z hz
    have hyBall := hchiSupport a i hy
    have hzBall := hchiSupport a j hz
    rw [Metric.mem_ball, dist_eq_norm] at hyBall hzBall
    have hQi : norm (Q a i) <= C :=
      (norm_le_pi_norm (Q a) i).trans (hnorm (Q a) a.1.2)
    have hQj : norm (Q a j) <= C :=
      (norm_le_pi_norm (Q a) j).trans (hnorm (Q a) a.1.2)
    have hyNorm : norm y < C + delta / 8 := by
      have htri : norm y <= norm (y - Q a i) + norm (Q a i) := by
        conv_lhs => rw [← sub_add_cancel y (Q a i)]
        exact norm_add_le _ _
      dsimp only [epsilon] at hyBall
      nlinarith
    have hzNorm : norm z < C + delta / 8 := by
      have htri : norm z <= norm (z - Q a j) + norm (Q a j) := by
        conv_lhs => rw [← sub_add_cancel z (Q a j)]
        exact norm_add_le _ _
      dsimp only [epsilon] at hzBall
      nlinarith
    have hgap := hfactorTimeGap a i j hij y hy z hz
    have hTdelta : T * (delta / 2) = delta + 4 * (C + delta) := by
      dsimp only [T]
      field_simp
      ring
    have hsmall : 2 * (C + delta / 8) < T * (delta / 2) := by
      rw [hTdelta]
      nlinarith
    have hscaledGap : T * (delta / 2) < T * (z 0 - y 0) :=
      mul_lt_mul_of_pos_left hgap hTpos
    have hratio :
        2 * (C + delta / 8) < T * (z 0 - y 0) :=
      hsmall.trans hscaledGap
    have hyCoord : abs (y (Fin.succ b.1)) < C + delta / 8 := by
      calc
        abs (y (Fin.succ b.1)) = norm (y (Fin.succ b.1)) := by
          simp [Real.norm_eq_abs]
        _ <= norm y := norm_le_pi_norm y (Fin.succ b.1)
        _ < _ := hyNorm
    have hzCoord : abs (z (Fin.succ b.1)) < C + delta / 8 := by
      calc
        abs (z (Fin.succ b.1)) = norm (z (Fin.succ b.1)) := by
          simp [Real.norm_eq_abs]
        _ <= norm z := norm_le_pi_norm z (Fin.succ b.1)
        _ < _ := hzNorm
    rw [(osiiAxisPairRotationData T b).mulVec_time,
      (osiiAxisPairRotationData T b).mulVec_time,
      mul_lt_mul_iff_right₀ (inv_pos.mpr (osiiAxisPairRadius_pos T))]
    rcases b with ⟨axis, sign⟩
    cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rcases abs_lt.mp hyCoord with ⟨hyLower, hyUpper⟩
      rcases abs_lt.mp hzCoord with ⟨hzLower, hzUpper⟩
      nlinarith
    · rcases abs_lt.mp hyCoord with ⟨hyLower, hyUpper⟩
      rcases abs_lt.mp hzCoord with ⟨hzLower, hzUpper⟩
      nlinarith
  exact ⟨{
    localization := localization
    T := T
    hT := hT
    axisPairOrdered := haxis }, rfl⟩

/-- Fixed dimension-only norm bound for the normalized spacetime basepoint
cutoff used in the coherent reduced lift. -/
theorem exists_osiiStep4PositiveTimeBasepointCutoff_normBound
    (d : Nat) [NeZero d] :
    ∃ B : Real, 0 <= B ∧ forall x,
      x ∈ tsupport
          (((osiiStep4PositiveTimeBasepointCutoff d).toSchwartz :
            SchwartzMap (SpacetimeDim d) Complex) :
            SpacetimeDim d -> Complex) ->
        norm x <= B := by
  let K : Set (SpacetimeDim d) :=
    tsupport
      (((osiiStep4PositiveTimeBasepointCutoff d).toSchwartz :
        SchwartzMap (SpacetimeDim d) Complex) :
        SpacetimeDim d -> Complex)
  have hK : IsCompact K :=
    (osiiStep4PositiveTimeBasepointCutoff_hasCompactSupport d).isCompact
  obtain ⟨B0, hB0⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let B : Real := max B0 0
  refine ⟨B, le_max_right _ _, ?_⟩
  intro x hx
  exact (hB0 (Set.mem_image_of_mem norm hx)).trans (le_max_left _ _)

noncomputable def osiiStep4PositiveTimeBasepointCutoffNormBound
    (d : Nat) [NeZero d] : Real :=
  Classical.choose (exists_osiiStep4PositiveTimeBasepointCutoff_normBound d)

theorem osiiStep4PositiveTimeBasepointCutoffNormBound_nonneg
    (d : Nat) [NeZero d] :
    0 <= osiiStep4PositiveTimeBasepointCutoffNormBound d :=
  (Classical.choose_spec
    (exists_osiiStep4PositiveTimeBasepointCutoff_normBound d)).1

theorem osiiStep4PositiveTimeBasepointCutoff_norm_le
    (d : Nat) [NeZero d]
    (x : SpacetimeDim d)
    (hx : x ∈ tsupport
      (((osiiStep4PositiveTimeBasepointCutoff d).toSchwartz :
        SchwartzMap (SpacetimeDim d) Complex) :
        SpacetimeDim d -> Complex)) :
    norm x <= osiiStep4PositiveTimeBasepointCutoffNormBound d :=
  (Classical.choose_spec
    (exists_osiiStep4PositiveTimeBasepointCutoff_normBound d)).2 x hx

/-- The positive-lifted common carrier retains the same `rho / 4`
chronological gap as its reduced difference-coordinate carrier. -/
theorem osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_gap_lower
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    forall x,
      x ∈ osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k rho center ->
      forall i j : Fin (k + 1), i < j ->
        rho / 4 <= x j 0 - x i 0 := by
  intro x hx i j hij
  have hordered :=
    osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_ordered
      d k hrho center hcenter x hx
  rcases hx with ⟨p, hp, rfl⟩
  let X : NPointDomain d (k + 1) :=
    (BHW.realDiffCoordCLE (k + 1) d).symm
      (BHW.prependBasepointReal d k p.1 p.2)
  have hstrict : StrictMono (fun q : Fin (k + 1) => X q 0) := by
    intro q r hqr
    exact hordered q r hqr
  let q : Fin k := ⟨i.val, by omega⟩
  have hqCast : q.castSucc = i := by
    apply Fin.ext
    rfl
  have hqSuccLe : q.succ <= j := by
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
  have hright : X q.succ 0 <= X j 0 := hstrict.monotone hqSuccLe
  rw [hqCast] at hadj
  change rho / 4 <= X j 0 - X i 0
  linarith

/-- Norm bound for the coherent positive-lifted carrier. -/
theorem osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_norm_le
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real) :
    forall x,
      x ∈ osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k rho center ->
      norm x <=
        norm (BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap *
          (osiiStep4PositiveTimeBasepointCutoffNormBound d +
            norm center + rho) := by
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
  have hp1Norm : norm p.1 <=
      osiiStep4PositiveTimeBasepointCutoffNormBound d :=
    osiiStep4PositiveTimeBasepointCutoff_norm_le d p.1 hp.1
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
  have hprepend : norm (BHW.prependBasepointReal d k p.1 p2) <=
      norm p.1 + norm p2 := by
    rw [pi_norm_le_iff_of_nonneg
      (add_nonneg (norm_nonneg p.1) (norm_nonneg p2))]
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
  have hinput : norm (BHW.prependBasepointReal d k p.1 p2) <=
      osiiStep4PositiveTimeBasepointCutoffNormBound d + norm center + rho := by
    calc
      norm (BHW.prependBasepointReal d k p.1 p2) <=
          norm p.1 + norm p2 := hprepend
      _ <= osiiStep4PositiveTimeBasepointCutoffNormBound d +
          (norm center + rho) := add_le_add hp1Norm hp2Norm
      _ = osiiStep4PositiveTimeBasepointCutoffNormBound d +
          norm center + rho := by ring
  calc
    norm ((BHW.realDiffCoordCLE (k + 1) d).symm
        (BHW.prependBasepointReal d k p.1 p2)) <=
      norm L * norm (BHW.prependBasepointReal d k p.1 p2) := by
        simpa only [L] using hop
    _ <= norm L *
        (osiiStep4PositiveTimeBasepointCutoffNormBound d +
          norm center + rho) :=
      mul_le_mul_of_nonneg_left hinput (norm_nonneg L)
    _ = norm (BHW.realDiffCoordCLE
        (k + 1) d).symm.toContinuousLinearMap *
        (osiiStep4PositiveTimeBasepointCutoffNormBound d +
          norm center + rho) := by rfl

noncomputable def osiiStep4PositiveLiftedCarrierNormConstant
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real) : Real :=
  norm (BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap *
    (osiiStep4PositiveTimeBasepointCutoffNormBound d +
      norm center + rho)

/-- Quantitative coherent continuation for the positive-lifted radial source
family, retaining the exact selected slope formula. -/
theorem exists_osiiStep4QuantitativeCoherentContinuationData
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    ∃ D : OSIIChronologicalCompactLocalizationContinuationData d k
        (osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
          d k rho center),
      D.T = 2 + 8 *
        (osiiStep4PositiveLiftedCarrierNormConstant d k rho center + rho / 4) /
          (rho / 4) := by
  let K := osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
    d k rho center
  let C := osiiStep4PositiveLiftedCarrierNormConstant d k rho center
  have hC : 0 <= C := by
    unfold C osiiStep4PositiveLiftedCarrierNormConstant
    apply mul_nonneg (norm_nonneg _)
    have hB := osiiStep4PositiveTimeBasepointCutoffNormBound_nonneg d
    nlinarith [norm_nonneg center]
  obtain ⟨D, hD⟩ :=
    nonempty_osiiChronologicalQuantitativeLocalizationContinuationData
      d k K
      (osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_isCompact
        d k rho center)
      (rho / 4) C (by positivity) hC
      (by
        intro x hx i j hij
        exact osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_gap_lower
          d k hrho center hcenter x hx i j hij)
      (by
        intro x hx
        exact osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_norm_le
          d k hrho center x hx)
  exact ⟨D, by simpa only [K, C] using hD⟩

noncomputable def osiiStep4QuantitativeCoherentContinuationData
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    OSIIChronologicalCompactLocalizationContinuationData d k
      (osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k rho center) :=
  Classical.choose
    (exists_osiiStep4QuantitativeCoherentContinuationData
      d k hrho center hcenter)

@[simp] theorem osiiStep4QuantitativeCoherentContinuationData_T
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    (osiiStep4QuantitativeCoherentContinuationData
      d k hrho center hcenter).T =
      2 + 8 *
        (osiiStep4PositiveLiftedCarrierNormConstant d k rho center + rho / 4) /
          (rho / 4) :=
  Classical.choose_spec
    (exists_osiiStep4QuantitativeCoherentContinuationData
      d k hrho center hcenter)

/-- Dimension/arity-only coefficient absorbing the fixed positive basepoint
cutoff in the coherent slope estimate. -/
noncomputable def osiiStep4CoherentSlopePolynomialConstant
    (d k : Nat) [NeZero d] : Real :=
  10 + 2 *
    norm (BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap *
      (osiiStep4PositiveTimeBasepointCutoffNormBound d + 17)

theorem osiiStep4CoherentSlopePolynomialConstant_nonneg
    (d k : Nat) [NeZero d] :
    0 <= osiiStep4CoherentSlopePolynomialConstant d k := by
  unfold osiiStep4CoherentSlopePolynomialConstant
  have hB := osiiStep4PositiveTimeBasepointCutoffNormBound_nonneg d
  have hprod : 0 <=
      2 * norm (BHW.realDiffCoordCLE
        (k + 1) d).symm.toContinuousLinearMap *
          (osiiStep4PositiveTimeBasepointCutoffNormBound d + 17) := by
    positivity
  linarith

theorem osiiStep4QuantitativeCoherentContinuationData_T_le
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    (osiiStep4QuantitativeCoherentContinuationData
      d k hrho center hcenter).T <=
      osiiStep4CoherentSlopePolynomialConstant d k *
        (16 / rho) * (1 + norm center) := by
  let R := norm (BHW.realDiffCoordCLE
    (k + 1) d).symm.toContinuousLinearMap
  let B := osiiStep4PositiveTimeBasepointCutoffNormBound d
  let C := osiiStep4PositiveLiftedCarrierNormConstant d k rho center
  let A := osiiStep4CoherentSlopePolynomialConstant d k
  have hR : 0 <= R := norm_nonneg _
  have hB : 0 <= B := osiiStep4PositiveTimeBasepointCutoffNormBound_nonneg d
  have hn : 0 <= norm center := norm_nonneg center
  have hcoef : 1 <= B + 17 := by linarith
  have hcoefMul : norm center <= (B + 17) * norm center := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hn
  have hinside : B + norm center + rho <=
      (B + 17) * (1 + norm center) := by
    nlinarith [mul_nonneg hB hn]
  have hC : C <= R * (B + 17) * (1 + norm center) := by
    unfold C osiiStep4PositiveLiftedCarrierNormConstant
    dsimp only [R, B] at hinside ⊢
    calc
      norm (BHW.realDiffCoordCLE
          (k + 1) d).symm.toContinuousLinearMap *
          (osiiStep4PositiveTimeBasepointCutoffNormBound d +
            norm center + rho) <=
        norm (BHW.realDiffCoordCLE
          (k + 1) d).symm.toContinuousLinearMap *
          ((osiiStep4PositiveTimeBasepointCutoffNormBound d + 17) *
            (1 + norm center)) :=
        mul_le_mul_of_nonneg_left hinside (norm_nonneg _)
      _ = R * (B + 17) * (1 + norm center) := by
        dsimp only [R, B]
        ring
  have hnum : 10 * rho + 32 * C <=
      16 * A * (1 + norm center) := by
    have hten : 10 * rho <= 160 * (1 + norm center) := by nlinarith
    have hthirtytwo : 32 * C <=
        32 * R * (B + 17) * (1 + norm center) := by
      nlinarith
    calc
      10 * rho + 32 * C <=
          160 * (1 + norm center) +
            32 * R * (B + 17) * (1 + norm center) :=
        add_le_add hten hthirtytwo
      _ = 16 * A * (1 + norm center) := by
        simp only [A, osiiStep4CoherentSlopePolynomialConstant, R, B]
        ring
  rw [osiiStep4QuantitativeCoherentContinuationData_T]
  have hleft : 2 + 8 * (C + rho / 4) / (rho / 4) =
      (10 * rho + 32 * C) / rho := by
    field_simp
    ring
  have hright : A * (16 / rho) * (1 + norm center) =
      (16 * A * (1 + norm center)) / rho := by
    field_simp
  rw [show osiiStep4PositiveLiftedCarrierNormConstant
      d k rho center = C by rfl,
    show osiiStep4CoherentSlopePolynomialConstant d k = A by rfl,
    hleft, hright]
  exact (div_le_div_iff_of_pos_right hrho).2 hnum

/-- Quantitative synchronized data: both the selected packet family and the
coherent full-source continuation are raised to the maximum of their two
explicit slopes. -/
noncomputable def osiiStep4QuantitativeSynchronizedMultiGapContinuationData
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    OSIIStep4SynchronizedMultiGapContinuationData
      d k hrho center hcenter := by
  let U0 := osiiStep4MultiGapExplicitUniformCommonSlopeData
    d k hrho center hcenter
  let C0 := osiiStep4QuantitativeCoherentContinuationData
    d k hrho center hcenter
  let T := max U0.T C0.T
  have hUT : U0.T <= T := le_max_left _ _
  have hCT : C0.T <= T := le_max_right _ _
  have hUpos : 0 < U0.T := lt_trans zero_lt_one U0.hT
  let U : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter := {
    T := T
    hT := U0.hT.trans_le hUT
    left_carrier_support := by
      intro i
      exact subset_all_orientedPositive_mono
        (osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center i)
        hUpos hUT (U0.left_carrier_support i)
    right_carrier_support := by
      intro i
      exact subset_all_orientedPositive_mono
        (osiiStep4MultiGapSelectedRightCommonCarrier d k rho center i)
        hUpos hUT (U0.right_carrier_support i) }
  let C : OSIIChronologicalCompactLocalizationContinuationData d k
      (osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k rho center) := {
    localization := C0.localization
    T := T
    hT := C0.hT.trans_le hCT
    axisPairOrdered := by
      intro a
      exact OSIIChapterV.axisPairOrdered_mono
        (C0.localization.carrier a) hCT (C0.axisPairOrdered a) }
  exact {
    uniform := U
    coherent := C
    slope_eq := rfl }

@[simp] theorem osiiStep4QuantitativeSynchronizedMultiGapContinuationData_T
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    (osiiStep4QuantitativeSynchronizedMultiGapContinuationData
      d k hrho center hcenter).uniform.T =
      max
        (osiiStep4MultiGapExplicitUniformCommonSlopeData
          d k hrho center hcenter).T
        (osiiStep4QuantitativeCoherentContinuationData
          d k hrho center hcenter).T := by
  rfl

noncomputable def osiiStep4SynchronizedSlopePolynomialConstant
    (d k : Nat) [NeZero d] : Real :=
  (2 + 32 * osiiStep4MultiGapReconstructionNormSum d k) +
    osiiStep4CoherentSlopePolynomialConstant d k

theorem osiiStep4SynchronizedSlopePolynomialConstant_nonneg
    (d k : Nat) [NeZero d] :
    0 <= osiiStep4SynchronizedSlopePolynomialConstant d k := by
  unfold osiiStep4SynchronizedSlopePolynomialConstant
  have hR := osiiStep4MultiGapReconstructionNormSum_nonneg d k
  have hA := osiiStep4CoherentSlopePolynomialConstant_nonneg d k
  nlinarith

/-- Final synchronized slope bound in the exact polynomial form consumed by
the first-carrier and MZ estimates. -/
theorem osiiStep4QuantitativeSynchronizedMultiGapContinuationData_T_le
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    (osiiStep4QuantitativeSynchronizedMultiGapContinuationData
      d k hrho center hcenter).uniform.T <=
      osiiStep4SynchronizedSlopePolynomialConstant d k *
        (16 / rho) * (1 + norm center) := by
  let AU := 2 + 32 * osiiStep4MultiGapReconstructionNormSum d k
  let AC := osiiStep4CoherentSlopePolynomialConstant d k
  let F := (16 / rho) * (1 + norm center)
  have hAU : 0 <= AU := by
    dsimp only [AU]
    have := osiiStep4MultiGapReconstructionNormSum_nonneg d k
    nlinarith
  have hAC : 0 <= AC :=
    osiiStep4CoherentSlopePolynomialConstant_nonneg d k
  have hF : 0 <= F := by
    dsimp only [F]
    positivity
  have hU :
      (osiiStep4MultiGapExplicitUniformCommonSlopeData
        d k hrho center hcenter).T <= AU * F := by
    simpa only [AU, F, mul_assoc] using
      osiiStep4MultiGapExplicitUniformCommonSlopeData_T_le
        d k hrho hrho_le center hcenter
  have hC :
      (osiiStep4QuantitativeCoherentContinuationData
        d k hrho center hcenter).T <= AC * F := by
    simpa only [AC, F, mul_assoc] using
      osiiStep4QuantitativeCoherentContinuationData_T_le
        d k hrho hrho_le center hcenter
  rw [osiiStep4QuantitativeSynchronizedMultiGapContinuationData_T]
  have hUtotal : AU * F <= (AU + AC) * F := by
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hAC) hF
  have hCtotal : AC * F <= (AU + AC) * F := by
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hAU) hF
  have hmax : max
      (osiiStep4MultiGapExplicitUniformCommonSlopeData
        d k hrho center hcenter).T
      (osiiStep4QuantitativeCoherentContinuationData
        d k hrho center hcenter).T <= (AU + AC) * F :=
    max_le (hU.trans hUtotal) (hC.trans hCtotal)
  simpa only [osiiStep4SynchronizedSlopePolynomialConstant, AU, AC, F,
    mul_assoc] using hmax

end OSReconstruction

