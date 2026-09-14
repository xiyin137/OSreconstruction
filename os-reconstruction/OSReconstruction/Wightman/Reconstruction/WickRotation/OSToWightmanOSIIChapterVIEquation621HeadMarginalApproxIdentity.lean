import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery

/-!
# Head marginals of spatial approximate identities

The reflected diagonal terms in equation `(6.29)` are obtained by applying a
unit-Jacobian linear coordinate change to a normalized full spatial probe and
then integrating out one absolute basepoint.  This file records the general
finite-dimensional fact that the resulting tail probe is again a normalized
shrinking approximate identity.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Classical

namespace OSReconstruction
namespace OSIIEquation621SpatialApproxIdentityData

/-- The support radius of a normalized approximate identity is positive at
every finite stage. -/
theorem radius_pos
    {m : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData m)
    (N : Nat) :
    0 < Q.radius N := by
  have hexists : exists x : Fin m -> Real, Q.test N x ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : Q.test N = 0 := by
      ext x
      exact h x
    have hone := Q.integral_eq_one N
    rw [hzero] at hone
    simp at hone
  obtain ⟨x, hx⟩ := hexists
  have hx_support :
      x ∈ Function.support (Q.test N : (Fin m -> Real) -> Complex) := by
    simpa [Function.mem_support] using hx
  have hx_ball := Q.support_subset_ball N hx_support
  rw [Metric.mem_ball, dist_zero_right] at hx_ball
  exact (norm_nonneg x).trans_lt hx_ball

/-- A fixed positive bound for the operator norm of a linear coordinate
equivalence.  The lower bound by one also covers zero-dimensional spaces. -/
def coordinateBound
    {m : Nat}
    (e : (Fin m -> Real) ≃L[Real] (Fin m -> Real)) : Real :=
  max 1 ‖e.toContinuousLinearMap‖

theorem coordinateBound_pos
    {m : Nat}
    (e : (Fin m -> Real) ≃L[Real] (Fin m -> Real)) :
    0 < coordinateBound e := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem coordinateBound_nonneg
    {m : Nat}
    (e : (Fin m -> Real) ≃L[Real] (Fin m -> Real)) :
    0 <= coordinateBound e :=
  (coordinateBound_pos e).le

theorem norm_apply_le_coordinateBound_mul
    {m : Nat}
    (e : (Fin m -> Real) ≃L[Real] (Fin m -> Real))
    (x : Fin m -> Real) :
    ‖e x‖ <= coordinateBound e * ‖x‖ := by
  exact (e.toContinuousLinearMap.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right
      (le_max_right (1 : Real) ‖e.toContinuousLinearMap‖)
      (norm_nonneg x))

/-- Pull a full approximate identity through a volume-preserving linear chart
and integrate out its first `head` coordinates.  The factor `2` in the output
radius converts the inherited closed-ball bound into the open-ball support
contract used by `OSIIEquation621SpatialApproxIdentityData`. -/
noncomputable def headMarginalPullback
    {head tail : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData (head + tail))
    (e : (Fin (head + tail) -> Real) ≃L[Real]
      (Fin (head + tail) -> Real))
    (he : MeasurePreserving
      e.symm.toHomeomorph.toMeasurableEquiv) :
    OSIIEquation621SpatialApproxIdentityData tail where
  test N :=
    integrateHeadBlock
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm (Q.test N))
  radius N := 2 * coordinateBound e * Q.radius N
  nonneg := by
    intro N x
    apply integrateHeadBlock_re_nonneg_of_re_nonneg
    intro y
    exact Q.nonneg N (e.symm y)
  real := by
    intro N x
    apply integrateHeadBlock_im_eq_zero_of_im_eq_zero
    intro y
    exact Q.real N (e.symm y)
  integral_eq_one := by
    intro N
    let F : SchwartzMap (Fin (head + tail) -> Real) Complex :=
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm (Q.test N)
    calc
      (∫ x : Fin tail -> Real,
          integrateHeadBlock (m := head) (n := tail) F x) =
          ∫ y : Fin (head + tail) -> Real, F y := by
            exact integral_integrateHeadBlock F
      _ = ∫ y : Fin (head + tail) -> Real, Q.test N y := by
        simpa [F, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
          Function.comp_def] using he.integral_comp' (Q.test N)
      _ = 1 := Q.integral_eq_one N
  compactSupport := by
    intro N
    let F : SchwartzMap (Fin (head + tail) -> Real) Complex :=
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm (Q.test N)
    let R : Real := coordinateBound e * Q.radius N
    have hF_support :
        Function.support (F : (Fin (head + tail) -> Real) -> Complex) ⊆
          Metric.closedBall 0 R := by
      intro x hx
      have hxQ :
          e.symm x ∈ Function.support
            (Q.test N : (Fin (head + tail) -> Real) -> Complex) := by
        simpa [F, Function.mem_support,
          SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hx
      have hxQ_ball := Q.support_subset_ball N hxQ
      rw [Metric.mem_ball, dist_zero_right] at hxQ_ball
      rw [Metric.mem_closedBall, dist_zero_right]
      calc
        ‖x‖ = ‖e (e.symm x)‖ := by rw [e.apply_symm_apply]
        _ <= coordinateBound e * ‖e.symm x‖ :=
          norm_apply_le_coordinateBound_mul e (e.symm x)
        _ <= coordinateBound e * Q.radius N :=
          mul_le_mul_of_nonneg_left hxQ_ball.le (coordinateBound_nonneg e)
    have hF_tsupport :
        tsupport (F : (Fin (head + tail) -> Real) -> Complex) ⊆
          Metric.closedBall 0 R :=
      closure_minimal hF_support Metric.isClosed_closedBall
    have htail :
        tsupport
            ((integrateHeadBlock (m := head) (n := tail) F :
              SchwartzMap (Fin tail -> Real) Complex) :
              (Fin tail -> Real) -> Complex) ⊆
          Metric.closedBall 0 R :=
      integrateHeadBlock_tsupport_subset_closedBall F hF_tsupport
    exact IsCompact.of_isClosed_subset
      (isCompact_closedBall 0 R) (isClosed_tsupport _) htail
  support_subset_ball := by
    intro N x hx
    let F : SchwartzMap (Fin (head + tail) -> Real) Complex :=
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm (Q.test N)
    let R : Real := coordinateBound e * Q.radius N
    have hF_support :
        Function.support (F : (Fin (head + tail) -> Real) -> Complex) ⊆
          Metric.closedBall 0 R := by
      intro y hy
      have hyQ :
          e.symm y ∈ Function.support
            (Q.test N : (Fin (head + tail) -> Real) -> Complex) := by
        simpa [F, Function.mem_support,
          SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hy
      have hyQ_ball := Q.support_subset_ball N hyQ
      rw [Metric.mem_ball, dist_zero_right] at hyQ_ball
      rw [Metric.mem_closedBall, dist_zero_right]
      calc
        ‖y‖ = ‖e (e.symm y)‖ := by rw [e.apply_symm_apply]
        _ <= coordinateBound e * ‖e.symm y‖ :=
          norm_apply_le_coordinateBound_mul e (e.symm y)
        _ <= coordinateBound e * Q.radius N :=
          mul_le_mul_of_nonneg_left hyQ_ball.le (coordinateBound_nonneg e)
    have hF_tsupport :
        tsupport (F : (Fin (head + tail) -> Real) -> Complex) ⊆
          Metric.closedBall 0 R :=
      closure_minimal hF_support Metric.isClosed_closedBall
    have hx_closed : x ∈ Metric.closedBall (0 : Fin tail -> Real) R :=
      integrateHeadBlock_tsupport_subset_closedBall F hF_tsupport
        (subset_tsupport _ hx)
    rw [Metric.mem_closedBall, dist_zero_right] at hx_closed
    rw [Metric.mem_ball, dist_zero_right]
    have hR_pos : 0 < R :=
      mul_pos (coordinateBound_pos e) (Q.radius_pos N)
    calc
      ‖x‖ <= R := hx_closed
      _ < 2 * R := by linarith
      _ = 2 * coordinateBound e * Q.radius N := by
        simp [R, mul_assoc]
  radius_tendsto := by
    simpa [mul_assoc] using
      (Q.radius_tendsto.const_mul (2 * coordinateBound e))

@[simp]
theorem headMarginalPullback_test
    {head tail : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData (head + tail))
    (e : (Fin (head + tail) -> Real) ≃L[Real]
      (Fin (head + tail) -> Real))
    (he : MeasurePreserving e.symm.toHomeomorph.toMeasurableEquiv)
    (N : Nat) :
    (Q.headMarginalPullback e he).test N =
      integrateHeadBlock
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm
          (Q.test N)) :=
  rfl

/-- Pullback and head marginalization transport a full translation to the
tail of the transformed center.  The transformed head translation disappears
under integration. -/
theorem headMarginalPullback_translatedTest
    {head tail : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData (head + tail))
    (e : (Fin (head + tail) -> Real) ≃L[Real]
      (Fin (head + tail) -> Real))
    (he : MeasurePreserving e.symm.toHomeomorph.toMeasurableEquiv)
    (a : Fin (head + tail) -> Real)
    (N : Nat) :
    integrateHeadBlock
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm
          (Q.translatedTest a N)) =
      (Q.headMarginalPullback e he).translatedTest
        (splitLast head tail (e a)) N := by
  let F : SchwartzMap (Fin (head + tail) -> Real) Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm (Q.test N)
  have hpull :
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm
          (Q.translatedTest a N) =
        SCV.translateSchwartz (-(e a)) F := by
    ext x
    change Q.test N (e.symm x + -a) =
      Q.test N (e.symm (x + -(e a)))
    congr 1
    rw [map_add, map_neg, e.symm_apply_apply]
  let ahead := splitFirst head tail (e a)
  let atail := splitLast head tail (e a)
  have hfst (x : Fin (head + tail) -> Real) :
      ((SCV.finAppendCLE head tail).symm x).1 =
        splitFirst head tail x := by
    ext i
    rfl
  have hsnd (x : Fin (head + tail) -> Real) :
      ((SCV.finAppendCLE head tail).symm x).2 =
        splitLast head tail x := by
    ext i
    rfl
  have hdecomp :
      -(e a) =
        zeroTailBlockShift (m := head) (n := tail) (-ahead) +
          zeroHeadBlockShift (m := head) (n := tail) (-atail) := by
    apply (SCV.finAppendCLE head tail).symm.injective
    apply Prod.ext
    · rw [map_add, Prod.fst_add]
      simp only [hfst, splitFirst_zeroTailBlockShift_eq,
        splitFirst_zeroHeadBlockShift_eq_zero, add_zero]
      ext i
      rfl
    · rw [map_add, Prod.snd_add]
      simp only [hsnd, splitLast_zeroTailBlockShift_eq_zero,
        splitLast_zeroHeadBlockShift_eq, zero_add]
      ext i
      rfl
  have htranslate :
      SCV.translateSchwartz (-(e a)) F =
        SCV.translateSchwartz
          (zeroTailBlockShift (m := head) (n := tail) (-ahead))
          (SCV.translateSchwartz
            (zeroHeadBlockShift (m := head) (n := tail) (-atail)) F) := by
    ext x
    simp only [SCV.translateSchwartz_apply]
    rw [hdecomp]
    congr 1
    abel
  calc
    integrateHeadBlock
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm
          (Q.translatedTest a N)) =
        integrateHeadBlock
          (SCV.translateSchwartz (-(e a)) F) := by rw [hpull]
    _ = integrateHeadBlock
          (SCV.translateSchwartz
            (zeroTailBlockShift (m := head) (n := tail) (-ahead))
            (SCV.translateSchwartz
              (zeroHeadBlockShift (m := head) (n := tail) (-atail)) F)) := by
        rw [htranslate]
    _ = integrateHeadBlock
          (SCV.translateSchwartz
            (zeroHeadBlockShift (m := head) (n := tail) (-atail)) F) :=
      integrateHeadBlock_translateSchwartz_head (-ahead) _
    _ = SCV.translateSchwartz (-atail)
          (integrateHeadBlock F) :=
      integrateHeadBlock_translateSchwartz_tail (-atail) F
    _ = (Q.headMarginalPullback e he).translatedTest
          (splitLast head tail (e a)) N := by
      rfl

end OSIIEquation621SpatialApproxIdentityData
end OSReconstruction
