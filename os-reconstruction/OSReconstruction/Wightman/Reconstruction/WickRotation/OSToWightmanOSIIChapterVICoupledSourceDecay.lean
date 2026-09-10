import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Operator.NormedSpace
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeSpatialCurrying

/-!
# Coupled Schwartz-source decay

Taking a spatial slice of a coupled source preserves rapid decay in the time
parameter. The explicit loss below is additive in the time and spatial
weights; in particular, the later time integral costs exactly `k + 1` powers.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterVI

/-- The full-source seminorm rectangle needed to retain `w` powers of decay
in the first variable. -/
def coupledSourceSeminorms (s : Finset (Nat × Nat)) (w : Nat) :
    Finset (Nat × Nat) :=
  Finset.Iic (w + s.sup Prod.fst, s.sup Prod.snd)

theorem schwartzPartialEval_finsetSeminorm_decay
    {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup X] [NormedSpace Real X]
    (Phi : SchwartzMap (E × X) Complex) (x : E)
    (s : Finset (Nat × Nat)) (w : Nat) :
    s.sup (schwartzSeminormFamily Complex X Complex)
        (SCV.schwartzPartialEval₁ Phi x) <=
      (1 + ‖x‖) ^ (-(w : Real)) *
        (2 ^ (w + s.sup Prod.fst) *
          (coupledSourceSeminorms s w).sup
            (schwartzSeminormFamily Complex (E × X) Complex) Phi) := by
  apply Seminorm.finset_sup_apply_le
  · positivity
  intro a ha
  have ha₁ : a.1 <= s.sup Prod.fst := Finset.le_sup ha
  have ha₂ : a.2 <= s.sup Prod.snd := Finset.le_sup ha
  apply SchwartzMap.seminorm_le_bound Complex a.1 a.2 _ (by positivity)
  intro y
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast,
    ← div_eq_inv_mul, le_div_iff₀' (by positivity)]
  have hweight :
      (1 + ‖x‖) ^ w * ‖y‖ ^ a.1 <=
        (1 + ‖(x, y)‖) ^ (w + a.1) := by
    rw [pow_add]
    gcongr
    · exact le_max_left _ _
    · exact (le_max_right ‖x‖ ‖y‖).trans (by simp [Prod.norm_def])
  calc
    (1 + ‖x‖) ^ w *
        (‖y‖ ^ a.1 * ‖iteratedFDeriv Real a.2
          (fun z => SCV.schwartzPartialEval₁ Phi x z) y‖) <=
      (1 + ‖(x, y)‖) ^ (w + a.1) *
        ‖iteratedFDeriv Real a.2 (Phi : E × X -> Complex) (x, y)‖ := by
      rw [← mul_assoc]
      exact mul_le_mul hweight
        (SCV.norm_iteratedFDeriv_partialEval₁_le Phi x a.2 y)
        (by positivity) (by positivity)
    _ <= 2 ^ (w + s.sup Prod.fst) *
        (coupledSourceSeminorms s w).sup
          (schwartzSeminormFamily Complex (E × X) Complex) Phi := by
      exact SchwartzMap.one_add_le_sup_seminorm_apply
        (m := (w + s.sup Prod.fst, s.sup Prod.snd))
        (Nat.add_le_add_left ha₁ w) ha₂ Phi (x, y)

variable {d k : Nat}

/-- A polynomially growing spatial-distribution family can be integrated
against the moving spatial slices of one coupled Schwartz source. -/
def coupledSourceIntegral
    (L : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) : Complex :=
  ∫ x : Fin k -> Real, L x (SCV.schwartzPartialEval₁ Phi x)

theorem continuous_coupledSourcePairing
    (L : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (hL : forall chi : SchwartzMap (Section43SpatialSpace d k) Complex,
      Continuous (fun x => L x chi))
    (s : Finset (Nat × Nat)) (C : Real) (N : Nat) (hC : 0 < C)
    (hbound : forall x chi,
      ‖L x chi‖ <= C * (1 + ‖x‖) ^ N *
        s.sup (schwartzSeminormFamily Complex
          (Section43SpatialSpace d k) Complex) chi)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    Continuous (fun x => L x (SCV.schwartzPartialEval₁ Phi x)) := by
  let F := (nPointTimeSpatialSchwartzCLE (d := d) (n := k)).symm Phi
  apply continuous_iff_continuousAt.2
  intro x
  have hlocal : forall y, y ∈ Metric.ball x 1 -> forall chi,
      ‖L y chi‖ <= (C * (2 + ‖x‖) ^ N) *
        s.sup (schwartzSeminormFamily Complex
          (Section43SpatialSpace d k) Complex) chi := by
    intro y hy chi
    have hnorm : ‖y‖ <= ‖x‖ + 1 := (norm_lt_of_mem_ball hy).le
    have hbase : 1 + ‖y‖ <= 2 + ‖x‖ := by linarith
    exact (hbound y chi).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hbase N) hC.le)
        (apply_nonneg _ _))
  have hmove := continuousOn_osiiMovingSpatialSlicePairing L
    (Metric.ball x 1) (fun chi => (hL chi).continuousOn)
    s (C * (2 + ‖x‖) ^ N) (by positivity) hlocal F
  have heq : (fun y => L y (osiiFullSourceSpatialSlice F y)) =
      fun y => L y (SCV.schwartzPartialEval₁ Phi y) := by
    funext y
    simp [F, osiiFullSourceSpatialSlice]
  rw [heq] at hmove
  exact (hmove x (Metric.mem_ball_self zero_lt_one)).continuousAt
    (Metric.ball_mem_nhds x zero_lt_one)

/-- An explicit integrable time weight. This choice retains the arity-linear
Schwartz order instead of hiding the dimension in `integrablePower`. -/
theorem integrable_timeDecay (k : Nat) :
    Integrable (fun x : Fin k -> Real =>
      (1 + ‖x‖) ^ (-((k + 1 : Nat) : Real))) := by
  apply integrable_one_add_norm
  simp

def timeDecayIntegral (k : Nat) : Real :=
  ∫ x : Fin k -> Real, (1 + ‖x‖) ^ (-((k + 1 : Nat) : Real))

theorem timeDecayIntegral_nonneg (k : Nat) : 0 <= timeDecayIntegral k := by
  exact integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _

theorem norm_coupledSourcePairing_le
    (L : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (s : Finset (Nat × Nat)) (C : Real) (N : Nat) (hC : 0 <= C)
    (hbound : forall x chi,
      ‖L x chi‖ <= C * (1 + ‖x‖) ^ N *
        s.sup (schwartzSeminormFamily Complex
          (Section43SpatialSpace d k) Complex) chi)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (x : Fin k -> Real) :
    ‖L x (SCV.schwartzPartialEval₁ Phi x)‖ <=
      (1 + ‖x‖) ^ (-((k + 1 : Nat) : Real)) *
        (C * 2 ^ (N + (k + 1) + s.sup Prod.fst) *
          (coupledSourceSeminorms s (N + (k + 1))).sup
            (schwartzSeminormFamily Complex
              (Section43TimeSpatialSpace d k) Complex) Phi) := by
  have hdecay := schwartzPartialEval_finsetSeminorm_decay Phi x s (N + (k + 1))
  have hcancel :
      (1 + ‖x‖) ^ N * (1 + ‖x‖) ^ (-((N + (k + 1) : Nat) : Real)) =
        (1 + ‖x‖) ^ (-((k + 1 : Nat) : Real)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast,
      Real.rpow_neg (by positivity), Real.rpow_natCast, pow_add]
    field_simp
  calc
    ‖L x (SCV.schwartzPartialEval₁ Phi x)‖ <=
        C * (1 + ‖x‖) ^ N *
          ((1 + ‖x‖) ^ (-((N + (k + 1) : Nat) : Real)) *
            (2 ^ (N + (k + 1) + s.sup Prod.fst) *
              (coupledSourceSeminorms s (N + (k + 1))).sup
                (schwartzSeminormFamily Complex
                  (Section43TimeSpatialSpace d k) Complex) Phi)) :=
      (hbound x _).trans (mul_le_mul_of_nonneg_left hdecay (by positivity))
    _ = _ := by rw [← mul_assoc, mul_assoc C, hcancel]; ring

theorem integrable_coupledSourcePairing
    (L : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (hL : forall chi : SchwartzMap (Section43SpatialSpace d k) Complex,
      Continuous (fun x => L x chi))
    (s : Finset (Nat × Nat)) (C : Real) (N : Nat) (hC : 0 < C)
    (hbound : forall x chi,
      ‖L x chi‖ <= C * (1 + ‖x‖) ^ N *
        s.sup (schwartzSeminormFamily Complex
          (Section43SpatialSpace d k) Complex) chi)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    Integrable (fun x => L x (SCV.schwartzPartialEval₁ Phi x)) := by
  refine Integrable.mono'
    ((integrable_timeDecay k).mul_const
      (C * 2 ^ (N + (k + 1) + s.sup Prod.fst) *
        (coupledSourceSeminorms s (N + (k + 1))).sup
          (schwartzSeminormFamily Complex
            (Section43TimeSpatialSpace d k) Complex) Phi))
    (continuous_coupledSourcePairing L hL s C N hC hbound Phi
      ).aestronglyMeasurable ?_
  exact Eventually.of_forall
    (norm_coupledSourcePairing_le L s C N hC.le hbound Phi)

theorem norm_coupledSourceIntegral_le
    (L : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (s : Finset (Nat × Nat)) (C : Real) (N : Nat) (hC : 0 <= C)
    (hbound : forall x chi,
      ‖L x chi‖ <= C * (1 + ‖x‖) ^ N *
        s.sup (schwartzSeminormFamily Complex
          (Section43SpatialSpace d k) Complex) chi)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    ‖coupledSourceIntegral L Phi‖ <=
      (C * 2 ^ (N + (k + 1) + s.sup Prod.fst) * timeDecayIntegral k) *
        (coupledSourceSeminorms s (N + (k + 1))).sup
          (schwartzSeminormFamily Complex
            (Section43TimeSpatialSpace d k) Complex) Phi := by
  calc
    ‖coupledSourceIntegral L Phi‖ <=
        ∫ x : Fin k -> Real,
          (1 + ‖x‖) ^ (-((k + 1 : Nat) : Real)) *
            (C * 2 ^ (N + (k + 1) + s.sup Prod.fst) *
              (coupledSourceSeminorms s (N + (k + 1))).sup
                (schwartzSeminormFamily Complex
                  (Section43TimeSpatialSpace d k) Complex) Phi) := by
      exact norm_integral_le_of_norm_le ((integrable_timeDecay k).mul_const _)
        (Eventually.of_forall
          (norm_coupledSourcePairing_le L s C N hC hbound Phi))
    _ = _ := by rw [integral_mul_const]; unfold timeDecayIntegral; ring

/-- The actual coupled-source integral as a continuous linear map, with no
separated-source or compact-time-support assumption. -/
def coupledSourceIntegralCLM
    (L : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (hL : forall chi : SchwartzMap (Section43SpatialSpace d k) Complex,
      Continuous (fun x => L x chi))
    (s : Finset (Nat × Nat)) (C : Real) (N : Nat) (hC : 0 < C)
    (hbound : forall x chi,
      ‖L x chi‖ <= C * (1 + ‖x‖) ^ N *
        s.sup (schwartzSeminormFamily Complex
          (Section43SpatialSpace d k) Complex) chi) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex :=
  SchwartzMap.mkCLMtoNormedSpace (𝕜 := Complex) (coupledSourceIntegral L)
    (fun Phi Psi => by
      unfold coupledSourceIntegral
      rw [← integral_add
        (integrable_coupledSourcePairing L hL s C N hC hbound Phi)
        (integrable_coupledSourcePairing L hL s C N hC hbound Psi)]
      apply integral_congr_ae
      filter_upwards with x
      have hslice : SCV.schwartzPartialEval₁ (Phi + Psi) x =
          SCV.schwartzPartialEval₁ Phi x + SCV.schwartzPartialEval₁ Psi x := by
        ext y
        rfl
      rw [hslice, map_add])
    (fun c Phi => by
      unfold coupledSourceIntegral
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with x
      have hslice : SCV.schwartzPartialEval₁ (c • Phi) x =
          c • SCV.schwartzPartialEval₁ Phi x := by
        ext y
        rfl
      rw [hslice, map_smul]
      rfl)
    (by
      refine ⟨coupledSourceSeminorms s (N + (k + 1)),
        C * 2 ^ (N + (k + 1) + s.sup Prod.fst) * timeDecayIntegral k,
        mul_nonneg (by positivity) (timeDecayIntegral_nonneg k), ?_⟩
      exact norm_coupledSourceIntegral_le L s C N hC.le hbound)

@[simp] theorem coupledSourceIntegralCLM_apply
    (L : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (hL : forall chi : SchwartzMap (Section43SpatialSpace d k) Complex,
      Continuous (fun x => L x chi))
    (s : Finset (Nat × Nat)) (C : Real) (N : Nat) (hC : 0 < C)
    (hbound : forall x chi,
      ‖L x chi‖ <= C * (1 + ‖x‖) ^ N *
        s.sup (schwartzSeminormFamily Complex
          (Section43SpatialSpace d k) Complex) chi)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    coupledSourceIntegralCLM L hL s C N hC hbound Phi =
      coupledSourceIntegral L Phi := rfl

set_option backward.isDefEq.respectTransparency false in
theorem schwartz_seminorm_lineDeriv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (Phi : SchwartzMap E Complex) (v : E) (p l : Nat) :
    SchwartzMap.seminorm Complex p l
        (LineDeriv.lineDerivOpCLM Complex (SchwartzMap E Complex) v Phi) <=
      ‖v‖ * SchwartzMap.seminorm Complex p (l + 1) Phi := by
  apply SchwartzMap.seminorm_le_bound Complex p l _ (by positivity)
  intro x
  let ev : (E →L[Real] Complex) →L[Real] Complex :=
    ContinuousLinearMap.apply Real Complex v
  have hev : ‖ev‖ <= ‖v‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro T
    exact (ContinuousLinearMap.le_opNorm T v).trans_eq (mul_comm _ _)
  have hf : ContDiff Real (↑(⊤ : ℕ∞)) (fderiv Real (Phi : E -> Complex)) :=
    (SchwartzMap.fderivCLM Complex E Complex Phi).smooth'
  change ‖x‖ ^ p * ‖iteratedFDeriv Real l
      (ev ∘ fderiv Real (Phi : E -> Complex)) x‖ <= _
  rw [ev.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast le_top)]
  calc
    ‖x‖ ^ p * ‖ev.compContinuousMultilinearMap
        (iteratedFDeriv Real l (fderiv Real (Phi : E -> Complex)) x)‖ <=
        ‖x‖ ^ p *
          (‖v‖ * ‖iteratedFDeriv Real l (fderiv Real (Phi : E -> Complex)) x‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (ev.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_right hev (norm_nonneg _))
    _ = (‖x‖ ^ p * ‖iteratedFDeriv Real (l + 1) (Phi : E -> Complex) x‖) *
        ‖v‖ := by rw [norm_iteratedFDeriv_fderiv]; ring
    _ <= SchwartzMap.seminorm Complex p (l + 1) Phi * ‖v‖ :=
      mul_le_mul_of_nonneg_right (SchwartzMap.le_seminorm Complex p (l + 1) Phi x)
        (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem schwartz_seminorm_directionalPow_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (Phi : SchwartzMap E Complex) (v : E) (p l j : Nat) :
    SchwartzMap.seminorm Complex p l
        (((LineDeriv.lineDerivOpCLM Complex (SchwartzMap E Complex) v) ^ j) Phi) <=
      ‖v‖ ^ j * SchwartzMap.seminorm Complex p (l + j) Phi := by
  induction j generalizing l with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    calc
      _ <= ‖v‖ * SchwartzMap.seminorm Complex p (l + 1)
          (((LineDeriv.lineDerivOpCLM Complex (SchwartzMap E Complex) v) ^ j) Phi) :=
        schwartz_seminorm_lineDeriv_le _ v p l
      _ <= ‖v‖ * (‖v‖ ^ j * SchwartzMap.seminorm Complex p (l + 1 + j) Phi) :=
        mul_le_mul_of_nonneg_left (ih (l + 1)) (norm_nonneg _)
      _ = _ := by
        rw [show l + 1 + j = l + (j + 1) by omega, pow_succ']
        ring

theorem schwartz_rectangle_directionalPow_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (Phi : SchwartzMap E Complex) (v : E) (p l j : Nat) :
    (Finset.Iic (p, l)).sup (schwartzSeminormFamily Complex E Complex)
        (((LineDeriv.lineDerivOpCLM Complex (SchwartzMap E Complex) v) ^ j) Phi) <=
      ‖v‖ ^ j *
        (Finset.Iic (p, l + j)).sup
          (schwartzSeminormFamily Complex E Complex) Phi := by
  apply Seminorm.finset_sup_apply_le
  · positivity
  intro a ha
  have ha' : a.1 <= p ∧ a.2 <= l := Finset.mem_Iic.mp ha
  have hmem : (a.1, a.2 + j) ∈ Finset.Iic (p, l + j) :=
    Finset.mem_Iic.mpr ⟨ha'.1, Nat.add_le_add_right ha'.2 j⟩
  exact (schwartz_seminorm_directionalPow_le Phi v a.1 a.2 j).trans
    (mul_le_mul_of_nonneg_left
      (Seminorm.le_finset_sup_apply
        (p := schwartzSeminormFamily Complex E Complex) (x := Phi) hmem)
      (by positivity))

end OSIIChapterVI
end OSReconstruction
