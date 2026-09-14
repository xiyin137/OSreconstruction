import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Explicit decay constants for OS II

The boundary construction integrates a power just above the dimension.
Its constant must remain explicit when the number of variables increases.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace OSReconstruction

theorem natCast_le_three_pow (n : Nat) : (n : Real) <= (3 : Real) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    have hone : (1 : Real) <= 3 ^ n := one_le_pow₀ (by norm_num)
    nlinarith

/-- A dimension-explicit bound for the integrable sup-norm decay weight. -/
theorem integral_one_add_pi_norm_neg_succ_le (m : Nat) :
    (∫ x : Fin m -> Real, (1 + ‖x‖) ^ (-((m + 1 : Nat) : Real))) <=
      (m + 1 : Real) * 2 ^ m := by
  let r : Real := (m + 1 : Nat)
  let q : Real := -(r⁻¹ * m)
  have hr : 0 < r := by dsimp [r]; positivity
  have hq : -1 < q := by
    dsimp [q]
    rw [neg_lt_neg_iff, inv_mul_lt_iff₀' hr, one_mul]
    dsimp [r]
    norm_num
  have hq_one : q + 1 = r⁻¹ := by
    dsimp [q, r]
    push_cast
    field_simp
    ring
  let f : (Fin m -> Real) -> Real := fun x => (1 + ‖x‖) ^ (-r)
  have hf : Integrable f := by
    apply integrable_one_add_norm
    simp [r]
  have hf_nonneg : ∀ x, 0 <= f x := fun x => Real.rpow_nonneg (by positivity) _
  have hf_le_one : ∀ x, f x <= 1 := by
    intro x
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [norm_nonneg x]) (by linarith)
  have hg : IntegrableOn (fun t : Real => (2 : Real) ^ m * t ^ q) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : Real) <= 1)]
    exact (intervalIntegral.intervalIntegrable_rpow' hq).const_mul _
  have hlevel (t : Real) (ht : t ∈ Ioc (0 : Real) 1) :
      volume.real {x : Fin m -> Real | t <= f x} <= (2 : Real) ^ m * t ^ q := by
    have ha : 0 <= t ^ (-r⁻¹) - 1 := by
      apply sub_nonneg.mpr
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (by simp [hr.le])
    have hset : {x : Fin m -> Real | t <= f x} =
        Metric.closedBall 0 (t ^ (-r⁻¹) - 1) := by
      ext x
      simp only [mem_setOf_eq, mem_closedBall_zero_iff]
      exact le_rpow_one_add_norm_iff_norm_le hr ht.1 x
    rw [hset, measureReal_def, Real.volume_pi_closedBall _ ha,
      ENNReal.toReal_ofReal (by positivity), Fintype.card_fin, mul_pow]
    calc
      (2 : Real) ^ m * (t ^ (-r⁻¹) - 1) ^ m <=
          (2 : Real) ^ m * (t ^ (-r⁻¹)) ^ m := by
        gcongr
        exact sub_le_self _ zero_le_one
      _ = (2 : Real) ^ m * t ^ q := by
        rw [← Real.rpow_natCast (t ^ (-r⁻¹)) m, ← Real.rpow_mul ht.1.le]
        simp only [q, neg_mul]
  change (∫ x, f x) <= _
  rw [hf.integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hf_nonneg) (Filter.Eventually.of_forall hf_le_one)]
  calc
    (∫ t in Ioc (0 : Real) 1, volume.real {x | t <= f x}) <=
        ∫ t in Ioc (0 : Real) 1, (2 : Real) ^ m * t ^ q := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
      · exact hg
      · exact (ae_restrict_mem measurableSet_Ioc).mono hlevel
    _ = (2 : Real) ^ m * r := by
      rw [integral_const_mul,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : Real) <= 1),
        integral_rpow (Or.inl hq), hq_one]
      simp [ne_of_gt (inv_pos.mpr hr)]
    _ = (m + 1 : Real) * 2 ^ m := by dsimp [r]; push_cast; ring

theorem integral_one_add_pi_norm_neg_succ_le_three_pow (m : Nat) :
    (∫ x : Fin m -> Real, (1 + ‖x‖) ^ (-((m + 1 : Nat) : Real))) <=
      (3 : Real) ^ (2 * m + 1) := by
  apply (integral_one_add_pi_norm_neg_succ_le m).trans
  calc
    (m + 1 : Real) * 2 ^ m <= (3 : Real) ^ (m + 1) * 3 ^ m := by
      exact mul_le_mul (by simpa using natCast_le_three_pow (m + 1))
        (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by positivity) (by positivity)
    _ = (3 : Real) ^ (2 * m + 1) := by rw [← pow_add]; congr 1; omega

end OSReconstruction
