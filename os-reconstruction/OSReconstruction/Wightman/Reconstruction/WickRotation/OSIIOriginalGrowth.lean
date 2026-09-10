/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Specification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIOriginalSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIQuantitativeCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIQuantitativeGrowthArithmetic

/-!
# The original OS II growth conventions

Equation (4.1) is imposed only on zero-diagonal Euclidean tests. Equation
(4.3) is a conclusion about full Schwartz-space Wightman distributions.
The norm comparisons and factorial absorption below are uniform in arity.
-/

noncomputable section

open Complex
open scoped Classical

namespace OSReconstruction

theorem osiiOriginalNPointSeminorm_nonneg (d n r : Nat) (f : SchwartzNPoint d n) :
    0 <= osiiOriginalNPointSeminorm d n r f := osiiOriginalSeminorm_nonneg _ _

theorem osiiOriginalNPointSeminorm_le (d n s : Nat) (f : SchwartzNPoint d n) :
    osiiOriginalNPointSeminorm d n (n * s) f <=
      (n * (d + 1) + 1 : Real) ^ (n * s) * osArityLinearSchwartzSeminorm d n s f := by
  have hQ := osiiOriginalSeminorm_le_squareSeminorm (n * s)
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (flattenCLEquivReal n (d + 1)).symm f)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hQ
  apply hQ.trans
  have h := squareSeminorm_compContinuousLinearEquiv_le
    (flattenCLEquivReal n (d + 1)).symm 1 1 le_rfl le_rfl
      (osiiFlatten_opNorm_le _ _) (osiiFlatten_symm_opNorm_le _ _) f (n * s)
  simp only [one_mul, one_pow] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem osArityLinearSchwartzSeminorm_le_original (d n s : Nat) (f : SchwartzNPoint d n) :
    osArityLinearSchwartzSeminorm d n s f <=
      (n * (d + 1) + 1 : Real) ^ (n * s) * osiiOriginalNPointSeminorm d n (n * s) f := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (flattenCLEquivReal n (d + 1)).symm f
  have h := squareSeminorm_compContinuousLinearEquiv_le
    (flattenCLEquivReal n (d + 1)) 1 1 le_rfl le_rfl
      (osiiFlatten_symm_opNorm_le _ _) (osiiFlatten_opNorm_le _ _) g (n * s)
  have heq : SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (flattenCLEquivReal n (d + 1)) g = f := by
    ext x
    exact congrArg f ((flattenCLEquivReal n (d + 1)).symm_apply_apply x)
  rw [heq] at h
  simp only [one_mul, one_pow] at h
  have hfinal := h.trans (squareSeminorm_le_osiiOriginalSeminorm (n * s) g)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hfinal

/-- Original E0' supplies the current arity-linear input without an additional
hypothesis. Only the uniformly controlled numerical convention changes. -/
def OSIIOriginalLinearGrowthCondition.toArityLinearGrowthCondition
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (g : OSIIOriginalLinearGrowthCondition d OS) : OSLinearGrowthCondition d OS where
  normalized_zero := g.normalized_zero
  sobolev_index := g.sobolev_index
  alpha := max 1 g.alpha
  beta := (d + 2 : Real) ^ g.sobolev_index
  gamma := g.gamma + ((2 * g.sobolev_index : Nat) : Real)
  alpha_pos := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  beta_pos := pow_pos (by positivity) _
  growth_estimate := by
    intro n f
    by_cases hn : n = 0
    · subst n
      rw [g.normalized_zero, osArityLinearSchwartzSeminorm_zero]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, Real.one_rpow, mul_one]
      exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hfpos : 0 < (n.factorial : Real) := by exact_mod_cast Nat.factorial_pos n
      have hdim := osiiDimensionPower_le_factorial (d + 1) n g.sobolev_index
      have hcoef : (g.alpha * (n.factorial : Real) ^ g.gamma) *
          (n * (d + 1) + 1 : Real) ^ (n * g.sobolev_index) <=
        max 1 g.alpha * ((d + 2 : Real) ^ g.sobolev_index) ^ n *
          (n.factorial : Real) ^ (g.gamma + ((2 * g.sobolev_index : Nat) : Real)) := by
        rw [Real.rpow_add hfpos, Real.rpow_natCast]
        calc
          _ <= (max 1 g.alpha * (n.factorial : Real) ^ g.gamma) *
              (((d + 2 : Real) ^ g.sobolev_index) ^ n *
                (n.factorial : Real) ^ (2 * g.sobolev_index)) := by
            apply mul_le_mul
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
              (by simpa [Nat.cast_add, Nat.cast_one, add_assoc,
                show (1 : Real) + 1 = 2 by norm_num] using hdim)
              (by positivity) (by positivity)
          _ = _ := by ring
      have hb := (g.growth_estimate n hnpos f).trans
        (mul_le_mul_of_nonneg_left (osiiOriginalNPointSeminorm_le d n g.sobolev_index f.1)
          (mul_nonneg g.alpha_pos.le (by positivity)))
      exact hb.trans (by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcoef (apply_nonneg _ _))

/-- The current E0' input also implies the paper's original factorial-only
condition. The comparison constants are chosen once, not arity by arity. -/
theorem OSArityLinearGrowthCondition.exists_original
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS) : Nonempty (OSIIOriginalLinearGrowthCondition d OS) := by
  let s := lgc.sobolev_index + 1
  obtain ⟨C, Gamma, hC, hfactor⟩ := exponential_dimensionPower_le_factorial
    (d + 1) s lgc.beta lgc.gamma lgc.beta_pos.le
  refine ⟨{
    normalized_zero := lgc.normalized_zero
    sobolev_index := s
    sobolev_index_pos := Nat.succ_pos _
    alpha := lgc.alpha * C
    gamma := Gamma
    alpha_pos := mul_pos lgc.alpha_pos hC
    growth_estimate := ?_ }⟩
  intro n _hn f
  have ha := lgc.alpha_pos
  have hb := lgc.beta_pos
  have hQ := osiiOriginalNPointSeminorm_nonneg d n (n * s) f.1
  have hP := (lgc.growth_estimate n f).trans (mul_le_mul_of_nonneg_left
    (osArityLinearSchwartzSeminorm_mono d n (Nat.le_succ lgc.sobolev_index) f.1)
      (by positivity))
  have hcoef := mul_le_mul_of_nonneg_left (hfactor n) lgc.alpha_pos.le
  simp only [Nat.cast_add, Nat.cast_one] at hcoef
  calc
    ‖OS.S n f‖ <= (lgc.alpha * lgc.beta ^ n * (n.factorial : Real) ^ lgc.gamma) *
        ((n * (d + 1) + 1 : Real) ^ (n * s) * osiiOriginalNPointSeminorm d n (n * s) f.1) :=
      hP.trans (mul_le_mul_of_nonneg_left
        (osArityLinearSchwartzSeminorm_le_original d n s f.1) (by positivity))
    _ = (lgc.alpha * (lgc.beta ^ n * (n.factorial : Real) ^ lgc.gamma *
        (n * (d + 1) + 1 : Real) ^ (n * s))) * osiiOriginalNPointSeminorm d n (n * s) f.1 := by
      ring
    _ <= (lgc.alpha * (C * (n.factorial : Real) ^ Gamma)) *
        osiiOriginalNPointSeminorm d n (n * s) f.1 :=
      mul_le_mul_of_nonneg_right hcoef hQ
    _ = _ := by ring

theorem osiiOriginalLinearGrowth_iff {d : Nat} [NeZero d] (OS : OsterwalderSchraderAxioms d) :
    Nonempty (OSIIOriginalLinearGrowthCondition d OS) ↔ Nonempty (OSLinearGrowthCondition d OS) :=
  ⟨fun ⟨g⟩ => ⟨g.toArityLinearGrowthCondition⟩, fun ⟨lgc⟩ => lgc.exists_original⟩

theorem osiiWightmanGrowthCondition_of_uniformSchwartzBound
    {d : Nat} {W : (n : Nat) -> SchwartzNPoint d n -> Complex}
    (hW : ∃ (w : Nat) (A B : Real), 0 < w ∧ 0 < A ∧ 1 <= B ∧
      ∀ (n : Nat), 0 < n -> ∀ f : SchwartzNPoint d n,
        ‖W n f‖ <= A * B ^ (n ^ 2) * osArityLinearSchwartzSeminorm d n w f) :
    OSIIWightmanGrowthCondition d W := by
  obtain ⟨w, A, B, hw, hA, hB, hbound⟩ := hW
  refine ⟨w, A, B * (3 : Real) ^ ((d + 2) * w), hw, hA, by positivity, ?_⟩
  intro n hn f
  have hdim : (n * (d + 1) + 1 : Real) ^ (n * w) <=
      ((3 : Real) ^ ((d + 2) * w)) ^ (n ^ 2) := by
    have hbase : (n * (d + 1) + 1 : Real) <= (3 : Real) ^ ((d + 2) * n) := by
      have h1 : (n * (d + 1) + 1 : Real) <= (3 : Real) ^ (n * (d + 1) + 1) := by
        exact_mod_cast natCast_le_three_pow (n * (d + 1) + 1)
      exact h1.trans (pow_le_pow_right₀ (by norm_num) (by nlinarith))
    apply (pow_le_pow_left₀ (by positivity) hbase (n * w)).trans_eq
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hQ := osiiOriginalNPointSeminorm_nonneg d n (n * w) f
  calc
    ‖W n f‖ <= (A * B ^ (n ^ 2)) *
        ((n * (d + 1) + 1 : Real) ^ (n * w) * osiiOriginalNPointSeminorm d n (n * w) f) :=
      (hbound n hn f).trans (mul_le_mul_of_nonneg_left
        (osArityLinearSchwartzSeminorm_le_original d n w f) (by positivity))
    _ <= (A * B ^ (n ^ 2)) *
        ((((3 : Real) ^ ((d + 2) * w)) ^ (n ^ 2)) * osiiOriginalNPointSeminorm d n (n * w) f) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end OSReconstruction
