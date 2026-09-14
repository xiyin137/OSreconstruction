import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIQuantitativeBoundary
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIQuantitativeCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISameWitnessWickPair

/-!
# Uniform growth of the native full Wightman family

The mixed boundary estimate is transported through the actual basepoint fiber
integral. Only the single one-point distribution uses ordinary continuity;
all higher arities retain explicit uniform constants and linear orders.
-/

noncomputable section

open Complex
open scoped Classical

namespace OSReconstruction

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem norm_strictGeneratedFullBoundary_succ_le
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) [NeZero k]
    (f : SchwartzNPoint d (k + 1)) :
    let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
    let beta := osiiEquation621CanonicalSeedArityRate lgc
    let L := 2 * t + 2 * beta + d + 3
    let c := 25 * beta + 9 * t + 5 * d + 14
    let h := osiiFiberWeightLoss (d + 1)
    ‖initial.strictGeneratedFullBoundary lgc (k + 1) f‖ <=
      (2 * osiiFiberConstant (d + 1) * (osiiEquation621CanonicalSeedArityConstant lgc + 1)) *
        (3 : Real) ^ ((c + (d + 5) * L + 4 * h) * (k + 1) * (k + 1)) *
          osArityLinearSchwartzSeminorm d (k + 1) (L + h) f := by
  let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
  let beta := osiiEquation621CanonicalSeedArityRate lgc
  let L := 2 * t + 2 * beta + d + 3
  let c := 25 * beta + 9 * t + 5 * d + 14
  let h := osiiFiberWeightLoss (d + 1)
  let alpha := osiiEquation621CanonicalSeedArityConstant lgc
  let B := initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k
  let F := diffVarReduction d k f
  let Phi := nPointTimeSpatialSchwartzCLE (d := d) (n := k) F
  have halpha := osiiEquation621CanonicalSeedArityConstant_nonneg lgc
  have hC := osiiFiberConstant_nonneg (d + 1)
  have hnative : initial.strictGeneratedFullBoundary lgc (k + 1) f =
      B.timeSpatialBoundary Phi := by
    change B.reducedBoundary F =
      B.reducedBoundary ((nPointTimeSpatialSchwartzCLE (d := d) (n := k)).symm
        ((nPointTimeSpatialSchwartzCLE (d := d) (n := k)) F))
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hboundary := initial.norm_strictGeneratedTimeSpatialBoundary_le lgc k Phi
  dsimp only at hboundary
  rw [osiiSchwartzComplexFinsetSup_eq_real] at hboundary
  have htime := squareSeminorm_timeSpatial_le d k (k * L) F
  have hfiber := squareSeminorm_diffVarReduction_le d k (k * L) f
  have horder : k * L + h <= (k + 1) * (L + h) := by nlinarith
  have hseminorm :
      (Finset.Iic (k * L + h, k * L + h)).sup
        (schwartzSeminormFamily Real (NPointDomain d (k + 1)) Complex) f <=
      osArityLinearSchwartzSeminorm d (k + 1) (L + h) f :=
    Seminorm.le_def.mp (Finset.sup_mono
      (Finset.Iic_subset_Iic.mpr (show (k * L + h, k * L + h) <=
        ((k + 1) * (L + h), (k + 1) * (L + h)) from ⟨horder, horder⟩))) f
  have htimebase : (k * d + 1 : Real) <= (3 : Real) ^ ((d + 1) * (k + 1)) := by
    have hb := natCast_le_three_pow (k * d + 1)
    have he : k * d + 1 <= (d + 1) * (k + 1) := by nlinarith
    have hb' : (k * d + 1 : Real) <= (3 : Real) ^ (k * d + 1) := by simpa using hb
    exact hb'.trans (pow_le_pow_right₀ (by norm_num) he)
  have hfiberbase : 2 * (k + 2 : Real) <= (3 : Real) ^ (4 * (k + 1)) := by
    have hb := natCast_le_three_pow (2 * (k + 2))
    have he : 2 * (k + 2) <= 4 * (k + 1) := by omega
    have hb' : 2 * (k + 2 : Real) <= (3 : Real) ^ (2 * (k + 2)) := by simpa using hb
    exact hb'.trans (pow_le_pow_right₀ (by norm_num) he)
  have hpTime := pow_le_pow_left₀ (by positivity) htimebase (k * L)
  have hpFiber := pow_le_pow_left₀ (by positivity) hfiberbase (k * L + h)
  rw [← pow_mul] at hpTime hpFiber
  have he : c * k * k + ((d + 1) * (k + 1)) * (k * L) +
      (4 * (k + 1)) * (k * L + h) <=
        (c + (d + 5) * L + 4 * h) * (k + 1) * (k + 1) := by
    have hkk : k * k <= (k + 1) * (k + 1) := by nlinarith
    have hcc := Nat.mul_le_mul_left c hkk
    have hL : k * L <= (k + 1) * L := by nlinarith
    have ht := Nat.mul_le_mul_left ((d + 1) * (k + 1)) hL
    have hh := Nat.mul_le_mul_left (4 * (k + 1)) horder
    nlinarith
  have hcoef : ((alpha + 1) * (3 : Real) ^ (c * k * k)) *
      ((k * d + 1 : Real) ^ (k * L) *
        (2 * osiiFiberConstant (d + 1) * (2 * (k + 2 : Real)) ^ (k * L + h))) <=
      (2 * osiiFiberConstant (d + 1) * (alpha + 1)) *
        (3 : Real) ^ ((c + (d + 5) * L + 4 * h) * (k + 1) * (k + 1)) := by
    calc
      _ <= ((alpha + 1) * (3 : Real) ^ (c * k * k)) *
          (3 ^ (((d + 1) * (k + 1)) * (k * L)) *
            (2 * osiiFiberConstant (d + 1) * 3 ^ ((4 * (k + 1)) * (k * L + h)))) := by
        gcongr
      _ = (2 * osiiFiberConstant (d + 1) * (alpha + 1)) * (3 : Real) ^
          (c * k * k + ((d + 1) * (k + 1)) * (k * L) +
            (4 * (k + 1)) * (k * L + h)) := by
        simp only [pow_add]
        ring
      _ <= _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) he) (by positivity)
  rw [hnative]
  dsimp only
  apply hboundary.trans
  calc
    _ <= ((alpha + 1) * (3 : Real) ^ (c * k * k)) *
        ((k * d + 1 : Real) ^ (k * L) *
          ((2 * osiiFiberConstant (d + 1) * (2 * (k + 2 : Real)) ^ (k * L + h)) *
            osArityLinearSchwartzSeminorm d (k + 1) (L + h) f)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply htime.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hfiber.trans (mul_le_mul_of_nonneg_left hseminorm (by positivity))
    _ <= _ := by
      have hQ : 0 <= osArityLinearSchwartzSeminorm d (k + 1) (L + h) f := apply_nonneg _ _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hQ

private theorem exists_strictGeneratedOnePointBound
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (r : Nat) (C : Real), 0 < C ∧ ∀ f : SchwartzNPoint d 1,
      ‖initial.strictGeneratedFullBoundary lgc 1 f‖ <=
        C * osArityLinearSchwartzSeminorm d 1 r f := by
  let T := initial.strictGeneratedFullBoundary lgc 1
  let q : Seminorm Complex (SchwartzNPoint d 1) :=
    (normSeminorm Complex Complex).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms Complex (NPointDomain d 1) Complex) q hq
  let r := s.sup Prod.fst + s.sup Prod.snd
  refine ⟨r, C, by exact_mod_cast (pos_iff_ne_zero.mpr hC), ?_⟩
  intro f
  have hb : ‖T f‖ <= (C : Real) *
      s.sup (schwartzSeminormFamily Complex (NPointDomain d 1) Complex) f := by
    simpa only [q, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
      Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] using hbound f
  rw [osiiSchwartzComplexFinsetSup_eq_real] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  apply Seminorm.le_def.mp (Finset.sup_mono ?_) f
  intro j hj
  rw [one_mul]
  apply Finset.mem_Iic.mpr
  have ha : j.1 <= s.sup Prod.fst := Finset.le_sup hj
  have hr : j.2 <= s.sup Prod.snd := Finset.le_sup hj
  dsimp [r]
  exact ⟨by omega, by omega⟩

/-- One coefficient and one linear Schwartz order control every positive
arity of the original native Wightman family. -/
theorem exists_strictGeneratedUniformSchwartzBound
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (w : Nat) (A B : Real), 0 < w ∧ 0 < A ∧ 1 <= B ∧
      ∀ (n : Nat), 0 < n -> ∀ f : SchwartzNPoint d n,
        ‖initial.strictGeneratedFullBoundary lgc n f‖ <=
          A * B ^ (n ^ 2) * osArityLinearSchwartzSeminorm d n w f := by
  let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
  let beta := osiiEquation621CanonicalSeedArityRate lgc
  let L := 2 * t + 2 * beta + d + 3
  let h := osiiFiberWeightLoss (d + 1)
  let c := 25 * beta + 9 * t + 5 * d + 14
  let E := c + (d + 5) * L + 4 * h
  let A0 := 2 * osiiFiberConstant (d + 1) *
    (osiiEquation621CanonicalSeedArityConstant lgc + 1)
  obtain ⟨r, C, hC, hone⟩ := initial.exists_strictGeneratedOnePointBound lgc
  let w := max (L + h) (r + 1)
  let A := max A0 C + 1
  let B : Real := 3 ^ E
  have hA : 0 < A := by dsimp [A]; linarith [le_max_right A0 C]
  have hA0 : A0 <= A := by dsimp [A]; linarith [le_max_left A0 C]
  have hCA : C <= A := by dsimp [A]; linarith [le_max_right A0 C]
  have hB : 1 <= B := one_le_pow₀ (by norm_num)
  have hwL : L + h <= w := le_max_left _ _
  have hwr : r <= w := (Nat.le_succ r).trans (le_max_right _ _)
  have hw : 0 < w := lt_of_lt_of_le (Nat.succ_pos r) (le_max_right _ _)
  refine ⟨w, A, B, hw, hA, hB, ?_⟩
  intro n hn f
  cases n with
  | zero => omega
  | succ k =>
    by_cases hk : k = 0
    · subst k
      simp only [zero_add, one_pow, pow_one]
      have hAB : C <= A * B := hCA.trans (by nlinarith)
      exact (hone f).trans (mul_le_mul hAB
        (osArityLinearSchwartzSeminorm_mono d 1 hwr f) (apply_nonneg _ _) (by positivity))
    · letI : NeZero k := ⟨hk⟩
      have hhigh := initial.norm_strictGeneratedFullBoundary_succ_le lgc k f
      dsimp only at hhigh
      have hpower : (3 : Real) ^ (E * (k + 1) * (k + 1)) = B ^ ((k + 1) ^ 2) := by
        dsimp [B]
        rw [← pow_mul, pow_two, mul_assoc]
      change ‖initial.strictGeneratedFullBoundary lgc (k + 1) f‖ <=
        A0 * (3 : Real) ^ (E * (k + 1) * (k + 1)) *
          osArityLinearSchwartzSeminorm d (k + 1) (L + h) f at hhigh
      rw [hpower] at hhigh
      apply hhigh.trans
      exact mul_le_mul (mul_le_mul_of_nonneg_right hA0 (by positivity))
        (osArityLinearSchwartzSeminorm_mono d (k + 1) hwL f)
        (apply_nonneg _ _) (by positivity)

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

end OSReconstruction
