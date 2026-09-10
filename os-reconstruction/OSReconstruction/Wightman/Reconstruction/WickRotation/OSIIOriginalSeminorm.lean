/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real








noncomputable section

open scoped Classical
open SchwartzMap

namespace OSReconstruction

def osiiCoordinateWeight {m : Nat} (x : Fin m -> Real) : Real :=
  Real.sqrt (1 + ∑ i, (x i) ^ 2)

theorem osiiCoordinateWeight_ge_one {m : Nat} (x : Fin m -> Real) :
    1 <= osiiCoordinateWeight x := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  simp only [one_pow]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem norm_le_osiiCoordinateWeight {m : Nat} (x : Fin m -> Real) :
    ‖x‖ <= osiiCoordinateWeight x := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  have hi : (x i) ^ 2 <= ∑ j, (x j) ^ 2 :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using hi.trans (le_add_of_nonneg_left zero_le_one)

theorem osiiCoordinateWeight_le {m : Nat} (x : Fin m -> Real) :
    osiiCoordinateWeight x <= (m + 1 : Real) * max 1 ‖x‖ := by
  have hR : 1 <= max (1 : Real) ‖x‖ := le_max_left _ _
  have hx : ‖x‖ <= max (1 : Real) ‖x‖ := le_max_right _ _
  have hm : 0 <= (m : Real) := Nat.cast_nonneg m
  have hs : ∑ i, (x i) ^ 2 <= (m : Real) * (max 1 ‖x‖) ^ 2 := by
    calc
      _ <= ∑ _ : Fin m, (max 1 ‖x‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [← sq_abs (x i)]
        exact pow_le_pow_left₀ (abs_nonneg _) ((norm_le_pi_norm x i).trans hx) 2
      _ = _ := by simp
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hR2 : 1 <= (max 1 ‖x‖) ^ 2 := one_le_pow₀ hR
  have hfactor : (m + 1 : Real) <= (m + 1 : Real) ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (max 1 ‖x‖))
  rw [mul_pow]
  nlinarith

/-- Expanding each argument in the coordinate basis gives a dimension-explicit
operator-norm estimate for every multilinear derivative. -/
theorem multilinear_norm_le_coordinate_bound {m b : Nat}
    (M : ContinuousMultilinearMap Real (fun _ : Fin b => Fin m -> Real) Complex)
    (C : Real) (hC : 0 <= C)
    (hM : ∀ c : Fin b -> Fin m, ‖M (fun i => Pi.single (c i) 1)‖ <= C) :
    ‖M‖ <= (m + 1 : Real) ^ b * C := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hsum : (fun i => ∑ j : Fin m, v i j • (Pi.single j (1 : Real) : Fin m -> Real)) = v := by
    funext i
    ext j
    simp [Pi.single_apply]
  have hexpand : M v = ∑ c : Fin b -> Fin m,
      M (fun i => v i (c i) • (Pi.single (c i) (1 : Real) : Fin m -> Real)) := by
    calc
      M v = M (fun i => ∑ j : Fin m, v i j • (Pi.single j (1 : Real) : Fin m -> Real)) :=
        congrArg M hsum.symm
      _ = _ := M.map_sum _
  calc
    ‖M v‖ <= ∑ c : Fin b -> Fin m,
        ‖M (fun i => v i (c i) • (Pi.single (c i) (1 : Real) : Fin m -> Real))‖ := by
      rw [hexpand]
      exact norm_sum_le _ _
    _ <= ∑ _c : Fin b -> Fin m, (∏ i, ‖v i‖) * C := by
      apply Finset.sum_le_sum
      intro c _
      rw [M.map_smul_univ, norm_smul, norm_prod]
      exact mul_le_mul
        (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => norm_le_pi_norm (v i) (c i)))
        (hM c) (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (m : Real) ^ b * ((∏ i, ‖v i‖) * C) := by simp
    _ <= (m + 1 : Real) ^ b * C * ∏ i, ‖v i‖ := by
      have hh := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith : (m : Real) <= m + 1) b)
        (mul_nonneg (Finset.prod_nonneg (s := Finset.univ) fun i _ => norm_nonneg (v i)) hC)
      nlinarith

/-- A coordinate derivative, including order zero, with the paper's weight. -/
def osiiCoordinateJetValue {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) (x : Fin m -> Real)
    (b : Nat) (c : Fin b -> Fin m) : Real :=
  osiiCoordinateWeight x ^ r *
    ‖iteratedFDeriv Real b f x (fun i => Pi.single (c i) 1)‖

def osiiOriginalSeminormValues {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) : Set Real :=
  {v | ∃ (x : Fin m -> Real) (b : Nat), b <= r ∧
    ∃ c : Fin b -> Fin m, v = osiiCoordinateJetValue r f x b c}

/-- OS II (2.1): the supremum of Euclidean-weighted coordinate derivatives
through order `r`. Flattening point labels is handled separately. -/
def osiiOriginalSeminorm {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) : Real :=
  sSup (osiiOriginalSeminormValues r f)

theorem osiiCoordinateJetValue_le_squareSeminorm {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) (x : Fin m -> Real)
    (b : Nat) (hb : b <= r) (c : Fin b -> Fin m) :
    osiiCoordinateJetValue r f x b c <= (m + 1 : Real) ^ r *
      (Finset.Iic (r, r)).sup (schwartzSeminormFamily Real (Fin m -> Real) Complex) f := by
  have hcoord : ‖iteratedFDeriv Real b f x (fun i => Pi.single (c i) 1)‖ <=
      ‖iteratedFDeriv Real b f x‖ := by
    apply ContinuousMultilinearMap.unit_le_opNorm
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    simp [Pi.norm_single]
  have hweight := pow_le_pow_left₀ (Real.sqrt_nonneg _)
    (osiiCoordinateWeight_le x) r
  have hmax : (max 1 ‖x‖) ^ r * ‖iteratedFDeriv Real b f x‖ <=
      (Finset.Iic (r, r)).sup (schwartzSeminormFamily Real (Fin m -> Real) Complex) f := by
    by_cases hx : ‖x‖ <= 1
    · rw [max_eq_left hx, one_pow, one_mul]
      exact (f.norm_iteratedFDeriv_le_seminorm Real b x).trans
        (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily Real (Fin m -> Real) Complex)
          (s := Finset.Iic (r, r)) (i := (0, b)) (x := f)
            (Finset.mem_Iic.mpr ⟨Nat.zero_le _, hb⟩))
    · rw [max_eq_right (le_of_not_ge hx)]
      exact (f.le_seminorm Real r b x).trans
        (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily Real (Fin m -> Real) Complex)
          (s := Finset.Iic (r, r)) (i := (r, b)) (x := f)
            (Finset.mem_Iic.mpr ⟨le_rfl, hb⟩))
  calc
    _ <= ((m + 1 : Real) * max 1 ‖x‖) ^ r * ‖iteratedFDeriv Real b f x‖ :=
      mul_le_mul hweight hcoord (norm_nonneg _) (by positivity)
    _ = (m + 1 : Real) ^ r * ((max 1 ‖x‖) ^ r * ‖iteratedFDeriv Real b f x‖) := by
      rw [mul_pow, mul_assoc]
    _ <= _ := mul_le_mul_of_nonneg_left hmax (by positivity)

theorem osiiOriginalSeminormValues_bddAbove {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) : BddAbove (osiiOriginalSeminormValues r f) := by
  refine ⟨(m + 1 : Real) ^ r *
    (Finset.Iic (r, r)).sup (schwartzSeminormFamily Real (Fin m -> Real) Complex) f, ?_⟩
  rintro v ⟨x, b, hb, c, rfl⟩
  exact osiiCoordinateJetValue_le_squareSeminorm r f x b hb c

theorem osiiOriginalSeminormValues_nonempty {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) : (osiiOriginalSeminormValues r f).Nonempty :=
  ⟨osiiCoordinateJetValue r f 0 0 Fin.elim0, 0, 0, Nat.zero_le r, Fin.elim0, rfl⟩

theorem osiiCoordinateJetValue_le {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) (x : Fin m -> Real)
    (b : Nat) (hb : b <= r) (c : Fin b -> Fin m) :
    osiiCoordinateJetValue r f x b c <= osiiOriginalSeminorm r f :=
  le_csSup (osiiOriginalSeminormValues_bddAbove r f) ⟨x, b, hb, c, rfl⟩

theorem osiiOriginalSeminorm_nonneg {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) : 0 <= osiiOriginalSeminorm r f := by
  apply le_trans _ (osiiCoordinateJetValue_le r f 0 0 (Nat.zero_le r) Fin.elim0)
  unfold osiiCoordinateJetValue
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)

theorem osiiOriginalSeminorm_le_squareSeminorm {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) :
    osiiOriginalSeminorm r f <= (m + 1 : Real) ^ r *
      (Finset.Iic (r, r)).sup (schwartzSeminormFamily Real (Fin m -> Real) Complex) f := by
  apply csSup_le (osiiOriginalSeminormValues_nonempty r f)
  rintro v ⟨x, b, hb, c, rfl⟩
  exact osiiCoordinateJetValue_le_squareSeminorm r f x b hb c

theorem squareSeminorm_le_osiiOriginalSeminorm {m : Nat} (r : Nat)
    (f : SchwartzMap (Fin m -> Real) Complex) :
    (Finset.Iic (r, r)).sup (schwartzSeminormFamily Real (Fin m -> Real) Complex) f <=
      (m + 1 : Real) ^ r * osiiOriginalSeminorm r f := by
  have hQ := osiiOriginalSeminorm_nonneg r f
  apply Seminorm.finset_sup_apply_le (mul_nonneg (by positivity) hQ)
  intro j hj
  obtain ⟨hja, hjb⟩ := Finset.mem_Iic.mp hj
  apply SchwartzMap.seminorm_le_bound _ _ _ _ (mul_nonneg (by positivity) hQ)
  intro x
  let w := osiiCoordinateWeight x ^ r
  have hw : 0 <= w := pow_nonneg (Real.sqrt_nonneg _) _
  have hM := multilinear_norm_le_coordinate_bound
    (w • iteratedFDeriv Real j.2 f x) (osiiOriginalSeminorm r f) hQ
    (fun c => by
      simpa only [ContinuousMultilinearMap.smul_apply, norm_smul,
        Real.norm_of_nonneg hw] using osiiCoordinateJetValue_le r f x j.2 hjb c)
  rw [norm_smul, Real.norm_of_nonneg hw] at hM
  have hweight : ‖x‖ ^ j.1 <= w :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_osiiCoordinateWeight x) j.1).trans
      (pow_le_pow_right₀ (osiiCoordinateWeight_ge_one x) hja)
  exact (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)).trans (hM.trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := Real) m]) hjb) hQ))

end OSReconstruction
