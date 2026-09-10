import OSReconstruction.SCV.HeadBlockIntegral

/-!
# Quantitative basepoint integration

Integrating a fixed-dimensional block costs a fixed number of weight orders,
no derivative orders, and a constant independent of the remaining dimension.
-/

noncomputable section

open MeasureTheory

namespace OSReconstruction

def osiiFiberWeightLoss (m : Nat) : Nat :=
  (volume : Measure (Fin m -> Real)).integrablePower

def osiiFiberConstant (m : Nat) : Real :=
  2 ^ osiiFiberWeightLoss m *
    (∫ t : Fin m -> Real, (1 + ‖t‖) ^ (-(osiiFiberWeightLoss m : Real)))

theorem osiiFiberConstant_nonneg (m : Nat) : 0 <= osiiFiberConstant m := by
  unfold osiiFiberConstant
  exact mul_nonneg (by positivity)
    (integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _)

private theorem norm_pow_mul_realFiberIntegralRaw_le_zero {m n : Nat}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n -> Real) × (Fin m -> Real)) V) (a : Nat)
    (u : Fin n -> Real) :
    ‖u‖ ^ a * ‖SCV.realFiberIntegralRaw F u‖ <= osiiFiberConstant m *
      (SchwartzMap.seminorm Real a 0 F +
        SchwartzMap.seminorm Real (a + osiiFiberWeightLoss m) 0 F) := by
  let c : Real := ‖u‖ ^ a
  have hc : 0 <= c := by positivity
  have hu (t : Fin m -> Real) : ‖u‖ <= ‖(u, t)‖ := norm_fst_le (u, t)
  have ht (t : Fin m -> Real) : ‖t‖ <= ‖(u, t)‖ := norm_snd_le (u, t)
  have hbound := integral_pow_mul_le_of_le_of_pow_mul_le
    (μ := (volume : Measure (Fin m -> Real))) (k := 0)
    (f := fun t => c • F (u, t))
    (C₁ := SchwartzMap.seminorm Real a 0 F)
    (C₂ := SchwartzMap.seminorm Real (a + osiiFiberWeightLoss m) 0 F)
    (fun t => show ‖c • F (u, t)‖ <= SchwartzMap.seminorm Real a 0 F by
      rw [norm_smul, Real.norm_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hu t) _) (norm_nonneg _)).trans
          (by simpa [norm_iteratedFDeriv_zero] using F.le_seminorm Real a 0 (u, t)))
    (fun t => show ‖t‖ ^ (0 + osiiFiberWeightLoss m) * ‖c • F (u, t)‖ <= _ by
      rw [norm_smul, Real.norm_of_nonneg hc, zero_add, ← mul_assoc]
      have hp : ‖t‖ ^ osiiFiberWeightLoss m * c <=
          ‖(u, t)‖ ^ (a + osiiFiberWeightLoss m) := by
        dsimp [c]
        calc
          _ <= ‖(u, t)‖ ^ osiiFiberWeightLoss m * ‖(u, t)‖ ^ a := by
            gcongr
            exact ht t
            exact hu t
          _ = _ := by rw [← pow_add, Nat.add_comm]; rfl
      exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
        (by simpa [norm_iteratedFDeriv_zero] using
          F.le_seminorm Real (a + osiiFiberWeightLoss m) 0 (u, t)))
  calc
    _ <= ‖u‖ ^ a * ∫ t : Fin m -> Real, ‖F (u, t)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ t : Fin m -> Real, ‖t‖ ^ 0 * ‖c • F (u, t)‖ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by simp [norm_smul, c]
    _ <= _ := hbound

private theorem seminorm_realFiberBaseFDeriv_le {m n : Nat}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n -> Real) × (Fin m -> Real)) V) (a r : Nat) :
    SchwartzMap.seminorm Real a r (SCV.realFiberBaseFDerivSchwartz F) <=
      SchwartzMap.seminorm Real a (r + 1) F := by
  let L : (((Fin n -> Real) × (Fin m -> Real)) →L[Real] V) →L[Real]
      ((Fin n -> Real) →L[Real] V) :=
    (ContinuousLinearMap.inl Real (Fin n -> Real) (Fin m -> Real)).precomp V
  have hL : ‖L‖ <= 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    rw [one_mul]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by
        simpa using mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_inl_le_one (𝕜 := Real)
            (E := Fin n -> Real) (F := Fin m -> Real)) (norm_nonneg f))
  apply SchwartzMap.seminorm_le_bound _ _ _ _ (apply_nonneg _ _)
  intro x
  have hi := L.norm_iteratedFDeriv_comp_left
    ((SchwartzMap.fderivCLM Real _ V F).smooth r).contDiffAt le_rfl (x := x)
  change ‖iteratedFDeriv Real r (fun y => L (fderiv Real F y)) x‖ <=
    ‖L‖ * ‖iteratedFDeriv Real r (fderiv Real F) x‖ at hi
  have hi' := hi.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  rw [one_mul, norm_iteratedFDeriv_fderiv] at hi'
  exact (mul_le_mul_of_nonneg_left hi' (by positivity)).trans
    (F.le_seminorm Real a (r + 1) x)

theorem norm_pow_mul_realFiberIntegralRaw_le {m n : Nat}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n -> Real) × (Fin m -> Real)) V) (a r : Nat)
    (u : Fin n -> Real) :
    ‖u‖ ^ a * ‖iteratedFDeriv Real r (SCV.realFiberIntegralRaw F) u‖ <=
      osiiFiberConstant m * (SchwartzMap.seminorm Real a r F +
        SchwartzMap.seminorm Real (a + osiiFiberWeightLoss m) r F) := by
  induction r generalizing V with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact norm_pow_mul_realFiberIntegralRaw_le_zero F a u
  | succ r ih =>
    rw [← norm_iteratedFDeriv_fderiv, SCV.fderiv_realFiberIntegralRaw_eq]
    exact (ih (SCV.realFiberBaseFDerivSchwartz F)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add (seminorm_realFiberBaseFDeriv_le F a r)
          (seminorm_realFiberBaseFDeriv_le F (a + osiiFiberWeightLoss m) r))
        (osiiFiberConstant_nonneg m))

theorem seminorm_realFiberIntegral_le {m n : Nat}
    (F : SchwartzMap ((Fin n -> Real) × (Fin m -> Real)) Complex) (a r : Nat) :
    SchwartzMap.seminorm Real a r (SCV.realFiberIntegral F) <=
      osiiFiberConstant m * (SchwartzMap.seminorm Real a r F +
        SchwartzMap.seminorm Real (a + osiiFiberWeightLoss m) r F) := by
  apply SchwartzMap.seminorm_le_bound _ _ _ _
    (mul_nonneg (osiiFiberConstant_nonneg m) (by positivity))
  exact norm_pow_mul_realFiberIntegralRaw_le F a r

theorem finsetSup_realFiberIntegral_le {m n : Nat}
    (F : SchwartzMap ((Fin n -> Real) × (Fin m -> Real)) Complex) (r : Nat) :
    (Finset.Iic (r, r)).sup (schwartzSeminormFamily Real (Fin n -> Real) Complex)
        (SCV.realFiberIntegral F) <=
      (2 * osiiFiberConstant m) *
        (Finset.Iic (r + osiiFiberWeightLoss m, r)).sup
          (schwartzSeminormFamily Real ((Fin n -> Real) × (Fin m -> Real)) Complex) F := by
  apply Seminorm.finset_sup_apply_le (mul_nonneg
    (mul_nonneg (by norm_num) (osiiFiberConstant_nonneg m)) (apply_nonneg _ _))
  intro j hj
  obtain ⟨hja, hjr⟩ := Finset.mem_Iic.mp hj
  apply (seminorm_realFiberIntegral_le F j.1 j.2).trans
  have hfirst := Seminorm.le_def.mp (Finset.le_sup (f :=
    schwartzSeminormFamily Real ((Fin n -> Real) × (Fin m -> Real)) Complex)
    (Finset.mem_Iic.mpr (show (j.1, j.2) <= (r + osiiFiberWeightLoss m, r) by
      exact ⟨by omega, hjr⟩))) F
  have hsecond := Seminorm.le_def.mp (Finset.le_sup (f :=
    schwartzSeminormFamily Real ((Fin n -> Real) × (Fin m -> Real)) Complex)
    (Finset.mem_Iic.mpr (show (j.1 + osiiFiberWeightLoss m, j.2) <=
      (r + osiiFiberWeightLoss m, r) by exact ⟨by omega, hjr⟩))) F
  have h := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
    (osiiFiberConstant_nonneg m)
  simpa only [schwartzSeminormFamily, mul_add, two_mul, add_mul] using h

end OSReconstruction
