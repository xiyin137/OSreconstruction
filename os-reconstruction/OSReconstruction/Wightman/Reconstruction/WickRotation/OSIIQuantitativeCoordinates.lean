import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIQuantitativeFiber
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformSchwartzDegree
import OSReconstruction.SCV.PartialFourierSpatial

/-!
# Quantitative coordinates for OS II

The existing difference and time/spatial coordinate changes preserve Schwartz
orders. Their numerical losses are bounded uniformly in the number of points.
-/

noncomputable section

open Complex MeasureTheory
open scoped Classical

namespace OSReconstruction

theorem squareSeminorm_compContinuousLinearEquiv_le
    {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace Real D]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (g : D ≃L[Real] E) (A B : Real) (hA : 1 <= A) (hB : 1 <= B)
    (hgA : ‖g.symm.toContinuousLinearMap‖ <= A)
    (hgB : ‖g.toContinuousLinearMap‖ <= B)
    (f : SchwartzMap E Complex) (r : Nat) :
    (Finset.Iic (r, r)).sup (schwartzSeminormFamily Real D Complex)
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex g f) <=
      (A * B) ^ r * (Finset.Iic (r, r)).sup
        (schwartzSeminormFamily Real E Complex) f := by
  have hA0 : 0 <= A := le_trans zero_le_one hA
  have hB0 : 0 <= B := le_trans zero_le_one hB
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro j hj
  obtain ⟨hja, hjb⟩ := Finset.mem_Iic.mp hj
  have hcoeff : ‖g.symm.toContinuousLinearMap‖ ^ j.1 *
      ‖g.toContinuousLinearMap‖ ^ j.2 <= (A * B) ^ r := by
    rw [mul_pow]
    exact mul_le_mul
      ((pow_le_pow_left₀ (norm_nonneg _) hgA _).trans (pow_le_pow_right₀ hA hja))
      ((pow_le_pow_left₀ (norm_nonneg _) hgB _).trans (pow_le_pow_right₀ hB hjb))
      (by positivity) (by positivity)
  apply (schwartzSeminorm_compContinuousLinearEquiv_le g f j.1 j.2).trans
  exact mul_le_mul hcoeff (Seminorm.le_def.mp
    (Finset.le_sup (f := schwartzSeminormFamily Real E Complex) hj) f)
    (apply_nonneg _ _) (by positivity)

theorem osiiFlatten_opNorm_le (n q : Nat) :
    ‖(flattenCLEquivReal n q).toContinuousLinearMap‖ <= 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using (flattenCLEquivReal_norm_eq n q x).le

theorem osiiFlatten_symm_opNorm_le (n q : Nat) :
    ‖(flattenCLEquivReal n q).symm.toContinuousLinearMap‖ <= 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(flattenCLEquivReal n q).symm x‖ <= 1 * ‖x‖
  rw [one_mul, ← flattenCLEquivReal_norm_eq n q ((flattenCLEquivReal n q).symm x)]
  simp

def osiiHeadTailNPointCLE (d k : Nat) :
    ((Fin (k * (d + 1)) -> Real) × (Fin (d + 1) -> Real)) ≃L[Real]
      NPointDomain d (k + 1) :=
  (((flattenCLEquivReal k (d + 1)).symm.prodCongr
    (ContinuousLinearEquiv.refl Real (Fin (d + 1) -> Real))).trans
      (ContinuousLinearEquiv.prodComm Real _ _)).trans
        (Fin.consEquivL Real (fun _ : Fin (k + 1) => Fin (d + 1) -> Real))

theorem osiiHeadTailNPointCLE_norm_eq (d k : Nat)
    (p : (Fin (k * (d + 1)) -> Real) × (Fin (d + 1) -> Real)) :
    ‖osiiHeadTailNPointCLE d k p‖ = ‖p‖ := by
  let x := (flattenCLEquivReal k (d + 1)).symm p.1
  have hx : ‖x‖ = ‖p.1‖ := by
    rw [← flattenCLEquivReal_norm_eq k (d + 1) x]
    simp [x]
  change ‖(Fin.cons p.2 x : NPointDomain d (k + 1))‖ = ‖p‖
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using norm_snd_le p
    · simpa using (norm_le_pi_norm x j).trans (hx.le.trans (norm_fst_le p))
  · rw [Prod.norm_def]
    apply max_le
    · rw [← hx]
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro j
      simpa using norm_le_pi_norm (Fin.cons p.2 x : NPointDomain d (k + 1)) j.succ
    · simpa using norm_le_pi_norm (Fin.cons p.2 x : NPointDomain d (k + 1)) 0

def osiiDiffFiberCLE (d k : Nat) :
    ((Fin (k * (d + 1)) -> Real) × (Fin (d + 1) -> Real)) ≃L[Real]
      NPointDomain d (k + 1) :=
  (osiiHeadTailNPointCLE d k).trans (BHW.realDiffCoordCLE (k + 1) d).symm

theorem osiiDiffFiberCLE_apply (d k : Nat)
    (u : Fin (k * (d + 1)) -> Real) (a : Fin (d + 1) -> Real) :
    osiiDiffFiberCLE d k (u, a) = fun j mu => a mu +
      diffVarSection d k ((flattenCLEquivReal k (d + 1)).symm u) j mu := by
  apply (BHW.realDiffCoordCLE (k + 1) d).injective
  change (BHW.realDiffCoordCLE (k + 1) d)
      ((BHW.realDiffCoordCLE (k + 1) d).symm (Fin.cons a
        ((flattenCLEquivReal k (d + 1)).symm u))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext j mu
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [BHW.realDiffCoordCLE_apply, diffVarSection_zero]
  · rw [Fin.cons_succ, BHW.realDiffCoordCLE_apply, dif_neg (by simp)]
    change _ = (a mu + diffVarSection d k ((flattenCLEquivReal k (d + 1)).symm u)
      i.succ mu) - (a mu + diffVarSection d k ((flattenCLEquivReal k (d + 1)).symm u)
        i.castSucc mu)
    rw [diffVarSection_succ]
    ring

theorem osiiDiffFiberCLE_opNorm_le (d k : Nat) :
    ‖(osiiDiffFiberCLE d k).toContinuousLinearMap‖ <= (k + 2 : Real) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  change ‖(BHW.realDiffCoordCLE (k + 1) d).symm (osiiHeadTailNPointCLE d k p)‖ <= _
  apply ((BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap.le_opNorm _).trans
  rw [osiiHeadTailNPointCLE_norm_eq]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg p)
  simpa [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : Real) + 1 = 2 by norm_num] using
    norm_realDiffCoordCLE_symm_le_arity_add_one (k + 1) d

theorem osiiDiffFiberCLE_symm_opNorm_le (d k : Nat) :
    ‖(osiiDiffFiberCLE d k).symm.toContinuousLinearMap‖ <= 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(osiiDiffFiberCLE d k).symm x‖ <= 2 * ‖x‖
  rw [← osiiHeadTailNPointCLE_norm_eq d k ((osiiDiffFiberCLE d k).symm x)]
  change ‖(osiiHeadTailNPointCLE d k)
    ((osiiHeadTailNPointCLE d k).symm ((BHW.realDiffCoordCLE (k + 1) d) x))‖ <= _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact ((BHW.realDiffCoordCLE (k + 1) d).toContinuousLinearMap.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (norm_realDiffCoordCLE_le_two (k + 1) d) (norm_nonneg x))

theorem diffVarReduction_eq_realFiberIntegral (d k : Nat) [NeZero d]
    (f : SchwartzNPoint d (k + 1)) :
    diffVarReduction d k f =
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex (flattenCLEquivReal k (d + 1))
        (SCV.realFiberIntegral
          (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiDiffFiberCLE d k) f)) := by
  ext x
  change (∫ a : Fin (d + 1) -> Real, f (fun j mu => a mu + diffVarSection d k x j mu)) =
    ∫ a : Fin (d + 1) -> Real, f (osiiDiffFiberCLE d k (flattenCLEquivReal k (d + 1) x, a))
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    dsimp only
    rw [osiiDiffFiberCLE_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem squareSeminorm_diffVarReduction_le (d k r : Nat) [NeZero d]
    (f : SchwartzNPoint d (k + 1)) :
    (Finset.Iic (r, r)).sup (schwartzSeminormFamily Real (NPointDomain d k) Complex)
      (diffVarReduction d k f) <=
        (2 * osiiFiberConstant (d + 1) * (2 * (k + 2 : Real)) ^
          (r + osiiFiberWeightLoss (d + 1))) *
        (Finset.Iic (r + osiiFiberWeightLoss (d + 1), r + osiiFiberWeightLoss (d + 1))).sup
          (schwartzSeminormFamily Real (NPointDomain d (k + 1)) Complex) f := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiDiffFiberCLE d k) f
  rw [diffVarReduction_eq_realFiberIntegral]
  have hflat := squareSeminorm_compContinuousLinearEquiv_le
    (flattenCLEquivReal k (d + 1)) 1 1 le_rfl le_rfl
      (osiiFlatten_symm_opNorm_le _ _) (osiiFlatten_opNorm_le _ _)
        (SCV.realFiberIntegral g) r
  simp only [one_mul, one_pow] at hflat
  apply hflat.trans
  have hfiber := finsetSup_realFiberIntegral_le g r
  have hsub : Finset.Iic (r + osiiFiberWeightLoss (d + 1), r) ⊆
      Finset.Iic (r + osiiFiberWeightLoss (d + 1), r + osiiFiberWeightLoss (d + 1)) :=
    Finset.Iic_subset_Iic.mpr ⟨le_rfl, Nat.le_add_right _ _⟩
  have hmono :
      (Finset.Iic (r + osiiFiberWeightLoss (d + 1), r)).sup
          (schwartzSeminormFamily Real _ Complex) g <=
        (Finset.Iic (r + osiiFiberWeightLoss (d + 1), r + osiiFiberWeightLoss (d + 1))).sup
          (schwartzSeminormFamily Real _ Complex) g :=
    Seminorm.le_def.mp (Finset.sup_mono hsub) g
  have hcoord := squareSeminorm_compContinuousLinearEquiv_le (osiiDiffFiberCLE d k)
    2 (k + 2) (by norm_num) (by linarith [Nat.cast_nonneg (α := Real) k])
      (osiiDiffFiberCLE_symm_opNorm_le d k)
      (osiiDiffFiberCLE_opNorm_le d k) f (r + osiiFiberWeightLoss (d + 1))
  have h := hfiber.trans (mul_le_mul_of_nonneg_left (hmono.trans hcoord)
    (mul_nonneg (by norm_num) (osiiFiberConstant_nonneg _)))
  simpa only [mul_assoc] using h

theorem nPointTimeSpatialCLE_symm_opNorm_le_one (d k : Nat) [NeZero d] :
    ‖(nPointTimeSpatialCLE (d := d) k).symm.toContinuousLinearMap‖ <= 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
  intro mu
  refine Fin.cases ?_ (fun j => ?_) mu
  · exact (norm_le_pi_norm p.1 i).trans (norm_fst_le p)
  · exact (PiLp.norm_apply_le p.2 (i, j)).trans (norm_snd_le p)

theorem nPointTimeSpatialCLE_opNorm_le (d k : Nat) [NeZero d] :
    ‖(nPointTimeSpatialCLE (d := d) k).toContinuousLinearMap‖ <= (k * d + 1 : Real) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖nPointTimeSpatialCLE (d := d) k x‖ <= _
  rw [Prod.norm_def]
  apply max_le
  · have htime : ‖(nPointTimeSpatialCLE (d := d) k x).1‖ <= ‖x‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
      intro i
      exact (norm_le_pi_norm (x i) 0).trans (norm_le_pi_norm x i)
    apply htime.trans
    have hdim0 : (0 : Real) <= k * d := by positivity
    nlinarith [norm_nonneg x]
  · have hspace : ‖(nPointTimeSpatialCLE (d := d) k x).2‖ ^ 2 <=
        (k * d : Real) * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc
        _ <= ∑ _ : Fin k × Fin d, ‖x‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro p _
          apply pow_le_pow_left₀ (norm_nonneg _)
          exact (norm_le_pi_norm (x p.1) p.2.succ).trans (norm_le_pi_norm x p.1)
        _ = _ := by simp [Nat.cast_mul]
    have hdim : (k * d : Real) <= (k * d + 1 : Real) ^ 2 := by
      have hdim0 : (0 : Real) <= k * d := by positivity
      nlinarith
    have hsquare := hspace.trans (mul_le_mul_of_nonneg_right hdim (sq_nonneg ‖x‖))
    rw [← mul_pow] at hsquare
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsquare

theorem squareSeminorm_timeSpatial_le (d k r : Nat) [NeZero d]
    (f : SchwartzNPoint d k) :
    (Finset.Iic (r, r)).sup
      (schwartzSeminormFamily Real ((Fin k -> Real) × EuclideanSpace Real (Fin k × Fin d))
        Complex) (nPointTimeSpatialSchwartzCLE (d := d) (n := k) f) <=
      (k * d + 1 : Real) ^ r *
        (Finset.Iic (r, r)).sup (schwartzSeminormFamily Real (NPointDomain d k) Complex) f := by
  have h := squareSeminorm_compContinuousLinearEquiv_le
    (nPointTimeSpatialCLE (d := d) k).symm (k * d + 1) 1
      (by nlinarith [Nat.cast_nonneg (α := Real) (k * d)]) le_rfl
      (nPointTimeSpatialCLE_opNorm_le d k) (nPointTimeSpatialCLE_symm_opNorm_le_one d k) f r
  simpa only [mul_one] using h

end OSReconstruction
