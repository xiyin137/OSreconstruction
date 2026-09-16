import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialEndpointSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIProductionRadialGlobal

/-!
# OS II Chapter VI: explicit production endpoint Schwartz estimates

The globally normalized radial Gevrey estimate is restricted to the actual
fixed-imaginary Schwartz endpoint. Contractive real-coordinate inclusion,
support, and centering give explicit complete seminorm-rectangle constants.
-/

noncomputable section

open Complex Topology
open scoped BigOperators Classical

namespace OSReconstruction

def osiiProductionRealBlockSliceCLM
    (q : Nat) :
    (Fin q → Real) →L[Real] (Fin (q * 2) → Real) :=
  ContinuousLinearMap.pi fun j =>
    let p := (finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm j
    if p.2 = 0 then ContinuousLinearMap.proj p.1 else 0

def osiiProductionImagBlockOffset
    (q : Nat) (imag : Fin q → Real) (j : Fin (q * 2)) : Real :=
  let p := (finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm j
  if p.2 = 0 then 0 else imag p.1

theorem osiiProductionRealBlockSliceCLM_norm_le_one
    (q : Nat) :
    ‖osiiProductionRealBlockSliceCLM q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  let p := (finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm j
  change ‖(if p.2 = 0 then
    (ContinuousLinearMap.proj p.1 :
      (Fin q → Real) →L[Real] Real) else 0) x‖ ≤ ‖x‖
  split
  · exact norm_le_pi_norm x p.1
  · simp

theorem osiiProductionComplexBlockRealCoordinateCLM_realImag
    (q : Nat) (x imag : Fin q → Real) :
    osiiProductionComplexBlockRealCoordinateCLM q
        (osiiStep4ComplexOfRealImag x imag) =
      osiiProductionRealBlockSliceCLM q x +
        osiiProductionImagBlockOffset q imag := by
  funext j
  let p := (finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm j
  rw [osiiProductionComplexBlockRealCoordinateCLM_apply]
  change
    (if p.2 = 0 then
      (osiiStep4ComplexOfRealImag x imag p.1).re
     else (osiiStep4ComplexOfRealImag x imag p.1).im) =
      (if p.2 = 0 then
        (ContinuousLinearMap.proj p.1 :
          (Fin q → Real) →L[Real] Real) else 0) x +
        (if p.2 = 0 then 0 else imag p.1)
  split <;> simp

theorem osiiProductionNormalizedRadialRealProfile_contDiff
    (q : Nat) (rho : Real) :
    ContDiff Real (⊤ : ℕ∞)
      (osiiProductionNormalizedRadialRealProfile q rho) := by
  unfold osiiProductionNormalizedRadialRealProfile
  exact
    (contDiff_const.mul
      ((osiiProductionRealRadialScalarProfile_contDiff (q * 2)).comp
        (contDiff_const_smul (16 / rho)))).div_const _

theorem osiiStep4ComplexBlockRadialGRealSlice_iteratedFDeriv_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag x : Fin (q + 1) → Real) (n : Nat) :
    ‖iteratedFDeriv Real n
        (osiiStep4ComplexBlockRadialGRealSlice (q + 1) rho imag) x‖ ≤
      ((∫ z : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
        Real.exp 6 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2) *
        (16 / rho) ^ (2 * (q + 1) + n) := by
  let L := osiiProductionRealBlockSliceCLM (q + 1)
  let b := osiiProductionImagBlockOffset (q + 1) imag
  let G := osiiProductionNormalizedRadialRealProfile (q + 1) rho
  let B : Real :=
    ((∫ z : Fin (q + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
      Real.exp 6 *
      (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
        (n.factorial : Real) ^ 2) *
      (16 / rho) ^ (2 * (q + 1) + n)
  have hB : 0 ≤ B := by
    have hmass :
        0 < ∫ z : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 z :=
      osiiStep4ComplexBlockRadialRaw_integral_pos
        (q + 1) (by norm_num)
    dsimp [B]
    positivity
  have hG : ContDiff Real (⊤ : ℕ∞) G :=
    osiiProductionNormalizedRadialRealProfile_contDiff (q + 1) rho
  have hshift :
      ContDiff Real (⊤ : ℕ∞)
        (fun w : Fin ((q + 1) * 2) → Real => G (b + w)) :=
    hG.comp (contDiff_const.add contDiff_id)
  have hfun :
      osiiStep4ComplexBlockRadialGRealSlice (q + 1) rho imag =
        fun w => G (b + L w) := by
    funext w
    unfold osiiStep4ComplexBlockRadialGRealSlice
    rw [osiiStep4ComplexBlockRadialG_eq_normalizedRealProfile
      (q + 1) hrho]
    rw [osiiProductionComplexBlockRealCoordinateCLM_realImag]
    simp [G, L, b, add_comm]
  have hiter :
      iteratedFDeriv Real n
        (osiiStep4ComplexBlockRadialGRealSlice (q + 1) rho imag) x =
      (iteratedFDeriv Real n G (b + L x)).compContinuousLinearMap
        (fun _ => L) := by
    rw [hfun]
    have hcompose :=
      L.iteratedFDeriv_comp_right hshift x (i := n)
        (by exact_mod_cast le_top)
    rw [iteratedFDeriv_comp_add_left] at hcompose
    exact hcompose
  have hglobal : ‖iteratedFDeriv Real n G (b + L x)‖ ≤ B := by
    exact osiiProductionNormalizedRadialRealProfile_global_gevrey_bound
      q hrho (b + L x) n
  have hL : ‖L‖ ≤ 1 :=
    osiiProductionRealBlockSliceCLM_norm_le_one (q + 1)
  change ‖iteratedFDeriv Real n
    (osiiStep4ComplexBlockRadialGRealSlice (q + 1) rho imag) x‖ ≤ B
  rw [hiter]
  calc
    ‖(iteratedFDeriv Real n G (b + L x)).compContinuousLinearMap
        (fun _ => L)‖ ≤
      ‖iteratedFDeriv Real n G (b + L x)‖ *
        ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ B * 1 := by
      apply mul_le_mul hglobal
      · exact Finset.prod_le_one
          (fun _ _ => norm_nonneg _) (fun _ _ => hL)
      · positivity
      · exact hB
    _ = B := mul_one _

theorem osiiStep4ComplexBlockRadialGRealSchwartz_iteratedFDeriv_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag x : Fin (q + 1) → Real) (n : Nat) :
    ‖iteratedFDeriv Real n
        (osiiStep4ComplexBlockRadialGRealSchwartz (q + 1) hrho imag :
          (Fin (q + 1) → Real) → Complex) x‖ ≤
      ((∫ z : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
        Real.exp 6 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2) *
        (16 / rho) ^ (2 * (q + 1) + n) := by
  have hfun :
      (osiiStep4ComplexBlockRadialGRealSchwartz (q + 1) hrho imag :
        (Fin (q + 1) → Real) → Complex) =
      Complex.ofRealLI ∘
        osiiStep4ComplexBlockRadialGRealSlice (q + 1) rho imag := by
    funext w
    simp [osiiStep4ComplexBlockRadialGRealSchwartz_apply,
      osiiStep4ComplexBlockRadialGRealSlice]
  rw [hfun, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    (osiiStep4ComplexBlockRadialGRealSlice_contDiff
      (q + 1) hrho imag).contDiffAt (by exact_mod_cast le_top)]
  exact osiiStep4ComplexBlockRadialGRealSlice_iteratedFDeriv_gevrey_bound
    q hrho imag x n

theorem osiiStep4ComplexBlockRadialGRealSchwartz_seminorm_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho) (hrho_le : rho ≤ 16)
    (imag : Fin (q + 1) → Real) (p n : Nat) :
    SchwartzMap.seminorm Real p n
        (osiiStep4ComplexBlockRadialGRealSchwartz
          (q + 1) hrho imag) ≤
      2 ^ p *
        (((∫ z : Fin (q + 1) → Complex,
            osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
          Real.exp 6 *
          (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
            (n.factorial : Real) ^ 2) *
          (16 / rho) ^ (2 * (q + 1) + n)) := by
  let f : SchwartzMap (Fin (q + 1) → Real) Complex :=
    osiiStep4ComplexBlockRadialGRealSchwartz (q + 1) hrho imag
  let B : Real :=
    ((∫ z : Fin (q + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
      Real.exp 6 *
      (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
        (n.factorial : Real) ^ 2) *
      (16 / rho) ^ (2 * (q + 1) + n)
  have hmass :
      0 < ∫ z : Fin (q + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (q + 1) 16 z :=
    osiiStep4ComplexBlockRadialRaw_integral_pos
      (q + 1) (by norm_num)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hcenter :
      osiiStep4CenteredComplexBlockRadialGRealSchwartz
        (q + 1) hrho 0 imag = f := by
    ext y
    simp [f, osiiStep4CenteredComplexBlockRadialGRealSchwartz_apply,
      osiiStep4ComplexBlockRadialGRealSchwartz_apply]
  have hsupp :
      tsupport (f : (Fin (q + 1) → Real) → Complex) ⊆
        Metric.closedBall 0 (rho / 8) := by
    simpa [hcenter] using
      osiiStep4CenteredComplexBlockRadialGRealSchwartz_tsupport_subset_closedBall
        (q + 1) hrho 0 imag
  change SchwartzMap.seminorm Real p n f ≤ 2 ^ p * B
  apply SchwartzMap.seminorm_le_bound Real p n f (by positivity)
  intro x
  by_cases hzero : iteratedFDeriv Real n
      (f : (Fin (q + 1) → Real) → Complex) x = 0
  · rw [hzero, norm_zero, mul_zero]
    positivity
  have hsupport :
      x ∈ Function.support
        (iteratedFDeriv Real n
          (f : (Fin (q + 1) → Real) → Complex)) := by
    exact hzero
  have hxball := hsupp
    (support_iteratedFDeriv_subset (𝕜 := Real) n hsupport)
  rw [Metric.mem_closedBall, dist_zero_right] at hxball
  have hxnorm : ‖x‖ ≤ 2 := by
    linarith
  have hderiv :
      ‖iteratedFDeriv Real n
        (f : (Fin (q + 1) → Real) → Complex) x‖ ≤ B := by
    exact osiiStep4ComplexBlockRadialGRealSchwartz_iteratedFDeriv_gevrey_bound
      q hrho imag x n
  exact mul_le_mul
    (pow_le_pow_left₀ (norm_nonneg x) hxnorm p)
    hderiv (norm_nonneg _) (by positivity)

theorem osiiStep4ComplexBlockRadialGRealSchwartz_Iic_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho) (hrho_le : rho ≤ 16)
    (imag : Fin (q + 1) → Real) (p l : Nat) :
    (Finset.Iic (p, l)).sup
        (schwartzSeminormFamily Real (Fin (q + 1) → Real) Complex)
        (osiiStep4ComplexBlockRadialGRealSchwartz
          (q + 1) hrho imag) ≤
      (2 ^ p *
        (∫ z : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
        Real.exp 6 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ l *
          (l.factorial : Real) ^ 2) *
        (16 / rho) ^ (2 * (q + 1) + l) := by
  let I : Real := ∫ z : Fin (q + 1) → Complex,
    osiiStep4ComplexBlockRadialRaw (q + 1) 16 z
  let A : Real := 98304 * (((q + 1) * 2 : Nat) : Real) ^ 2
  let a : Real := 16 / rho
  have hI : 0 < I :=
    osiiStep4ComplexBlockRadialRaw_integral_pos
      (q + 1) (by norm_num)
  have hA : 1 ≤ A := by
    dsimp [A]
    have hdimension : (1 : Real) ≤ (((q + 1) * 2 : Nat) : Real) := by
      exact_mod_cast (show 1 ≤ (q + 1) * 2 by omega)
    nlinarith [sq_nonneg ((((q + 1) * 2 : Nat) : Real)),
      mul_self_le_mul_self (by positivity) hdimension]
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  apply Seminorm.finset_sup_apply_le
  · positivity
  intro j hj
  have hjle : j.1 ≤ p ∧ j.2 ≤ l := Finset.mem_Iic.mp hj
  have hjp : j.1 ≤ p := hjle.1
  have hjl : j.2 ≤ l := hjle.2
  have hbase :=
    osiiStep4ComplexBlockRadialGRealSchwartz_seminorm_gevrey_bound
      q hrho hrho_le imag j.1 j.2
  have hfactorial : (j.2.factorial : Real) ≤ l.factorial := by
    exact_mod_cast Nat.factorial_le hjle.2
  change
    SchwartzMap.seminorm Real j.1 j.2
      (osiiStep4ComplexBlockRadialGRealSchwartz
        (q + 1) hrho imag) ≤
      (2 ^ p * I⁻¹ * Real.exp 6 * A ^ l *
        (l.factorial : Real) ^ 2) *
        a ^ (2 * (q + 1) + l)
  calc
    SchwartzMap.seminorm Real j.1 j.2
      (osiiStep4ComplexBlockRadialGRealSchwartz
        (q + 1) hrho imag) ≤
      2 ^ j.1 *
        ((I⁻¹ * Real.exp 6 * A ^ j.2 *
          (j.2.factorial : Real) ^ 2) *
          a ^ (2 * (q + 1) + j.2)) := hbase
    _ ≤ 2 ^ p *
        ((I⁻¹ * Real.exp 6 * A ^ l *
          (l.factorial : Real) ^ 2) *
          a ^ (2 * (q + 1) + l)) := by
      gcongr <;> try norm_num <;> assumption
    _ = (2 ^ p * I⁻¹ * Real.exp 6 * A ^ l *
        (l.factorial : Real) ^ 2) *
        a ^ (2 * (q + 1) + l) := by ring

theorem osiiStep4CenteredComplexBlockRadialGRealSchwartz_Iic_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho) (hrho_le : rho ≤ 16)
    (center imag : Fin (q + 1) → Real) (p l : Nat) :
    (Finset.Iic (p, l)).sup
        (schwartzSeminormFamily Real (Fin (q + 1) → Real) Complex)
        (osiiStep4CenteredComplexBlockRadialGRealSchwartz
          (q + 1) hrho center imag) ≤
      (2 ^ (2 * p + 1) *
        (∫ z : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
        Real.exp 6 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ l *
          (l.factorial : Real) ^ 2) *
        (16 / rho) ^ (2 * (q + 1) + l) *
          (1 + ‖center‖) ^ p := by
  let I : Real := ∫ z : Fin (q + 1) → Complex,
    osiiStep4ComplexBlockRadialRaw (q + 1) 16 z
  let A : Real := 98304 * (((q + 1) * 2 : Nat) : Real) ^ 2
  let a : Real := 16 / rho
  let b : Real := 1 + ‖center‖
  let C : Real := 2 ^ p * I⁻¹ * Real.exp 6 * A ^ l *
    (l.factorial : Real) ^ 2
  have hI : 0 < I :=
    osiiStep4ComplexBlockRadialRaw_integral_pos
      (q + 1) (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C, A]
    positivity
  have hb : 1 ≤ b := by
    dsimp [b]
    linarith [norm_nonneg center]
  have hbase :
      (Finset.Iic (p, l)).sup
          (schwartzSeminormFamily Real (Fin (q + 1) → Real) Complex)
          (osiiStep4ComplexBlockRadialGRealSchwartz
            (q + 1) hrho imag) ≤
        C * a ^ (2 * (q + 1) + l) :=
    osiiStep4ComplexBlockRadialGRealSchwartz_Iic_gevrey_bound
      q hrho hrho_le imag p l
  apply Seminorm.finset_sup_apply_le
  · positivity
  intro j hj
  have hjle : j.1 ≤ p ∧ j.2 ≤ l := Finset.mem_Iic.mp hj
  have hjzero : (0, j.2) ∈ Finset.Iic (p, l) := by
    simp [hjle.2]
  have hfirst :
      SchwartzMap.seminorm Real j.1 j.2
          (osiiStep4ComplexBlockRadialGRealSchwartz
            (q + 1) hrho imag) ≤
        C * a ^ (2 * (q + 1) + l) :=
    (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily Real
        (Fin (q + 1) → Real) Complex) hj).trans hbase
  have hzero :
      SchwartzMap.seminorm Real 0 j.2
          (osiiStep4ComplexBlockRadialGRealSchwartz
            (q + 1) hrho imag) ≤
        C * a ^ (2 * (q + 1) + l) :=
    (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily Real
        (Fin (q + 1) → Real) Complex) hjzero).trans hbase
  have hweight : (2 : Real) ^ (j.1 - 1) ≤ 2 ^ p :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hcenter : b ^ j.1 ≤ b ^ p :=
    pow_le_pow_right₀ hb hjle.1
  change SchwartzMap.seminorm Real j.1 j.2
      (osiiStep4CenteredComplexBlockRadialGRealSchwartz
        (q + 1) hrho center imag) ≤
      (2 ^ (2 * p + 1) * I⁻¹ * Real.exp 6 * A ^ l *
        (l.factorial : Real) ^ 2) *
        a ^ (2 * (q + 1) + l) * b ^ p
  calc
    SchwartzMap.seminorm Real j.1 j.2
      (osiiStep4CenteredComplexBlockRadialGRealSchwartz
        (q + 1) hrho center imag) ≤
      2 ^ (j.1 - 1) *
        (SchwartzMap.seminorm Real j.1 j.2
            (osiiStep4ComplexBlockRadialGRealSchwartz
              (q + 1) hrho imag) +
          SchwartzMap.seminorm Real 0 j.2
            (osiiStep4ComplexBlockRadialGRealSchwartz
              (q + 1) hrho imag)) * b ^ j.1 := by
        simpa [b] using
          osiiStep4CenteredComplexBlockRadialGRealSchwartz_seminorm_le
            (q + 1) hrho j.1 j.2 center imag
    _ ≤ 2 ^ p *
        (C * a ^ (2 * (q + 1) + l) +
          C * a ^ (2 * (q + 1) + l)) * b ^ p := by
      gcongr
    _ = (2 ^ (2 * p + 1) * I⁻¹ * Real.exp 6 * A ^ l *
        (l.factorial : Real) ^ 2) *
        a ^ (2 * (q + 1) + l) * b ^ p := by
      have htwo : (2 : Real) ^ (2 * p + 1) =
          2 ^ p * 2 ^ p * 2 := by
        rw [show 2 * p + 1 = p + p + 1 by omega,
          pow_add, pow_add]
        norm_num
      rw [htwo]
      dsimp [C]
      ring

end OSReconstruction
