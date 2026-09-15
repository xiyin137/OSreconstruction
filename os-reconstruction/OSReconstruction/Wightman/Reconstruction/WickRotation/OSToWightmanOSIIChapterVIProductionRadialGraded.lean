/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformSchwartzDegree
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIProductionRadialEndpoint












noncomputable section

open MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

local instance osiiProduction_complexRealCoordinateCLMNorm (q m : Nat) :
    Norm ((Fin q → Complex) →L[Real] (Fin m → Real)) :=
  ContinuousLinearMap.hasOpNorm
    (𝕜 := Real) (𝕜₂ := Real)
    (E := Fin q → Complex) (F := Fin m → Real)
    (σ₁₂ := RingHom.id Real)

local instance osiiProduction_complexRealMultilinearNorm (q n : Nat) :
    Norm
      (ContinuousMultilinearMap Real
        (fun _ : Fin n => Fin q → Complex) Real) :=
  ContinuousMultilinearMap.hasOpNorm

theorem osiiProduction_schwartzTensorProductFinsetFactor_Iic
    (p l : Nat) :
    schwartzTensorProductFinsetFactor (Finset.Iic (p, l)) =
      2 * ((2 : Real) ^ (p + 1) - 1) *
        ((2 : Real) ^ (l + 1) - 1) := by
  have hrectangle :
      Finset.Iic (p, l) =
        (Finset.range (p + 1)).product (Finset.range (l + 1)) := by
    ext j
    rcases j with ⟨a, b⟩
    simp
  have hchoose (n : Nat) :
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : Real) * (1 + 1)) =
        2 * (2 : Real) ^ n := by
    have hsum :
        (∑ i ∈ Finset.range (n + 1), (n.choose i : Real)) =
          (2 : Real) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [← Finset.sum_mul, hsum]
    ring
  have hgeom (n : Nat) :
      (∑ i ∈ Finset.range (n + 1), (2 : Real) ^ i) =
        (2 : Real) ^ (n + 1) - 1 := by
    simpa only [show (2 : Real) - 1 = 1 by norm_num, mul_one] using
      geom_sum_mul (2 : Real) (n + 1)
  unfold schwartzTensorProductFinsetFactor
  rw [hrectangle]
  calc
    (∑ j ∈ (Finset.range (p + 1)).product (Finset.range (l + 1)),
        (2 : Real) ^ j.1 *
          ∑ i ∈ Finset.range (j.2 + 1),
            (j.2.choose i : Real) * (1 + 1)) =
        ∑ a ∈ Finset.range (p + 1),
          ∑ b ∈ Finset.range (l + 1),
            (2 : Real) ^ a *
              ∑ i ∈ Finset.range (b + 1),
                (b.choose i : Real) * (1 + 1) := by
      exact Finset.sum_product
        (Finset.range (p + 1)) (Finset.range (l + 1))
        (fun j : Nat × Nat =>
          (2 : Real) ^ j.1 *
            ∑ i ∈ Finset.range (j.2 + 1),
              (j.2.choose i : Real) * (1 + 1))
    _ = ∑ a ∈ Finset.range (p + 1),
        ∑ b ∈ Finset.range (l + 1),
          (2 : Real) ^ a * (2 * (2 : Real) ^ b) := by
      simp_rw [hchoose]
    _ =
        (∑ a ∈ Finset.range (p + 1), (2 : Real) ^ a) *
          (2 * (∑ b ∈ Finset.range (l + 1), (2 : Real) ^ b)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = 2 * ((2 : Real) ^ (p + 1) - 1) *
          ((2 : Real) ^ (l + 1) - 1) := by
      rw [hgeom p, hgeom l]
      ring

theorem osiiProduction_countPerms_eq_multinomial
    (r n : Nat) (p : Sym (Fin r) n) :
    (p : Multiset (Fin r)).countPerms =
      Nat.multinomial (Finset.univ : Finset (Fin r))
        (fun i => (p : Multiset (Fin r)).count i) := by
  unfold Multiset.countPerms
  rw [Finsupp.multinomial_eq_of_support_subset
    (Finset.subset_univ _)]
  rfl

theorem osiiProduction_symmetric_gevrey_sum
    (r n : Nat) :
    (∑ p ∈ (Finset.univ : Finset (Fin r)).sym n,
      (p : Multiset (Fin r)).countPerms *
        ∏ i : Fin r,
          ((p : Multiset (Fin r)).count i).factorial ^ 2) ≤
      r ^ n * n.factorial ^ 2 := by
  calc
    (∑ p ∈ (Finset.univ : Finset (Fin r)).sym n,
      (p : Multiset (Fin r)).countPerms *
        ∏ i : Fin r,
          ((p : Multiset (Fin r)).count i).factorial ^ 2) =
      ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) n,
        Nat.multinomial Finset.univ a *
          ∏ i : Fin r, (a i).factorial ^ 2 := by
      rw [← Finset.map_sym_eq_piAntidiag, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro p hp
      rw [osiiProduction_countPerms_eq_multinomial]
      rfl
    _ ≤ r ^ n * n.factorial ^ 2 :=
      osiiProductionMultinomial_gevrey_sum r n

theorem osiiProduction_iteratedFDeriv_prod_gevrey_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (r n : Nat) (f : Fin r → E → Complex)
    (hf : ∀ i, ContDiff Real (⊤ : ℕ∞) (f i))
    (x : E) (A B : Real) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ (i : Fin r) (j : Nat),
      ‖iteratedFDeriv Real j (f i) x‖ ≤
        A * B ^ j * (j.factorial : Real) ^ 2) :
    ‖iteratedFDeriv Real n
        (fun z : E => ∏ i : Fin r, f i z) x‖ ≤
      A ^ r * B ^ n * (r : Real) ^ n *
        (n.factorial : Real) ^ 2 := by
  have hcounts (p : Sym (Fin r) n) :
      (∑ i : Fin r, (p : Multiset (Fin r)).count i) = n := by
    calc
      (∑ i : Fin r, (p : Multiset (Fin r)).count i) =
          (p : Multiset (Fin r)).card := by
        exact Multiset.sum_count_eq_card
          (s := (Finset.univ : Finset (Fin r)))
          (by simp)
      _ = n := Sym.card_coe
  have hproduct (p : Sym (Fin r) n) :
      (∏ i : Fin r,
        ‖iteratedFDeriv Real
          ((p : Multiset (Fin r)).count i) (f i) x‖) ≤
      A ^ r * B ^ n *
        ∏ i : Fin r,
          (((p : Multiset (Fin r)).count i).factorial : Real) ^ 2 := by
    calc
      (∏ i : Fin r,
        ‖iteratedFDeriv Real
          ((p : Multiset (Fin r)).count i) (f i) x‖) ≤
          ∏ i : Fin r,
            (A * B ^ ((p : Multiset (Fin r)).count i) *
              (((p : Multiset (Fin r)).count i).factorial : Real) ^ 2) := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          exact hbound i ((p : Multiset (Fin r)).count i)
      _ = (∏ _i : Fin r, A) *
            (∏ i : Fin r, B ^ ((p : Multiset (Fin r)).count i)) *
            (∏ i : Fin r,
              (((p : Multiset (Fin r)).count i).factorial : Real) ^ 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      _ = A ^ r * B ^ n *
            ∏ i : Fin r,
              (((p : Multiset (Fin r)).count i).factorial : Real) ^ 2 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow_eq_pow_sum, hcounts]
  have hsym :
      (∑ p ∈ (Finset.univ : Finset (Fin r)).sym n,
        ((p : Multiset (Fin r)).countPerms : Real) *
          ∏ i : Fin r,
            (((p : Multiset (Fin r)).count i).factorial : Real) ^ 2) ≤
        (r : Real) ^ n * (n.factorial : Real) ^ 2 := by
    exact_mod_cast osiiProduction_symmetric_gevrey_sum r n
  calc
    ‖iteratedFDeriv Real n
        (fun z : E => ∏ i : Fin r, f i z) x‖ ≤
      ∑ p ∈ (Finset.univ : Finset (Fin r)).sym n,
        ((p : Multiset (Fin r)).countPerms : Real) *
          ∏ i : Fin r,
            ‖iteratedFDeriv Real
              ((p : Multiset (Fin r)).count i) (f i) x‖ := by
      exact norm_iteratedFDeriv_prod_le
        (𝕜 := Real) (u := (Finset.univ : Finset (Fin r)))
        (fun i hi => hf i)
        (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin r)).sym n,
        ((p : Multiset (Fin r)).countPerms : Real) *
          (A ^ r * B ^ n *
            ∏ i : Fin r,
              (((p : Multiset (Fin r)).count i).factorial : Real) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hproduct p) (by positivity)
    _ = A ^ r * B ^ n *
          (∑ p ∈ (Finset.univ : Finset (Fin r)).sym n,
            ((p : Multiset (Fin r)).countPerms : Real) *
              ∏ i : Fin r,
                (((p : Multiset (Fin r)).count i).factorial : Real) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ A ^ r * B ^ n *
          ((r : Real) ^ n * (n.factorial : Real) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsym
        (mul_nonneg (pow_nonneg hA _) (pow_nonneg hB _))
    _ = A ^ r * B ^ n * (r : Real) ^ n *
          (n.factorial : Real) ^ 2 := by
      ring

theorem osiiProduction_iteratedFDeriv_prod_scaled_gevrey_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (r n degree : Nat) (f : Fin r → E → Complex)
    (hf : ∀ i, ContDiff Real (⊤ : ℕ∞) (f i))
    (x : E) (A B scale : Real)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hscale : 0 ≤ scale)
    (hbound : ∀ (i : Fin r) (j : Nat),
      ‖iteratedFDeriv Real j (f i) x‖ ≤
        A * B ^ j * (j.factorial : Real) ^ 2 *
          scale ^ (degree + j)) :
    ‖iteratedFDeriv Real n
        (fun z : E => ∏ i : Fin r, f i z) x‖ ≤
      A ^ r * B ^ n * (r : Real) ^ n *
        (n.factorial : Real) ^ 2 *
          scale ^ (degree * r + n) := by
  have hbase := osiiProduction_iteratedFDeriv_prod_gevrey_bound
    r n f hf x (A * scale ^ degree) (B * scale)
    (mul_nonneg hA (pow_nonneg hscale _)) (mul_nonneg hB hscale)
    (by
      intro i j
      calc
        ‖iteratedFDeriv Real j (f i) x‖ ≤
            A * B ^ j * (j.factorial : Real) ^ 2 *
              scale ^ (degree + j) := hbound i j
        _ = (A * scale ^ degree) * (B * scale) ^ j *
              (j.factorial : Real) ^ 2 := by
          rw [pow_add, mul_pow]
          ring)
  calc
    ‖iteratedFDeriv Real n
        (fun z : E => ∏ i : Fin r, f i z) x‖ ≤
        (A * scale ^ degree) ^ r * (B * scale) ^ n *
          (r : Real) ^ n * (n.factorial : Real) ^ 2 := hbase
    _ = A ^ r * B ^ n * (r : Real) ^ n *
          (n.factorial : Real) ^ 2 *
            scale ^ (degree * r + n) := by
      rw [mul_pow, mul_pow, ← pow_mul, pow_add]
      ring

theorem osiiProduction_integral_norm_le_closedBall_volume
    (q : Nat) (phi : SchwartzMap (Fin q → Real) Complex)
    {radius coefficient : Real}
    (hradius : 0 ≤ radius)
    (hsupport :
      Function.support (phi : (Fin q → Real) → Complex) ⊆
        Metric.closedBall 0 radius)
    (hbound : ∀ x : Fin q → Real, ‖phi x‖ ≤ coefficient) :
    (∫ x : Fin q → Real, ‖phi x‖) ≤
      coefficient * (2 * radius) ^ q := by
  let s : Set (Fin q → Real) := Metric.closedBall 0 radius
  have hs : MeasurableSet s := isClosed_closedBall.measurableSet
  have hfinite :
      (volume : Measure (Fin q → Real)) s ≠ ⊤ :=
    (isCompact_closedBall (0 : Fin q → Real) radius).measure_ne_top
  have hrestrict :
      (∫ x : Fin q → Real, ‖phi x‖) =
        ∫ x in s, ‖phi x‖ := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · have hzero : phi x = 0 := by
        by_contra hn
        exact hx (hsupport (by simpa [Function.mem_support] using hn))
      simp [Set.indicator_of_notMem hx, hzero]
  have hvolume :
      (volume : Measure (Fin q → Real)).real s =
        (2 * radius) ^ q := by
    rw [measureReal_def, Real.volume_pi_closedBall 0 hradius,
      ENNReal.toReal_ofReal (by positivity)]
    simp
  calc
    (∫ x : Fin q → Real, ‖phi x‖) = ∫ x in s, ‖phi x‖ :=
      hrestrict
    _ ≤ ∫ _x in s, coefficient := by
      exact setIntegral_mono_on
        phi.integrable.norm.integrableOn
        (integrableOn_const hfinite) hs
        (fun x _ => hbound x)
    _ = coefficient * (2 * radius) ^ q := by
      rw [setIntegral_const, smul_eq_mul, hvolume]
      ring

theorem osiiStep4ComplexBlockRadialGRealSchwartz_integral_norm_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag : Fin (q + 1) → Real) :
    (∫ x : Fin (q + 1) → Real,
        ‖osiiStep4ComplexBlockRadialGRealSchwartz
          (q + 1) hrho imag x‖) ≤
      ((∫ z : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
        Real.exp 6) *
        (rho / 4) ^ (q + 1) *
        (16 / rho) ^ (2 * (q + 1)) := by
  let phi := osiiStep4ComplexBlockRadialGRealSchwartz
    (q + 1) hrho imag
  let C : Real :=
    ((∫ z : Fin (q + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
      Real.exp 6) *
      (16 / rho) ^ (2 * (q + 1))
  have hsupport :
      Function.support (phi : (Fin (q + 1) → Real) → Complex) ⊆
        Metric.closedBall 0 (rho / 8) := by
    intro x hx
    apply osiiStep4ComplexBlockRadialGRealSlice_support_subset_closedBall
      (q + 1) hrho imag
    simpa [Function.mem_support, phi,
      osiiStep4ComplexBlockRadialGRealSlice] using hx
  have hbound (x : Fin (q + 1) → Real) : ‖phi x‖ ≤ C := by
    simpa [phi, C] using
      osiiStep4ComplexBlockRadialGRealSchwartz_iteratedFDeriv_gevrey_bound
        q hrho imag x 0
  have h := osiiProduction_integral_norm_le_closedBall_volume
    (q + 1) phi (radius := rho / 8) (coefficient := C)
    (by positivity) hsupport hbound
  change (∫ x : Fin (q + 1) → Real, ‖phi x‖) ≤
    ((∫ z : Fin (q + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
      Real.exp 6) *
      (rho / 4) ^ (q + 1) *
      (16 / rho) ^ (2 * (q + 1))
  calc
    (∫ x : Fin (q + 1) → Real, ‖phi x‖) ≤
        C * (2 * (rho / 8)) ^ (q + 1) := h
    _ = ((∫ z : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
        Real.exp 6) *
        (rho / 4) ^ (q + 1) *
        (16 / rho) ^ (2 * (q + 1)) := by
      dsimp [C]
      rw [show 2 * (rho / 8) = rho / 4 by ring]
      ring

noncomputable def osiiStep4ComplexBlockRadialGComplexSchwartz
    (q : Nat) {rho : Real} (hrho : 0 < rho) :
    SchwartzMap (Fin q → Complex) Complex :=
  SchwartzMap.ofRealCLM
    ((osiiStep4ComplexBlockRadialG_hasCompactSupport q hrho).toSchwartzMap
      (osiiStep4ComplexBlockRadialG_contDiff q hrho))

@[simp] theorem osiiStep4ComplexBlockRadialGComplexSchwartz_apply
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (z : Fin q → Complex) :
    osiiStep4ComplexBlockRadialGComplexSchwartz q hrho z =
      osiiStep4ComplexBlockRadialG q rho z := by
  simp [osiiStep4ComplexBlockRadialGComplexSchwartz]

theorem osiiProductionComplexBlockRealCoordinateCLM_norm_le_one
    (q : Nat) :
    ‖osiiProductionComplexBlockRealCoordinateCLM q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa using osiiProductionComplexBlockRealCoordinateCLM_apply_norm_le q z

theorem osiiStep4ComplexBlockRadialG_iteratedFDeriv_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (z : Fin (q + 1) → Complex) (n : Nat) :
    ‖iteratedFDeriv Real n
        (osiiStep4ComplexBlockRadialG (q + 1) rho) z‖ ≤
      ((∫ w : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
        Real.exp 6 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2) *
        (16 / rho) ^ (2 * (q + 1) + n) := by
  let L := osiiProductionComplexBlockRealCoordinateCLM (q + 1)
  let G := osiiProductionNormalizedRadialRealProfile (q + 1) rho
  let C : Real :=
    ((∫ w : Fin (q + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
      Real.exp 6 *
      (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
        (n.factorial : Real) ^ 2) *
      (16 / rho) ^ (2 * (q + 1) + n)
  have hC : 0 ≤ C := by
    have hmass :
        0 < ∫ w : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 w :=
      osiiStep4ComplexBlockRadialRaw_integral_pos
        (q + 1) (by norm_num)
    dsimp [C]
    positivity
  have hG : ContDiff Real (⊤ : ℕ∞) G :=
    osiiProductionNormalizedRadialRealProfile_contDiff (q + 1) rho
  have hfun :
      osiiStep4ComplexBlockRadialG (q + 1) rho =
        G ∘ L := by
    funext w
    exact osiiStep4ComplexBlockRadialG_eq_normalizedRealProfile
      (q + 1) hrho w
  have hglobal : ‖iteratedFDeriv Real n G (L z)‖ ≤ C :=
    osiiProductionNormalizedRadialRealProfile_global_gevrey_bound
      q hrho (L z) n
  have hL : ‖L‖ ≤ 1 :=
    osiiProductionComplexBlockRealCoordinateCLM_norm_le_one (q + 1)
  have hLnonneg : 0 ≤ ‖L‖ :=
    ContinuousLinearMap.opNorm_nonneg L
  have hiter :
      iteratedFDeriv Real n (G ∘ L) z =
        (iteratedFDeriv Real n G (L z)).compContinuousLinearMap
          (fun _ => L) := by
    exact L.iteratedFDeriv_comp_right hG z (i := n)
      (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
  change ‖iteratedFDeriv Real n
    (osiiStep4ComplexBlockRadialG (q + 1) rho) z‖ ≤ C
  rw [hfun, hiter]
  calc
    ‖(iteratedFDeriv Real n G (L z)).compContinuousLinearMap
        (fun _ => L)‖ ≤
      ‖iteratedFDeriv Real n G (L z)‖ *
        ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * 1 := by
      apply mul_le_mul hglobal
      · exact Finset.prod_le_one
          (fun _ _ => hLnonneg) (fun _ _ => hL)
      · exact Finset.prod_nonneg (fun _ _ => hLnonneg)
      · exact hC
    _ = C := mul_one _

theorem osiiStep4ComplexBlockRadialGComplexSchwartz_iteratedFDeriv_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (z : Fin (q + 1) → Complex) (n : Nat) :
    ‖iteratedFDeriv Real n
        (osiiStep4ComplexBlockRadialGComplexSchwartz
          (q + 1) hrho : (Fin (q + 1) → Complex) → Complex) z‖ ≤
      ((∫ w : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
        Real.exp 6 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2) *
        (16 / rho) ^ (2 * (q + 1) + n) := by
  have hfun :
      (osiiStep4ComplexBlockRadialGComplexSchwartz
        (q + 1) hrho : (Fin (q + 1) → Complex) → Complex) =
      Complex.ofRealLI ∘ osiiStep4ComplexBlockRadialG (q + 1) rho := by
    funext w
    simp
  rw [hfun, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    (osiiStep4ComplexBlockRadialG_contDiff
      (q + 1) hrho).contDiffAt
    (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))]
  exact osiiStep4ComplexBlockRadialG_iteratedFDeriv_gevrey_bound
    q hrho z n

theorem osiiProduction_realConvolutionTest_iteratedFDeriv_norm_le_L1
    (q : Nat)
    (theta : SchwartzMap (Fin q → Complex) Complex)
    (psi : SchwartzMap (Fin q → Real) Complex)
    (n : Nat) (z : Fin q → Complex) (C : Real)
    (hbound : ∀ w : Fin q → Complex,
      ‖iteratedFDeriv Real n
        (theta : (Fin q → Complex) → Complex) w‖ ≤ C) :
    ‖iteratedFDeriv Real n
        (SCV.realConvolutionTest theta psi :
          (Fin q → Complex) → Complex) z‖ ≤
      C * ∫ u : Fin q → Real, ‖psi u‖ := by
  rw [SCV.iteratedFDeriv_realConvolutionTest_eq_integral]
  calc
    ‖∫ u : Fin q → Real,
        (psi u) • iteratedFDeriv Real n
          (theta : (Fin q → Complex) → Complex)
            (z - SCV.realEmbed u)‖ ≤
      ∫ u : Fin q → Real, C * ‖psi u‖ := by
      apply norm_integral_le_of_norm_le
        (psi.integrable.norm.const_mul C)
      filter_upwards with u
      rw [norm_smul]
      calc
        ‖psi u‖ *
            ‖iteratedFDeriv Real n
              (theta : (Fin q → Complex) → Complex)
                (z - SCV.realEmbed u)‖ ≤
          ‖psi u‖ * C := by
            exact mul_le_mul_of_nonneg_left
              (hbound (z - SCV.realEmbed u)) (norm_nonneg _)
        _ = C * ‖psi u‖ := by ring
    _ = C * ∫ u : Fin q → Real, ‖psi u‖ := by
      rw [integral_const_mul]

theorem osiiStep4ComplexBlockRadialConvolution_iteratedFDeriv_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag : Fin (q + 1) → Real)
    (z : Fin (q + 1) → Complex) (n : Nat) :
    ‖iteratedFDeriv Real n
        (SCV.realConvolutionTest
          (osiiStep4ComplexBlockRadialGComplexSchwartz
            (q + 1) hrho)
          (osiiStep4ComplexBlockRadialGRealSchwartz
            (q + 1) hrho imag) :
              (Fin (q + 1) → Complex) → Complex) z‖ ≤
      (4 : Real) ^ (q + 1) *
        ((∫ w : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
          Real.exp 6) ^ 2 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2 *
        (16 / rho) ^ (3 * (q + 1) + n) := by
  let M : Real :=
    (∫ w : Fin (q + 1) → Complex,
      osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
      Real.exp 6
  let B : Real := 98304 * (((q + 1) * 2 : Nat) : Real) ^ 2
  let a : Real := 16 / rho
  let theta := osiiStep4ComplexBlockRadialGComplexSchwartz
    (q + 1) hrho
  let psi := osiiStep4ComplexBlockRadialGRealSchwartz
    (q + 1) hrho imag
  let C : Real :=
    M * B ^ n * (n.factorial : Real) ^ 2 *
      a ^ (2 * (q + 1) + n)
  have hmass :
      0 < ∫ w : Fin (q + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (q + 1) 16 w :=
    osiiStep4ComplexBlockRadialRaw_integral_pos
      (q + 1) (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C, M, B, a]
    positivity
  have htheta (w : Fin (q + 1) → Complex) :
      ‖iteratedFDeriv Real n
        (theta : (Fin (q + 1) → Complex) → Complex) w‖ ≤ C := by
    simpa [theta, C, M, B, a] using
      osiiStep4ComplexBlockRadialGComplexSchwartz_iteratedFDeriv_gevrey_bound
        q hrho w n
  have hpsi :
      (∫ u : Fin (q + 1) → Real, ‖psi u‖) ≤
        M * (rho / 4) ^ (q + 1) * a ^ (2 * (q + 1)) := by
    simpa [psi, M, a] using
      osiiStep4ComplexBlockRadialGRealSchwartz_integral_norm_gevrey_bound
        q hrho imag
  have hratio : (rho / 4) * a = 4 := by
    dsimp [a]
    field_simp
    ring
  have hcombine :
      (rho / 4) ^ (q + 1) * a ^ (q + 1) =
        (4 : Real) ^ (q + 1) := by
    rw [← mul_pow, hratio]
  have htwo :
      a ^ (2 * (q + 1)) = a ^ (q + 1) * a ^ (q + 1) := by
    rw [show 2 * (q + 1) = (q + 1) + (q + 1) by omega,
      pow_add]
  have hthree :
      a ^ (3 * (q + 1)) =
        a ^ (q + 1) * a ^ (q + 1) * a ^ (q + 1) := by
    rw [show 3 * (q + 1) =
      ((q + 1) + (q + 1)) + (q + 1) by omega,
      pow_add, pow_add]
  change ‖iteratedFDeriv Real n
      (SCV.realConvolutionTest theta psi :
        (Fin (q + 1) → Complex) → Complex) z‖ ≤
    (4 : Real) ^ (q + 1) * M ^ 2 * B ^ n *
      (n.factorial : Real) ^ 2 * a ^ (3 * (q + 1) + n)
  calc
    ‖iteratedFDeriv Real n
        (SCV.realConvolutionTest theta psi :
          (Fin (q + 1) → Complex) → Complex) z‖ ≤
        C * ∫ u : Fin (q + 1) → Real, ‖psi u‖ :=
      osiiProduction_realConvolutionTest_iteratedFDeriv_norm_le_L1
        (q + 1) theta psi n z C htheta
    _ ≤ C *
          (M * (rho / 4) ^ (q + 1) * a ^ (2 * (q + 1))) :=
      mul_le_mul_of_nonneg_left hpsi hC
    _ = M ^ 2 * B ^ n * (n.factorial : Real) ^ 2 *
          ((rho / 4) ^ (q + 1) * a ^ (q + 1)) *
            a ^ (3 * (q + 1) + n) := by
      dsimp [C]
      rw [show a ^ (2 * (q + 1) + n) =
        a ^ (2 * (q + 1)) * a ^ n by rw [pow_add],
        show a ^ (3 * (q + 1) + n) =
          a ^ (3 * (q + 1)) * a ^ n by rw [pow_add],
        htwo, hthree]
      ring
    _ = (4 : Real) ^ (q + 1) * M ^ 2 * B ^ n *
          (n.factorial : Real) ^ 2 *
            a ^ (3 * (q + 1) + n) := by
      rw [hcombine]
      ring

theorem osiiStep4ComplexBlockPartialConvolutionKernel_eq_slice_convolution
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (x y y' : Fin q → Real) :
    (osiiStep4ComplexBlockPartialConvolutionKernel q rho
      (osiiStep4ComplexOfRealImag x y) y' : Complex) =
      ∫ u : Fin q → Real,
        osiiStep4ComplexBlockRadialGRealSchwartz q hrho (y - y') (x - u) *
          osiiStep4ComplexBlockRadialGRealSchwartz q hrho y' u := by
  rw [osiiStep4ComplexBlockPartialConvolutionKernel_eq_integral,
    ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with u
  have hargument :
      osiiStep4ComplexOfRealImag x y -
          osiiStep4ComplexOfRealImag u y' =
        osiiStep4ComplexOfRealImag (x - u) (y - y') := by
    ext i
    simp [osiiStep4ComplexOfRealImag]
    ring
  simp only [osiiStep4ComplexBlockPartialConvolutionIntegrand,
    osiiStep4ComplexBlockRadialGRealSchwartz_apply]
  push_cast
  rw [hargument]

theorem osiiStep4ComplexBlockPartialConvolutionKernel_eq_realConvolution
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (x y y' : Fin q → Real) :
    (osiiStep4ComplexBlockPartialConvolutionKernel q rho
      (osiiStep4ComplexOfRealImag x y) y' : Complex) =
      SCV.realConvolutionTest
        (osiiStep4ComplexBlockRadialGComplexSchwartz q hrho)
        (osiiStep4ComplexBlockRadialGRealSchwartz q hrho y')
        (osiiStep4ComplexOfRealImag x (y - y')) := by
  rw [osiiStep4ComplexBlockPartialConvolutionKernel_eq_slice_convolution
    q hrho x y y',
    SCV.realConvolutionTest_apply]
  apply integral_congr_ae
  filter_upwards with u
  have hargument :
      osiiStep4ComplexOfRealImag x (y - y') - SCV.realEmbed u =
        osiiStep4ComplexOfRealImag (x - u) (y - y') := by
    ext i
    simp [osiiStep4ComplexOfRealImag, SCV.realEmbed]
    ring
  simp [hargument]

theorem osiiProduction_realEmbedContinuousLinearMap_norm_le_one
    (q : Nat) :
    ‖SCV.realEmbedContinuousLinearMap q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using SCV.norm_realEmbed_le x

set_option maxHeartbeats 1000000 in
theorem osiiStep4ComplexBlockPartialConvolutionKernel_iteratedFDeriv_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (x y y' : Fin (q + 1) → Real) (n : Nat) :
    ‖iteratedFDeriv Real n
        (fun w : Fin (q + 1) → Real =>
          (osiiStep4ComplexBlockPartialConvolutionKernel (q + 1) rho
            (osiiStep4ComplexOfRealImag w y) y' : Complex)) x‖ ≤
      (4 : Real) ^ (q + 1) *
        ((∫ w : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
          Real.exp 6) ^ 2 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2 *
        (16 / rho) ^ (3 * (q + 1) + n) := by
  let L := SCV.realEmbedContinuousLinearMap (q + 1)
  let b := osiiStep4ComplexOfRealImag 0 (y - y')
  let theta := osiiStep4ComplexBlockRadialGComplexSchwartz
    (q + 1) hrho
  let psi := osiiStep4ComplexBlockRadialGRealSchwartz
    (q + 1) hrho y'
  let F := SCV.realConvolutionTest theta psi
  let C : Real :=
    (4 : Real) ^ (q + 1) *
      ((∫ w : Fin (q + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
        Real.exp 6) ^ 2 *
      (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
        (n.factorial : Real) ^ 2 *
      (16 / rho) ^ (3 * (q + 1) + n)
  have hC : 0 ≤ C := by
    have hmass :
        0 < ∫ w : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 w :=
      osiiStep4ComplexBlockRadialRaw_integral_pos
        (q + 1) (by norm_num)
    dsimp [C]
    positivity
  have hfun :
      (fun w : Fin (q + 1) → Real =>
        (osiiStep4ComplexBlockPartialConvolutionKernel (q + 1) rho
          (osiiStep4ComplexOfRealImag w y) y' : Complex)) =
        fun w => F (b + L w) := by
    funext w
    rw [osiiStep4ComplexBlockPartialConvolutionKernel_eq_realConvolution
      (q + 1) hrho w y y']
    congr 1
    ext i
    simp [b, L, osiiStep4ComplexOfRealImag, SCV.realEmbed]
    ring
  have hshift :
      ContDiff Real (⊤ : ℕ∞)
        (fun w : Fin (q + 1) → Complex => F (b + w)) :=
    F.smooth'.comp (contDiff_const.add contDiff_id)
  have hiter :
      iteratedFDeriv Real n
        (fun w : Fin (q + 1) → Real => F (b + L w)) x =
        (iteratedFDeriv Real n
          (F : (Fin (q + 1) → Complex) → Complex) (b + L x)).compContinuousLinearMap
            (fun _ => L) := by
    have hcompose :=
      L.iteratedFDeriv_comp_right hshift x (i := n)
        (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
    rw [iteratedFDeriv_comp_add_left] at hcompose
    exact hcompose
  have hF :
      ‖iteratedFDeriv Real n
        (F : (Fin (q + 1) → Complex) → Complex) (b + L x)‖ ≤ C := by
    simpa [F, theta, psi, C] using
      osiiStep4ComplexBlockRadialConvolution_iteratedFDeriv_gevrey_bound
        q hrho y' (b + L x) n
  have hL : ‖L‖ ≤ 1 :=
    osiiProduction_realEmbedContinuousLinearMap_norm_le_one (q + 1)
  have hLnonneg : 0 ≤ ‖L‖ :=
    ContinuousLinearMap.opNorm_nonneg L
  change ‖iteratedFDeriv Real n
      (fun w : Fin (q + 1) → Real =>
        (osiiStep4ComplexBlockPartialConvolutionKernel (q + 1) rho
          (osiiStep4ComplexOfRealImag w y) y' : Complex)) x‖ ≤ C
  rw [hfun, hiter]
  calc
    ‖(iteratedFDeriv Real n
        (F : (Fin (q + 1) → Complex) → Complex) (b + L x)).compContinuousLinearMap
          (fun _ => L)‖ ≤
      ‖iteratedFDeriv Real n
        (F : (Fin (q + 1) → Complex) → Complex) (b + L x)‖ *
          ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * 1 := by
      apply mul_le_mul hF
      · exact Finset.prod_le_one
          (fun _ _ => hLnonneg) (fun _ _ => hL)
      · exact Finset.prod_nonneg (fun _ _ => hLnonneg)
      · exact hC
    _ = C := mul_one _

theorem osiiStep4ComplexBlockPartialConvolutionKernel_contDiff
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (y y' : Fin q → Real) :
    ContDiff Real (⊤ : ℕ∞)
      (fun x : Fin q → Real =>
        (osiiStep4ComplexBlockPartialConvolutionKernel q rho
          (osiiStep4ComplexOfRealImag x y) y' : Complex)) := by
  let theta := osiiStep4ComplexBlockRadialGComplexSchwartz q hrho
  let psi := osiiStep4ComplexBlockRadialGRealSchwartz q hrho y'
  have hfun :
      (fun x : Fin q → Real =>
        (osiiStep4ComplexBlockPartialConvolutionKernel q rho
          (osiiStep4ComplexOfRealImag x y) y' : Complex)) =
        fun x => SCV.realConvolutionTest theta psi
          (osiiStep4ComplexOfRealImag x (y - y')) := by
    funext x
    exact osiiStep4ComplexBlockPartialConvolutionKernel_eq_realConvolution
      q hrho x y y'
  have hargument :
      ContDiff Real (⊤ : ℕ∞)
        (fun x : Fin q → Real =>
          osiiStep4ComplexOfRealImag x (y - y')) := by
    rw [contDiff_pi]
    intro i
    change ContDiff Real (⊤ : ℕ∞)
      (fun x : Fin q → Real =>
        (x i : Complex) + (((y - y') i : Real) : Complex) * Complex.I)
    have hreal : ContDiff Real (⊤ : ℕ∞)
        (fun x : Fin q → Real => (x i : Complex)) :=
      Complex.ofRealCLM.contDiff.comp
        (ContinuousLinearMap.proj
          (R := Real) (ι := Fin q) (φ := fun _ => Real) i).contDiff
    exact hreal.add contDiff_const
  rw [hfun]
  exact (SCV.realConvolutionTest theta psi).smooth'.comp hargument

def osiiProductionRealBlockProjection
    (q k : Nat) (i : Fin k) :
    (Fin (k * q) → Real) →L[Real] (Fin q → Real) :=
  ContinuousLinearMap.pi fun mu =>
    ContinuousLinearMap.proj (finProdFinEquiv (i, mu))

@[simp] theorem osiiProductionRealBlockProjection_apply
    (q k : Nat) (i : Fin k) (x : Fin (k * q) → Real) (mu : Fin q) :
    osiiProductionRealBlockProjection q k i x mu =
      x (finProdFinEquiv (i, mu)) := by
  rfl

theorem osiiProductionRealBlockProjection_norm_le_one
    (q k : Nat) (i : Fin k) :
    ‖osiiProductionRealBlockProjection q k i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro mu
  simp only [osiiProductionRealBlockProjection_apply]
  exact norm_le_pi_norm x _

theorem osiiStep4ComplexBlockPartialConvolutionKernel_projected_derivative
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' x : Fin (k * (q + 1)) → Real)
    (i : Fin k) (n : Nat) :
    ‖iteratedFDeriv Real n
        (fun w : Fin (k * (q + 1)) → Real =>
          (osiiStep4ComplexBlockPartialConvolutionKernel (q + 1) rho
            (osiiStep4ComplexOfRealImag
              (fun mu =>
                w (finProdFinEquiv (i, mu)) -
                  center (finProdFinEquiv (i, mu)))
              (fun mu => y (finProdFinEquiv (i, mu))))
            (fun mu => y' (finProdFinEquiv (i, mu))) : Complex)) x‖ ≤
      (4 : Real) ^ (q + 1) *
        ((∫ w : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
          Real.exp 6) ^ 2 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2 *
        (16 / rho) ^ (3 * (q + 1) + n) := by
  let P := osiiProductionRealBlockProjection (q + 1) k i
  let c : Fin (q + 1) → Real :=
    fun mu => center (finProdFinEquiv (i, mu))
  let v : Fin (q + 1) → Real :=
    fun mu => y (finProdFinEquiv (i, mu))
  let v' : Fin (q + 1) → Real :=
    fun mu => y' (finProdFinEquiv (i, mu))
  let g : (Fin (q + 1) → Real) → Complex :=
    fun w =>
      (osiiStep4ComplexBlockPartialConvolutionKernel (q + 1) rho
        (osiiStep4ComplexOfRealImag w v) v' : Complex)
  let C : Real :=
    (4 : Real) ^ (q + 1) *
      ((∫ w : Fin (q + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
        Real.exp 6) ^ 2 *
      (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
        (n.factorial : Real) ^ 2 *
      (16 / rho) ^ (3 * (q + 1) + n)
  have hC : 0 ≤ C := by
    have hmass :
        0 < ∫ w : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 w :=
      osiiStep4ComplexBlockRadialRaw_integral_pos
        (q + 1) (by norm_num)
    dsimp [C]
    positivity
  have hg : ContDiff Real (⊤ : ℕ∞) g :=
    osiiStep4ComplexBlockPartialConvolutionKernel_contDiff
      (q + 1) hrho v v'
  have hshift :
      ContDiff Real (⊤ : ℕ∞)
        (fun w : Fin (q + 1) → Real => g (-c + w)) :=
    hg.comp (contDiff_const.add contDiff_id)
  have hfun :
      (fun w : Fin (k * (q + 1)) → Real =>
        (osiiStep4ComplexBlockPartialConvolutionKernel (q + 1) rho
          (osiiStep4ComplexOfRealImag
            (fun mu =>
              w (finProdFinEquiv (i, mu)) -
                center (finProdFinEquiv (i, mu)))
            (fun mu => y (finProdFinEquiv (i, mu))))
          (fun mu => y' (finProdFinEquiv (i, mu))) : Complex)) =
        fun w => g (-c + P w) := by
    funext w
    congr 2
    funext mu
    simp [c, P, v, osiiStep4ComplexOfRealImag]
    ring
  have hiter :
      iteratedFDeriv Real n
          (fun w : Fin (k * (q + 1)) → Real => g (-c + P w)) x =
        (iteratedFDeriv Real n g (-c + P x)).compContinuousLinearMap
          (fun _ => P) := by
    have hcompose :=
      P.iteratedFDeriv_comp_right hshift x (i := n)
        (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
    rw [iteratedFDeriv_comp_add_left] at hcompose
    exact hcompose
  have hbase : ‖iteratedFDeriv Real n g (-c + P x)‖ ≤ C := by
    exact osiiStep4ComplexBlockPartialConvolutionKernel_iteratedFDeriv_gevrey_bound
      q hrho (-c + P x) v v' n
  have hP : ‖P‖ ≤ 1 :=
    osiiProductionRealBlockProjection_norm_le_one (q + 1) k i
  change ‖iteratedFDeriv Real n _ x‖ ≤ C
  rw [hfun, hiter]
  calc
    ‖(iteratedFDeriv Real n g (-c + P x)).compContinuousLinearMap
        (fun _ => P)‖ ≤
      ‖iteratedFDeriv Real n g (-c + P x)‖ *
        ∏ _ : Fin n, ‖P‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * 1 := by
      apply mul_le_mul hbase
      · exact Finset.prod_le_one
          (fun _ _ => norm_nonneg _) (fun _ _ => hP)
      · positivity
      · exact hC
    _ = C := mul_one _

set_option maxHeartbeats 1200000 in
theorem osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_iteratedFDeriv_gevrey_bound
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' x : Fin (k * (q + 1)) → Real) (n : Nat) :
    ‖iteratedFDeriv Real n
        (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          (q + 1) k hrho center y y' :
            (Fin (k * (q + 1)) → Real) → Complex) x‖ ≤
      ((4 : Real) ^ (q + 1) *
        ((∫ w : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
          Real.exp 6) ^ 2) ^ k *
      (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
        (k : Real) ^ n * (n.factorial : Real) ^ 2 *
      (16 / rho) ^ (3 * (q + 1) * k + n) := by
  let A : Real := (4 : Real) ^ (q + 1) *
    ((∫ w : Fin (q + 1) → Complex,
      osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
      Real.exp 6) ^ 2
  let B : Real := 98304 * (((q + 1) * 2 : Nat) : Real) ^ 2
  let a : Real := 16 / rho
  let f : Fin k → (Fin (k * (q + 1)) → Real) → Complex :=
    fun i w =>
      (osiiStep4ComplexBlockPartialConvolutionKernel (q + 1) rho
        (osiiStep4ComplexOfRealImag
          (fun mu =>
            w (finProdFinEquiv (i, mu)) -
              center (finProdFinEquiv (i, mu)))
          (fun mu => y (finProdFinEquiv (i, mu))))
        (fun mu => y' (finProdFinEquiv (i, mu))) : Complex)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hf (i : Fin k) : ContDiff Real (⊤ : ℕ∞) (f i) := by
    let P := osiiProductionRealBlockProjection (q + 1) k i
    let c : Fin (q + 1) → Real :=
      fun mu => center (finProdFinEquiv (i, mu))
    let v : Fin (q + 1) → Real :=
      fun mu => y (finProdFinEquiv (i, mu))
    let v' : Fin (q + 1) → Real :=
      fun mu => y' (finProdFinEquiv (i, mu))
    have hargument :
        ContDiff Real (⊤ : ℕ∞)
          (fun w : Fin (k * (q + 1)) → Real => P w - c) :=
      P.contDiff.sub contDiff_const
    have h :=
      (osiiStep4ComplexBlockPartialConvolutionKernel_contDiff
        (q + 1) hrho v v').comp hargument
    have hfi :
        f i =
          (fun z =>
            (osiiStep4ComplexBlockPartialConvolutionKernel (q + 1) rho
              (osiiStep4ComplexOfRealImag z v) v' : Complex)) ∘
            (fun w => P w - c) := by
      funext w
      simp only [f, Function.comp_apply]
      have hreal :
          (fun mu =>
            w (finProdFinEquiv (i, mu)) -
              center (finProdFinEquiv (i, mu))) = P w - c := by
        funext mu
        rw [Pi.sub_apply, osiiProductionRealBlockProjection_apply]
      rw [hreal]
    rw [hfi]
    exact h
  have hfactor (i : Fin k) (j : Nat) :
      ‖iteratedFDeriv Real j (f i) x‖ ≤
        A * B ^ j * (j.factorial : Real) ^ 2 *
          a ^ (3 * (q + 1) + j) := by
    simpa [f, A, B, a] using
      osiiStep4ComplexBlockPartialConvolutionKernel_projected_derivative
        q k hrho center y y' x i j
  have hsource :
      (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        (q + 1) k hrho center y y' :
          (Fin (k * (q + 1)) → Real) → Complex) =
        fun w => ∏ i : Fin k, f i w := by
    funext w
    simpa [f] using
      osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply_eq_prod
        (q + 1) k hrho center y y' w
  change ‖iteratedFDeriv Real n
      (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        (q + 1) k hrho center y y' :
          (Fin (k * (q + 1)) → Real) → Complex) x‖ ≤
    A ^ k * B ^ n * (k : Real) ^ n *
      (n.factorial : Real) ^ 2 * a ^ (3 * (q + 1) * k + n)
  rw [hsource]
  exact osiiProduction_iteratedFDeriv_prod_scaled_gevrey_bound
    k n (3 * (q + 1)) f hf x A B a hA hB ha hfactor

theorem osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_seminorm_gevrey_bound
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (hrho_le : rho ≤ 16)
    (center y y' : Fin (k * (q + 1)) → Real) (p n : Nat) :
    SchwartzMap.seminorm Real p n
        (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          (q + 1) k hrho center y y') ≤
      (4 : Real) ^ p *
        ((4 : Real) ^ (q + 1) *
          ((∫ w : Fin (q + 1) → Complex,
            osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
            Real.exp 6) ^ 2) ^ k *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (k : Real) ^ n * (n.factorial : Real) ^ 2 *
        (16 / rho) ^ (3 * (q + 1) * k + n) *
          (1 + ‖center‖) ^ p := by
  let phi := osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
    (q + 1) k hrho center y y'
  let A : Real := (4 : Real) ^ (q + 1) *
    ((∫ w : Fin (q + 1) → Complex,
      osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
      Real.exp 6) ^ 2
  let B : Real := 98304 * (((q + 1) * 2 : Nat) : Real) ^ 2
  let a : Real := 16 / rho
  let C : Real := A ^ k * B ^ n *
    (k : Real) ^ n * (n.factorial : Real) ^ 2 *
      a ^ (3 * (q + 1) * k + n)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C, B, a]
    positivity
  have hsupp :
      tsupport (phi : (Fin (k * (q + 1)) → Real) → Complex) ⊆
        Metric.closedBall center (rho / 4) := by
    apply closure_minimal
    · exact
        osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_support_subset
          (q + 1) k hrho center y y'
    · exact isClosed_closedBall
  change SchwartzMap.seminorm Real p n phi ≤
    (4 : Real) ^ p * A ^ k * B ^ n *
      (k : Real) ^ n * (n.factorial : Real) ^ 2 *
        a ^ (3 * (q + 1) * k + n) * (1 + ‖center‖) ^ p
  suffices hmain : SchwartzMap.seminorm Real p n phi ≤
      (4 : Real) ^ p * C * (1 + ‖center‖) ^ p by
    calc
      SchwartzMap.seminorm Real p n phi ≤
          (4 : Real) ^ p * C * (1 + ‖center‖) ^ p := hmain
      _ = (4 : Real) ^ p * A ^ k * B ^ n *
          (k : Real) ^ n * (n.factorial : Real) ^ 2 *
            a ^ (3 * (q + 1) * k + n) * (1 + ‖center‖) ^ p := by
        dsimp [C]
        ring
  apply SchwartzMap.seminorm_le_bound Real p n phi (by positivity)
  intro x
  by_cases hzero : iteratedFDeriv Real n
      (phi : (Fin (k * (q + 1)) → Real) → Complex) x = 0
  · rw [hzero, norm_zero, mul_zero]
    positivity
  have hxball := hsupp
    (support_iteratedFDeriv_subset (𝕜 := Real) n hzero)
  rw [Metric.mem_closedBall, dist_eq_norm] at hxball
  have hxnorm : ‖x‖ ≤ 4 * (1 + ‖center‖) := by
    calc
      ‖x‖ = ‖(x - center) + center‖ := by
        congr 1
        abel
      _ ≤ ‖x - center‖ + ‖center‖ := norm_add_le _ _
      _ ≤ rho / 4 + ‖center‖ := by gcongr
      _ ≤ 4 * (1 + ‖center‖) := by
        have hradius : rho / 4 ≤ 4 := by linarith
        nlinarith [norm_nonneg center]
  have hderivative :
      ‖iteratedFDeriv Real n
        (phi : (Fin (k * (q + 1)) → Real) → Complex) x‖ ≤ C := by
    exact
      osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_iteratedFDeriv_gevrey_bound
        q k hrho center y y' x n
  calc
    ‖x‖ ^ p *
        ‖iteratedFDeriv Real n
          (phi : (Fin (k * (q + 1)) → Real) → Complex) x‖ ≤
      (4 * (1 + ‖center‖)) ^ p * C := by
        exact mul_le_mul
          (pow_le_pow_left₀ (norm_nonneg x) hxnorm p)
          hderivative (norm_nonneg _) (by positivity)
    _ = (4 : Real) ^ p * C * (1 + ‖center‖) ^ p := by
      rw [mul_pow]
      ring

set_option maxHeartbeats 800000 in
theorem osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_Iic_gevrey_bound
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (hrho_le : rho ≤ 16)
    (center y y' : Fin (k * (q + 1)) → Real) (p l : Nat) :
    (Finset.Iic (p, l)).sup
        (schwartzSeminormFamily Real
          (Fin (k * (q + 1)) → Real) Complex)
        (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          (q + 1) k hrho center y y') ≤
      (4 : Real) ^ p *
        ((4 : Real) ^ (q + 1) *
          ((∫ w : Fin (q + 1) → Complex,
            osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
            Real.exp 6) ^ 2) ^ k *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ l *
          ((k + 1 : Nat) : Real) ^ l *
          (l.factorial : Real) ^ 2 *
        (16 / rho) ^ (3 * (q + 1) * k + l) *
          (1 + ‖center‖) ^ p := by
  let A : Real := (4 : Real) ^ (q + 1) *
    ((∫ w : Fin (q + 1) → Complex,
      osiiStep4ComplexBlockRadialRaw (q + 1) 16 w)⁻¹ *
      Real.exp 6) ^ 2
  let B : Real := 98304 * (((q + 1) * 2 : Nat) : Real) ^ 2
  let a : Real := 16 / rho
  let b : Real := 1 + ‖center‖
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 1 ≤ B := by
    dsimp [B]
    have hdimension :
        (1 : Real) ≤ (((q + 1) * 2 : Nat) : Real) := by
      exact_mod_cast (show 1 ≤ (q + 1) * 2 by omega)
    nlinarith [sq_nonneg ((((q + 1) * 2 : Nat) : Real)),
      mul_self_le_mul_self (by positivity) hdimension]
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  have hb : 1 ≤ b := by
    dsimp [b]
    linarith [norm_nonneg center]
  apply Seminorm.finset_sup_apply_le
  · positivity
  intro j hj
  have horders : j.1 ≤ p ∧ j.2 ≤ l := Finset.mem_Iic.mp hj
  have hfactorial : (j.2.factorial : Real) ≤ l.factorial := by
    exact_mod_cast Nat.factorial_le horders.2
  have harity :
      (k : Real) ^ j.2 ≤ ((k + 1 : Nat) : Real) ^ l := by
    calc
      (k : Real) ^ j.2 ≤ ((k + 1 : Nat) : Real) ^ j.2 := by
        gcongr
        exact_mod_cast (show k ≤ k + 1 by omega)
      _ ≤ ((k + 1 : Nat) : Real) ^ l := by
        apply pow_le_pow_right₀
        · exact_mod_cast (show 1 ≤ k + 1 by omega)
        · exact horders.2
  have hscale :
      a ^ (3 * (q + 1) * k + j.2) ≤
        a ^ (3 * (q + 1) * k + l) :=
    pow_le_pow_right₀ ha (by omega)
  change SchwartzMap.seminorm Real j.1 j.2
      (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        (q + 1) k hrho center y y') ≤
    (4 : Real) ^ p * A ^ k * B ^ l *
      ((k + 1 : Nat) : Real) ^ l *
      (l.factorial : Real) ^ 2 *
      a ^ (3 * (q + 1) * k + l) * b ^ p
  calc
    SchwartzMap.seminorm Real j.1 j.2
        (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          (q + 1) k hrho center y y') ≤
      (4 : Real) ^ j.1 * A ^ k * B ^ j.2 *
        (k : Real) ^ j.2 * (j.2.factorial : Real) ^ 2 *
        a ^ (3 * (q + 1) * k + j.2) * b ^ j.1 := by
      exact
        osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_seminorm_gevrey_bound
          q k hrho hrho_le center y y' j.1 j.2
    _ ≤ (4 : Real) ^ p * A ^ k * B ^ l *
        ((k + 1 : Nat) : Real) ^ l *
        (l.factorial : Real) ^ 2 *
        a ^ (3 * (q + 1) * k + l) * b ^ p := by
      gcongr <;> try norm_num <;> aesop

theorem osiiProduction_flattenCLEquivReal_norm_le_one
    (k q : Nat) :
    ‖(flattenCLEquivReal k q).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using (flattenCLEquivReal_norm_eq k q x).le

theorem osiiProduction_flattenCLEquivReal_symm_norm_le_one
    (k q : Nat) :
    ‖(flattenCLEquivReal k q).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  calc
    ‖(flattenCLEquivReal k q).symm x‖ =
      ‖flattenCLEquivReal k q ((flattenCLEquivReal k q).symm x)‖ :=
        (flattenCLEquivReal_norm_eq k q
          ((flattenCLEquivReal k q).symm x)).symm
    _ ≤ ‖x‖ := by simp

theorem osiiProduction_unflattenSchwartzNPoint_seminorm_le
    (d k p l : Nat)
    (phi : SchwartzMap (Fin (k * (d + 1)) → Real) Complex) :
    SchwartzMap.seminorm Real p l
        (unflattenSchwartzNPoint (d := d) phi) ≤
      SchwartzMap.seminorm Real p l phi := by
  let e := flattenCLEquivReal k (d + 1)
  have hforward : ‖e.toContinuousLinearMap‖ ≤ 1 :=
    osiiProduction_flattenCLEquivReal_norm_le_one k (d + 1)
  have hinverse : ‖e.symm.toContinuousLinearMap‖ ≤ 1 :=
    osiiProduction_flattenCLEquivReal_symm_norm_le_one k (d + 1)
  calc
    SchwartzMap.seminorm Real p l
        (unflattenSchwartzNPoint (d := d) phi) ≤
      (‖e.symm.toContinuousLinearMap‖ ^ p *
        ‖e.toContinuousLinearMap‖ ^ l) *
          SchwartzMap.seminorm Real p l phi := by
      exact schwartzSeminorm_compContinuousLinearEquiv_le e phi p l
    _ ≤ (1 ^ p * 1 ^ l) *
        SchwartzMap.seminorm Real p l phi := by
      gcongr
    _ = SchwartzMap.seminorm Real p l phi := by simp

theorem osiiStep4CenteredPartialConvolutionKernelFullSource_Iic_gevrey_bound
    (d k : Nat) {rho : Real} (hrho : 0 < rho)
    (hrho_le : rho ≤ 16)
    (center y y' : Fin (k * (d + 1)) → Real) (p l : Nat) :
    (Finset.Iic (p, l)).sup
        (schwartzSeminormFamily Real (NPointDomain d k) Complex)
        (osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center y y') ≤
      (4 : Real) ^ p *
        ((4 : Real) ^ (d + 1) *
          ((∫ w : Fin (d + 1) → Complex,
            osiiStep4ComplexBlockRadialRaw (d + 1) 16 w)⁻¹ *
            Real.exp 6) ^ 2) ^ k *
        (98304 * (((d + 1) * 2 : Nat) : Real) ^ 2) ^ l *
          ((k + 1 : Nat) : Real) ^ l *
          (l.factorial : Real) ^ 2 *
        (16 / rho) ^ (3 * (d + 1) * k + l) *
          (1 + ‖center‖) ^ p := by
  let phi := osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
    (d + 1) k hrho center y y'
  have hflat :=
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_Iic_gevrey_bound
      d k hrho hrho_le center y y' p l
  apply Seminorm.finset_sup_apply_le
  · positivity
  intro j hj
  calc
    SchwartzMap.seminorm Real j.1 j.2
        (osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center y y') ≤
      SchwartzMap.seminorm Real j.1 j.2 phi :=
        osiiProduction_unflattenSchwartzNPoint_seminorm_le
          d k j.1 j.2 phi
    _ ≤ (Finset.Iic (p, l)).sup
          (schwartzSeminormFamily Real
            (Fin (k * (d + 1)) → Real) Complex) phi :=
      Seminorm.le_finset_sup_apply
        (p := schwartzSeminormFamily Real
          (Fin (k * (d + 1)) → Real) Complex) hj
    _ ≤ (4 : Real) ^ p *
        ((4 : Real) ^ (d + 1) *
          ((∫ w : Fin (d + 1) → Complex,
            osiiStep4ComplexBlockRadialRaw (d + 1) 16 w)⁻¹ *
            Real.exp 6) ^ 2) ^ k *
        (98304 * (((d + 1) * 2 : Nat) : Real) ^ 2) ^ l *
          ((k + 1 : Nat) : Real) ^ l *
          (l.factorial : Real) ^ 2 *
        (16 / rho) ^ (3 * (d + 1) * k + l) *
          (1 + ‖center‖) ^ p := hflat

end OSReconstruction
