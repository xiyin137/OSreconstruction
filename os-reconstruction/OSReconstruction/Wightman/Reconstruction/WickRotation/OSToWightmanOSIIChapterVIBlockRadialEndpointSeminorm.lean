/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPositiveSource














noncomputable section

open Complex Metric Set
open scoped Classical

namespace OSReconstruction

private theorem osiiStep4_endpoint_sixteen_pos : (0 : Real) < 16 := by
  norm_num

private def osiiStep4ComplexBlockRadialGJointRealSlice
    (q : Nat) (rho : Real)
    (p : (Fin q -> Real) × (Fin q -> Real)) : Complex :=
  osiiStep4ComplexBlockRadialG q rho
    (osiiStep4ComplexOfRealImag p.1 p.2)

private theorem osiiStep4ComplexBlockRadialGJointRealSlice_contDiff
    (q : Nat) {rho : Real} (hrho : 0 < rho) :
    ContDiff Real (⊤ : ℕ∞)
      (osiiStep4ComplexBlockRadialGJointRealSlice q rho) := by
  have harg : ContDiff Real (⊤ : ℕ∞)
      (fun p : (Fin q -> Real) × (Fin q -> Real) =>
        osiiStep4ComplexOfRealImag p.1 p.2) := by
    rw [contDiff_pi]
    intro a
    have hreReal : ContDiff Real (⊤ : ℕ∞)
        (fun p : (Fin q -> Real) × (Fin q -> Real) => p.1 a) := by
      fun_prop
    have hre : ContDiff Real (⊤ : ℕ∞)
        (fun p : (Fin q -> Real) × (Fin q -> Real) =>
          (p.1 a : Complex)) := by
      exact Complex.ofRealCLM.contDiff.comp hreReal
    have himReal : ContDiff Real (⊤ : ℕ∞)
        (fun p : (Fin q -> Real) × (Fin q -> Real) => p.2 a) := by
      fun_prop
    have him : ContDiff Real (⊤ : ℕ∞)
        (fun p : (Fin q -> Real) × (Fin q -> Real) =>
          (p.2 a : Complex) * I) := by
      exact (Complex.ofRealCLM.contDiff.comp himReal).mul contDiff_const
    simpa only [osiiStep4ComplexOfRealImag] using hre.add him
  exact Complex.ofRealCLM.contDiff.comp
    ((osiiStep4ComplexBlockRadialG_contDiff q hrho).comp harg)

private theorem
    osiiStep4ComplexBlockRadialGJointRealSlice_support_subset_closedBall
    (q : Nat) {rho : Real} (hrho : 0 < rho) :
    Function.support
        (osiiStep4ComplexBlockRadialGJointRealSlice q rho) <=
      Metric.closedBall
        (0 : (Fin q -> Real) × (Fin q -> Real)) (rho / 8) := by
  intro p hp
  let z : Fin q -> Complex := osiiStep4ComplexOfRealImag p.1 p.2
  have hz : z ∈ Function.support (osiiStep4ComplexBlockRadialG q rho) := by
    simpa [osiiStep4ComplexBlockRadialGJointRealSlice, z,
      Function.mem_support] using hp
  have hzball := osiiStep4ComplexBlockRadialG_support_subset q hrho hz
  have hfull :
      norm (osiiStep4ComplexBlockToEuclideanCLE q z) < rho / 8 := by
    simpa [osiiStep4ComplexBlockBall] using hzball
  have hreal : norm p.1 <= rho / 8 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro a
    calc
      norm (p.1 a) = abs (z a).re := by
        simp [z, osiiStep4ComplexOfRealImag, Real.norm_eq_abs]
      _ <= norm (z a) := Complex.abs_re_le_norm _
      _ <= norm (osiiStep4ComplexBlockToEuclideanCLE q z) := by
        simpa using
          PiLp.norm_apply_le (osiiStep4ComplexBlockToEuclideanCLE q z) a
      _ <= rho / 8 := hfull.le
  have himag : norm p.2 <= rho / 8 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro a
    calc
      norm (p.2 a) = abs (z a).im := by
        simp [z, osiiStep4ComplexOfRealImag, Real.norm_eq_abs]
      _ <= norm (z a) := Complex.abs_im_le_norm _
      _ <= norm (osiiStep4ComplexBlockToEuclideanCLE q z) := by
        simpa using
          PiLp.norm_apply_le (osiiStep4ComplexBlockToEuclideanCLE q z) a
      _ <= rho / 8 := hfull.le
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le hreal himag

private theorem
    osiiStep4ComplexBlockRadialGJointRealSlice_hasCompactSupport
    (q : Nat) {rho : Real} (hrho : 0 < rho) :
    HasCompactSupport
      (osiiStep4ComplexBlockRadialGJointRealSlice q rho) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall
      (0 : (Fin q -> Real) × (Fin q -> Real)) (rho / 8))
  exact
    osiiStep4ComplexBlockRadialGJointRealSlice_support_subset_closedBall
      q hrho

/-- The normalized block bump, jointly in its real and imaginary blocks, as a
Schwartz test. -/
noncomputable def osiiStep4ComplexBlockRadialGJointRealSchwartz
    (q : Nat) {rho : Real} (hrho : 0 < rho) :
    SchwartzMap ((Fin q -> Real) × (Fin q -> Real)) Complex :=
  (osiiStep4ComplexBlockRadialGJointRealSlice_hasCompactSupport
      q hrho).toSchwartzMap
    (osiiStep4ComplexBlockRadialGJointRealSlice_contDiff q hrho)

@[simp] theorem osiiStep4ComplexBlockRadialGJointRealSchwartz_apply
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (x imag : Fin q -> Real) :
    osiiStep4ComplexBlockRadialGJointRealSchwartz q hrho (x, imag) =
      osiiStep4ComplexBlockRadialG q rho
        (osiiStep4ComplexOfRealImag x imag) := by
  rfl

/-- A fixed-imaginary endpoint bump is the corresponding partial evaluation
of the joint real/imaginary Schwartz test. -/
theorem osiiStep4ComplexBlockRadialGRealSchwartz_eq_partialEval
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag : Fin q -> Real) :
    osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag =
      SchwartzMap.partialEval₂
        (osiiStep4ComplexBlockRadialGJointRealSchwartz q hrho) imag := by
  ext x
  rw [osiiStep4ComplexBlockRadialGRealSchwartz_apply]
  exact
    (osiiStep4ComplexBlockRadialGJointRealSchwartz_apply
      q hrho x imag).symm

/-- The fixed-imaginary endpoint bump varies continuously in the imaginary
block for the Schwartz topology. -/
theorem continuous_osiiStep4ComplexBlockRadialGRealSchwartz
    (q : Nat) {rho : Real} (hrho : 0 < rho) :
    Continuous (fun imag : Fin q -> Real =>
      osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) := by
  let K := osiiStep4ComplexBlockRadialGJointRealSchwartz q hrho
  have hpartial : Continuous (fun imag : Fin q -> Real =>
      SchwartzMap.partialEval₂ K imag) :=
    continuous_partialEval₂ K
  rw [show (fun imag : Fin q -> Real =>
      osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) =
      fun imag => SchwartzMap.partialEval₂ K imag by
    funext imag
    exact osiiStep4ComplexBlockRadialGRealSchwartz_eq_partialEval
      q hrho imag]
  exact hpartial

set_option maxHeartbeats 800000 in
/-- At the reference radius, every finite family of endpoint-bump Schwartz
seminorms is uniformly bounded over the closed imaginary support ball. -/
theorem exists_osiiStep4ComplexBlockRadialGRealSchwartz_reference_finsetSeminorm_bound
    (q : Nat) (s : Finset (Nat × Nat)) :
    ∃ C : Real, 0 <= C ∧
      ∀ imag ∈ Metric.closedBall (0 : Fin q -> Real) (16 / 8 : Real),
        s.sup (schwartzSeminormFamily Real (Fin q -> Real) Complex)
            (osiiStep4ComplexBlockRadialGRealSchwartz
              q osiiStep4_endpoint_sixteen_pos imag) <= C := by
  have hF : Continuous (fun imag : Fin q -> Real =>
      s.sup (schwartzSeminormFamily Real (Fin q -> Real) Complex)
        (osiiStep4ComplexBlockRadialGRealSchwartz
          q osiiStep4_endpoint_sixteen_pos imag)) := by
    exact (((schwartz_withSeminorms Real (Fin q -> Real) Complex).finset_sups
      ).continuous_seminorm s).comp
        (continuous_osiiStep4ComplexBlockRadialGRealSchwartz
          q osiiStep4_endpoint_sixteen_pos)
  have hK : IsCompact
      (Metric.closedBall (0 : Fin q -> Real) (16 / 8 : Real)) :=
    isCompact_closedBall _ _
  rcases hK.bddAbove_image hF.continuousOn with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro imag himag
  have hFC :
      s.sup (schwartzSeminormFamily Real (Fin q -> Real) Complex)
          (osiiStep4ComplexBlockRadialGRealSchwartz
            q osiiStep4_endpoint_sixteen_pos imag) <= C :=
    hC ⟨imag, himag, rfl⟩
  exact hFC.trans (le_max_left C 0)

set_option backward.isDefEq.respectTransparency false in
/-- Exact inverse-radius estimate for one endpoint-bump Schwartz seminorm.
The normalized block density contributes `2 * q`, and each derivative
contributes one additional inverse-radius power. -/
theorem osiiStep4ComplexBlockRadialGRealSchwartz_seminorm_scale
    (q : Nat) {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (p l : Nat) (imag : Fin q -> Real) :
    SchwartzMap.seminorm Real p l
        (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) <=
      (16 / rho) ^ (2 * q + l) *
        SchwartzMap.seminorm Real p l
          (osiiStep4ComplexBlockRadialGRealSchwartz
            q osiiStep4_endpoint_sixteen_pos ((16 / rho) • imag)) := by
  let a : Real := 16 / rho
  let G0 : SchwartzMap (Fin q -> Real) Complex :=
    osiiStep4ComplexBlockRadialGRealSchwartz
      q osiiStep4_endpoint_sixteen_pos (a • imag)
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_one : 1 <= a := by
    dsimp [a]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  have hfun :
      (⇑(osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) :
          (Fin q -> Real) -> Complex) =
        fun x => (a ^ (2 * q) : Real) • G0 (a • x) := by
    funext x
    rw [osiiStep4ComplexBlockRadialGRealSchwartz_apply,
      osiiStep4ComplexBlockRadialGRealSchwartz_apply,
      osiiStep4ComplexBlockRadialG_scale q hrho]
    have hcplx := osiiStep4ComplexOfRealImag_smul a x imag
    dsimp only [a] at hcplx ⊢
    rw [← hcplx]
    push_cast
    simp [Complex.real_smul]
  refine SchwartzMap.seminorm_le_bound Real p l
    (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag)
    (mul_nonneg (pow_nonneg ha_pos.le _)
      (apply_nonneg (SchwartzMap.seminorm Real p l) G0)) ?_
  intro x
  have hcomp_smooth :
      ContDiff Real l (fun u : Fin q -> Real => G0 (a • u)) :=
    (G0.smooth l).comp (contDiff_const_smul a)
  have hderiv :
      iteratedFDeriv Real l
          (⇑(osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag)) x =
        (a ^ (2 * q) : Real) •
          (a ^ l : Real) •
            iteratedFDeriv Real l (⇑G0) (a • x) := by
    rw [hfun]
    calc
      iteratedFDeriv Real l
          (fun u : Fin q -> Real =>
            (a ^ (2 * q) : Real) • G0 (a • u)) x =
        (a ^ (2 * q) : Real) •
          iteratedFDeriv Real l
            (fun u : Fin q -> Real => G0 (a • u)) x := by
              exact iteratedFDeriv_const_smul_apply'
                hcomp_smooth.contDiffAt
      _ = (a ^ (2 * q) : Real) •
          (a ^ l : Real) •
            iteratedFDeriv Real l (⇑G0) (a • x) := by
        rw [show
          iteratedFDeriv Real l
              (fun u : Fin q -> Real => G0 (a • u)) x =
            (a ^ l : Real) • iteratedFDeriv Real l (⇑G0) (a • x) by
              simpa using congrFun
                (iteratedFDeriv_comp_const_smul a (G0.smooth l)) x]
  have hxnorm : norm x <= norm (a • x) := by
    calc
      norm x = 1 * norm x := by simp
      _ <= a * norm x :=
        mul_le_mul_of_nonneg_right ha_one (norm_nonneg x)
      _ = norm (a • x) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha_pos]
  letI : Norm
      (ContinuousMultilinearMap Real (fun _ : Fin l => Fin q -> Real) Complex) :=
    ContinuousMultilinearMap.hasOpNorm
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap Real (fun _ : Fin l => Fin q -> Real) Complex) :=
    ContinuousMultilinearMap.normedAddCommGroup
  letI : NormedSpace Real
      (ContinuousMultilinearMap Real (fun _ : Fin l => Fin q -> Real) Complex) :=
    ContinuousMultilinearMap.normedSpace
  letI : NormSMulClass Real
      (ContinuousMultilinearMap Real (fun _ : Fin l => Fin q -> Real) Complex) :=
    NormedSpace.toNormSMulClass
  rw [hderiv]
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg ha_pos.le (2 * q)),
    abs_of_nonneg (pow_nonneg ha_pos.le l)]
  calc
    norm x ^ p *
        (a ^ (2 * q) *
          (a ^ l * norm (iteratedFDeriv Real l (⇑G0) (a • x)))) =
      a ^ (2 * q + l) *
        (norm x ^ p * norm (iteratedFDeriv Real l (⇑G0) (a • x))) := by
          rw [pow_add]
          ring
    _ <= a ^ (2 * q + l) *
        (norm (a • x) ^ p *
          norm (iteratedFDeriv Real l (⇑G0) (a • x))) := by
      gcongr
    _ <= a ^ (2 * q + l) *
        SchwartzMap.seminorm Real p l G0 := by
      exact mul_le_mul_of_nonneg_left
        (SchwartzMap.le_seminorm Real p l G0 (a • x))
        (pow_nonneg ha_pos.le _)
    _ = (16 / rho) ^ (2 * q + l) *
        SchwartzMap.seminorm Real p l
          (osiiStep4ComplexBlockRadialGRealSchwartz
            q osiiStep4_endpoint_sixteen_pos ((16 / rho) • imag)) := by
      rfl

private theorem
    endpointImaginaryClosedBall_scale_to_reference
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    {imag : Fin q -> Real}
    (himag : imag ∈ Metric.closedBall 0 (rho / 8)) :
    (16 / rho) • imag ∈
      Metric.closedBall 0 (16 / 8 : Real) := by
  rw [Metric.mem_closedBall, dist_zero_right] at himag ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    (16 / rho) * norm imag <= (16 / rho) * (rho / 8) := by
      gcongr
    _ = 16 / 8 := by field_simp

set_option maxHeartbeats 800000 in
/-- Uniform inverse-radius estimate for any finite family of endpoint-bump
Schwartz seminorms. -/
theorem exists_osiiStep4ComplexBlockRadialGRealSchwartz_finsetSeminorm_scale_bound
    (q : Nat) (s : Finset (Nat × Nat)) :
    ∃ C : Real, ∃ M : Nat, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ imag ∈ Metric.closedBall (0 : Fin q -> Real) (rho / 8),
          s.sup (schwartzSeminormFamily Real (Fin q -> Real) Complex)
              (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) <=
            C * (16 / rho) ^ M := by
  let derivativeOrder : Nat := s.sup fun j => j.2
  let M : Nat := 2 * q + derivativeOrder
  obtain ⟨C, hC, href⟩ :=
    exists_osiiStep4ComplexBlockRadialGRealSchwartz_reference_finsetSeminorm_bound
      q s
  refine ⟨C, M, hC, ?_⟩
  intro rho hrho hrho_le imag himag
  let a : Real := 16 / rho
  have ha_one : 1 <= a := by
    dsimp [a]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  have himagRef : a • imag ∈
      Metric.closedBall (0 : Fin q -> Real) (16 / 8 : Real) := by
    simpa [a] using
      endpointImaginaryClosedBall_scale_to_reference q hrho himag
  have hrefImag := href (a • imag) himagRef
  apply Seminorm.finset_sup_apply_le
  · exact mul_nonneg hC (pow_nonneg (by positivity) _)
  intro j hj
  change SchwartzMap.seminorm Real j.1 j.2
      (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) <=
        C * a ^ M
  have hscale :=
    osiiStep4ComplexBlockRadialGRealSchwartz_seminorm_scale
      q hrho hrho_le j.1 j.2 imag
  have hjderiv : j.2 <= derivativeOrder :=
    Finset.le_sup (f := fun z => z.2) hj
  have hexp : 2 * q + j.2 <= M :=
    Nat.add_le_add_left hjderiv (2 * q)
  have hpow : a ^ (2 * q + j.2) <= a ^ M :=
    pow_le_pow_right₀ ha_one hexp
  have hrefj :
      SchwartzMap.seminorm Real j.1 j.2
          (osiiStep4ComplexBlockRadialGRealSchwartz
            q osiiStep4_endpoint_sixteen_pos (a • imag)) <= C := by
    exact (Finset.le_sup
      (f := schwartzSeminormFamily Real (Fin q -> Real) Complex) hj
      (osiiStep4ComplexBlockRadialGRealSchwartz
        q osiiStep4_endpoint_sixteen_pos (a • imag))).trans hrefImag
  calc
    SchwartzMap.seminorm Real j.1 j.2
        (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) <=
      a ^ (2 * q + j.2) *
        SchwartzMap.seminorm Real j.1 j.2
          (osiiStep4ComplexBlockRadialGRealSchwartz
            q osiiStep4_endpoint_sixteen_pos (a • imag)) := by
              simpa [a] using hscale
    _ <= a ^ M * C :=
      mul_le_mul hpow hrefj
        (apply_nonneg _ _) (pow_nonneg (by positivity) _)
    _ = C * a ^ M := by ring

/-- Translating the endpoint bump costs a polynomial power in its real
center, with no change to the inverse-radius exponent. -/
theorem osiiStep4CenteredComplexBlockRadialGRealSchwartz_seminorm_le
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (p l : Nat) (center imag : Fin q -> Real) :
    SchwartzMap.seminorm Real p l
        (osiiStep4CenteredComplexBlockRadialGRealSchwartz
          q hrho center imag) <=
      2 ^ (p - 1) *
        (SchwartzMap.seminorm Real p l
            (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) +
          SchwartzMap.seminorm Real 0 l
            (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag)) *
        (1 + norm center) ^ p := by
  let G : SchwartzMap (Fin q -> Real) Complex :=
    osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag
  rw [show
      osiiStep4CenteredComplexBlockRadialGRealSchwartz
          q hrho center imag = SCV.translateSchwartz (-center) G by
      rfl]
  refine SchwartzMap.seminorm_le_bound Real p l
    (SCV.translateSchwartz (-center) G) (by positivity) ?_
  intro x
  have hcoe :
      (⇑(SCV.translateSchwartz (-center) G) : (Fin q -> Real) -> Complex) =
        fun z => G (z + (-center)) := by
    rfl
  rw [hcoe, iteratedFDeriv_comp_add_right]
  have hnorm_x : norm x <= norm (x + (-center)) + norm center := by
    calc
      norm x = norm ((x + (-center)) - (-center)) := by simp
      _ <= norm (x + (-center)) + norm (-center) := norm_sub_le _ _
      _ = norm (x + (-center)) + norm center := by rw [norm_neg]
  have hp :
      norm (x + (-center)) ^ p *
          norm (iteratedFDeriv Real l (⇑G) (x + (-center))) <=
        SchwartzMap.seminorm Real p l G :=
    SchwartzMap.le_seminorm Real p l G (x + (-center))
  have h0 :
      norm (iteratedFDeriv Real l (⇑G) (x + (-center))) <=
        SchwartzMap.seminorm Real 0 l G := by
    simpa using SchwartzMap.le_seminorm Real 0 l G (x + (-center))
  have hbase : 1 <= 1 + norm center := by
    linarith [norm_nonneg center]
  have hconstants :
      SchwartzMap.seminorm Real p l G +
          norm center ^ p * SchwartzMap.seminorm Real 0 l G <=
        (1 + norm center) ^ p *
          (SchwartzMap.seminorm Real p l G +
            SchwartzMap.seminorm Real 0 l G) := by
    rw [mul_add]
    apply add_le_add
    · exact le_mul_of_one_le_left
        (apply_nonneg (SchwartzMap.seminorm Real p l) G)
        (one_le_pow₀ hbase)
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg center)
          (le_add_of_nonneg_left zero_le_one) p)
        (apply_nonneg (SchwartzMap.seminorm Real 0 l) G)
  calc
    norm x ^ p *
        norm (iteratedFDeriv Real l (⇑G) (x + (-center))) <=
      (norm (x + (-center)) + norm center) ^ p *
        norm (iteratedFDeriv Real l (⇑G) (x + (-center))) := by
      gcongr
    _ <=
      (2 ^ (p - 1) *
          (norm (x + (-center)) ^ p + norm center ^ p)) *
        norm (iteratedFDeriv Real l (⇑G) (x + (-center))) := by
      gcongr
      exact add_pow_le (norm_nonneg _) (norm_nonneg _) p
    _ =
      2 ^ (p - 1) *
        (norm (x + (-center)) ^ p *
            norm (iteratedFDeriv Real l (⇑G) (x + (-center))) +
          norm center ^ p *
            norm (iteratedFDeriv Real l (⇑G) (x + (-center)))) := by
      ring
    _ <=
      2 ^ (p - 1) *
        (SchwartzMap.seminorm Real p l G +
          norm center ^ p * SchwartzMap.seminorm Real 0 l G) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hp
          (mul_le_mul_of_nonneg_left h0
            (pow_nonneg (norm_nonneg center) p)))
        (by positivity)
    _ <=
      2 ^ (p - 1) *
        ((1 + norm center) ^ p *
          (SchwartzMap.seminorm Real p l G +
            SchwartzMap.seminorm Real 0 l G)) := by
      exact mul_le_mul_of_nonneg_left hconstants (by positivity)
    _ =
      2 ^ (p - 1) *
        (SchwartzMap.seminorm Real p l
            (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) +
          SchwartzMap.seminorm Real 0 l
            (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag)) *
        (1 + norm center) ^ p := by
      dsimp only [G]
      ring

set_option maxHeartbeats 800000 in
/-- A finite family of centered endpoint-bump seminorms has one simultaneous
inverse-radius exponent and one endpoint-center growth degree. -/
theorem
    exists_osiiStep4CenteredComplexBlockRadialGRealSchwartz_finsetSeminorm_scale_bound
    (q : Nat) (s : Finset (Nat × Nat)) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ center : Fin q -> Real,
          ∀ imag ∈ Metric.closedBall (0 : Fin q -> Real) (rho / 8),
            s.sup (schwartzSeminormFamily Real (Fin q -> Real) Complex)
                (osiiStep4CenteredComplexBlockRadialGRealSchwartz
                  q hrho center imag) <=
              C * (16 / rho) ^ M * (1 + norm center) ^ N := by
  let s' : Finset (Nat × Nat) :=
    s ∪ s.image (fun j => (0, j.2))
  let N : Nat := s.sup fun j => j.1
  obtain ⟨C0, M, hC0, hscale⟩ :=
    exists_osiiStep4ComplexBlockRadialGRealSchwartz_finsetSeminorm_scale_bound
      q s'
  let C : Real := 2 ^ N * (C0 + C0)
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  refine ⟨C, M, N, hC, ?_⟩
  intro rho hrho hrho_le center imag himag
  let a : Real := 16 / rho
  let b : Real := 1 + norm center
  have hb_one : 1 <= b := by
    dsimp [b]
    linarith [norm_nonneg center]
  have hbase := hscale hrho hrho_le imag himag
  apply Seminorm.finset_sup_apply_le
  · exact mul_nonneg
      (mul_nonneg hC (pow_nonneg (by positivity) M))
      (pow_nonneg (by positivity) N)
  intro j hj
  change SchwartzMap.seminorm Real j.1 j.2
      (osiiStep4CenteredComplexBlockRadialGRealSchwartz
        q hrho center imag) <= C * a ^ M * b ^ N
  have hj_mem : j ∈ s' := Finset.mem_union_left _ hj
  have hj0_mem : (0, j.2) ∈ s' := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hjbase :
      SchwartzMap.seminorm Real j.1 j.2
          (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) <=
        C0 * a ^ M := by
    exact (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily Real (Fin q -> Real) Complex) hj_mem).trans
      (by simpa [a] using hbase)
  have hj0base :
      SchwartzMap.seminorm Real 0 j.2
          (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) <=
        C0 * a ^ M := by
    exact (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily Real (Fin q -> Real) Complex) hj0_mem).trans
      (by simpa [a] using hbase)
  have hjN : j.1 <= N :=
    Finset.le_sup (f := fun z => z.1) hj
  have hjpredN : j.1 - 1 <= N := (Nat.sub_le j.1 1).trans hjN
  have hpow_two : (2 : Real) ^ (j.1 - 1) <= 2 ^ N :=
    pow_le_pow_right₀ (by norm_num) hjpredN
  have hpow_center : b ^ j.1 <= b ^ N :=
    pow_le_pow_right₀ hb_one hjN
  calc
    SchwartzMap.seminorm Real j.1 j.2
        (osiiStep4CenteredComplexBlockRadialGRealSchwartz
          q hrho center imag) <=
      2 ^ (j.1 - 1) *
        (SchwartzMap.seminorm Real j.1 j.2
            (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag) +
          SchwartzMap.seminorm Real 0 j.2
            (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag)) *
        b ^ j.1 := by
      simpa [b] using
        osiiStep4CenteredComplexBlockRadialGRealSchwartz_seminorm_le
          q hrho j.1 j.2 center imag
    _ <= 2 ^ N * ((C0 * a ^ M) + (C0 * a ^ M)) * b ^ N := by
      gcongr
    _ = C * a ^ M * b ^ N := by
      dsimp [C]
      ring

end OSReconstruction
