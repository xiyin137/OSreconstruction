import OSReconstruction.SCV.PaleyWienerSchwartz

/-!
# Spectral damping on closed cone faces

The fixed spectral cutoff makes exponential damping legitimate on Schwartz
tests even when the height lies on a cone face. The full supported
distribution, not a pointwise boundary function, determines the resulting
pairing. Interior Fourier-Laplace slices converge to that same pairing.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {m : Nat}

private def coneCutoff (C : Set (Fin m -> Real)) : FixedConeCutoff (DualConeFlat C) :=
  (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some

private theorem coneCutoff_temperate (C : Set (Fin m -> Real)) :
    (fun p => ((coneCutoff C).val p : Complex)).HasTemperateGrowth := by
  have h : (coneCutoff C).val.HasTemperateGrowth := by
    refine ⟨(coneCutoff C).smooth, fun n => ?_⟩
    obtain ⟨A, hA⟩ := (coneCutoff C).deriv_bound n
    exact ⟨0, A, by simpa using hA⟩
  exact Function.Complex.hasTemperateGrowth_ofReal.comp h

private def coneCutoffTest (C : Set (Fin m -> Real))
    (f : SchwartzMap (Fin m -> Real) Complex) : SchwartzMap (Fin m -> Real) Complex :=
  SchwartzMap.smulLeftCLM Complex (fun p => ((coneCutoff C).val p : Complex)) f

private theorem coneCutoffTest_apply (C : Set (Fin m -> Real))
    (f : SchwartzMap (Fin m -> Real) Complex) (p : Fin m -> Real) :
    coneCutoffTest C f p = ((coneCutoff C).val p : Complex) * f p := by
  exact SchwartzMap.smulLeftCLM_apply_apply (coneCutoff_temperate C) f p

private theorem coneCutoff_eq_one {C : Set (Fin m -> Real)}
    {p : Fin m -> Real} (hp : p ∈ DualConeFlat C) : (coneCutoff C).val p = 1 := by
  obtain ⟨r, hr, hone⟩ := (coneCutoff C).one_on_neighborhood
  exact hone p (by simpa [Metric.infDist_zero_of_mem hp] using hr)

private def conePairingCLM (y : Fin m -> Real) : (Fin m -> Real) →L[Real] Real :=
  ∑ i, y i • (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin m => Real) i)

private theorem conePairingCLM_apply (y p : Fin m -> Real) :
    conePairingCLM y p = ∑ i, y i * p i := by simp [conePairingCLM]

theorem osiiConePairing_nonneg_of_mem_closure
    {C : Set (Fin m -> Real)} {y p : Fin m -> Real}
    (hy : y ∈ closure C) (hp : p ∈ DualConeFlat C) : 0 ≤ ∑ i, y i * p i := by
  exact closure_minimal (fun z hz => (mem_dualConeFlat.mp hp) z hz)
    (isClosed_le continuous_const
      (show Continuous (fun z : Fin m -> Real => ∑ i, z i * p i) by fun_prop)) hy

private theorem coneCutoff_pairing_lower_bound
    {C : Set (Fin m -> Real)} {y : Fin m -> Real} (hy : y ∈ closure C)
    {p : Fin m -> Real} (hp : (coneCutoff C).val p ≠ 0) :
    -(2 * ‖conePairingCLM y‖) ≤ conePairingCLM y p := by
  have hdist : Metric.infDist p (DualConeFlat C) ≤ 1 := by
    by_contra h
    exact hp ((coneCutoff C).support_bound p (lt_of_not_ge h))
  obtain ⟨q, hq, hpq⟩ := (Metric.infDist_lt_iff
    (show (DualConeFlat C).Nonempty from ⟨0, zero_mem_dualConeFlat C⟩)).mp
      (show Metric.infDist p (DualConeFlat C) < 2 by linarith)
  have hqpos : 0 ≤ conePairingCLM y q := by
    rw [conePairingCLM_apply]
    exact osiiConePairing_nonneg_of_mem_closure hy hq
  have hnorm := (conePairingCLM y).le_opNorm (p - q)
  have hbound : ‖conePairingCLM y‖ * ‖p - q‖ ≤ 2 * ‖conePairingCLM y‖ := by
    rw [dist_eq_norm] at hpq
    nlinarith [norm_nonneg (conePairingCLM y)]
  rw [Real.norm_eq_abs, map_sub] at hnorm
  linarith [neg_abs_le (conePairingCLM y p - conePairingCLM y q)]

private theorem coneCutoffTest_support_bound
    {C : Set (Fin m -> Real)} {y : Fin m -> Real} (hy : y ∈ closure C)
    (f : SchwartzMap (Fin m -> Real) Complex) :
    ∃ M : Real, ∀ p ∈ Function.support (coneCutoffTest C f), -M ≤ conePairingCLM y p := by
  refine ⟨2 * ‖conePairingCLM y‖, fun p hp => coneCutoff_pairing_lower_bound hy ?_⟩
  intro hzero
  exact hp (by simp [coneCutoffTest_apply, hzero])

def osiiClosedConeDampedTest (C : Set (Fin m -> Real))
    (y : Fin m -> Real) (hy : y ∈ closure C)
    (f : SchwartzMap (Fin m -> Real) Complex) : Real -> SchwartzMap (Fin m -> Real) Complex :=
  (schwartz_exp_damping_tendsto (coneCutoffTest C f) (conePairingCLM y)
    (coneCutoffTest_support_bound hy f)).choose

theorem osiiClosedConeDampedTest_apply
    (C : Set (Fin m -> Real)) (y : Fin m -> Real) (hy : y ∈ closure C)
    (f : SchwartzMap (Fin m -> Real) Complex) {u : Real} (hu : 0 < u) (p : Fin m -> Real) :
    osiiClosedConeDampedTest C y hy f u p =
      Complex.exp (-(u : Complex) * (∑ i, y i * p i : Real)) *
        ((coneCutoff C).val p : Complex) * f p := by
  have h := (schwartz_exp_damping_tendsto (coneCutoffTest C f) (conePairingCLM y)
    (coneCutoffTest_support_bound hy f)).choose_spec.1 u hu p
  simpa [osiiClosedConeDampedTest, conePairingCLM_apply, coneCutoffTest_apply, mul_assoc] using h

theorem osiiClosedConeDampedTest_apply_of_mem_dualCone
    (C : Set (Fin m -> Real)) (y : Fin m -> Real) (hy : y ∈ closure C)
    (f : SchwartzMap (Fin m -> Real) Complex) {u : Real} (hu : 0 < u)
    {p : Fin m -> Real} (hp : p ∈ DualConeFlat C) :
    osiiClosedConeDampedTest C y hy f u p =
      Complex.exp (-(u : Complex) * (∑ i, y i * p i : Real)) * f p := by
  rw [osiiClosedConeDampedTest_apply C y hy f hu, coneCutoff_eq_one hp]
  simp

theorem osiiClosedConeDampedTest_pairing_tendsto
    (C : Set (Fin m -> Real)) (y : Fin m -> Real) (hy : y ∈ closure C)
    (T : SchwartzMap (Fin m -> Real) Complex →L[Complex] Complex)
    (hT : HasFourierSupportInDualCone C T) (f : SchwartzMap (Fin m -> Real) Complex) :
    Tendsto (fun u => T (osiiClosedConeDampedTest C y hy f u))
      (𝓝[>] (0 : Real)) (𝓝 (T f)) := by
  have hlim := (schwartz_exp_damping_tendsto (coneCutoffTest C f) (conePairingCLM y)
    (coneCutoffTest_support_bound hy f)).choose_spec.2
  have heq : T (coneCutoffTest C f) = T f := by
    apply hasFourierSupportIn_eqOn hT
    intro p hp
    simp [coneCutoffTest_apply, coneCutoff_eq_one hp]
  rw [← heq]
  exact T.continuous.tendsto (coneCutoffTest C f) |>.comp hlim

theorem osiiFourierLaplace_slice_pairing
    (C : Set (Fin m -> Real)) (hopen : IsOpen C) (hconv : Convex Real C)
    (hcone : IsCone C) (hsalient : IsSalientCone C)
    (T : SchwartzMap (Fin m -> Real) Complex →L[Complex] Complex)
    (hT : HasFourierSupportInDualCone C T) {y : Fin m -> Real} (hy : y ∈ C)
    (f g : SchwartzMap (Fin m -> Real) Complex)
    (hg : ∀ p ∈ DualConeFlat C,
      g p = Complex.exp (-(∑ i, y i * p i : Real) : Complex) * physicsFourierFlatCLM f p) :
    (∫ x : Fin m -> Real, fourierLaplaceExtMultiDim C hopen hconv hcone hsalient T
      (fun i => (x i : Complex) + (y i : Complex) * I) * f x) = T g := by
  let z : (Fin m -> Real) -> Fin m -> Complex := fun x i => (x i : Complex) + (y i : Complex) * I
  have hz (x : Fin m -> Real) : z x ∈ SCV.TubeDomain C := by
    simpa [z, SCV.TubeDomain] using hy
  let psi := fun x => multiDimPsiZExt C hopen hconv hcone hsalient (z x)
  obtain ⟨Phi, hPhi, hTPhi⟩ := schwartz_clm_fubini_exchange T psi f
    (continuous_multiDimPsiZExt_comp_of_mem_tube C hopen hconv hcone hsalient z (by fun_prop) hz)
    (fun a b => multiDimPsiZExt_fixedImaginary_seminorm_bound C hopen hconv hcone hsalient hy a b)
  have hPhiOn (p : Fin m -> Real) (hp : p ∈ DualConeFlat C) : Phi p = g p := by
    rw [hPhi, hg p hp]
    calc
      (∫ x, psi x p * f x) =
          ∫ x, Complex.exp (-(∑ i, y i * p i : Real) : Complex) *
            (Complex.exp (I * ∑ i, (x i : Complex) * (p i : Complex)) * f x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [multiDimPsiZExt_apply_of_mem_dualCone C hopen hconv hcone hsalient (z x) (hz x) hp]
        have hexp : I * ∑ i, z x i * (p i : Complex) =
            (-(∑ i, y i * p i : Real) : Complex) + I * ∑ i, (x i : Complex) * (p i : Complex) := by
          simp only [z, add_mul, Finset.sum_add_distrib, Complex.ofReal_sum, Complex.ofReal_mul]
          rw [mul_add]
          have hsum : ∑ i, (y i : Complex) * I * (p i : Complex) =
              I * ∑ i, (y i : Complex) * (p i : Complex) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
          rw [hsum]
          simp [← mul_assoc]
          ring
        rw [hexp, Complex.exp_add]
        ring
      _ = Complex.exp (-(∑ i, y i * p i : Real) : Complex) * physicsFourierFlatCLM f p := by
        exact (MeasureTheory.integral_const_mul
          (Complex.exp (-(∑ i, y i * p i : Real) : Complex))
          (fun x : Fin m -> Real => Complex.exp (I * ∑ i, (x i : Complex) * (p i : Complex)) * f x)
          ).trans (congrArg (fun a : Complex => Complex.exp (-(∑ i, y i * p i : Real) : Complex) * a)
            (physicsFourierFlatCLM_integral f p))
  calc
    _ = ∫ x, T (psi x) * f x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [fourierLaplaceExtMultiDim_eq_ext]
    _ = T Phi := hTPhi.symm
    _ = T g := hasFourierSupportIn_eqOn hT hPhiOn

theorem osiiCone_add_mem_of_closure
    {C : Set (Fin m -> Real)} (hopen : IsOpen C) (hconv : Convex Real C) (hcone : IsCone C)
    {y eta : Fin m -> Real} (hy : y ∈ closure C) (heta : eta ∈ C) : y + eta ∈ C := by
  have hhalf : (1 / 2 : Real) • y + (1 / 2 : Real) • eta ∈ interior C :=
    hconv.combo_closure_interior_mem_interior hy (by rwa [hopen.interior_eq])
      (by norm_num) (by norm_num) (by norm_num)
  have h := hcone _ (interior_subset hhalf) 2 (by norm_num)
  simpa only [smul_add, smul_smul, show (2 : Real) * (1 / 2) = 1 by norm_num, one_smul] using h

theorem osiiCone_smul_mem_closure
    {C : Set (Fin m -> Real)} (hcone : IsCone C)
    {y : Fin m -> Real} (hy : y ∈ closure C) {u : Real} (hu : 0 < u) : u • y ∈ closure C := by
  have hclosed : IsClosed {z : Fin m -> Real | u • z ∈ closure C} :=
    isClosed_closure.preimage
      (show Continuous (fun z : Fin m -> Real => u • z) by fun_prop)
  have hsub : C ⊆ {z : Fin m -> Real | u • z ∈ closure C} :=
    fun z hz => subset_closure (hcone z hz u hu)
  exact closure_minimal hsub hclosed hy

theorem osiiClosedConeDampedTest_smul
    (C : Set (Fin m -> Real)) (hcone : IsCone C)
    (y : Fin m -> Real) (hy : y ∈ closure C)
    (f : SchwartzMap (Fin m -> Real) Complex) {u : Real} (hu : 0 < u) :
    osiiClosedConeDampedTest C (u • y) (osiiCone_smul_mem_closure hcone hy hu) f 1 =
      osiiClosedConeDampedTest C y hy f u := by
  ext p
  simp only [osiiClosedConeDampedTest_apply C (u • y) _ f zero_lt_one,
    osiiClosedConeDampedTest_apply C y hy f hu, Pi.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum, Complex.ofReal_one, neg_mul, one_mul, Complex.ofReal_mul]

theorem osiiFourierLaplace_closedFace_boundary
    (C : Set (Fin m -> Real)) (hopen : IsOpen C) (hconv : Convex Real C)
    (hcone : IsCone C) (hsalient : IsSalientCone C)
    (T : SchwartzMap (Fin m -> Real) Complex →L[Complex] Complex)
    (hT : HasFourierSupportInDualCone C T) {y eta : Fin m -> Real}
    (hy : y ∈ closure C) (heta : eta ∈ C) (f : SchwartzMap (Fin m -> Real) Complex) :
    Tendsto (fun t : Real => ∫ x : Fin m -> Real,
      fourierLaplaceExtMultiDim C hopen hconv hcone hsalient T
        (fun i => (x i : Complex) + ((y i + t * eta i : Real) : Complex) * I) * f x)
      (𝓝[>] (0 : Real))
      (𝓝 (T (osiiClosedConeDampedTest C y hy (physicsFourierFlatCLM f) 1))) := by
  let g := osiiClosedConeDampedTest C y hy (physicsFourierFlatCLM f) 1
  have hsupport : ∃ M : Real, ∀ p ∈ Function.support g, -M ≤ conePairingCLM eta p := by
    refine ⟨2 * ‖conePairingCLM eta‖, fun p hp =>
      coneCutoff_pairing_lower_bound (subset_closure heta) ?_⟩
    intro hzero
    exact hp (by simp [g, osiiClosedConeDampedTest_apply C y hy _ zero_lt_one, hzero])
  obtain ⟨gt, hgt, hlim⟩ := schwartz_exp_damping_tendsto g (conePairingCLM eta) hsupport
  apply (T.continuous.tendsto g |>.comp hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  apply (osiiFourierLaplace_slice_pairing C hopen hconv hcone hsalient T hT
    (osiiCone_add_mem_of_closure hopen hconv hcone hy (hcone eta heta t htpos)) f (gt t) ?_).symm
  intro p hp
  rw [hgt t htpos, conePairingCLM_apply,
    osiiClosedConeDampedTest_apply_of_mem_dualCone C y hy _ zero_lt_one hp]
  simp only [Complex.ofReal_one, neg_mul, one_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- Local continuity on the compact support is sufficient for the boundary
integral; the arbitrary totalization outside the analytic domain is irrelevant. -/
theorem osiiContinuousOn_compactIntegral_tendsto
    {X Z : Type*} [TopologicalSpace X] [MeasureSpace X] [OpensMeasurableSpace X]
    [T2Space X] [IsFiniteMeasureOnCompacts (volume : Measure X)] [TopologicalSpace Z]
    {U : Set Z} (hU : IsOpen U) {G : Z -> Complex} (hG : ContinuousOn G U)
    (z : Real × X -> Z) (hz : Continuous z)
    (f : X -> Complex) (hf : Continuous f) (hfcompact : HasCompactSupport f)
    (hmem : ∀ x ∈ tsupport f, z (0, x) ∈ U) :
    Tendsto (fun t : Real => ∫ x : X, G (z (t, x)) * f x)
      (𝓝 0) (𝓝 (∫ x : X, G (z (0, x)) * f x)) := by
  have hnear : ∀ᶠ t in 𝓝 (0 : Real), ∀ x ∈ tsupport f, z (t, x) ∈ U :=
    hfcompact.isCompact.eventually_forall_of_forall_eventually
      (fun x hx => (hz.tendsto (0, x)).eventually (hU.mem_nhds (hmem x hx)))
  obtain ⟨V, hVsub, hVopen, hVzero⟩ := mem_nhds_iff.mp hnear
  have hcont : ContinuousOn
      (Function.uncurry (fun t : Real => fun x : X => G (z (t, x)) * f x)) (V ×ˢ univ) := by
    intro p hp
    by_cases hx : p.2 ∈ tsupport f
    · exact (((hG.continuousAt (hU.mem_nhds (hVsub hp.1 p.2 hx))).comp hz.continuousAt).mul
        (hf.comp continuous_snd).continuousAt).continuousWithinAt
    · have heq : (fun q : Real × X => G (z q) * f q.2) =ᶠ[𝓝 p] fun _ => (0 : Complex) := by
        filter_upwards [(continuous_snd.tendsto p).eventually
          (hfcompact.isCompact.isClosed.isOpen_compl.mem_nhds hx)] with q hq
        rw [image_eq_zero_of_notMem_tsupport hq, mul_zero]
      exact (continuousAt_const.congr heq.symm).continuousWithinAt
  have hIntegral := continuousOn_integral_of_compact_support (μ := volume) hfcompact.isCompact hcont
    (fun t x _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])
  exact (hIntegral 0 hVzero).continuousAt (hVopen.mem_nhds hVzero)

theorem osiiFourierLaplace_closedFace_eq_integral
    (C : Set (Fin m -> Real)) (hopen : IsOpen C) (hconv : Convex Real C)
    (hcone : IsCone C) (hsalient : IsSalientCone C)
    (T : SchwartzMap (Fin m -> Real) Complex →L[Complex] Complex)
    (hT : HasFourierSupportInDualCone C T) {y eta : Fin m -> Real}
    (hy : y ∈ closure C) (heta : eta ∈ C)
    (f : SchwartzMap (Fin m -> Real) Complex) (hf : HasCompactSupport (f : _ -> Complex))
    {U : Set (Fin m -> Complex)} (hU : IsOpen U)
    {G : (Fin m -> Complex) -> Complex} (hG : ContinuousOn G U)
    (hmatch : ∀ z ∈ SCV.TubeDomain C,
      G z = fourierLaplaceExtMultiDim C hopen hconv hcone hsalient T z)
    (hmem : ∀ x ∈ tsupport (f : _ -> Complex),
      (fun i => (x i : Complex) + (y i : Complex) * I) ∈ U) :
    T (osiiClosedConeDampedTest C y hy (physicsFourierFlatCLM f) 1) =
      ∫ x : Fin m -> Real, G (fun i => (x i : Complex) + (y i : Complex) * I) * f x := by
  have hlocal := osiiContinuousOn_compactIntegral_tendsto hU hG
    (fun q : Real × (Fin m -> Real) =>
      fun i => (q.2 i : Complex) + ((y i + q.1 * eta i : Real) : Complex) * I)
    (by fun_prop) f f.continuous hf (by simpa using hmem)
  simp only [zero_mul, add_zero] at hlocal
  have hnative := osiiFourierLaplace_closedFace_boundary C hopen hconv hcone hsalient T hT hy heta f
  apply tendsto_nhds_unique hnative
  apply (hlocal.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply integral_congr_ae
  filter_upwards with x
  rw [hmatch _ (by
    have := osiiCone_add_mem_of_closure hopen hconv hcone hy (hcone eta heta t ht)
    have hpoint : (fun i => y i + t * eta i) ∈ C := by
      change y + t • eta ∈ C
      exact this
    simpa [SCV.TubeDomain] using hpoint)]

end OSReconstruction
