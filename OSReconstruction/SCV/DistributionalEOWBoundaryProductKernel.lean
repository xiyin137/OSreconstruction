/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernel

/-!
# Boundary Product Kernel from the Real-Fiber Integral

This file isolates the algebraic part of the upstream Streater-Wightman
product-kernel construction.  Once the real-fiber integration map is available
as a continuous linear map with its pointwise integral formula, composing it
with the real-convolution shear and the chart boundary distribution gives the
covariant product kernel required by the checked distributional EOW recovery
theorem.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

variable {m : ℕ}

/-- Uniform zeroth-derivative seminorm bound for the real-fiber integral.

This is the base case of the `SchwartzMap.mkCLM` proof for
`complexRealFiberIntegralCLM`.  It strengthens the pointwise decay theorem for
`complexRealFiberIntegralRaw` by making the constant linear in a finite
supremum of Schwartz seminorms of the mixed test function. -/
theorem exists_seminorm_bound_complexRealFiberIntegralRaw_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V]
    (k : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V)
        (z : ComplexChartSpace m),
        ‖z‖ ^ k * ‖complexRealFiberIntegralRaw F z‖ ≤
          C * s.sup
            (schwartzSeminormFamily ℂ
              (ComplexChartSpace m × (Fin m → ℝ)) V) F := by
  let μ : Measure (Fin m → ℝ) := volume
  let s : Finset (ℕ × ℕ) := {(k, 0), (k + μ.integrablePower, 0)}
  let A : ℝ :=
    2 ^ μ.integrablePower *
      ∫ t : Fin m → ℝ, (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))
  refine ⟨s, 2 * A, ?_, ?_⟩
  · dsimp [A]
    positivity
  · intro F z
    let C₁ : ℝ := SchwartzMap.seminorm ℂ k 0 F
    let C₂ : ℝ := SchwartzMap.seminorm ℂ (k + μ.integrablePower) 0 F
    let S : ℝ :=
      s.sup (schwartzSeminormFamily ℂ
        (ComplexChartSpace m × (Fin m → ℝ)) V) F
    have hC₁_le : C₁ ≤ S := by
      have hmem : ((k, 0) : ℕ × ℕ) ∈ s := by simp [s]
      exact (show
        (schwartzSeminormFamily ℂ
          (ComplexChartSpace m × (Fin m → ℝ)) V ((k, 0) : ℕ × ℕ)) F ≤
          S from
        (Finset.le_sup
          (f := schwartzSeminormFamily ℂ
            (ComplexChartSpace m × (Fin m → ℝ)) V) hmem) F)
    have hC₂_le : C₂ ≤ S := by
      have hmem : ((k + μ.integrablePower, 0) : ℕ × ℕ) ∈ s := by simp [s]
      exact (show
        (schwartzSeminormFamily ℂ
          (ComplexChartSpace m × (Fin m → ℝ)) V
            ((k + μ.integrablePower, 0) : ℕ × ℕ)) F ≤
          S from
        (Finset.le_sup
          (f := schwartzSeminormFamily ℂ
            (ComplexChartSpace m × (Fin m → ℝ)) V) hmem) F)
    have hbound :
        ∫ t : Fin m → ℝ, ‖t‖ ^ 0 *
            ‖(‖z‖ ^ k : ℝ) • F (z, t)‖ ∂μ ≤
          A * (C₁ + C₂) := by
      refine integral_pow_mul_le_of_le_of_pow_mul_le (μ := μ) (k := 0)
        (f := fun t : Fin m → ℝ => (‖z‖ ^ k : ℝ) • F (z, t))
        (C₁ := C₁) (C₂ := C₂) ?hf ?hpow
      · intro t
        have hz_norm : ‖z‖ ≤ ‖(z, t)‖ := by
          rw [Prod.norm_def]
          exact le_max_left ‖z‖ ‖t‖
        have hzpow : ‖z‖ ^ k ≤ ‖(z, t)‖ ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) hz_norm _
        have h := SchwartzMap.le_seminorm ℂ k 0 F (z, t)
        have h' : ‖(z, t)‖ ^ k * ‖F (z, t)‖ ≤ C₁ := by
          simpa [C₁] using h
        calc
          ‖(‖z‖ ^ k : ℝ) • F (z, t)‖ =
              ‖z‖ ^ k * ‖F (z, t)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg z) k)]
          _ ≤ ‖(z, t)‖ ^ k * ‖F (z, t)‖ := by
            exact mul_le_mul_of_nonneg_right hzpow (norm_nonneg _)
          _ ≤ C₁ := h'
      · intro t
        have hz_norm : ‖z‖ ≤ ‖(z, t)‖ := by
          rw [Prod.norm_def]
          exact le_max_left ‖z‖ ‖t‖
        have ht_norm : ‖t‖ ≤ ‖(z, t)‖ := by
          rw [Prod.norm_def]
          exact le_max_right ‖z‖ ‖t‖
        have hprod : ‖t‖ ^ (0 + μ.integrablePower) * ‖z‖ ^ k ≤
            ‖(z, t)‖ ^ (k + μ.integrablePower) := by
          have ht_pow :
              ‖t‖ ^ μ.integrablePower ≤ ‖(z, t)‖ ^ μ.integrablePower :=
            pow_le_pow_left₀ (norm_nonneg _) ht_norm _
          have hz_pow : ‖z‖ ^ k ≤ ‖(z, t)‖ ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) hz_norm _
          calc
            ‖t‖ ^ (0 + μ.integrablePower) * ‖z‖ ^ k =
                ‖t‖ ^ μ.integrablePower * ‖z‖ ^ k := by simp
            _ ≤ ‖(z, t)‖ ^ μ.integrablePower * ‖(z, t)‖ ^ k :=
              mul_le_mul ht_pow hz_pow (pow_nonneg (norm_nonneg _) _)
                (pow_nonneg (norm_nonneg _) _)
            _ = ‖(z, t)‖ ^ (k + μ.integrablePower) := by
              rw [← pow_add]
              ring_nf
        have h := SchwartzMap.le_seminorm ℂ (k + μ.integrablePower) 0 F (z, t)
        have h' : ‖(z, t)‖ ^ (k + μ.integrablePower) * ‖F (z, t)‖ ≤ C₂ := by
          simpa [C₂] using h
        calc
          ‖t‖ ^ (0 + μ.integrablePower) *
              ‖(‖z‖ ^ k : ℝ) • F (z, t)‖
              = (‖t‖ ^ (0 + μ.integrablePower) * ‖z‖ ^ k) *
                  ‖F (z, t)‖ := by
                rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg z) k)]
                ring
          _ ≤ ‖(z, t)‖ ^ (k + μ.integrablePower) * ‖F (z, t)‖ :=
            mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
          _ ≤ C₂ := h'
    have hnorm_int :
        ‖complexRealFiberIntegralRaw F z‖ ≤ ∫ t : Fin m → ℝ, ‖F (z, t)‖ := by
      simpa [complexRealFiberIntegralRaw, μ] using
        (norm_integral_le_integral_norm
          (μ := μ) (f := fun t : Fin m → ℝ => F (z, t)))
    calc
      ‖z‖ ^ k * ‖complexRealFiberIntegralRaw F z‖
          ≤ ‖z‖ ^ k * ∫ t : Fin m → ℝ, ‖F (z, t)‖ := by
            gcongr
      _ = ∫ t : Fin m → ℝ, ‖z‖ ^ k * ‖F (z, t)‖ := by
            rw [← integral_const_mul]
      _ = ∫ t : Fin m → ℝ, ‖t‖ ^ 0 *
              ‖(‖z‖ ^ k : ℝ) • F (z, t)‖ ∂μ := by
            apply integral_congr_ae
            filter_upwards with t
            rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg z) k)]
            simp
      _ ≤ A * (C₁ + C₂) := hbound
      _ ≤ A * (2 * S) := by
            gcongr
            linarith
      _ = 2 * A * S := by ring

/-- Precomposition with the base-coordinate inclusion on real-linear maps,
viewed as a complex-linear continuous map because the scalar action is on the
codomain. -/
def basePrecompCLM {m : ℕ}
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] :
    ((ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] V) →L[ℂ]
      (ComplexChartSpace m →L[ℝ] V) := by
  let inl : ComplexChartSpace m →L[ℝ] (ComplexChartSpace m × (Fin m → ℝ)) :=
    ContinuousLinearMap.inl ℝ (ComplexChartSpace m) (Fin m → ℝ)
  let Llin : ((ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] V) →ₗ[ℂ]
      (ComplexChartSpace m →L[ℝ] V) :=
    { toFun := fun T => T.comp inl
      map_add' := by
        intro T U
        ext z
        rfl
      map_smul' := by
        intro c T
        ext z
        rfl }
  exact Llin.mkContinuous 1 (by
    intro T
    have hcomp : ‖T.comp inl‖ ≤ ‖T‖ * ‖inl‖ := T.opNorm_comp_le inl
    have hinl : ‖inl‖ ≤ (1 : ℝ) := by
      simpa [inl] using
        (ContinuousLinearMap.norm_inl_le_one ℝ (ComplexChartSpace m) (Fin m → ℝ))
    calc
      ‖Llin T‖ = ‖T.comp inl‖ := rfl
      _ ≤ ‖T‖ * ‖inl‖ := hcomp
      _ ≤ 1 * ‖T‖ := by
        rw [one_mul]
        exact mul_le_of_le_one_right (norm_nonneg T) hinl
      _ = 1 * ‖T‖ := rfl)

@[simp]
theorem basePrecompCLM_apply {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V]
    (T : (ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] V) :
    basePrecompCLM (m := m) V T =
      T.comp (ContinuousLinearMap.inl ℝ (ComplexChartSpace m) (Fin m → ℝ)) := by
  rfl

/-- The existing base-variable derivative field as a genuine continuous
complex-linear map on mixed Schwartz space. -/
def baseFDerivSchwartzCLM {m : ℕ}
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V] :
    SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V →L[ℂ]
      SchwartzMap (ComplexChartSpace m × (Fin m → ℝ))
        (ComplexChartSpace m →L[ℝ] V) :=
  (SchwartzMap.postcompCLM (basePrecompCLM (m := m) V)).comp
    (SchwartzMap.fderivCLM ℂ
      (ComplexChartSpace m × (Fin m → ℝ)) V)

@[simp]
theorem baseFDerivSchwartzCLM_apply {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V) :
    baseFDerivSchwartzCLM V F = baseFDerivSchwartz F := by
  ext p v
  simp [baseFDerivSchwartzCLM, basePrecompCLM, baseFDerivSchwartz]

/-- Finite-supremum Schwartz seminorms of the base-derivative field are
controlled by finitely many Schwartz seminorms of the original mixed function. -/
theorem exists_seminorm_bound_baseFDerivSchwartz
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V]
    (s0 : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V,
        s0.sup (schwartzSeminormFamily ℂ
          (ComplexChartSpace m × (Fin m → ℝ)) (ComplexChartSpace m →L[ℝ] V))
          (baseFDerivSchwartz F) ≤
        C * s.sup (schwartzSeminormFamily ℂ
          (ComplexChartSpace m × (Fin m → ℝ)) V) F := by
  let D := ComplexChartSpace m × (Fin m → ℝ)
  let L := baseFDerivSchwartzCLM (m := m) V
  let p := schwartzSeminormFamily ℂ D V
  let q := schwartzSeminormFamily ℂ D (ComplexChartSpace m →L[ℝ] V)
  have hbounded : Seminorm.IsBounded p q L.toLinearMap := by
    intro i
    let qi : Seminorm ℂ (SchwartzMap D V) := (q i).comp L.toLinearMap
    have hqi_cont : Continuous qi := by
      exact ((schwartz_withSeminorms ℂ D
        (ComplexChartSpace m →L[ℝ] V)).continuous_seminorm i).comp L.continuous
    obtain ⟨s, C, _hCne, hbound⟩ :=
      Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ D V) qi hqi_cont
    exact ⟨s, C, hbound⟩
  obtain ⟨Cnn, s, hsup⟩ := Seminorm.isBounded_sup hbounded s0
  refine ⟨s, (Cnn : ℝ), Cnn.2, ?_⟩
  intro F
  have h := Seminorm.le_def.mp hsup F
  simpa [L, p, q] using h

/-- Uniform finite-seminorm bound for every base derivative of the real-fiber
integral.  This is the analytic estimate needed by `SchwartzMap.mkCLM` for the
continuous linear real-fiber integration map. -/
theorem exists_seminorm_bound_complexRealFiberIntegralRaw_deriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V]
    (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V)
        (z : ComplexChartSpace m),
        ‖z‖ ^ k *
          ‖iteratedFDeriv ℝ n (complexRealFiberIntegralRaw F) z‖ ≤
        C * s.sup
          (schwartzSeminormFamily ℂ
            (ComplexChartSpace m × (Fin m → ℝ)) V) F := by
  induction n generalizing V with
  | zero =>
      obtain ⟨s, C, hC, hbound⟩ :=
        exists_seminorm_bound_complexRealFiberIntegralRaw_zero (m := m) (V := V) k
      refine ⟨s, C, hC, ?_⟩
      intro F z
      simpa [norm_iteratedFDeriv_zero] using hbound F z
  | succ n ih =>
      obtain ⟨s0, C0, hC0, hIH⟩ :=
        ih (V := ComplexChartSpace m →L[ℝ] V)
      obtain ⟨s, C1, hC1, hbase⟩ :=
        exists_seminorm_bound_baseFDerivSchwartz (m := m) (V := V) s0
      refine ⟨s, C0 * C1, mul_nonneg hC0 hC1, ?_⟩
      intro F z
      calc
        ‖z‖ ^ k *
            ‖iteratedFDeriv ℝ (n + 1) (complexRealFiberIntegralRaw F) z‖
            = ‖z‖ ^ k *
                ‖iteratedFDeriv ℝ n
                  (fderiv ℝ (complexRealFiberIntegralRaw F)) z‖ := by
              rw [norm_iteratedFDeriv_fderiv]
        _ = ‖z‖ ^ k *
              ‖iteratedFDeriv ℝ n
                (complexRealFiberIntegralRaw (baseFDerivSchwartz F)) z‖ := by
              rw [fderiv_complexRealFiberIntegralRaw_eq]
        _ ≤ C0 * s0.sup
              (schwartzSeminormFamily ℂ
                (ComplexChartSpace m × (Fin m → ℝ))
                (ComplexChartSpace m →L[ℝ] V)) (baseFDerivSchwartz F) :=
            hIH (baseFDerivSchwartz F) z
        _ ≤ C0 * (C1 * s.sup
              (schwartzSeminormFamily ℂ
                (ComplexChartSpace m × (Fin m → ℝ)) V) F) := by
            gcongr
            exact hbase F
        _ = (C0 * C1) * s.sup
              (schwartzSeminormFamily ℂ
                (ComplexChartSpace m × (Fin m → ℝ)) V) F := by
            ring

/-- Real-fiber integration over the local chart real direction as a continuous
complex-linear map of Schwartz spaces. -/
noncomputable def complexRealFiberIntegralCLM {m : ℕ} :
    SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m) ℂ :=
  SchwartzMap.mkCLM (𝕜 := ℂ) (𝕜' := ℂ)
    (fun F z => ∫ t : Fin m → ℝ, F (z, t))
    (fun F G z => by
      simpa using
        (integral_add (integrable_complexRealFiber F z) (integrable_complexRealFiber G z)))
    (fun a F z => by
      simpa using
        (integral_const_mul (μ := (volume : Measure (Fin m → ℝ))) a
          (fun t : Fin m → ℝ => F (z, t))))
    (fun F => contDiff_complexRealFiberIntegralRaw F)
    (fun kn => by
      rcases kn with ⟨k, n⟩
      simpa using
        (exists_seminorm_bound_complexRealFiberIntegralRaw_deriv (m := m) (V := ℂ) k n))

@[simp]
theorem complexRealFiberIntegralCLM_apply {m : ℕ}
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (z : ComplexChartSpace m) :
    complexRealFiberIntegralCLM F z = ∫ t : Fin m → ℝ, F (z, t) := by
  rfl

@[simp]
theorem complexRealFiberIntegralCLM_eq_complexRealFiberIntegral {m : ℕ}
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    complexRealFiberIntegralCLM F = complexRealFiberIntegral F := by
  ext z
  rfl

/-- If real-fiber integration has been constructed as a continuous linear map,
then every chart boundary distribution gives the canonical product kernel
`K F = Tchart (∫ t, F (z - t,t))`.  On product tests this kernel is exactly
`Tchart (realConvolutionTest φ ψ)`, and product covariance is the checked
real-convolution translation identity.

The remaining analytic task is constructing the `I` supplied here from
`complexRealFiberIntegral`; this theorem is the algebraic consumer of that
construction. -/
theorem boundaryProductKernel_from_fiberIntegralCLM
    (I : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m) ℂ)
    (hI_apply :
      ∀ (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
        (z : ComplexChartSpace m),
        I F z = ∫ t : Fin m → ℝ, F (z, t))
    (Tchart : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ) :
    ∃ K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ,
      ProductKernelRealTranslationCovariantGlobal K ∧
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        K (schwartzTensorProduct₂ φ ψ) =
          Tchart (realConvolutionTest φ ψ) := by
  let shearCLM :
      SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ]
        SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realConvolutionShearCLE m)
  let K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ :=
    Tchart.comp (I.comp shearCLM)
  have hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        K (schwartzTensorProduct₂ φ ψ) =
          Tchart (realConvolutionTest φ ψ) := by
    intro φ ψ
    suffices
        I (shearCLM (schwartzTensorProduct₂ φ ψ)) =
          realConvolutionTest φ ψ by
      simpa [K, shearCLM] using congrArg Tchart this
    ext z
    simp [hI_apply, shearCLM, realConvolutionTest, complexRealFiberIntegral_apply]
  refine ⟨K, ?_, hK_rep⟩
  intro a φ ψ
  calc
    K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ)
        = Tchart (realConvolutionTest (complexTranslateSchwartz a φ) ψ) :=
          hK_rep (complexTranslateSchwartz a φ) ψ
    _ = Tchart (realConvolutionTest φ (translateSchwartz a ψ)) := by
          rw [realConvolutionTest_complexTranslate_eq_translateSchwartz]
    _ = K (schwartzTensorProduct₂ φ (translateSchwartz a ψ)) :=
          (hK_rep φ (translateSchwartz a ψ)).symm

/-- The unconditional boundary product kernel obtained from the checked
real-fiber integration continuous linear map. -/
theorem boundaryProductKernel_from_complexRealFiberIntegralCLM
    (Tchart : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ) :
    ∃ K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ,
      ProductKernelRealTranslationCovariantGlobal K ∧
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        K (schwartzTensorProduct₂ φ ψ) =
          Tchart (realConvolutionTest φ ψ) := by
  exact boundaryProductKernel_from_fiberIntegralCLM
    (I := complexRealFiberIntegralCLM) (by intro F z; rfl) Tchart

end SCV
